-- Prove2me | solution 1 for LinearSetReconciliation327.Main.conjunct8_topDec
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-21T10:25:50.442185+00:00
-- url     : https://prove2.me/submissions/473a90c0-119c-4c06-ad75-28ab9d6115b9

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Top65Correct

/-!
# `_65_correct_block` — Theorem 6.5, conjunct 8: the top-level decoder's correctness

This block states `TopDecCorrects` precisely (per seed, worst case, no probability), proves it from
the six per-stage `StageRun`s of §9.2, and derives the platform's conjunct 8 from it (probability
over the seed, with `ε` entering only through the stages, never through the composition).

What is *proved* here (every goal closed, no new axiom):

* §1 the bridge between the machine's explicit output list and `OutputsSupport`
  (`OutListIs`, `outputsSupport_iff_outListIs`);
* §2 the two payload predicates a stage hands over (`HoldsVec`, `DecInputAt`);
* §3 the residual step `x̂ + ê = x` at one node (`residual_sketch`, from `CR.Recovers` and
  additivity of the syndrome) and the column-bit step `P_s + D̂_s = C_s(x)`
  (`column_add_childInput`), plus `assembled_truePrefix`;
* §4 `hint_decode_correct` at each child (`child_decode_exact`) — the tree's recovery law *used*,
  never re-derived;
* §5 the six stage contracts in data-carrying form (`TopDecStages`) and their composition
  (`topDecCorrects_of_stages`): the six runs chain into one, and the final `x̂ + (x + x̂) = x`
  turns the CR stage's output into `OutputsSupport s' x`;
* §6 the seed-indexed correctness (`TopDecCorrectsSeed`), the probability form
  (`conjunct8_of_seedCorrects`) and conjunct 8 of `theorem_6_5` (`conjunct8_topDec`).

Nothing here re-derives `Node.decode`: the tree's recovery law is *used* — `hint_decode_correct`
at each child, `CR.Recovers` at the residual.

Imports: only `Mathlib` and `Definitions.Def_…_Top65Correct`, which supplies `StageRun`,
`progDecOfTop` and its address algebra, `TopDecCorrects`, `TopDecCorrectsEnv`,
`conjunct8_of_correctsEnv`, `C65.sketch_symmDiff`, `C65.symmDiff_self_cancel`,
`C65.symmDiff_subset_range`, `decode_of_allValid` and `allValid_of_valid`.
-/


open scoped ENNReal
open Finset

set_option autoImplicit false

noncomputable section

namespace LinearSetReconciliation327.Main

/-! ## 0. `halt` facts

`Sol_theorem_6_5.lean` §11.4 proves these, but it is not importable (`import Solutions.*` is
banned) and `Def_…_Top65Dec` keeps its own copies inside proof bodies.  They are needed here to
identify the two halting runs from the same start state, so they are re-proved. -/

/-- A `halt` is a fixed point of `step`. -/
theorem step_halt_self {P : Program} {E : RAMEnv} {s : RAMState} (h : P[s.pc]? = some .halt) :
    step P E s = s := by
  simp [step, h]

/-- A run that reaches a `halt` never moves again. -/
theorem step_iterate_halt {P : Program} {E : RAMEnv} {s : RAMState}
    (h : P[s.pc]? = some .halt) (k : ℕ) : (step P E)^[k] s = s := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show (step P E)^[k + 1] s = s
      rw [Function.iterate_succ_apply, step_halt_self h, ih]

/-- `Halted` is "the program counter holds a `halt`". -/
theorem halted_iff {P : Program} {s : RAMState} : Halted P s ↔ P[s.pc]? = some .halt := by
  unfold Halted
  cases h : P[s.pc]? with
  | none => simp
  | some i => cases i <;> simp

/-- The trailing `halt` of the composite decoder sits at `dEnd`. -/
theorem halt_at_dEnd {Sinit Srow Sdec Sassem Sres Scr : Stmt} :
    (progDecOfTop Sinit Srow Sdec Sassem Sres Scr)[dEnd Sinit Srow Sdec Sassem Sres Scr]? =
      some Instr.halt := by
  have hlen : dEnd Sinit Srow Sdec Sassem Sres Scr =
      ((topDecStmt Sinit Srow Sdec Sassem Sres Scr).compile 0).length := by
    rw [Stmt.length_compile]
    simp only [dEnd, dCrBase, dResBase, dAsBase, dColBase, dRowBase, topDecStmt, topLoop, Stmt.len]
    omega
  rw [hlen]
  rw [show progDecOfTop Sinit Srow Sdec Sassem Sres Scr =
      (topDecStmt Sinit Srow Sdec Sassem Sres Scr).compile 0 ++ [Instr.halt] from rfl,
    List.getElem?_append_right (le_refl _)]
  simp

namespace C8

/-! ## 1. Explicit lists, supports, and the bridge to `OutputsSupport` -/

/-- The `0/1` vector of a set of coordinates (the canonical vector of a `Finset ℕ`). -/
def setVec (N : ℕ) (S : Finset ℕ) : Fin N → ZMod 2 := fun i => if (i : ℕ) ∈ S then 1 else 0

theorem setVec_eq_one {N : ℕ} {S : Finset ℕ} {i : Fin N} :
    setVec N S i = 1 ↔ (i : ℕ) ∈ S := by
  unfold setVec
  by_cases h : (i : ℕ) ∈ S <;> simp [h]

/-- Membership in the support of a vector, in the form `OutputsSupport` uses. -/
theorem mem_support {n : ℕ} (x : Fin n → ZMod 2) (v : ℕ) :
    v ∈ C65.support x ↔ ∃ i : Fin n, (i : ℕ) = v ∧ x i = 1 := by
  rw [C65.support, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, hv⟩
    exact ⟨i, hv, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i, hv, hx⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, hv⟩

/-- A list is an enumeration of the set `S`: duplicate-free with exactly `S`'s members. -/
def Lists (L : List ℕ) (S : Finset ℕ) : Prop := L.Nodup ∧ ∀ v : ℕ, v ∈ L ↔ v ∈ S

/-- The state's explicit output list enumerates `S`. -/
def OutListIs (s : RAMState) (S : Finset ℕ) : Prop := Lists (outList s) S

/-- **The bridge**: "the decoder outputs the support of `x`" is exactly "its output list
enumerates `supp x`".  Every correctness statement below is proved in the `OutListIs` vocabulary
and transported by this equivalence. -/
theorem outputsSupport_iff_outListIs {n : ℕ} (s : RAMState) (x : Fin n → ZMod 2) :
    OutputsSupport s x ↔ OutListIs s (C65.support x) := by
  unfold OutputsSupport OutListIs Lists
  constructor
  · rintro ⟨hnd, hmem⟩
    exact ⟨hnd, fun v => (hmem v).trans (mem_support x v).symm⟩
  · rintro ⟨hnd, hmem⟩
    exact ⟨hnd, fun v => (hmem v).trans (mem_support x v)⟩

/-- **The estimate §9.2's assembly must produce**, as one symbol: `x̂` of `Definition 4.7` at the
support of `x`. -/
def xhatOf (sch : RowScheme) (lr : sch.LocalSeed) (J : Finset ℕ) {n : ℕ}
    (x : Fin n → ZMod 2) : Finset ℕ :=
  sch.exactEstimate lr (C65.support x) J

/-! ## 2. The two payloads a stage hands to the next one -/

/-- The words `[base, base + wordsOf W M)` of `s` are the packed vector `y` (nothing is said about
the rest of memory).  This is the payload representation of `packMem`. -/
def HoldsVec (W M : ℕ) (base : ℕ) (s : RAMState) (y : Fin M → ZMod 2) : Prop :=
  ∀ j : ℕ, j < wordsOf W M → s.mem (base + j) = packMem W y j

/-- **A decoder's input state**, exactly as `decoderStart` lays it out: the hinted payload at word
`0`, the hint length in register `2`, the payload length in register `1`, register `0` zero.  This
is the precondition of `proposition_2_1`'s, `theorem_5_1`'s and `proposition_2_3`'s decoders, so it
is what `Sinit`, `Sres` and `Scr` must produce/consume. -/
def DecInputAt (W M : ℕ) (y : Fin M → ZMod 2) (Jl : List ℕ) (s : RAMState) : Prop :=
  (∀ j : ℕ, s.mem j = hintMem W y Jl j) ∧ s.regs 0 = 0 ∧ s.regs 1 = wordsOf W M ∧
    s.regs 2 = Jl.length

/-- `decoderStart` satisfies `DecInputAt` — so the predicate is not vacuous. -/
theorem decInputAt_decoderStart (W M : ℕ) (y : Fin M → ZMod 2) (Jl : List ℕ) :
    DecInputAt W M y Jl (decoderStart W y Jl) := by
  refine ⟨fun j => rfl, ?_, ?_, ?_⟩ <;> simp [decoderStart, initState]

/-! ## 3. The proved recovery laws this block consumes

Three steps of §9.2's argument are pure algebra on the abstract data, and are proved here.  They
are the *only* abstract content the composition needs; the tree's own recovery law is not
re-derived anywhere. -/

/-- `CR`'s syndrome is additive, in the orientation the residual uses
(restated from `C65.sketch_symmDiff`). -/
theorem sketch_symmDiff' (CR : CRFamily) (N t : ℕ) (x y : Finset ℕ) :
    symmDiff (CR.sketch N t x) (CR.sketch N t y) = CR.sketch N t (symmDiff x y) :=
  (C65.sketch_symmDiff CR N t x y).symm

/-- **The residual step, proved.**  Forming `a + CR x̂` from the stored syndrome `a = CR x` and
recovering it with `CR.Recovers` returns `x` — i.e. `x̂ + ê = x`, with `ê` the decoded residual.
This is `Node.residual` at one node; it uses only `CR.Recovers` and additivity of the syndrome, and
is where "residual, CR recovery reconstruct `x`" is closed. -/
theorem residual_sketch {CR : CRFamily} (hRec : CR.Recovers) {N t : ℕ} {x xhat : Finset ℕ}
    (hx : x ⊆ Finset.range N) (hxhat : xhat ⊆ Finset.range N) (ht : t ≤ N)
    (hZ : (symmDiff x xhat).card ≤ t) :
    Node.residual CR N t (CR.sketch N t x) xhat = some x := by
  have hsub : symmDiff x xhat ⊆ Finset.range N := C65.symmDiff_subset_range hx hxhat
  have hdec : CR.dec N t (CR.sketch N t (symmDiff x xhat)) = some (symmDiff x xhat) :=
    hRec N t ht (symmDiff x xhat) hsub hZ
  unfold Node.residual
  rw [sketch_symmDiff' CR N t x xhat, hdec, Option.map_some, Option.some.injEq]
  exact C65.symmDiff_self_cancel xhat x

/-- **The column-bit step, proved.**  Once the child of column `s` returns the exact child input
`D̂_s = C_s(x) + P_s`, the bit the manager appends for worker `j` — `1 ⟺ j ∈ P_s + D̂_s` — is the
true column bit `C_s(x)_j`.  (In the paper's notation: `P_s + D̂_s = C_s`.) -/
theorem column_add_childInput (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (s : Fin sch.ℓ) :
    symmDiff (sch.exactP lr x J s) (sch.exactChildInput lr x J s) = sch.column lr x s := by
  unfold RowScheme.exactChildInput
  exact C65.symmDiff_self_cancel (sch.exactP lr x J s) (sch.column lr x s)

/-- **The assembly step, proved.**  Assembling the exact row transcripts gives the exact estimate
`x̂` of `Definition 4.7`.  (Definitional, but it is the interface `Sassem` must meet.) -/
theorem assembled_truePrefix (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ) :
    sch.assembled lr J (fun j => sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) sch.ℓ) =
      sch.exactEstimate lr x J := rfl

/-- The exact estimate lies in the universe (from `C65.assembled_subset_range`). -/
theorem exactEstimate_subset (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ) :
    sch.exactEstimate lr x J ⊆ Finset.range sch.N :=
  C65.assembled_subset_range sch lr J _

/-- **Assembly + residual + CR recovery, end to end, at the abstract level.**  Given the exact row
prefixes, `Sassem`'s estimate is `x̂`; if the residual weight `Z = ‖x + x̂‖₀` is within `t`, then
decoding `a + CR x̂` returns `x`.  This is the paper's last three steps (`Algorithm 1`, lines
"assemble", "x̂ + ê") as one statement: `assembled_truePrefix` composed with `residual_sketch`. -/
theorem assembled_residual_exact {CR : CRFamily} (hRec : CR.Recovers) (sch : RowScheme)
    (lr : sch.LocalSeed) (J : Finset ℕ) {x : Finset ℕ} {t : ℕ}
    (hx : x ⊆ Finset.range sch.N) (ht : t ≤ sch.N)
    (hZ : (symmDiff x (sch.exactEstimate lr x J)).card ≤ t) :
    Node.residual CR sch.N t (CR.sketch sch.N t x)
        (sch.assembled lr J (fun j => sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) sch.ℓ)) =
      some x := by
  rw [assembled_truePrefix]
  exact residual_sketch hRec hx (exactEstimate_subset sch lr x J) ht hZ

/-! ## 4. `hint_decode_correct` at each child: the child decoders give the column bits -/

/-- **The child-decode step, from the platform's proved recovery law.**  At a `recursive` node the
child of column `s` decodes the sketch of the exact child input `C_s(x) + P_s` with the exact hint
`J_s`, and returns `C_s(x) + P_s`.

This is `hint_decode_correct` (`decode_of_allValid`) instantiated at the child; the node's `WF`,
the root's `Valid` and `AllBounds` supply the child's hypotheses, with `allValid_of_valid` turning
the root's `Valid` into `AllValid` at every node.  It is the only use of the tree's recovery law at
the child level, and it is a direct application. -/
theorem child_decode_exact {CR : CRFamily} (hRec : CR.Recovers)
    {sch : RowScheme} {t Xs Ys : ℕ} {child : Fin sch.ℓ → Node} {X Y : ℕ}
    {r : sch.LocalSeed × ∀ s : Fin sch.ℓ, Node.Seed (child s)} {x J : Finset ℕ}
    (hWF : Node.WF (Node.recursive sch t Xs Ys child) X Y)
    (hB : Node.AllBounds (Node.recursive sch t Xs Ys child) r x J)
    (hV : Node.Valid sch.N X Y x J) (s : Fin sch.ℓ) :
    Node.decode CR (child s) (r.2 s)
      (Node.sketch CR (child s) (r.2 s) (sch.exactChildInput r.1 x J s))
      (sch.exactHint r.1 x J s) = some (sch.exactChildInput r.1 x J s) := by
  have hAV : AllValid X Y (Node.recursive sch t Xs Ys child) r x J :=
    allValid_of_valid (Node.recursive sch t Xs Ys child) X Y r x J hWF hB hV
  exact decode_of_allValid hRec (hWF.2 s).2 (hB.2 s).2.2 (hAV.2 s)

/-! ## 5. The six stage contracts, carrying their data -/

/-- Weakening a stage's postcondition. -/
theorem stageRun_post {P : Program} {E : RAMEnv} {a b : ℕ} {T : ℝ} {I Q Q' : RAMState → Prop}
    (h : StageRun P E a b T I Q) (hQ : ∀ s, Q s → Q' s) : StageRun P E a b T I Q' := by
  intro s hpc hI
  obtain ⟨k, s', hk, hstep, hb, hQ'⟩ := h s hpc hI
  exact ⟨k, s', hk, hstep, hb, hQ s' hQ'⟩

/-- Weakening a stage's precondition. -/
theorem stageRun_pre {P : Program} {E : RAMEnv} {a b : ℕ} {T : ℝ} {I I' Q : RAMState → Prop}
    (h : StageRun P E a b T I' Q) (hI : ∀ s, I s → I' s) : StageRun P E a b T I Q := by
  intro s hpc hI'
  exact h s hpc (hI s hI')

/-- **The six stage contracts of §9.2's decoder, in data-carrying form.**

`Sinit → loop Srow (d rows) → loop Sdec (ℓ columns) → Sassem → Sres → Scr`, one `StageRun` per
block, at the addresses `compile` gives them (`dRowBase`, …, `dEnd`).  Unlike `TopDecRuns` — whose
four middle postconditions are `fun _ => True` and which therefore composes to conjunct 7 only —
each field here carries the data it hands to the next block, so the chain composes to *correctness*.

Three payloads are fixed by this block (they are what the sub-decoders consume and produce):

* `HoldsVec E.W sch.N xhatBase (setVec sch.N (xhatOf sch lr J x))` — the recovered estimate `x̂`,
  packed at the word base `xhatBase`;
* `DecInputAt E.W (CR.rows sch.N t) (setVec … (CR.sketch … S)) []` — a state laid out exactly like
  `decoderStart`, i.e. the input `proposition_2_3`'s decoder consumes;
* `OutListIs s' (symmDiff (xhatOf …) S)` — the halted state's explicit output list.

The row-support and prefix buffers are deliberately *open*: `RowOut` and `ColOut` are parameters,
shared by `row`/`col` and by `col`/`as` respectively, so the three not-yet-written blocks have a
precise interface to be proved against.  `RowOut` must also record the counter state the column
loop needs (`ColIn`), which is why the row stage's postcondition is `RowOut ∧ ColIn`. -/
structure TopDecStages (Sinit Srow Sdec Sassem Sres Scr : Stmt) (E : RAMEnv) (sch : RowScheme)
    (lr : sch.LocalSeed) {M : ℕ} (J : Finset ℕ)
    (D : (Fin sch.N → ZMod 2) → Fin M → ZMod 2)
    (RowOut : RAMState → Prop) (ColOut : RAMState → (Fin sch.m → List (ZMod 2)) → Prop)
    (xhatBase : ℕ) (CR : CRFamily) (t : ℕ) (x : Fin sch.N → ZMod 2)
    (Tini Trow Tdec Tas Tres Tcr : ℝ) : Prop where
  /-- **`Sinit`**, the prologue: from `decoderStart` to the row loop's head.  *Program missing.* -/
  init : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E 0 (dRowBase Sinit) Tini
    (fun s => s = decoderStart E.W (D x) []) (RowIn sch.m)
  /-- **`Srow`**, `d` calls of Proposition 2.1's decoder: its output is the row supports, in the
  `RowOut` layout, with the column loop armed.  *2.1's `down` contract + missing dispatcher.* -/
  row : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dRowBase Sinit)
    (dColBase Sinit Srow) Trow (RowIn sch.m) (fun s => RowOut s ∧ ColIn sch.ℓ s)
  /-- **`Sdec`**, the `ℓ` child decoders of Theorem 5.1 and the prefix prediction: its output is the
  buffer of exact row transcripts `truePrefix j (lr.2 j) (rowOf lr (supp x) j) ℓ`.
  *5.1's `down` export + missing dispatcher; per-child exactness is `child_decode_exact`.* -/
  col : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dColBase Sinit Srow)
    (dAsBase Sinit Srow Sdec) Tdec (fun s => RowOut s ∧ ColIn sch.ℓ s)
    (fun s => ColOut s
      (fun j => sch.truePrefix j (lr.2 j) (sch.rowOf lr (C65.support x) j) sch.ℓ))
  /-- **`Sassem`**, prefix assembly: from a prefix buffer it builds `x̂ = RowScheme.assembled`.
  *Program missing.* -/
  as : ∀ pref : Fin sch.m → List (ZMod 2),
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dAsBase Sinit Srow Sdec)
      (dResBase Sinit Srow Sdec Sassem) Tas (fun s => ColOut s pref)
      (fun s => HoldsVec E.W sch.N xhatBase s (setVec sch.N (sch.assembled lr J pref)))
  /-- **`Sres`**, residual-syndrome formation: form `a + CR x̂` from the stored `a = CR x` and the
  recovered `x̂`, and leave it where `proposition_2_3`'s decoder reads it, *without disturbing the
  estimate* (the frame conjunct: `Scr` still needs `x̂` for the final merge).  *Program missing.*
  Note that `a + CR x̂ = CR (x + x̂)` is *not* assumed: the postcondition is the literal
  `CR x + CR x̂`, and §5 rewrites it with the proved `sketch_symmDiff'`. -/
  res : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dResBase Sinit Srow Sdec Sassem)
    (dCrBase Sinit Srow Sdec Sassem Sres) Tres
    (fun s => HoldsVec E.W sch.N xhatBase s (setVec sch.N (xhatOf sch lr J x)))
    (fun s => DecInputAt E.W (CR.rows sch.N t)
        (setVec (CR.rows sch.N t)
          (symmDiff (CR.sketch sch.N t (C65.support x))
            (CR.sketch sch.N t (xhatOf sch lr J x)))) [] s ∧
      HoldsVec E.W sch.N xhatBase s (setVec sch.N (xhatOf sch lr J x)))
  /-- **`Scr`**, Proposition 2.3's decoder at a *generic* sparse `S`, plus the final merge
  `x̂ + ê`: from the residual's syndrome and the recovered `x̂`, it halts with the output list of
  `x̂ + S`.  *2.3's decoder export + the merge.* -/
  cr : ∀ S : Finset ℕ,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dCrBase Sinit Srow Sdec Sassem Sres)
      (dEnd Sinit Srow Sdec Sassem Sres Scr) Tcr
      (fun s => DecInputAt E.W (CR.rows sch.N t)
          (setVec (CR.rows sch.N t) (CR.sketch sch.N t S)) [] s ∧
        HoldsVec E.W sch.N xhatBase s (setVec sch.N (xhatOf sch lr J x)))
      (fun s => OutListIs s (symmDiff (xhatOf sch lr J x) S))

/-- **`TopDecCorrects`, proved from the six stages.**  The six `StageRun`s chain into one, the
residual stage's payload is rewritten to the syndrome of the *true* error `x + x̂`
(`sketch_symmDiff'`), the CR stage decodes it, and the final merge is the symmetric difference
`x̂ + (x + x̂) = x` (`C65.symmDiff_self_cancel`).  The budget is `Tini + Trow + Tdec + Tas + Tres +
Tcr`, i.e. conjunct 7's `haltsWithin_topDec_final` shape on the nose. -/
theorem topDecCorrects_of_stages {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {M : ℕ} {sch : RowScheme} {lr : sch.LocalSeed} {J : Finset ℕ}
    {D : (Fin sch.N → ZMod 2) → Fin M → ZMod 2}
    {RowOut : RAMState → Prop} {ColOut : RAMState → (Fin sch.m → List (ZMod 2)) → Prop}
    {xhatBase : ℕ} {CR : CRFamily} {t : ℕ}
    {Tini Trow Tdec Tas Tres Tcr : ℝ}
    (h : ∀ x : Fin sch.N → ZMod 2,
      TopDecStages Sinit Srow Sdec Sassem Sres Scr E sch lr J D RowOut ColOut xhatBase CR t x
        Tini Trow Tdec Tas Tres Tcr) :
    TopDecCorrects Sinit Srow Sdec Sassem Sres Scr E D
      (Tini + Trow + Tdec + Tas + Tres + Tcr) := by
  intro x s' ⟨k, hk, hstep, hhalt⟩
  obtain hS := h x
  -- the residual stage, with its payload rewritten to the syndrome of the true error `x + x̂`
  have hres : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
      (dResBase Sinit Srow Sdec Sassem) (dCrBase Sinit Srow Sdec Sassem Sres) Tres
      (fun s => HoldsVec E.W sch.N xhatBase s (setVec sch.N (xhatOf sch lr J x)))
      (fun s => DecInputAt E.W (CR.rows sch.N t)
          (setVec (CR.rows sch.N t)
            (CR.sketch sch.N t (symmDiff (C65.support x) (xhatOf sch lr J x)))) [] s ∧
        HoldsVec E.W sch.N xhatBase s (setVec sch.N (xhatOf sch lr J x))) := by
    have h0 := hS.res
    rw [sketch_symmDiff' CR sch.N t (C65.support x) (xhatOf sch lr J x)] at h0
    exact h0
  -- the whole chain
  have hchain : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E 0
      (dEnd Sinit Srow Sdec Sassem Sres Scr)
      (Tini + Trow + Tdec + Tas + Tres + Tcr)
      (fun s => s = decoderStart E.W (D x) [])
      (fun s => OutListIs s
        (symmDiff (xhatOf sch lr J x) (symmDiff (C65.support x) (xhatOf sch lr J x)))) :=
    ((((hS.init.trans hS.row).trans hS.col).trans
        (hS.as (fun j => sch.truePrefix j (lr.2 j) (sch.rowOf lr (C65.support x) j) sch.ℓ))).trans
        hres).trans
      (hS.cr (symmDiff (C65.support x) (xhatOf sch lr J x)))
  obtain ⟨k', s₁, hk', hrun, hpc, hQ⟩ := hchain (decoderStart E.W (D x) []) rfl rfl
  -- the two halting runs from the same start coincide
  have hhalt₁ : (progDecOfTop Sinit Srow Sdec Sassem Sres Scr)[s₁.pc]? = some Instr.halt := by
    rw [hpc]
    exact halt_at_dEnd
  have hs'h : (progDecOfTop Sinit Srow Sdec Sassem Sres Scr)[s'.pc]? = some Instr.halt :=
    halted_iff.mp hhalt
  have hEq : s' = s₁ := by
    rcases le_total k k' with hle | hle
    · have hk'k : k' - k + k = k' := Nat.sub_add_cancel hle
      have h1 : s₁ = (step (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E)^[k' - k] s' := by
        rw [← hrun, ← hstep, ← Function.iterate_add_apply, hk'k]
      rw [h1, step_iterate_halt hs'h]
    · have hkk : k - k' + k' = k := Nat.sub_add_cancel hle
      have h1 : s' = (step (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E)^[k - k'] s₁ := by
        rw [← hstep, ← hrun, ← Function.iterate_add_apply, hkk]
      rw [h1, step_iterate_halt hhalt₁]
  subst hEq
  refine outputsSupport_iff_outListIs s' x |>.mpr ?_
  rw [show symmDiff (xhatOf sch lr J x) (symmDiff (C65.support x) (xhatOf sch lr J x)) =
      C65.support x from C65.symmDiff_self_cancel _ _] at hQ
  exact hQ

/-! ## 6. Conjunct 8: the seed-indexed form, and the platform's statement

`theorem_6_5` runs its decoder under `spec.env W det r` and its payload is `H r x`, so *both* the
environment and the payload depend on the seed.  `TopDecCorrectsEnv` (`Def_…_Top65Correct` §4)
indexes only the environment (`D : (Fin n → ZMod 2) → Fin M → ZMod 2` is seed-independent), which
is not the 6.5 instance; `TopDecCorrectsSeed` below indexes both, and is what §5 proves.
`TopDecCorrectsEnv` is its constant-`D` special case (`topDecCorrectsEnv_of_seed`), so nothing is
lost and `conjunct8_of_correctsEnv` becomes an instance of `conjunct8_of_seedCorrects`. -/

/-- **The correctness half of conjunct 8, per seed, worst case, no probability**: the environment
*and* the payload are indexed by the seed. -/
def TopDecCorrectsSeed {ι : Type} (Sinit Srow Sdec Sassem Sres Scr : Stmt) (env : ι → RAMEnv)
    {n M : ℕ} (D : ι → (Fin n → ZMod 2) → Fin M → ZMod 2) (Tdec : ℝ) : Prop :=
  ∀ (i : ι) (x : Fin n → ZMod 2) (s' : RAMState),
    (∃ k : ℕ, (k : ℝ) ≤ Tdec ∧
      (step (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (env i))^[k]
        (decoderStart (env i).W (D i x) []) = s' ∧
      Halted (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) s') →
    OutputsSupport s' x

/-- The fixed-payload environment form is the seed-indexed form at a constant `D`. -/
theorem topDecCorrectsSeed_of_env {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {n M : ℕ} {D : (Fin n → ZMod 2) → Fin M → ZMod 2} {Tdec : ℝ}
    (h : TopDecCorrects Sinit Srow Sdec Sassem Sres Scr E D Tdec) :
    TopDecCorrectsSeed Sinit Srow Sdec Sassem Sres Scr (fun _ : Unit => E) (fun _ => D) Tdec := by
  intro i x s' hs'
  exact h x s' hs'

/-- Conversely, the seed-indexed form at a constant `D` *is* `TopDecCorrectsEnv`. -/
theorem topDecCorrectsEnv_of_seed {ι : Type} {Sinit Srow Sdec Sassem Sres Scr : Stmt}
    {env : ι → RAMEnv} {n M : ℕ} {D : (Fin n → ZMod 2) → Fin M → ZMod 2} {Tdec : ℝ}
    (h : TopDecCorrectsSeed Sinit Srow Sdec Sassem Sres Scr env (fun _ => D) Tdec) :
    TopDecCorrectsEnv Sinit Srow Sdec Sassem Sres Scr env D Tdec := by
  intro i x s' hs'
  exact h i x s' hs'

/-- **`TopDecCorrectsSeed` from the six stages**, uniformly over the seeds of the family. -/
theorem topDecCorrectsSeed_of_stages {ι : Type} {Sinit Srow Sdec Sassem Sres Scr : Stmt}
    {env : ι → RAMEnv} {M : ℕ} {sch : RowScheme} (lr : ι → sch.LocalSeed) {J : Finset ℕ}
    (D : ι → (Fin sch.N → ZMod 2) → Fin M → ZMod 2)
    (RowOut : ι → RAMState → Prop)
    (ColOut : ι → RAMState → (Fin sch.m → List (ZMod 2)) → Prop)
    (xhatBase : ℕ) (CR : CRFamily) (t : ℕ) {Tini Trow Tdec Tas Tres Tcr : ℝ}
    (h : ∀ (i : ι) (x : Fin sch.N → ZMod 2),
      TopDecStages Sinit Srow Sdec Sassem Sres Scr (env i) sch (lr i) J (D i) (RowOut i)
        (ColOut i) xhatBase CR t x Tini Trow Tdec Tas Tres Tcr) :
    TopDecCorrectsSeed Sinit Srow Sdec Sassem Sres Scr env D
      (Tini + Trow + Tdec + Tas + Tres + Tcr) :=
  fun i => topDecCorrects_of_stages (h i)

/-- **Conjunct 8 from per-seed correctness, with no `ε` loss.**  The event holds at *every* seed,
so its `prU` is `1`; `ε` enters 6.5 only through the stages' own failure probabilities.  (This is
`conjunct8_of_correctsEnv`'s argument at the seed-indexed payload `D i x`.) -/
theorem conjunct8_of_seedCorrects {ι : Type} [Fintype ι] [Nonempty ι]
    {Sinit Srow Sdec Sassem Sres Scr : Stmt} {env : ι → RAMEnv} {n M : ℕ}
    {D : ι → (Fin n → ZMod 2) → Fin M → ZMod 2} {Tdec eps : ℝ}
    (hHalt : ∀ (i : ι) (y : Fin M → ZMod 2), ∃ s' : RAMState,
      HaltsWithin (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (env i) Tdec
        (decoderStart (env i).W y []) s')
    (hCorr : TopDecCorrectsSeed Sinit Srow Sdec Sassem Sres Scr env D Tdec) (heps : 0 ≤ eps)
    (x : Fin n → ZMod 2) :
    1 - eps ≤ prU (fun i : ι => ∃ s' : RAMState,
      HaltsWithin (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (env i) Tdec
        (decoderStart (env i).W (D i x) []) s' ∧ OutputsSupport s' x) := by
  have hle : prU (fun _ : ι => True) ≤
      prU (fun i : ι => ∃ s' : RAMState,
        HaltsWithin (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (env i) Tdec
          (decoderStart (env i).W (D i x) []) s' ∧ OutputsSupport s' x) := by
    apply prU_mono
    intro i _
    obtain ⟨s', hs'⟩ := hHalt i (D i x)
    exact ⟨s', hs', hCorr i x s' hs'⟩
  rw [prU_true] at hle
  linarith

/-- **Conjunct 8 of `theorem_6_5`, at the composite decoder `progDecOfTop`**: for every
`d`-sparse `x`, with probability `1 - ε` over the seed `r` the decoder halts within
`Cd · d · exp (Cd (lg lg n)²)` from `decoderStart W (H r x) []` and outputs `supp x`.

`hHalt` is conjunct 7 (`haltsWithin_topDec_final`), `hCorr` is §5; nothing else enters. -/
theorem conjunct8_topDec {Sinit Srow Sdec Sassem Sres Scr : Stmt} {W M n d : ℕ} {spec : TableSpec}
    (det : ℕ → ℕ) (H : spec.Seed → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2))
    {Cd eps : ℝ} (heps : 0 ≤ eps)
    (hHalt : ∀ (r : spec.Seed) (y : Fin M → ZMod 2), ∃ s' : RAMState,
      HaltsWithin (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (spec.env W det r)
        (Cd * (d : ℝ) * Real.exp (Cd * lg (lg (n : ℝ)) ^ 2)) (decoderStart W y []) s')
    (hCorr : TopDecCorrectsSeed Sinit Srow Sdec Sassem Sres Scr (fun r => spec.env W det r)
      (fun r x => H r x) (Cd * (d : ℝ) * Real.exp (Cd * lg (lg (n : ℝ)) ^ 2))) :
    ∀ x : Fin n → ZMod 2, (univ.filter fun i => x i = 1).card ≤ d →
      1 - eps ≤ prU (fun r : spec.Seed => ∃ s' : RAMState,
        HaltsWithin (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (spec.env W det r)
          (Cd * (d : ℝ) * Real.exp (Cd * lg (lg (n : ℝ)) ^ 2))
          (decoderStart W (H r x) []) s' ∧
        OutputsSupport s' x) :=
  fun x _ => conjunct8_of_seedCorrects hHalt hCorr heps x

end C8

end LinearSetReconciliation327.Main


/-! ## Root-level platform wrapper

`C8.conjunct8_topDec` is this block's own theorem; the platform requires the submitted proof to be a
root-level `theorem solution` whose type is the target `formal_statement`.  `hCorr` is that theorem's
`TopDecCorrectsSeed …` unfolded (definitionally equal). -/

open LinearSetReconciliation327.Main

theorem solution {Sinit Srow Sdec Sassem Sres Scr : Stmt} {W M n d : ℕ} {spec : TableSpec}
    (det : ℕ → ℕ) (H : spec.Seed → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2))
    {Cd eps : ℝ} (heps : 0 ≤ eps)
    (hHalt : ∀ (r : spec.Seed) (y : Fin M → ZMod 2), ∃ s' : RAMState,
      HaltsWithin (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (spec.env W det r)
        (Cd * (d : ℝ) * Real.exp (Cd * lg (lg (n : ℝ)) ^ 2)) (decoderStart W y []) s')
    (hCorr : ∀ (r : spec.Seed) (x : Fin n → ZMod 2) (s' : RAMState),
      (∃ k : ℕ, (k : ℝ) ≤ Cd * (d : ℝ) * Real.exp (Cd * lg (lg (n : ℝ)) ^ 2) ∧
        (step (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (spec.env W det r))^[k]
          (decoderStart (spec.env W det r).W (H r x) []) = s' ∧
        Halted (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) s') →
      OutputsSupport s' x) :
    ∀ x : Fin n → ZMod 2, (Finset.univ.filter fun i => x i = 1).card ≤ d →
      1 - eps ≤ prU (fun r : spec.Seed => ∃ s' : RAMState,
        HaltsWithin (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (spec.env W det r)
          (Cd * (d : ℝ) * Real.exp (Cd * lg (lg (n : ℝ)) ^ 2))
          (decoderStart W (H r x) []) s' ∧
        OutputsSupport s' x) := by
  have h : LinearSetReconciliation327.Main.C8.TopDecCorrectsSeed Sinit Srow Sdec Sassem Sres Scr
      (fun r => spec.env W det r) (fun r x => H r x)
      (Cd * (d : ℝ) * Real.exp (Cd * lg (lg (n : ℝ)) ^ 2)) := hCorr
  exact LinearSetReconciliation327.Main.C8.conjunct8_topDec det H heps hHalt h
