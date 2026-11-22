-- Prove2me | solution 1 for LinearSetReconciliation327.Main.pinsketch_decoding_at_bounded
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-22T06:23:20.20914+00:00
-- url     : https://prove2.me/submissions/25994975-0395-4102-a7ad-3fe7b2036ad4

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_Pinsketch
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderTables
import Definitions.Def_LinearSetReconciliation327_Main_DecoderProgram
import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas
import Definitions.Def_LinearSetReconciliation327_Main_P21RunStmt
import Definitions.Def_LinearSetReconciliation327_Main_P21BndRead20261122
import Definitions.Def_LinearSetReconciliation327_Main_P21BndKey20261122
import Definitions.Def_LinearSetReconciliation327_Main_P21BndAux20261122
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_root_search
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_verifier_frame

/-!
# Proposition 2.1's decoder from the bounded zero hypothesis

Target: `LinearSetReconciliation327.Main.pinsketch_decoding_at_bounded`.  At the bounded hypothesis

  `m = 0` on `[L, beta)` and on `[beta + L, decoderAllocEnd t)`,  `L = wordsOf (8w) (tw)`,

with the layout conditions `beta + 2L <= decoderAllocEnd t` and `beta + 2L < 2^(8w)`, the glued
program `pinsketchRunStmt t w beta` halts within `positiveDecoderBudget t w + 24L + 40` steps with
`decoderPost`, **and leaves every word at or above `decoderAllocEnd t` untouched**.

The four stage contracts are used at their bounded forms:

* `P21Bnd.pinsketch_decoder_readB` -- read stage, ambient memory agreeing with `hintMem` on the
  workspace, conclusion bounded at `decoderAllocEnd t`, with a frame above it;
* `P21Bnd.pinsketch_decoder_key_solverB` -- key solver at the bounded `hTail`, with
  `MemoryFrame (solverInitWritable t)`;
* `pinsketch_decoder_root_search` -- unchanged, with `MemoryFrame (rootSearchWritable ...)`;
* `pinsketch_decoder_verifier_frame` -- the verifier *with* its frame
  `MemoryFrame (verifierWritable (decoderVerifyBase t) (2t))` (platform theorem `07ee0bad-...`).

The three writable sets are inside the scratch (`rootSearchWritable_lt_allocEnd`,
`solverInitWritable_lt_allocEnd`, `verifierWritable_lt_allocEnd` in `Def_..._P21BndAux20261122`), so
`frame_above_of_writable` turns each stage frame into "nothing at or above `decoderAllocEnd t`
moves", and the four frames compose into the single frame of the statement.

The copy-in half is `pinsketch_copyin_at_bounded` (platform theorem `3961732f-...`), carried here
byte-identically with its proof from `bnd21/Sol_p21_copyin_bounded.lean`; its memory equation
`layerMem_eq_workspace` is what makes `hzeroB` (rather than the unbounded `hzero`) suffice: only
`[0, decoderAllocEnd t)` is rebuilt, and the frame above is transported unchanged.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 40000
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

section Glue

theorem layerCopy_run (E : RAMEnv) (pc dst src L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ)
    (hW : 1 < 2 ^ E.W) (hdst : dst < 2 ^ E.W) (hsrc : src < 2 ^ E.W) (hL : L < 2 ^ E.W) :
    runBlock (layerCopyRegs dst src L) E ⟨pc, r, m⟩ = copyState (pc + 9) dst src L m r 0 := by
  have h0 : (0 : ℕ) % 2 ^ E.W = 0 := Nat.zero_mod _
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  have hd : dst % 2 ^ E.W = dst := Nat.mod_eq_of_lt hdst
  have hs : src % 2 ^ E.W = src := Nat.mod_eq_of_lt hsrc
  have hl : L % 2 ^ E.W = L := Nat.mod_eq_of_lt hL
  apply ramState_eq_of
  · simp only [layerCopyRegs, copyState, runBlock_cons, runBlock_nil, execInstr,
      Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
      Fin.isValue] <;> omega
  · rfl
  · intro d
    fin_cases d <;>
      simp only [layerCopyRegs, copyState, runBlock_cons, runBlock_nil, execInstr, h0, h1, hd, hs,
        hl, Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
        Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero, reduceIte]

theorem layerLength_run (E : RAMEnv) (pc L : ℕ) (m : ℕ → ℕ) (hL : L < 2 ^ E.W) :
    runBlock [iImm r1 L] E (boundaryState pc m) = ⟨pc + 1, layerDecoderRegs L, m⟩ := by
  have hl : L % 2 ^ E.W = L := Nat.mod_eq_of_lt hL
  rw [runBlock_cons, runBlock_nil]
  apply ramState_eq_of
  · simp only [execInstr, boundaryState] <;> omega
  · rfl
  · intro d
    simp only [execInstr, boundaryState, layerDecoderRegs, hl, Function.update_apply]

theorem layerDecoderRegs_eq_start (W L : ℕ) {M : ℕ} (y : Fin M → ZMod 2)
    (hL : L = wordsOf W M) : layerDecoderRegs L = (decoderStart W y []).regs := by
  subst hL
  funext d
  fin_cases d <;> simp [layerDecoderRegs, decoderStart, initState]

end Glue

theorem runAtStmt_length (β L : ℕ) (Sdec : Stmt) : (runAtStmt β L Sdec).len = Sdec.len + 59 := by
  simp only [runAtStmt, Stmt.len, copyStmt, zeroRegsCode, layerCopyRegs, copyCond, copyBody,
    Cond.code, List.length_cons, List.length_nil]
  omega

theorem pinsketchRunStmt_length (t w β : ℕ) :
    (pinsketchRunStmt t w β).len = positiveDecoderStmt.len + 59 :=
  runAtStmt_length _ _ _

section Main

variable {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {N t w : ℕ}

/-- The universe embeds into the field, so `N < 2^w`. -/
theorem layerUniverse_lt_two_pow {N w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (h0 : ∀ i < N, ι i ≠ 0) (hinj : Set.InjOn ι (Set.Iio N)) : N < 2 ^ w := by
  classical
  letI : Fintype F := Fintype.ofEquiv (Fin w → ZMod 2) b.equivFun.toEquiv.symm
  have hcard : Fintype.card F = 2 ^ w := by
    calc
      Fintype.card F = Fintype.card (Fin w → ZMod 2) := Fintype.card_congr b.equivFun.toEquiv
      _ = 2 ^ w := by simp
  let D : Finset F := Finset.univ.image (fun i : Fin N => ι i.val)
  have hDcard : D.card = N := by
    dsimp only [D]
    rw [Finset.card_image_of_injOn (fun i _ j _ hij => Fin.ext (hinj i.isLt j.isLt hij))]
    simp
  have hD0 : (0 : F) ∉ D := by
    intro hz
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
    exact h0 i.val i.isLt hi
  have hle : (insert 0 D).card ≤ (Finset.univ : Finset F).card :=
    Finset.card_le_card (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_insert_of_notMem hD0, Finset.card_univ, hcard, hDcard] at hle
  omega

/-- A nonempty universe forces a nonzero word width. -/
theorem layerDimension_pos {N w : ℕ} (hN : 1 ≤ N) (hNw : N < 2 ^ w) : 1 ≤ w := by
  by_contra h
  have hw : w = 0 := by omega
  rw [hw] at hNw
  norm_num at hNw
  omega

/-- The machine does not move at a `halt`. -/
theorem layerStep_halt (P : Program) (E : RAMEnv) (s : RAMState)
    (h : P[s.pc]? = some .halt) : step P E s = s := by
  simp only [step, h]

/-- `Halted` from the instruction read. -/
theorem layerHalted_of (P : Program) (s : RAMState) (h : P[s.pc]? = some .halt) :
    Halted P s := by
  simp only [Halted, h]

/-- A `Sem` run that lands on a `halt` is a `HaltsWithin` run; the `halt` costs one more step. -/
theorem layerHalts_of_run (P : Program) (E : RAMEnv) (a e : ℕ) (s : RAMState) (B : ℝ)
    (Q : ℕ → RAMState → Prop) (Post : RAMState → Prop)
    (hAt : P[e]? = some .halt) (h : Sem P E a e s Q)
    (hQ : ∀ t s', Q t s' → (t : ℝ) + 1 ≤ B ∧ Post s') :
    ∃ s' : RAMState, HaltsWithin P E B s s' ∧ Post s' := by
  obtain ⟨-, k, s', hstep, hpe, hQ'⟩ := h
  obtain ⟨hB, hPost⟩ := hQ k s' hQ'
  refine ⟨s', ⟨k + 1, ?_, ?_, ?_⟩, hPost⟩
  · push_cast at hB ⊢
    linarith
  · rw [show k + 1 = 1 + k from by omega, Function.iterate_add_apply, Function.iterate_one, hstep,
      layerStep_halt P E s' (by rw [hpe]; exact hAt)]
  · exact layerHalted_of P s' (by rw [hpe]; exact hAt)

/-- A chunk spliced into a program at an address is `At` that address. -/
theorem layerAt_of_append {P : Program} {pre code post : Program} {a : ℕ}
    (hP : P = pre ++ code ++ post) (hbase : pre.length = a) : At P a code := by
  intro r hr
  rw [hP, show a + r = pre.length + r from by omega, List.append_assoc,
    List.getElem?_append_right (by omega : pre.length ≤ pre.length + r),
    show pre.length + r - pre.length = r from by omega]
  exact List.getElem?_append_left hr

theorem layerInputSaved_length : inputSavedProcedure.len = 110 := rfl

theorem layerKeySolver_length : keySolverProcedure.len = 960 := by
  simp only [keySolverProcedure, Stmt.len, solverInitializationProcedure_length]
  rfl

theorem layerRootSearch_length : rootSearchProcedure.len = 4047 := rfl

theorem layerVerifier_length : verificationFinalProcedure.len = 432 := rfl

theorem layerPositiveDecoderStmt_length : positiveDecoderStmt.len = 5549 := by
  simp only [positiveDecoderStmt, Stmt.len, layerInputSaved_length, layerKeySolver_length,
    layerRootSearch_length, layerVerifier_length]

/-- The decoder core, at an arbitrary embedding address.  This is the accepted
`positiveDecoderStmt_spec`, re-derived from the four *published* stage contracts
(`pinsketch_decoder_read`, `…_key_solver`, `…_root_search`, `…_verifier`). -/
theorem layerGet0 (m f : ℕ → ℕ) (n i : ℕ) (hi : i < n) : writeArray 0 m f n i = f i := by
  have h := writeArray_get 0 m f n i hi
  simpa using h

/-- **Bounded zero suffices for the two copy passes, on the decoder's own workspace.**  The payload
of `y` is staged at `β`; zeros are assumed only on `[L, β)` and on `[β+L, decoderAllocEnd t)`, i.e.
inside 2.1's scratch and outside the payload window, and *not* above `decoderAllocEnd t`.  Then the
two copy passes still build 2.1's canonical entry memory on `[0, decoderAllocEnd t)`.

This is the exact form the row loop of Theorem 6.5 needs: after the per-iteration clearing pass and
the staging copy the whole scratch is canonical, while the row bitmaps above it are untouched. -/
theorem layerMem_eq_workspace (y : Fin (t * w) → ZMod 2) (m : ℕ → ℕ) (β : ℕ)
    (hpayload : ∀ j < wordsOf (8 * w) (t * w), m (β + j) = packMem (8 * w) y j)
    (hzeroB : (∀ a, wordsOf (8 * w) (t * w) ≤ a → a < β → m a = 0) ∧
      (∀ a, β + wordsOf (8 * w) (t * w) ≤ a → a < decoderAllocEnd t → m a = 0))
    (hβL : wordsOf (8 * w) (t * w) ≤ β)
    (hβ2 : β + 2 * wordsOf (8 * w) (t * w) ≤ decoderAllocEnd t) :
    ∀ a, a < decoderAllocEnd t →
      writeArray β (writeArray 0 m (fun i => m (β + i)) (wordsOf (8 * w) (t * w)))
        (fun i => writeArray 0 m (fun j => m (β + j)) (wordsOf (8 * w) (t * w))
          (β + wordsOf (8 * w) (t * w) + i)) (wordsOf (8 * w) (t * w)) a
      = hintMem (8 * w) y [] a := by
  intro a haEnd
  by_cases h1 : a < wordsOf (8 * w) (t * w)
  · rw [writeArray_frame β _ _ _ a (Or.inl (by omega)),
      layerGet0 m (fun i => m (β + i)) _ a h1, hpayload a h1]
    simp [hintMem, h1]
  · rw [show hintMem (8 * w) y ([] : List ℕ) a = 0 from by simp [hintMem, h1]]
    by_cases h2 : a < β
    · rw [writeArray_frame β _ _ _ a (Or.inl h2),
        writeArray_frame 0 m _ _ a (Or.inr (by omega)), hzeroB.1 a (by omega) h2]
    · by_cases h3 : a < β + wordsOf (8 * w) (t * w)
      · have hOut : writeArray β (writeArray 0 m (fun i => m (β + i)) (wordsOf (8 * w) (t * w)))
            (fun i => writeArray 0 m (fun j => m (β + j)) (wordsOf (8 * w) (t * w))
              (β + wordsOf (8 * w) (t * w) + i)) (wordsOf (8 * w) (t * w)) a
            = (writeArray 0 m (fun i => m (β + i)) (wordsOf (8 * w) (t * w)))
              (a + wordsOf (8 * w) (t * w)) := by
          rw [show a = β + (a - β) from by omega,
            writeArray_get β _ _ _ (a - β) (by omega)]
          congr 1
          omega
        rw [hOut, writeArray_frame 0 m _ _ _ (Or.inr (by omega)),
          hzeroB.2 (a + wordsOf (8 * w) (t * w)) (by omega) (by omega)]
      · have h3' := Nat.not_lt.mp h3
        rw [writeArray_frame β _ _ _ a (Or.inr h3'),
          writeArray_frame 0 m _ _ a (Or.inr (by omega)), hzeroB.2 a h3' haEnd]

/-- **The copy-in half of Proposition 2.1's base-relative decoder, at a *bounded* zero
hypothesis.**  The two copy passes of `pinsketchRunStmt` need the memory to be zero only on
`[L, β)` and on `[β+L, decoderAllocEnd t)`; everything at or above `decoderAllocEnd t` is left
alone.  The postcondition is the decoder's canonical entry state *on the workspace*
(`hintMem` on `[0, decoderAllocEnd t)`) together with the frame `decoderAllocEnd t ≤ a`, so the
run composes with a stage contract that only reads the workspace. -/
theorem pinsketch_copyin_at_bounded (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (y : Fin (t * w) → ZMod 2) (P : Program) (E : RAMEnv) (pc β : ℕ) (s : RAMState)
    (hAt : At P pc (Stmt.compile (pinsketchRunStmt t w β) pc))
    (hpc : s.pc = pc)
    (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N) (hW : E.W = 8 * w)
    (hdet : E.det = detStd t N b ι)
    (h0 : ∀ i < N, ι i ≠ 0) (hinj : Set.InjOn ι (Set.Iio N))
    (hpayload : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) = packMem (8 * w) y j)
    (hpayloadWord : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) < 2 ^ E.W)
    (hzeroB : (∀ a, wordsOf (8 * w) (t * w) ≤ a → a < β → s.mem a = 0) ∧
      (∀ a, β + wordsOf (8 * w) (t * w) ≤ a → a < decoderAllocEnd t → s.mem a = 0))
    (hβL : wordsOf (8 * w) (t * w) ≤ β)
    (hβ2 : β + 2 * wordsOf (8 * w) (t * w) ≤ decoderAllocEnd t)
    (hβfit : β + 2 * wordsOf (8 * w) (t * w) < 2 ^ E.W) :
    Sem P E pc (pc + 59) s
      (fun k z => k ≤ 24 * wordsOf (8 * w) (t * w) + 39 ∧ z.pc = pc + 59 ∧
        z.regs = layerDecoderRegs (wordsOf (8 * w) (t * w)) ∧
        (∀ a, a < decoderAllocEnd t → z.mem a = hintMem (8 * w) y [] a) ∧
        (∀ a, decoderAllocEnd t ≤ a → z.mem a = s.mem a)) := by
  have hNw := layerUniverse_lt_two_pow b ι h0 hinj
  have hw1 : 1 ≤ w := layerDimension_pos hN hNw
  have htW : t < 2 ^ w := lt_of_le_of_lt htN hNw
  have hLle : wordsOf (8 * w) (t * w) ≤ t := wordsOf_le w t hw1
  have hLW : wordsOf (8 * w) (t * w) < 2 ^ E.W := by
    refine lt_of_le_of_lt hLle ?_
    exact lt_of_lt_of_le htW (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h1W : 1 < 2 ^ E.W := by
    have hp : (2 : ℕ) ^ 1 ≤ 2 ^ E.W := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_one] at hp
    omega
  have hβW : β < 2 ^ E.W := by omega
  have hβLW : β + wordsOf (8 * w) (t * w) < 2 ^ E.W := by omega
  have hβLW' : β + wordsOf (8 * w) (t * w) ≤ 2 ^ E.W := by omega
  have hzeroShadow : ∀ i < wordsOf (8 * w) (t * w),
      (writeArray 0 s.mem (fun i => s.mem (β + i)) (wordsOf (8 * w) (t * w)))
        (β + wordsOf (8 * w) (t * w) + i) < 2 ^ E.W := by
    intro i hi
    rw [writeArray_frame 0 s.mem _ _ _ (Or.inr (by omega)),
      hzeroB.2 (β + wordsOf (8 * w) (t * w) + i) (by omega) (by omega)]
    exact Nat.two_pow_pos E.W
  rw [pinsketchRunStmt, runAtStmt] at hAt
  obtain ⟨hAt1, hAtR1⟩ := At.seqStmt hAt
  obtain ⟨hAt2, hAtR2⟩ := At.seqStmt hAtR1
  obtain ⟨hAt3, hAtR3⟩ := At.seqStmt hAtR2
  obtain ⟨hAt4, hAtR4⟩ := At.seqStmt hAtR3
  obtain ⟨hAt5, hAtR5⟩ := At.seqStmt hAtR4
  obtain ⟨hAt6, hAt7⟩ := At.seqStmt hAtR5
  have hS1 : Sem P E pc (pc + 9) s
      (fun k z => k ≤ 9 ∧ z = copyState (pc + 9) 0 β (wordsOf (8 * w) (t * w)) s.mem s.regs 0) := by
    have hstep := layerCopy_run E pc 0 β (wordsOf (8 * w) (t * w)) s.mem s.regs h1W
      (by omega) hβW hLW
    have hs : (⟨pc, s.regs, s.mem⟩ : RAMState) = s := by rw [← hpc]
    rw [hs] at hstep
    refine Sem.mono (Sem.block P E pc (layerCopyRegs 0 β (wordsOf (8 * w) (t * w))) s hAt1
      (by simp [layerCopyRegs]) hpc) ?_
    intro k z hq
    obtain ⟨hk, hz⟩ := hq
    have hk9 : k = 9 := hk
    exact ⟨by omega, hz.trans hstep⟩
  have hS2 : Sem P E (pc + 9) (pc + 9 + 12)
      (copyState (pc + 9) 0 β (wordsOf (8 * w) (t * w)) s.mem s.regs 0)
      (fun k z => k ≤ 12 * wordsOf (8 * w) (t * w) + 2 ∧
        z = { copyState (pc + 9) 0 β (wordsOf (8 * w) (t * w)) s.mem s.regs
            (wordsOf (8 * w) (t * w)) with pc := pc + 9 + 12 }) :=
    copyArray_spec P E (pc + 9) 0 β (wordsOf (8 * w) (t * w)) s.mem s.regs hAt2 h1W hLW
      (by omega) hβLW' (Or.inr (by omega)) hpayloadWord
  have hS3 : Sem P E (pc + 21) (pc + 30)
      { copyState (pc + 9) 0 β (wordsOf (8 * w) (t * w)) s.mem s.regs
          (wordsOf (8 * w) (t * w)) with pc := pc + 21 }
      (fun k z => k ≤ 9 ∧ z = copyState (pc + 30) β (β + wordsOf (8 * w) (t * w))
        (wordsOf (8 * w) (t * w))
        (writeArray 0 s.mem (fun i => s.mem (β + i)) (wordsOf (8 * w) (t * w)))
        (copyState (pc + 9) 0 β (wordsOf (8 * w) (t * w)) s.mem s.regs
          (wordsOf (8 * w) (t * w))).regs 0) := by
    have hstep := layerCopy_run E (pc + 21) β (β + wordsOf (8 * w) (t * w))
      (wordsOf (8 * w) (t * w))
      (writeArray 0 s.mem (fun i => s.mem (β + i)) (wordsOf (8 * w) (t * w)))
      (copyState (pc + 9) 0 β (wordsOf (8 * w) (t * w)) s.mem s.regs
        (wordsOf (8 * w) (t * w))).regs h1W hβW hβLW hLW
    refine Sem.mono (Sem.block P E (pc + 21)
      (layerCopyRegs β (β + wordsOf (8 * w) (t * w)) (wordsOf (8 * w) (t * w)))
      _ hAt3 (by simp [layerCopyRegs]) rfl) ?_
    intro k z hq
    obtain ⟨hk, hz⟩ := hq
    have hk9 : k = 9 := hk
    exact ⟨by omega, hz.trans hstep⟩
  have hS4 : Sem P E (pc + 30) (pc + 30 + 12)
      (copyState (pc + 30) β (β + wordsOf (8 * w) (t * w)) (wordsOf (8 * w) (t * w))
        (writeArray 0 s.mem (fun i => s.mem (β + i)) (wordsOf (8 * w) (t * w)))
        (copyState (pc + 9) 0 β (wordsOf (8 * w) (t * w)) s.mem s.regs
          (wordsOf (8 * w) (t * w))).regs 0)
      (fun k z => k ≤ 12 * wordsOf (8 * w) (t * w) + 2 ∧
        z = { copyState (pc + 30) β (β + wordsOf (8 * w) (t * w)) (wordsOf (8 * w) (t * w))
            (writeArray 0 s.mem (fun i => s.mem (β + i)) (wordsOf (8 * w) (t * w)))
            (copyState (pc + 9) 0 β (wordsOf (8 * w) (t * w)) s.mem s.regs
              (wordsOf (8 * w) (t * w))).regs (wordsOf (8 * w) (t * w)) with pc := pc + 30 + 12 }) :=
    copyArray_spec P E (pc + 30) β (β + wordsOf (8 * w) (t * w)) (wordsOf (8 * w) (t * w))
      (writeArray 0 s.mem (fun i => s.mem (β + i)) (wordsOf (8 * w) (t * w)))
      (copyState (pc + 9) 0 β (wordsOf (8 * w) (t * w)) s.mem s.regs
        (wordsOf (8 * w) (t * w))).regs hAt4 h1W hLW (by omega) (by omega) (Or.inr (by omega))
      hzeroShadow
  have hS5 : Sem P E (pc + 42) (pc + 58)
      { copyState (pc + 30) β (β + wordsOf (8 * w) (t * w)) (wordsOf (8 * w) (t * w))
          (writeArray 0 s.mem (fun i => s.mem (β + i)) (wordsOf (8 * w) (t * w)))
          (copyState (pc + 9) 0 β (wordsOf (8 * w) (t * w)) s.mem s.regs
            (wordsOf (8 * w) (t * w))).regs (wordsOf (8 * w) (t * w)) with pc := pc + 42 }
      (fun k z => k ≤ 16 ∧ z = boundaryState (pc + 58)
        (writeArray β (writeArray 0 s.mem (fun i => s.mem (β + i)) (wordsOf (8 * w) (t * w)))
          (fun i => writeArray 0 s.mem (fun j => s.mem (β + j)) (wordsOf (8 * w) (t * w))
            (β + wordsOf (8 * w) (t * w) + i)) (wordsOf (8 * w) (t * w)))) :=
    Sem.zero_block P E (pc + 42) _ hAt5 rfl
  have hS6 : Sem P E (pc + 58) (pc + 59)
      (boundaryState (pc + 58)
        (writeArray β (writeArray 0 s.mem (fun i => s.mem (β + i)) (wordsOf (8 * w) (t * w)))
          (fun i => writeArray 0 s.mem (fun j => s.mem (β + j)) (wordsOf (8 * w) (t * w))
            (β + wordsOf (8 * w) (t * w) + i)) (wordsOf (8 * w) (t * w))))
      (fun k z => k ≤ 1 ∧ z = ⟨pc + 59, layerDecoderRegs (wordsOf (8 * w) (t * w)),
        writeArray β (writeArray 0 s.mem (fun i => s.mem (β + i)) (wordsOf (8 * w) (t * w)))
          (fun i => writeArray 0 s.mem (fun j => s.mem (β + j)) (wordsOf (8 * w) (t * w))
            (β + wordsOf (8 * w) (t * w) + i)) (wordsOf (8 * w) (t * w))⟩) := by
    refine Sem.mono (Sem.block P E (pc + 58) [iImm r1 (wordsOf (8 * w) (t * w))] _
      hAt6 (by simp) rfl) ?_
    intro k z hq
    obtain ⟨hk, hz⟩ := hq
    have hk1 : k = 1 := hk
    exact ⟨by omega, hz.trans (layerLength_run E (pc + 58) (wordsOf (8 * w) (t * w)) _ hLW)⟩
  have h12 : Sem P E pc (pc + 21) s
      (fun k z => k ≤ 9 + (12 * wordsOf (8 * w) (t * w) + 2) ∧
        z = { copyState (pc + 9) 0 β (wordsOf (8 * w) (t * w)) s.mem s.regs
            (wordsOf (8 * w) (t * w)) with pc := pc + 21 }) :=
    Sem.seq_bound hS1 (fun z1 _ hz1 => by subst hz1; exact hS2)
  have h123 : Sem P E pc (pc + 30) s
      (fun k z => k ≤ 9 + (12 * wordsOf (8 * w) (t * w) + 2) + 9 ∧
        z = copyState (pc + 30) β (β + wordsOf (8 * w) (t * w)) (wordsOf (8 * w) (t * w))
          (writeArray 0 s.mem (fun i => s.mem (β + i)) (wordsOf (8 * w) (t * w)))
          (copyState (pc + 9) 0 β (wordsOf (8 * w) (t * w)) s.mem s.regs
            (wordsOf (8 * w) (t * w))).regs 0) :=
    Sem.seq_bound h12 (fun z2 _ hz2 => by subst hz2; exact hS3)
  have h1234 : Sem P E pc (pc + 42) s
      (fun k z => k ≤ 9 + (12 * wordsOf (8 * w) (t * w) + 2) + 9 +
          (12 * wordsOf (8 * w) (t * w) + 2) ∧
        z = { copyState (pc + 30) β (β + wordsOf (8 * w) (t * w)) (wordsOf (8 * w) (t * w))
            (writeArray 0 s.mem (fun i => s.mem (β + i)) (wordsOf (8 * w) (t * w)))
            (copyState (pc + 9) 0 β (wordsOf (8 * w) (t * w)) s.mem s.regs
              (wordsOf (8 * w) (t * w))).regs (wordsOf (8 * w) (t * w)) with pc := pc + 42 }) :=
    Sem.seq_bound h123 (fun z3 _ hz3 => by subst hz3; exact hS4)
  have h12345 : Sem P E pc (pc + 58) s
      (fun k z => k ≤ 9 + (12 * wordsOf (8 * w) (t * w) + 2) + 9 +
          (12 * wordsOf (8 * w) (t * w) + 2) + 16 ∧
        z = boundaryState (pc + 58)
          (writeArray β (writeArray 0 s.mem (fun i => s.mem (β + i)) (wordsOf (8 * w) (t * w)))
            (fun i => writeArray 0 s.mem (fun j => s.mem (β + j)) (wordsOf (8 * w) (t * w))
              (β + wordsOf (8 * w) (t * w) + i)) (wordsOf (8 * w) (t * w)))) :=
    Sem.seq_bound h1234 (fun z4 _ hz4 => by subst hz4; exact hS5)
  have h123456 : Sem P E pc (pc + 59) s
      (fun k z => k ≤ 9 + (12 * wordsOf (8 * w) (t * w) + 2) + 9 +
          (12 * wordsOf (8 * w) (t * w) + 2) + 16 + 1 ∧
        z = ⟨pc + 59, layerDecoderRegs (wordsOf (8 * w) (t * w)),
          writeArray β (writeArray 0 s.mem (fun i => s.mem (β + i)) (wordsOf (8 * w) (t * w)))
            (fun i => writeArray 0 s.mem (fun j => s.mem (β + j)) (wordsOf (8 * w) (t * w))
              (β + wordsOf (8 * w) (t * w) + i)) (wordsOf (8 * w) (t * w))⟩) :=
    Sem.seq_bound h12345 (fun z5 _ hz5 => by subst hz5; exact hS6)
  refine Sem.mono h123456 ?_
  intro k z hq
  obtain ⟨hk, hz⟩ := hq
  subst hz
  refine ⟨by omega, rfl, rfl, ?_, ?_⟩
  · intro a ha
    exact layerMem_eq_workspace y s.mem β hpayload hzeroB hβL hβ2 a ha
  · intro a ha
    show writeArray β (writeArray 0 s.mem (fun i => s.mem (β + i)) (wordsOf (8 * w) (t * w)))
        (fun i => writeArray 0 s.mem (fun j => s.mem (β + j)) (wordsOf (8 * w) (t * w))
          (β + wordsOf (8 * w) (t * w) + i)) (wordsOf (8 * w) (t * w)) a = s.mem a
    rw [writeArray_frame β _ _ _ a (Or.inr (by omega)),
      writeArray_frame 0 s.mem _ _ a (Or.inr (by omega))]


/-! ## The bounded composition -/

/-- The memory the bounded copy-in produces: the canonical decoder entry memory on the workspace
`[0, decoderAllocEnd t)`, and the ambient memory above it. -/
def bndEntryMem (t w : ℕ) (y : Fin (t * w) → ZMod 2) (m : ℕ → ℕ) : ℕ → ℕ :=
  fun a => if a < decoderAllocEnd t then hintMem (8 * w) y [] a else m a

theorem bndEntryMem_lt {t w : ℕ} {y : Fin (t * w) → ZMod 2} {m : ℕ → ℕ} {a : ℕ}
    (ha : a < decoderAllocEnd t) : bndEntryMem t w y m a = hintMem (8 * w) y [] a := by
  unfold bndEntryMem
  rw [if_pos ha]

theorem bndEntryMem_ge {t w : ℕ} {y : Fin (t * w) → ZMod 2} {m : ℕ → ℕ} {a : ℕ}
    (ha : decoderAllocEnd t ≤ a) : bndEntryMem t w y m a = m a := by
  unfold bndEntryMem
  rw [if_neg (by omega)]

/-- **The decoder core at the bounded hypothesis.**  The accepted `positiveDecoderStmt_spec`,
re-derived from the bounded read stage (started at an arbitrary ambient memory `m` that agrees with
`hintMem` only on the workspace), the bounded key solver, the root search and the verifier with its
frame.  The conclusion adds `∀ a ≥ decoderAllocEnd t, z.mem a = m a`. -/
theorem layerPositiveDecoder_semB (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (y : Fin (t * w) → ZMod 2) (P : Program) (E : RAMEnv) (pc : ℕ) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile positiveDecoderStmt pc))
    (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N) (hW : E.W = 8 * w)
    (hdet : E.det = detStd t N b ι) (h0 : ∀ i < N, ι i ≠ 0) (hinj : Set.InjOn ι (Set.Iio N))
    (hmem : ∀ a, a < decoderAllocEnd t → m a = hintMem (8 * w) y [] a) :
    Sem P E pc (pc + positiveDecoderStmt.len) ⟨pc, (decoderStart (8 * w) y []).regs, m⟩
      (fun k z => k ≤ positiveDecoderBudget t w ∧ decoderPost (N := N) b ι y z ∧
        ∀ a, decoderAllocEnd t ≤ a → z.mem a = m a) := by
  have hNw := layerUniverse_lt_two_pow b ι h0 hinj
  have hw := layerDimension_pos hN hNw
  have hEnd : decoderAllocEnd t < 2 ^ E.W := by
    rw [hW]
    exact decoderAllocEnd_fits t w hw (lt_of_le_of_lt htN hNw)
  have hpow : 2 ^ w ≤ 2 ^ E.W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have htfit : t < 2 ^ E.W := lt_of_lt_of_le (lt_of_le_of_lt htN hNw) hpow
  have hwfit : w < 2 ^ E.W := lt_of_lt_of_le Nat.lt_two_pow_self hpow
  have hNfit : N < 2 ^ E.W := lt_of_lt_of_le hNw hpow
  have hh0 : E.det 0 % 2 ^ E.W = t := by
    rw [hdet, detStd_hdr t N w b ι (by norm_num : 0 < 13), hdrTab_zero, Nat.mod_eq_of_lt htfit]
  have hh1 : E.det 1 % 2 ^ E.W = w := by
    rw [hdet, detStd_hdr t N w b ι (by norm_num : 1 < 13), hdrTab_one, Nat.mod_eq_of_lt hwfit]
  have hh2 : E.det 2 % 2 ^ E.W = N := by
    rw [hdet, detStd_hdr t N w b ι (by norm_num : 2 < 13)]
    exact Nat.mod_eq_of_lt hNfit
  obtain ⟨hInputAt, hTailAt⟩ := At.seqStmt hAt
  have hTailAt' : At P (pc + 110)
      (Stmt.compile (.seq keySolverProcedure (.seq rootSearchProcedure verificationFinalProcedure))
        (pc + 110)) := by
    simpa only [layerInputSaved_length] using hTailAt
  obtain ⟨hKeyAt, hRootFinalAt⟩ := At.seqStmt hTailAt'
  have hRootFinalAt' : At P (pc + 1070)
      (Stmt.compile (.seq rootSearchProcedure verificationFinalProcedure) (pc + 1070)) := by
    simpa only [layerKeySolver_length] using hRootFinalAt
  obtain ⟨hRootAt, hFinalRaw⟩ := At.seqStmt hRootFinalAt'
  have hFinalAt : At P (pc + 5117) (Stmt.compile verificationFinalProcedure (pc + 5117)) := by
    simpa only [layerRootSearch_length] using hFinalRaw
  have hFull := Sem.seq_bound (P21Bnd.pinsketch_decoder_readB E P pc N t w y b ι m hInputAt hW hw
      hNw htN hdet hmem) (fun z _ hz => by
      obtain ⟨m1, rfl, hSaved, hPoly, hZero, hFrame⟩ := hz
      have hf1 : ∀ a, decoderAllocEnd t ≤ a → m1 a = m a := hFrame
      exact Sem.seq_bound (P21Bnd.pinsketch_decoder_key_solverB b ι t N P E (pc + 110) (eSeq b y) m1
          hKeyAt hw hW hdet ht hEnd (h0 0 (by omega)) hh0 hh1 hh2 hSaved hZero) (fun z _ hz => by
        obtain ⟨m2, rfl, hReady, hfSolver⟩ := hz
        have hf2 : ∀ a, decoderAllocEnd t ≤ a → m2 a = m1 a :=
          frame_above_of_writable (fun x hx => solverInitWritable_lt_allocEnd t x ht hx) hfSolver
        exact Sem.seq_bound (pinsketch_decoder_root_search b ι t N P E (pc + 1070) (eSeq b y) m2
            hRootAt hw hW hdet ht hEnd hNw hReady) (fun z _ hz => by
          obtain ⟨m3, rfl, hCandidate, hfRoot⟩ := hz
          have hf3 : ∀ a, decoderAllocEnd t ≤ a → m3 a = m2 a :=
            frame_above_of_writable (fun x hx => rootSearchWritable_lt_allocEnd t x ht hx) hfRoot
          have hVerFrame : Sem P E (pc + 5117) (pc + 5117 + 432) (boundaryState (pc + 5117) m3)
              (fun k z => k ≤ (170 * t + 117) * t + 172 * t + 149 ∧ decoderPost (N := N) b ι y z ∧
                ∀ a, decoderAllocEnd t ≤ a → z.mem a = m3 a) :=
            Sem.mono (Q' := fun k z => k ≤ (170 * t + 117) * t + 172 * t + 149 ∧
                decoderPost (N := N) b ι y z ∧ ∀ a, decoderAllocEnd t ≤ a → z.mem a = m3 a)
              (pinsketch_decoder_verifier_frame b ι y (eSeq b y) P E (pc + 5117) m3
                hFinalAt hN ht hw hW hdet hEnd hNw h0 hinj (fun k => eSeq_even b y k.val)
                (fun a _ => by
                  rw [show 2 * a - 1 = 2 * (a - 1) + 1 by omega]
                  exact eSeq_odd b y (a - 1))
                hCandidate) (fun k z hq => by
                obtain ⟨hk, hpost, hfVer⟩ := hq
                exact ⟨hk, hpost,
                  frame_above_of_writable (verifierWritable_lt_allocEnd t) hfVer⟩)
          have hVerAll : Sem P E (pc + 5117) (pc + 5117 + 432) (boundaryState (pc + 5117) m3)
              (fun k z => k ≤ (170 * t + 117) * t + 172 * t + 149 ∧ decoderPost (N := N) b ι y z ∧
                ∀ a, decoderAllocEnd t ≤ a → z.mem a = m a) :=
            Sem.mono (Q' := fun k z => k ≤ (170 * t + 117) * t + 172 * t + 149 ∧
                decoderPost (N := N) b ι y z ∧ ∀ a, decoderAllocEnd t ≤ a → z.mem a = m a)
              hVerFrame (fun k z hq => by
                obtain ⟨hk, hpost, hf4⟩ := hq
                exact ⟨hk, hpost, fun a ha => by rw [hf4 a ha, hf3 a ha, hf2 a ha, hf1 a ha]⟩)
          exact hVerAll)))
  refine Sem.mono hFull ?_
  intro k z hz
  obtain ⟨hk, hpost, hfr⟩ := hz
  refine ⟨?_, hpost, hfr⟩
  dsimp only [positiveDecoderBudget] at hk ⊢
  omega

/-- **The glued driver at the bounded hypothesis: copy-in, then the decoder core.**  The two halves
are `pinsketch_copyin_at_bounded` (59 instructions) and `layerPositiveDecoder_semB` (5549), and the
two frames compose into `∀ a ≥ decoderAllocEnd t, z.mem a = s.mem a`. -/
theorem pinsketchRun_semB (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (y : Fin (t * w) → ZMod 2) (P : Program) (E : RAMEnv) (pc β : ℕ) (s : RAMState)
    (hAt : At P pc (Stmt.compile (pinsketchRunStmt t w β) pc))
    (hpc : s.pc = pc)
    (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N) (hW : E.W = 8 * w)
    (hdet : E.det = detStd t N b ι)
    (h0 : ∀ i < N, ι i ≠ 0) (hinj : Set.InjOn ι (Set.Iio N))
    (hpayload : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) = packMem (8 * w) y j)
    (hpayloadWord : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) < 2 ^ E.W)
    (hzeroB : (∀ a, wordsOf (8 * w) (t * w) ≤ a → a < β → s.mem a = 0) ∧
      (∀ a, β + wordsOf (8 * w) (t * w) ≤ a → a < decoderAllocEnd t → s.mem a = 0))
    (hβL : wordsOf (8 * w) (t * w) ≤ β)
    (hβ2 : β + 2 * wordsOf (8 * w) (t * w) ≤ decoderAllocEnd t)
    (hβfit : β + 2 * wordsOf (8 * w) (t * w) < 2 ^ E.W) :
    Sem P E pc (pc + (pinsketchRunStmt t w β).len) s
      (fun k z => k ≤ layerCost t w ∧ decoderPost (N := N) b ι y z ∧
        ∀ a, decoderAllocEnd t ≤ a → z.mem a = s.mem a) := by
  have hAt7 : At P (pc + 59) (Stmt.compile positiveDecoderStmt (pc + 59)) := by
    have h := hAt
    rw [pinsketchRunStmt, runAtStmt] at h
    obtain ⟨-, h1⟩ := At.seqStmt h
    obtain ⟨-, h2⟩ := At.seqStmt h1
    obtain ⟨-, h3⟩ := At.seqStmt h2
    obtain ⟨-, h4⟩ := At.seqStmt h3
    obtain ⟨-, h5⟩ := At.seqStmt h4
    obtain ⟨-, h6⟩ := At.seqStmt h5
    exact h6
  have hcopy : Sem P E pc (pc + 59) s
      (fun k z => k ≤ 24 * wordsOf (8 * w) (t * w) + 39 ∧
        z = ⟨pc + 59, layerDecoderRegs (wordsOf (8 * w) (t * w)), bndEntryMem t w y s.mem⟩) := by
    have h := pinsketch_copyin_at_bounded b ι y P E pc β s hAt hpc hN ht htN hW hdet h0 hinj
      hpayload hpayloadWord hzeroB hβL hβ2 hβfit
    refine Sem.mono h (fun k z hz => ?_)
    obtain ⟨hk, hpc', hregs', hbelow, habove⟩ := hz
    refine ⟨hk, ?_⟩
    have hmem' : z.mem = bndEntryMem t w y s.mem := by
      funext a
      by_cases ha : a < decoderAllocEnd t
      · rw [hbelow a ha, bndEntryMem_lt ha]
      · rw [habove a (by omega), bndEntryMem_ge (by omega)]
    exact ramState_eq_of z ⟨pc + 59, layerDecoderRegs (wordsOf (8 * w) (t * w)),
      bndEntryMem t w y s.mem⟩ hpc' hmem' (fun d => by rw [hregs'])
  have hcore : Sem P E (pc + 59) (pc + 59 + positiveDecoderStmt.len)
      ⟨pc + 59, layerDecoderRegs (wordsOf (8 * w) (t * w)), bndEntryMem t w y s.mem⟩
      (fun k z => k ≤ positiveDecoderBudget t w ∧ decoderPost (N := N) b ι y z ∧
        ∀ a, decoderAllocEnd t ≤ a → z.mem a = bndEntryMem t w y s.mem a) := by
    rw [layerDecoderRegs_eq_start (8 * w) (wordsOf (8 * w) (t * w)) y rfl]
    exact layerPositiveDecoder_semB b ι y P E (pc + 59) (bndEntryMem t w y s.mem) hAt7 hN ht htN
      hW hdet h0 hinj (fun a ha => bndEntryMem_lt ha)
  have hlen : pc + 59 + positiveDecoderStmt.len = pc + (pinsketchRunStmt t w β).len := by
    rw [pinsketchRunStmt_length]
    omega
  rw [← hlen]
  refine Sem.mono (Sem.seq_bound hcopy (fun z _ hz => by subst hz; exact hcore)) ?_
  intro k z hz
  obtain ⟨hk, hpost, hfr⟩ := hz
  refine ⟨?_, hpost, ?_⟩
  · dsimp only [layerCost] at hk ⊢
    omega
  · intro a ha
    rw [hfr a ha, bndEntryMem_ge ha]

/-- **Proposition 2.1's decoder at an arbitrary payload base, from the bounded zero hypothesis that
Theorem 6.5's row loop supplies.**  The headline target: the run halts within the published budget
with `decoderPost`, and leaves every word at or above `decoderAllocEnd t` untouched. -/
theorem pinsketch_decoding_at_bounded (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (y : Fin (t * w) → ZMod 2) (β : ℕ) (s : RAMState)
    (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N) (h0 : ∀ i < N, ι i ≠ 0)
    (hinj : Set.InjOn ι (Set.Iio N)) (hpc : s.pc = 0)
    (hpayload : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) = packMem (8 * w) y j)
    (hpayloadWord : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) < 2 ^ (8 * w))
    (hzeroB : (∀ a, wordsOf (8 * w) (t * w) ≤ a → a < β → s.mem a = 0) ∧
      (∀ a, β + wordsOf (8 * w) (t * w) ≤ a → a < decoderAllocEnd t → s.mem a = 0))
    (hβL : wordsOf (8 * w) (t * w) ≤ β)
    (hβ2 : β + 2 * wordsOf (8 * w) (t * w) ≤ decoderAllocEnd t)
    (hβfit : β + 2 * wordsOf (8 * w) (t * w) < 2 ^ (8 * w)) :
    ∃ s', HaltsWithin (programOfStatement (pinsketchRunStmt t w β))
        (detEnv (8 * w) (detStd t N b ι))
        (((positiveDecoderBudget t w + (24 * wordsOf (8 * w) (t * w) + 40) : ℕ) : ℝ)) s s' ∧
      decoderPost (N := N) b ι y s' ∧
      (∀ a, decoderAllocEnd t ≤ a → s'.mem a = s.mem a) := by
  have hNw := layerUniverse_lt_two_pow b ι h0 hinj
  have hw1 : 1 ≤ w := layerDimension_pos hN hNw
  have hAt : At (programOfStatement (pinsketchRunStmt t w β)) 0
      (Stmt.compile (pinsketchRunStmt t w β) 0) :=
    layerAt_of_append (pre := []) (code := Stmt.compile (pinsketchRunStmt t w β) 0)
      (post := [iHalt]) rfl rfl
  have hsem := pinsketchRun_semB b ι y (programOfStatement (pinsketchRunStmt t w β))
    (detEnv (8 * w) (detStd t N b ι)) 0 β s hAt hpc hN ht htN rfl rfl h0 hinj hpayload
    hpayloadWord hzeroB hβL hβ2 hβfit
  rw [Nat.zero_add] at hsem
  have hhalt : (programOfStatement (pinsketchRunStmt t w β))[(pinsketchRunStmt t w β).len]?
      = some iHalt := by
    unfold programOfStatement
    rw [← Stmt.length_compile (pinsketchRunStmt t w β) 0,
      List.getElem?_append_right (by omega)]
    simp
  refine layerHalts_of_run (P := programOfStatement (pinsketchRunStmt t w β))
    (E := detEnv (8 * w) (detStd t N b ι)) (a := 0) (e := (pinsketchRunStmt t w β).len) (s := s)
    (B := (((positiveDecoderBudget t w + (24 * wordsOf (8 * w) (t * w) + 40) : ℕ) : ℝ)))
    (Q := fun k z => k ≤ layerCost t w ∧ decoderPost (N := N) b ι y z ∧
      ∀ a, decoderAllocEnd t ≤ a → z.mem a = s.mem a)
    (Post := fun s' => decoderPost (N := N) b ι y s' ∧
      ∀ a, decoderAllocEnd t ≤ a → s'.mem a = s.mem a) hhalt hsem ?_
  intro k z hq
  obtain ⟨hk, hpost, hfr⟩ := hq
  refine ⟨?_, hpost, hfr⟩
  have hcost : layerCost t w ≤ positiveDecoderBudget t w + 24 * wordsOf (8 * w) (t * w) + 39 := by
    rw [layerCost]
    omega
  have hkR : (k : ℝ) ≤ ((positiveDecoderBudget t w : ℕ) : ℝ)
      + 24 * ((wordsOf (8 * w) (t * w) : ℕ) : ℝ) + 39 := by
    have hcast : (k : ℝ) ≤ (layerCost t w : ℝ) := by exact_mod_cast hk
    have hcl : (layerCost t w : ℝ) ≤ ((positiveDecoderBudget t w : ℕ) : ℝ)
        + 24 * ((wordsOf (8 * w) (t * w) : ℕ) : ℝ) + 39 := by exact_mod_cast hcost
    linarith
  push_cast
  linarith

end Main

end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main in
/-- Proposition 2.1's decoder from the bounded zero hypothesis -- submission wrapper. -/
theorem solution {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {N t w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (y : Fin (t * w) → ZMod 2) (β : ℕ) (s : RAMState)
    (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N) (h0 : ∀ i < N, ι i ≠ 0)
    (hinj : Set.InjOn ι (Set.Iio N)) (hpc : s.pc = 0)
    (hpayload : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) = packMem (8 * w) y j)
    (hpayloadWord : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) < 2 ^ (8 * w))
    (hzeroB : (∀ a, wordsOf (8 * w) (t * w) ≤ a → a < β → s.mem a = 0) ∧
      (∀ a, β + wordsOf (8 * w) (t * w) ≤ a → a < LinearSetReconciliation327.Main.decoderAllocEnd t →
        s.mem a = 0))
    (hβL : wordsOf (8 * w) (t * w) ≤ β)
    (hβ2 : β + 2 * wordsOf (8 * w) (t * w) ≤
      LinearSetReconciliation327.Main.decoderAllocEnd t)
    (hβfit : β + 2 * wordsOf (8 * w) (t * w) < 2 ^ (8 * w)) :
    ∃ s', LinearSetReconciliation327.Main.HaltsWithin
        (LinearSetReconciliation327.Main.programOfStatement
          (LinearSetReconciliation327.Main.pinsketchRunStmt t w β))
        (LinearSetReconciliation327.Main.detEnv (8 * w)
          (LinearSetReconciliation327.Main.detStd t N b ι))
        (((LinearSetReconciliation327.Main.positiveDecoderBudget t w
          + (24 * LinearSetReconciliation327.Main.wordsOf (8 * w) (t * w) + 40) : ℕ) : ℝ)) s s' ∧
      LinearSetReconciliation327.Main.decoderPost (N := N) b ι y s' ∧
      (∀ a, LinearSetReconciliation327.Main.decoderAllocEnd t ≤ a → s'.mem a = s.mem a) :=
  LinearSetReconciliation327.Main.pinsketch_decoding_at_bounded b ι y β s hN ht htN h0 hinj hpc
    hpayload hpayloadWord hzeroB hβL hβ2 hβfit
