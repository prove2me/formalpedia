-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.mom_eq
-- status  : ACCEPTED   (disprove)
-- author  : @darkhipo
-- created : 2026-10-28T07:56:40.17878+00:00
-- url     : https://prove2.me/submissions/6a81ec59-f4dc-4b15-b7e1-d0c2d36432b8

import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0P
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# Disproof of `IntMul.Kappa.R8.Bit.Oppbank.mom_eq`

The statement `∀ τ : ℝ, histMoment net0P.hist 529 τ = histMoment bitR8 529 τ` is FALSE.

`net0P = NB.net (toNB ProjB.ch0P)`, and every edge of its program is either
`ProjB.dfltE` (no runs) or `ProjB.pickE (PE q R)` with `R ∈ {SideR r, DataR, AuxR}`.
Unfolding the run predicates (Defs4 `sideRuns`/`dataRuns`/`auxRuns`, ProjB
`SideR`/`DataR`/`AuxR`):

* `SideR r`: runs `sideRuns 23 529 r ++ rs'` — widths `2r - 23` (only when
  `23 < 2r`, and then `2r - 23 ≤ r` forces `r ≤ 23`) plus width-1 padding;
* `DataR`: widths `439`, `21` plus width-1 padding;
* `AuxR`: widths `23`, `483`.

So EVERY run width of `net0P` lies in `T = [1,3,5,…,23,439,483]` — all odd.
But `Jain.bitR8` carries even widths (`2, 4, …, 22, 484, 506, …, 528`) with
positive multiplicity.  Equality of the moments on ALL of `ℝ` would force the
two width multisets to agree; concretely, integer moments `q = 0..14` plus the
degree-14 polynomial `P(X) = ∏_{t ∈ T} (X - t)` give a linear relation that
every histogram supported on `T` satisfies but `bitR8` does not (`decide`).
-/

open IntMul.Kappa
open IntMul.Kappa.Jain
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.Net0P

namespace MmQ

open IntMul.Kappa.R8.Bit.Oppbank (v W Tmp wEnt wAuxEnd)
open IntMul.Kappa.R8.Bit.Oppbank.ProjB
open IntMul.Kappa.R8.Bit.Oppbank.NB (Wr prog chunkProg chunkInstrs blk1 blk2 entI corrI
  entE xorG)
open IntMul.Kappa.R6.Bit.NB (sideRuns dataRuns auxRuns runPairs)

/-- The finite support of every run width `net0P` can carry. -/
def T : List ℕ := [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 439, 483]

/-- Every run of a ProjB-family edge has width in `T`. -/
def OKEdge (e : Edge 529) : Prop := ∀ ρ ∈ e.runs, ρ.2.2 ∈ T

theorem OKEdge_dfltE : OKEdge (dfltE : Edge 529) := by
  intro ρ h
  simp [dfltE] at h

theorem twoR_sub_23_mem_T {r : ℕ} (h1 : 23 < 2 * r) (h2 : 2 * r - 23 ≤ r) :
    2 * r - 23 ∈ T := by
  have hr : 12 ≤ r ∧ r ≤ 23 := by omega
  obtain ⟨hlo, hhi⟩ := hr
  interval_cases r <;> decide

theorem sideR_widths {r : ℕ} {rs : List (ℕ × ℕ × ℕ)} (h : SideR r rs) :
    ∀ ρ ∈ rs, ρ.2.2 ∈ T := by
  obtain ⟨rs', hrs, h1, hlen⟩ := h
  intro ρ hρ
  rw [hrs] at hρ
  rcases List.mem_append.1 hρ with hρ | hρ
  · unfold sideRuns at hρ
    by_cases hc : 23 < 2 * r
    · simp only [if_pos hc] at hρ
      rcases List.mem_singleton.1 hρ with rfl
      have hlen' : 2 * r - 23 + rs'.length = r := by
        unfold sideRuns at hlen
        simp only [if_pos hc, runPairs, List.length_flatMap, List.length_map,
          List.length_range] at hlen
        exact hlen
      have h2 : 2 * r - 23 ≤ r := by omega
      exact twoR_sub_23_mem_T hc h2
    · simp only [if_neg hc] at hρ
      simp at hρ
  · have := h1 ρ hρ
    rw [this]
    decide

theorem dataR_widths {rs : List (ℕ × ℕ × ℕ)} (h : DataR rs) :
    ∀ ρ ∈ rs, ρ.2.2 ∈ T := by
  obtain ⟨rs', hrs, h1, _hlen⟩ := h
  intro ρ hρ
  rw [hrs] at hρ
  rcases List.mem_append.1 hρ with hρ | hρ
  · unfold dataRuns at hρ
    simp only [List.mem_cons, List.mem_nil_iff] at hρ
    rcases hρ with rfl | rfl | hfalse
    · decide
    · decide
    · simp at hfalse
  · have := h1 ρ hρ
    rw [this]
    decide

theorem auxR_widths {rs : List (ℕ × ℕ × ℕ)} (h : AuxR rs) :
    ∀ ρ ∈ rs, ρ.2.2 ∈ T := by
  intro ρ hρ
  have hrs : rs = auxRuns 19 := h
  rw [hrs] at hρ
  unfold auxRuns at hρ
  simp only [List.mem_cons, List.mem_nil_iff] at hρ
  rcases hρ with rfl | rfl | hfalse
  · decide
  · decide
  · simp at hfalse

theorem OKEdge_pickE {R : List (ℕ × ℕ × ℕ) → Prop}
    (q : Matrix (Fin 529) (Fin 529) ℚ)
    (hR : ∀ e : Edge 529, R e.runs → ∀ ρ ∈ e.runs, ρ.2.2 ∈ T) :
    OKEdge (pickE (PE q R)) := by
  unfold pickE
  by_cases h : ∃ e, PE q R e
  · rw [dif_pos h]
    exact hR _ (Classical.choose_spec h).2
  · rw [dif_neg h]
    exact OKEdge_dfltE

theorem OKEdge_e1 (b o c : ℕ) : OKEdge (ch0P.e1 b o c) := by
  change OKEdge (if b < v ∧ o < codeBound ∧ c < codeBound
    then pickE (PE (K S0 Si0 (Dm o c) (Pl b)) (SideR (rkC o c)))
    else dfltE)
  by_cases h : b < v ∧ o < codeBound ∧ c < codeBound
  · rw [if_pos h]
    exact OKEdge_pickE _ fun e he => sideR_widths he
  · rw [if_neg h]
    exact OKEdge_dfltE

theorem OKEdge_e2 (a o c : ℕ) : OKEdge (ch0P.e2 a o c) := by
  change OKEdge (if a < v ∧ o < codeBound ∧ c < codeBound
    then pickE (PE (K S0 Si0 (Pl a) (Dm o c)) (SideR (rkC o c)))
    else dfltE)
  by_cases h : a < v ∧ o < codeBound ∧ c < codeBound
  · rw [if_pos h]
    exact OKEdge_pickE _ fun e he => sideR_widths he
  · rw [if_neg h]
    exact OKEdge_dfltE

theorem OKEdge_ex (b : ℕ) : OKEdge (ch0P.ex b) := by
  change OKEdge (if b < v
    then pickE (PE (K S0 Si0 1 (1 - Pl b)) AuxR) else dfltE)
  by_cases h : b < v
  · rw [if_pos h]
    exact OKEdge_pickE _ fun e he => auxR_widths he
  · rw [if_neg h]
    exact OKEdge_dfltE

theorem OKEdge_en (a t : ℕ) : OKEdge (ch0P.en a t) := by
  change OKEdge (if a < v ∧ t < v
    then pickE (PE (K S0 Si0 (1 - Pl a) (1 - Pl t)) DataR) else dfltE)
  by_cases h : a < v ∧ t < v
  · rw [if_pos h]
    exact OKEdge_pickE _ fun e he => dataR_widths he
  · rw [if_neg h]
    exact OKEdge_dfltE

theorem OKEdge_ei (a : ℕ) : OKEdge (ch0P.ei a) := by
  change OKEdge (if a < v
    then pickE (PE (K S0 Si0 (1 - Pl a) 1) AuxR) else dfltE)
  by_cases h : a < v
  · rw [if_pos h]
    exact OKEdge_pickE _ fun e he => auxR_widths he
  · rw [if_neg h]
    exact OKEdge_dfltE

theorem OKEdge_ec (a s : ℕ) : OKEdge (ch0P.ec a s) := by
  change OKEdge (if a < v ∧ s < v
    then pickE (PE (K S0 Si0 (Pl a) (Pl s)) (SideR 1)) else dfltE)
  by_cases h : a < v ∧ s < v
  · rw [if_pos h]
    exact OKEdge_pickE _ fun e he => sideR_widths he
  · rw [if_neg h]
    exact OKEdge_dfltE

theorem OKEdge_toNB_e1 (b o c : ℕ) : OKEdge ((toNB ch0P).e1 b o c) := OKEdge_e1 b o c
theorem OKEdge_toNB_e2 (a o c : ℕ) : OKEdge ((toNB ch0P).e2 a o c) := OKEdge_e2 a o c
theorem OKEdge_toNB_ex (b : ℕ) : OKEdge ((toNB ch0P).ex b) := OKEdge_ex b
theorem OKEdge_toNB_en (a t : ℕ) : OKEdge ((toNB ch0P).en a t) := OKEdge_en a t
theorem OKEdge_toNB_ei (a : ℕ) : OKEdge ((toNB ch0P).ei a) := OKEdge_ei a
theorem OKEdge_toNB_ec (a s : ℕ) : OKEdge ((toNB ch0P).ec a s) := OKEdge_ec a s

theorem OKEdge_entE (a w : ℕ) : OKEdge (entE (toNB ch0P) a w) := by
  unfold entE
  split_ifs with h1 h2
  · exact OKEdge_toNB_en a w
  · exact OKEdge_toNB_en a (w - v)
  · exact OKEdge_toNB_ei a

/-! ## Lifting through the program -/

theorem ok_chunkInstrs {ι : ℕ → Wr} {E : ℕ → ℕ → Edge 529} {ch : LChunk}
    (hE : ∀ o c, OKEdge (E o c)) :
    ∀ i ∈ chunkInstrs ι E ch, ∀ e, Instr.edgeOf i = some e → OKEdge e := by
  intro i hi e hie
  unfold chunkInstrs at hi
  rcases List.mem_append.1 hi with hi | hi
  · rcases List.mem_map.1 hi with ⟨mv, _, rfl⟩
    simp only [Instr.edgeOf] at hie
    injection hie with h
    subst h
    exact hE _ _
  · rcases List.mem_map.1 hi with ⟨p, _, rfl⟩
    simp [xorG, Instr.edgeOf] at hie

theorem ok_chunkProg {ι : ℕ → Wr} {E : ℕ → ℕ → Edge 529} {cs : List LChunk}
    (hE : ∀ o c, OKEdge (E o c)) :
    ∀ i ∈ chunkProg ι E cs, ∀ e, Instr.edgeOf i = some e → OKEdge e := by
  intro i hi
  unfold chunkProg at hi
  rcases List.mem_flatMap.1 hi with ⟨c, _, hi⟩
  exact ok_chunkInstrs hE i hi

theorem ok_blk1 (b : ℕ) :
    ∀ i ∈ blk1 (toNB ch0P) b, ∀ e, Instr.edgeOf i = some e → OKEdge e := by
  intro i hi e hie
  unfold blk1 at hi
  rcases List.mem_append.1 hi with hi | hi
  · exact ok_chunkProg (fun o c => OKEdge_toNB_e1 b o c) i hi e hie
  · rcases List.mem_map.1 hi with ⟨w, _, rfl⟩
    simp only [Instr.edgeOf] at hie
    injection hie with h
    subst h
    exact OKEdge_toNB_ex b

theorem ok_entI (a : ℕ) :
    ∀ i ∈ entI (toNB ch0P) a, ∀ e, Instr.edgeOf i = some e → OKEdge e := by
  intro i hi e hie
  unfold entI at hi
  rcases List.mem_map.1 hi with ⟨w, _, rfl⟩
  simp only [Instr.edgeOf] at hie
  injection hie with h
  subst h
  exact OKEdge_entE a w

theorem ok_corrI (a s : ℕ) :
    ∀ i ∈ corrI (toNB ch0P) a s, ∀ e, Instr.edgeOf i = some e → OKEdge e := by
  intro i hi e hie
  unfold corrI at hi
  simp only [List.mem_cons, List.mem_nil_iff] at hi
  rcases hi with rfl | rfl | rfl | hfalse
  · simp [xorG, Instr.edgeOf] at hie
  · simp only [Instr.edgeOf] at hie
    injection hie with h
    subst h
    exact OKEdge_toNB_ec a s
  · simp [xorG, Instr.edgeOf] at hie
  · simp at hfalse

theorem ok_blk2 (a : ℕ) :
    ∀ i ∈ blk2 (toNB ch0P) a, ∀ e, Instr.edgeOf i = some e → OKEdge e := by
  intro i hi e hie
  unfold blk2 at hi
  rcases List.mem_append.1 hi with hi | hi
  · exact ok_entI a i hi e hie
  · rcases List.mem_append.1 hi with hi | hi
    · exact ok_chunkProg (fun o c => OKEdge_toNB_e2 a o c) i hi e hie
    · rcases List.mem_flatMap.1 hi with ⟨s, _, hi⟩
      exact ok_corrI a s i hi e hie

theorem ok_prog :
    ∀ i ∈ prog (toNB ch0P), ∀ e, Instr.edgeOf i = some e → OKEdge e := by
  intro i hi e hie
  unfold prog at hi
  rcases List.mem_append.1 hi with hi | hi
  · rcases List.mem_flatMap.1 hi with ⟨b, _, hi⟩
    exact ok_blk1 b i hi e hie
  · rcases List.mem_flatMap.1 hi with ⟨a, _, hi⟩
    exact ok_blk2 a i hi e hie

theorem ok_edges : ∀ e ∈ net0P.edges, OKEdge e := by
  have heq : net0P.edges = ((prog (toNB ch0P)).filterMap Instr.edgeOf) := rfl
  intro e he
  rw [heq] at he
  rcases List.mem_filterMap.1 he with ⟨i, hi, hie⟩
  exact ok_prog i hi e hie

theorem hist_width_mem_T : ∀ p ∈ (net0P.hist : List (ℕ × ℕ)), p.1 ∈ T := by
  have hdef : (net0P.hist : List (ℕ × ℕ)) = (net0P.widths.map fun w => (w, 1)) := rfl
  intro p hp
  rw [hdef] at hp
  rcases List.mem_map.1 hp with ⟨w, hw, rfl⟩
  show w ∈ T
  have hwdef : net0P.widths =
      (net0P.edges.flatMap fun e => e.runs.map fun ρ => ρ.2.2) := rfl
  rw [hwdef] at hw
  rcases List.mem_flatMap.1 hw with ⟨e, he, hw⟩
  rcases List.mem_map.1 hw with ⟨ρ, hρ, rfl⟩
  exact ok_edges e he ρ hρ

/-! ## Integer moments and the vanishing polynomial -/

/-- Power-sum moment `∑ n_w · w^q`. -/
def powSum (h : List (ℕ × ℕ)) (q : ℕ) : ℕ := (h.map fun p => p.2 * p.1 ^ q).sum

/-- Division as an additive homomorphism (for `List.sum_hom`). -/
noncomputable def divHom (c : ℝ) : ℝ →+ ℝ where
  toFun x := x / c
  map_zero' := by simp
  map_add' := by
    intro x y
    simp [add_div]

theorem sumDiv (l : List (ℕ × ℕ)) (g : (ℕ × ℕ) → ℝ) (c : ℝ) :
    (l.map fun p => g p / c).sum = (l.map g).sum / c := by
  have hkey : (l.map fun p => g p / c)
      = List.map (⇑(divHom c)) (l.map g) := by
    rw [List.map_map]
    rfl
  rw [hkey]
  show (List.map (⇑(divHom c)) (l.map g)).sum = ⇑(divHom c) ((l.map g).sum)
  exact List.sum_hom (l.map g) (divHom c)

theorem hsum (h : List (ℕ × ℕ)) (q : ℕ) :
    (h.map fun p => ((p.2 * p.1 ^ q : ℕ) : ℝ)).sum
      = (((h.map fun p => (p.2 * p.1 ^ q : ℕ))).sum : ℝ) := by
  have key : (h.map fun p => ((p.2 * p.1 ^ q : ℕ) : ℝ))
      = List.map (Nat.cast : ℕ → ℝ) (h.map fun p => (p.2 * p.1 ^ q : ℕ)) := by
    rw [List.map_map]
    rfl
  rw [key]
  exact (Nat.cast_list_sum _).symm

theorem histMoment_powSum (h : List (ℕ × ℕ)) (q : ℕ) :
    histMoment h 529 (q : ℝ) = (powSum h q : ℝ) / (529 : ℝ) ^ q := by
  have hterm : ∀ p : ℕ × ℕ,
      (p.2 : ℝ) * ((p.1 : ℝ) / (529 : ℕ)) ^ (q : ℝ) =
        ((p.2 * p.1 ^ q : ℕ) : ℝ) / (529 : ℝ) ^ q := by
    intro p
    push_cast
    rw [Real.rpow_natCast, div_pow, mul_div]
  unfold histMoment powSum
  simp only [hterm]
  rw [sumDiv h (fun p => ((p.2 * p.1 ^ q : ℕ) : ℝ)) ((529 : ℝ) ^ q), hsum]

/-- Coefficients of `P(X) = ∏_{t ∈ T} (X - t)` (degree 14). -/
def aL : List ℤ :=
  [67053339026999325, -149441852885597370, 125866494421536771, -56586699401393844,
    15633552112499133, -2852808722548246, 357445561481899, -31311845523992,
    1920742595519, -81252885318, 2281861329, -39378164, 354023, -1066, 1]

/-- `P(t)`. -/
def pEval (t : ℤ) : ℤ := ∑ j ∈ Finset.range 15, aL.getD j 0 * t ^ j

theorem pEval_T (t : ℕ) (ht : t ∈ T) : pEval t = 0 := by
  simp only [T, List.mem_cons, List.mem_nil_iff] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | hfalse
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp at hfalse

theorem sum_a_powSum : ∀ h : List (ℕ × ℕ),
    ∑ j ∈ Finset.range 15, aL.getD j 0 * ((powSum h j : ℕ) : ℤ)
      = (h.map fun p => (p.2 : ℤ) * pEval p.1).sum
  | [] => by simp [powSum]
  | p :: rest => by
    have ih := sum_a_powSum rest
    have hsplit : ∑ j ∈ Finset.range 15, aL.getD j 0 * ((powSum (p :: rest) j : ℕ) : ℤ) =
        ∑ j ∈ Finset.range 15, aL.getD j 0 * ((p.2 * p.1 ^ j : ℕ) : ℤ) +
        ∑ j ∈ Finset.range 15, aL.getD j 0 * ((powSum rest j : ℕ) : ℤ) := by
      show ∑ j ∈ Finset.range 15,
        aL.getD j 0 * (((p.2 * p.1 ^ j + powSum rest j : ℕ) : ℤ)) = _
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by
        push_cast
        ring
    have hpart : ∑ j ∈ Finset.range 15, aL.getD j 0 * ((p.2 * p.1 ^ j : ℕ) : ℤ)
        = (p.2 : ℤ) * pEval p.1 := by
      unfold pEval
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        push_cast [Nat.cast_mul, Nat.cast_pow]
        ring
    rw [hsplit, hpart, ih]
    show (p.2 : ℤ) * pEval p.1 + (rest.map fun p => (p.2 : ℤ) * pEval p.1).sum = _
    rfl

/-- Every histogram supported on `T` satisfies the degree-14 recurrence at `q = 0`. -/
theorem powSum_rec (h : List (ℕ × ℕ)) (hh : ∀ p ∈ h, p.1 ∈ T) :
    ∑ j ∈ Finset.range 15, aL.getD j 0 * ((powSum h j : ℕ) : ℤ) = 0 := by
  rw [sum_a_powSum]
  apply List.sum_eq_zero
  intro x hx
  rcases List.mem_map.1 hx with ⟨p, hp, rfl⟩
  exact mul_eq_zero_of_right _ (pEval_T p.1 (hh p hp))

theorem bitR8_rec_ne :
    ∑ j ∈ Finset.range 15, aL.getD j 0 * ((powSum bitR8 j : ℕ) : ℤ) ≠ 0 := by
  decide

end MmQ

open MmQ

theorem solution : ¬ (∀ τ : ℝ, histMoment net0P.hist 529 τ = histMoment bitR8 529 τ) := by
  intro H
  have key : ∀ q : ℕ, powSum net0P.hist q = powSum bitR8 q := by
    intro q
    have h1 := histMoment_powSum net0P.hist q
    have h2 := histMoment_powSum bitR8 q
    have hq := H (q : ℝ)
    rw [h1, h2] at hq
    have hc : ((529 : ℝ) ^ q) ≠ 0 := by positivity
    have hcast : (powSum net0P.hist q : ℝ) = (powSum bitR8 q : ℝ) := by
      have hmul := congrArg (· * ((529 : ℝ) ^ q)) hq
      have ha : (powSum net0P.hist q : ℝ) / (529 : ℝ) ^ q * (529 : ℝ) ^ q
          = (powSum net0P.hist q : ℝ) := div_mul_cancel₀ _ hc
      have hb : (powSum bitR8 q : ℝ) / (529 : ℝ) ^ q * (529 : ℝ) ^ q
          = (powSum bitR8 q : ℝ) := div_mul_cancel₀ _ hc
      rw [ha, hb] at hmul
      exact hmul
    exact_mod_cast hcast
  have hrec := powSum_rec net0P.hist hist_width_mem_T
  simp only [key] at hrec
  exact bitR8_rec_ne hrec
