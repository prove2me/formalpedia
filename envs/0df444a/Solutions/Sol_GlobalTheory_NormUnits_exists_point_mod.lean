-- Prove2me | solution 1 for GlobalTheory.NormUnits.exists_point_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:28:17.5162+00:00
-- url     : https://prove2.me/submissions/bd5f0323-8385-4dc9-a23a-885b4c16e963

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TotalDegreeCMulXMulX
import Theorems.Thm_GlobalTheory_NormUnits_finite_res
import Theorems.Thm_GlobalTheory_NormUnits_totalDegree_C_mul_X_mul_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NormUnits
open MvPolynomial
variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
namespace GlobalTheory.NormUnits
theorem _root_.solution [LocallyCompactSpace K] (s t c : K) (hs : ‖s‖ ≤ 1) (ht : ‖t‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    ∃ a b z : K, ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ ‖z‖ ≤ 1 ∧ (‖a‖ = 1 ∨ ‖b‖ = 1 ∨ ‖z‖ = 1) ∧
      ‖a ^ 2 + s * a * b + t * b ^ 2 - c * z ^ 2‖ < 1 := by
  classical
  haveI := finite_res K
  letI : Fintype (Res K) := Fintype.ofFinite _
  let k := Res K
  let π : intRing K →+* k := Ideal.Quotient.mk _
  let S : intRing K := ⟨s, mem_closedBall_zero_iff.2 hs⟩
  let T : intRing K := ⟨t, mem_closedBall_zero_iff.2 ht⟩
  let Cc : intRing K := ⟨c, mem_closedBall_zero_iff.2 hc⟩
  set p := ringChar k
  haveI : CharP k p := ringChar.charP k
  obtain ⟨n, hpp, -⟩ := FiniteField.card (K := k) p
  let f : MvPolynomial (Fin 3) k := C 1 * (X 0 * X 0) + C (π S) * (X 0 * X 1) + C (π T) * (X 1 * X 1) +
    C (-π Cc) * (X 2 * X 2)
  have hdeg : f.totalDegree < Fintype.card (Fin 3) := by
    have h1 := totalDegree_C_mul_X_mul_X (1 : k) 0 0
    have h2 := totalDegree_C_mul_X_mul_X (π S) 0 1
    have h3 := totalDegree_C_mul_X_mul_X (π T) 1 1
    have h4 := totalDegree_C_mul_X_mul_X (-π Cc) 2 2
    have := (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le
      ((totalDegree_add _ _).trans (max_le h1 h2)) h3)) h4)
    simp only [Fintype.card_fin]
    exact lt_of_le_of_lt this (by norm_num)
  have hdvd := char_dvd_card_solutions p hdeg
  have hpos : 0 < Fintype.card {x : Fin 3 → k // eval x f = 0} :=
    Fintype.card_pos_iff.2 ⟨⟨0, by simp [f]⟩⟩
  have h1lt : 1 < Fintype.card {x : Fin 3 → k // eval x f = 0} :=
    lt_of_lt_of_le hpp.one_lt (Nat.le_of_dvd hpos hdvd)
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card h1lt ⟨0, by simp [f]⟩
  have hx0 : x.1 ≠ 0 := fun h => hx (Subtype.ext h)
  choose l hl using fun i => Ideal.Quotient.mk_surjective (I := maxIdeal K) (x.1 i)
  have hval : π (l 0 * l 0 + S * (l 0 * l 1) + T * (l 1 * l 1) + (-Cc) * (l 2 * l 2)) = 0 := by
    have := x.2
    simp only [f, map_add, map_mul, eval_C, eval_X, map_neg, one_mul] at this
    simp only [map_add, map_mul, map_neg, π, hl]
    linear_combination this
  have hmem := (Ideal.Quotient.eq_zero_iff_mem).1 hval
  rw [mem_maxIdeal] at hmem
  have hunit : ∀ i, x.1 i ≠ 0 → ‖((l i : intRing K) : K)‖ = 1 := by
    intro i hi
    refine le_antisymm (norm_le_one K _) (not_lt.1 fun h => hi ?_)
    rw [← hl i]; exact (Ideal.Quotient.eq_zero_iff_mem).2 ((mem_maxIdeal K _).2 h)
  refine ⟨l 0, l 1, l 2, norm_le_one K _, norm_le_one K _, norm_le_one K _, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx0
    fin_cases i
    · exact Or.inl (hunit 0 hi)
    · exact Or.inr (Or.inl (hunit 1 hi))
    · exact Or.inr (Or.inr (hunit 2 hi))
  · convert hmem using 2
    simp only [S, T, Cc, Subring.coe_add, Subring.coe_mul, Subring.coe_neg]
    ring
end GlobalTheory.NormUnits
