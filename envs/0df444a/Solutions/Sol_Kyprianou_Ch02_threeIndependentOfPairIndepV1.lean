-- Prove2me | solution 1 for Kyprianou.Ch02.threeIndependentOfPairIndepV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:45:04.886307+00:00
-- url     : https://prove2.me/submissions/c0519808-d722-470e-a550-797a30b641c6

import Theorems.Thm_AvramDividend_Classical_avram_a28_probability_full_finite_rectangle_factorisation_implies_iIndepFun_20261116
import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (G L S : Ω → E)
    (hGP : IndepFun G (fun ω => (L ω, S ω)) P)
    (hLS : IndepFun L S P) :
    iIndepFun (fun (i : Fin 3) (ω : Ω) =>
      if i = 0 then G ω else if i = 1 then L ω else S ω) P := by
  let Y (i : ℕ) : Ω → E := if i = 0 then G else if i = 1 then L else S
  have hrect (A : Fin 3 → Set E) (hA : ∀ i, MeasurableSet (A i)) :
      P {ω | ∀ i : Fin 3, Y i.val ω ∈ A i} =
        ∏ i : Fin 3, P (Y i.val ⁻¹' A i) := by
    have he : {ω | ∀ i : Fin 3, Y i.val ω ∈ A i} =
        G ⁻¹' A 0 ∩ (L ⁻¹' A 1 ∩ S ⁻¹' A 2) := by
      ext ω
      simp [Fin.forall_fin_succ, Y]
    have hg := hGP.measure_inter_preimage_eq_mul (A 0) (A 1 ×ˢ A 2)
      (hA 0) ((hA 1).prod (hA 2))
    change P (G ⁻¹' A 0 ∩ (L ⁻¹' A 1 ∩ S ⁻¹' A 2)) =
      P (G ⁻¹' A 0) * P (L ⁻¹' A 1 ∩ S ⁻¹' A 2) at hg
    rw [he, hg, hLS.measure_inter_preimage_eq_mul (A 1) (A 2) (hA 1) (hA 2)]
    simp [Fin.prod_univ_three, Y, mul_assoc]
  have hind := AvramDividend.Classical.avram_a28_probability_full_finite_rectangle_factorisation_implies_iIndepFun_20261116
    P 3 Y hrect
  convert hind using 1
  funext i ω
  fin_cases i <;> rfl
