-- Prove2me | solution 1 for N25.jqRatioTwentyFive_middle_sub_const_limit
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:39.166727+00:00
-- url     : https://prove2.me/submissions/19229421-2d0c-421a-a24e-16421e6a98ac

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_N25_jAnalytic_middle_ratio_limit
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_N25_jAnalytic_sl_invariant
import Theorems.Thm_N25_jAnalytic_normalized_limit
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_hasSum_jNum_qParam
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_jqRatioTwentyFive_sub_const_realizeOf
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularForm_exists_degeneracy_Gamma0
import Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique
import Theorems.Thm_ModularCurve_realizeOf_eq_div

set_option autoImplicit false

open Filter Topology UpperHalfPlane ModularCurve

open scoped MatrixGroups

namespace N25

/-- The actual rational j-ratio has its exact finite limit at every width-five endpoint. -/
theorem _root_.solution (A : SL(2, ℤ))
    (hA5 : (5 : ℤ) ∣ A 1 0) (hA25 : ¬ (25 : ℤ) ∣ A 1 0) :
    ∃ v : ℤ, ¬ (5 : ℤ) ∣ v ∧ ∀ c : ℂ,
      Tendsto (fun τ : UpperHalfPlane =>
        realizeOf (CohCarrier.GammaH 25 N25.H25)
          (jqNModC ℂ 25 / jqModC ℂ - HahnSeries.C c) (A • τ))
        UpperHalfPlane.atImInfty
        (nhds (Complex.exp (-(2 * Real.pi * Complex.I * ((v : ℂ) / 5))) - c)) := by
  obtain ⟨v, hv, ht⟩ := jAnalytic_middle_ratio_limit A hA5 hA25
  refine ⟨v, hv, fun c => ?_⟩
  have hn : ∀ᶠ τ : UpperHalfPlane in atImInfty,
      Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) *
        (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) ≠ 0 :=
    jAnalytic_normalized_limit.eventually (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0))
  have he : ∀ᶠ τ : UpperHalfPlane in atImInfty, ModularForm.E₄ (A • τ) ≠ 0 := by
    filter_upwards [hn] with τ hτ
    have hj : ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ ≠ 0 :=
      (mul_ne_zero_iff.mp hτ).2
    have hjA : ModularForm.E₄ (A • τ) ^ 3 / ModularForm.discriminant (A • τ) ≠ 0 := by
      rwa [jAnalytic_sl_invariant]
    intro h
    apply hjA
    exact div_eq_zero_iff.mpr (Or.inl (by rw [h]; norm_num))
  apply (ht.sub_const c).congr'
  filter_upwards [he] with τ hτ
  exact (jqRatioTwentyFive_sub_const_realizeOf c (A • τ) hτ).symm

end N25
