-- Prove2me | solution 1 for Malliavin.homogeneousChaos_zero_eq_constants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:10:11.743303+00:00
-- url     : https://prove2.me/submissions/16909b5b-dadd-4fc2-8bac-568bb00fb296

import Definitions.Def_Malliavin_MultipleIntegral
import Definitions.Def_Malliavin_WienerChaos
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_multipleIntegralCLM_zeroOrder
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Topology symmDiff
noncomputable section
open Malliavin
universe u v u_1 u_2 u_4 u_6
universe u₁ u₂ u₃
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
set_option linter.style.haveILetI false
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) :
    letI : IsProbabilityMeasure P := (hB.hasLaw ∅).isProbabilityMeasure
    (homogeneousChaos hB 0 : Submodule ℝ (RandomL2 P)) = constantRandomVariables P := by
  letI : IsProbabilityMeasure P := (hB.hasLaw ∅).isProbabilityMeasure
  unfold homogeneousChaos multipleIntegralRange constantRandomVariables
  apply le_antisymm <;> apply Submodule.topologicalClosure_mono
  · rintro x ⟨f, rfl⟩
    refine ⟨∫ t, f t ∂iteratedKernelMeasure 0, ?_⟩
    change Lp.const 2 P _ = multipleIntegralCLM hB 0 f
    apply Lp.ext
    exact (Lp.coeFn_const 2 P _).trans (multipleIntegralCLM_zeroOrder hB f).symm
  · rintro x ⟨c, rfl⟩
    let f : IteratedKernel 0 := Lp.const 2 (iteratedKernelMeasure 0) c
    refine ⟨f, ?_⟩
    change multipleIntegralCLM hB 0 f = Lp.const 2 P c
    apply Lp.ext
    have hfc : (fun t => f t) =ᵐ[iteratedKernelMeasure 0] fun _ => c :=
      Lp.coeFn_const 2 (iteratedKernelMeasure 0) c
    have hint : ∫ t, f t ∂iteratedKernelMeasure 0 = c := by
      rw [integral_congr_ae hfc, integral_const]
      simp only [iteratedKernelMeasure, Measure.pi_empty_univ, Measure.real, ENNReal.toReal_one,
        one_smul]
    have hI := multipleIntegralCLM_zeroOrder hB f
    rw [hint] at hI
    exact hI.trans (Lp.coeFn_const 2 P c).symm
end Malliavin
