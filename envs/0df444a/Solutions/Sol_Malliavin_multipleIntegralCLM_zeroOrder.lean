-- Prove2me | solution 1 for Malliavin.multipleIntegralCLM_zeroOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:07:55.264799+00:00
-- url     : https://prove2.me/submissions/fda428dc-6024-40ee-8aa6-ffbc4ae77375

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
import Theorems.Thm_Malliavin_multipleIntegralCLM_apply
import Theorems.Thm_Malliavin_iteratedIntegralCLM_zeroOrder
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_symmetrizeL_eq_self_iff
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (f : IteratedKernel 0) :
    (fun ω => multipleIntegralCLM hB 0 f ω) =ᵐ[P]
      fun _ => ∫ t, f t ∂iteratedKernelMeasure 0 := by
  have hfixed : symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) 0 2 f = f := by
    rw [symmetrizeL_eq_self_iff]
    intro σ
    have hσ : σ = 1 := Subsingleton.elim _ _
    subst σ
    exact Filter.Eventually.of_forall fun _ => rfl
  simpa only [multipleIntegralCLM_apply, Nat.factorial_zero, Nat.cast_one, one_smul, hfixed] using
    iteratedIntegralCLM_zeroOrder hB f
end Malliavin
