-- Prove2me | solution 1 for Malliavin.exists_multipleIntegralCLM_eq_simplexIntegralLI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:07:18.998344+00:00
-- url     : https://prove2.me/submissions/a093f4f9-fc4f-4f17-b918-58decfff63cd

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
import Theorems.Thm_Malliavin_multipleIntegralCLM_apply
import Theorems.Thm_Malliavin_IteratedIntegralConstruction_symmetrizeRestrict_surjective
import Theorems.Thm_Malliavin_iteratedIntegralCLM_symmetrized
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (n : ℕ)
    (g : IteratedIntegralConstruction.SimplexKernel (n + 1)) :
    ∃ f : IteratedKernel (n + 1),
      multipleIntegralCLM hB (n + 1) f =
        IteratedIntegralConstruction.simplexIntegralLI hB n g := by
  let c : ℝ := ((n + 1).factorial : ℕ)
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact_mod_cast (n + 1).factorial_ne_zero
  obtain ⟨f, hf⟩ :=
    IteratedIntegralConstruction.symmetrizeRestrict_surjective (n + 1) (c⁻¹ • g)
  refine ⟨f, ?_⟩
  rw [multipleIntegralCLM_apply, iteratedIntegralCLM_symmetrized, hf, map_smul]
  change c • c⁻¹ • IteratedIntegralConstruction.simplexIntegralLI hB n g = _
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
end Malliavin
