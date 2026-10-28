-- Prove2me | solution 1 for OAI.ElasticityDistribution.lower_realization_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:34:52.429997+00:00
-- url     : https://prove2.me/submissions/91dc63f7-a82a-4cfa-a9cb-11f9cb6e4588

import Mathlib
import Definitions.Def_OAIQ6El006
import Theorems.Thm_OAI_ElasticityDistribution_exists_lower_realization

section
-- module Solutions.OAIQ6_Elast.Elasticity_CGO
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open scoped BigOperators
namespace ElasticityRegularity
/-- The precise polynomial loss for the shifted scalar-principal system. -/
theorem quadratic_parameter_norm {W ι : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [Fintype ι] (R₀ R₂ : W) (R₁ : ι → W) :
    ∃ C : ℝ, 0<C ∧ ∀ z : ι → ℂ,
      ‖R₀+(∑ i, z i • R₁ i)+(∑ i, z i*z i) • R₂‖ ≤ C*(1+∑ i, ‖z i‖)^2 := by
  classical
  let S := ∑ i, ‖R₁ i‖
  refine ⟨‖R₀‖+S+‖R₂‖+1,by dsimp [S]; positivity,fun z => ?_⟩
  let Z := ∑ i, ‖z i‖
  have hZ : 0≤Z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hS : 0≤S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hz (i : ι) : ‖z i‖≤Z := Finset.single_le_sum (fun j _ => norm_nonneg (z j)) (Finset.mem_univ i)
  have hr (i : ι) : ‖R₁ i‖≤S := Finset.single_le_sum (fun j _ => norm_nonneg (R₁ j)) (Finset.mem_univ i)
  have hlin : ‖∑ i, z i • R₁ i‖ ≤ Z*S := by
    calc
      ‖∑ i, z i • R₁ i‖ ≤ ∑ i, ‖z i • R₁ i‖ := norm_sum_le _ _
      _ = ∑ i, ‖z i‖*‖R₁ i‖ := by simp only [norm_smul]
      _ ≤ ∑ i, ‖z i‖*S := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hr i) (norm_nonneg _))
      _ = Z*S := (Finset.sum_mul _ _ _).symm
  have hquad : ‖∑ i, z i*z i‖ ≤ Z^2 := by
    calc
      ‖∑ i, z i*z i‖ ≤ ∑ i, ‖z i*z i‖ := norm_sum_le _ _
      _ = ∑ i, ‖z i‖*‖z i‖ := by simp only [norm_mul]
      _ ≤ ∑ i, ‖z i‖*Z := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hz i) (norm_nonneg _))
      _ = Z^2 := by rw [← Finset.sum_mul]; change Z*Z=Z^2; ring
  have hn : ‖R₀+(∑ i, z i • R₁ i)+(∑ i, z i*z i) • R₂‖ ≤ ‖R₀‖+Z*S+Z^2*‖R₂‖ := by
    calc
      _ ≤ ‖R₀+(∑ i, z i • R₁ i)‖+‖(∑ i, z i*z i) • R₂‖ := norm_add_le _ _
      _ ≤ ‖R₀‖+Z*S+Z^2*‖R₂‖ := by
        rw [norm_smul]
        exact add_le_add ((norm_add_le _ _).trans (add_le_add_right hlin _))
          (mul_le_mul_of_nonneg_right hquad (norm_nonneg _))
  apply hn.trans
  change ‖R₀‖+Z*S+Z^2*‖R₂‖ ≤ (‖R₀‖+S+‖R₂‖+1)*(1+Z)^2
  have hW : 1 ≤ (1+Z)^2 := by nlinarith
  have hL : Z ≤ (1+Z)^2 := by nlinarith
  have hQ : Z^2 ≤ (1+Z)^2 := by nlinarith
  calc
    _ ≤ ‖R₀‖*(1+Z)^2+S*(1+Z)^2+‖R₂‖*(1+Z)^2 := by
      have h₀ := mul_le_mul_of_nonneg_left hW (norm_nonneg R₀)
      have h₁ := mul_le_mul_of_nonneg_left hL hS
      have h₂ := mul_le_mul_of_nonneg_left hQ (norm_nonneg R₂)
      nlinarith
    _ ≤ _ := by nlinarith [sq_nonneg (1+Z)]
end ElasticityRegularity

end
namespace ElasticityDistribution
open MeasureTheory TemperedDistribution

section
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open ElasticityAugmented ElasticityRegularity

/-- A fixed quadratic phase loss, with no elliptic estimate assumed. -/
theorem lower_realization_bound_oai (k : ℤ) {η ξ : X → ℂ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
    (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hcξ : HasCompactSupport ξ)
    (h1 : Set.EqOn ξ 1 (tsupport η))
    (A : Fin 3 → Fin 4 → Fin 4 → Coeff) (V : Fin 4 → Fin 4 → Coeff) (i : Fin 4) :
    ∃ C : ℝ, 0<C ∧ ∀ (z : Fin 3 → ℂ) (U : Fin 4 → Dist) (f : HV),
      (∀ j, sobolevInjection (k : ℝ) (f j)=smulLeftCLM ℂ ξ (U j)) →
      ∃ q : H, sobolevInjection ((k : ℝ)-1) q=smulLeftCLM ℂ η (lowerPart z A V U i) ∧
        ‖q‖ ≤ C*(1+∑ d, ‖z d‖)^2*‖f‖ := by
  obtain ⟨L₀,L₂,L₁,hL⟩ := exists_lower_realization k hη hcη hξ hcξ h1 A V i
  obtain ⟨C,hC,hn⟩ := quadratic_parameter_norm L₀ L₂ L₁
  refine ⟨C,hC,fun z U f hf => ⟨_,hL z U f hf,?_⟩⟩
  exact ((L₀+(∑ d, z d • L₁ d)+(∑ d, z d*z d) • L₂).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (hn z) (norm_nonneg f))

end
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal
open ElasticityAugmented ElasticityRegularity
end ElasticityDistribution

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityDistribution.lower_realization_bound_oai := @OAI.ElasticityDistribution.lower_realization_bound_oai
