-- Prove2me | solution 1 for OAI.Dixmier.DayDixmier.averagedForm_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:13:57.478535+00:00
-- url     : https://prove2.me/submissions/75159434-d4a2-448b-b785-6e06c4149adc

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/AveragedForm.lean:L97-L125
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.DayDixmier.averagedForm_lower. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Regular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Parameters__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FrameParameters__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_ComplexFrames__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Frames__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Masked__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_MaskAlgebra__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_LocalBounds__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_UniverseTransport__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_MeanBounds
import Definitions.Def_OAI_Analysis_Unitarizability_AveragedForm

-- ---- from OAI.Analysis.Unitarizability.MeanBounds ----
namespace OAI

noncomputable section
namespace Dixmier
namespace DayDixmier
open scoped BoundedContinuousFunction ComplexConjugate
variable {G : Type*} [TopologicalSpace G]

lemma mean_const (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ)
    (h1 : m (BoundedContinuousFunction.const G 1) = 1) (z : ℂ) :
    m (BoundedContinuousFunction.const G z) = z := by
  have hc : BoundedContinuousFunction.const G z =
      z • BoundedContinuousFunction.const G (1 : ℂ) := by
    ext g
    simp
  rw [hc, map_smul, h1, smul_eq_mul, mul_one]

variable [DiscreteTopology G]

end DayDixmier
end Dixmier
end

end OAI

-- ---- from OAI.Analysis.Unitarizability.AveragedForm ----
namespace OAI

noncomputable section
namespace Dixmier
namespace DayDixmier
open scoped BoundedContinuousFunction ComplexConjugate
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

section Form
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (π : G →* (H →L[ℂ] H)) {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ g, ‖π g‖ ≤ M)

lemma averagedForm_lower (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ)
    (h1 : m (BoundedContinuousFunction.const G 1) = 1)
    (hp : ∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) (x : H) :
    ‖x‖^2 ≤ M^2 * (m (coefficient π hM hπ x x)).re := by
  have hnorm (g : G) : ‖x‖ ≤ M * ‖π g⁻¹ x‖ := by
    calc
      ‖x‖ = ‖π g (π g⁻¹ x)‖ := by simp [← mul_apply_eq_comp, ← map_mul]
      _ ≤ ‖π g‖ * ‖π g⁻¹ x‖ := (π g).le_opNorm _
      _ ≤ M * ‖π g⁻¹ x‖ := mul_le_mul_of_nonneg_right (hπ g) (norm_nonneg _)
  have hpos := hp (((M^2 : ℝ) : ℂ) • coefficient π hM hπ x x -
      BoundedContinuousFunction.const G ((‖x‖^2 : ℝ) : ℂ)) (by
    intro g
    have hre : (inner ℂ (π g⁻¹ x) (π g⁻¹ x)).re = ‖π g⁻¹ x‖^2 := by
      simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) (π g⁻¹ x)
    have him : (inner ℂ (π g⁻¹ x) (π g⁻¹ x)).im = 0 := by
      simpa only [RCLike.im_to_complex] using inner_self_im (𝕜 := ℂ) (π g⁻¹ x)
    simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply,
      BoundedContinuousFunction.const_apply, coefficient_apply, smul_eq_mul, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.sub_im, Complex.mul_im, zero_add, hre, him, mul_zero]
    constructor
    · have hsqr := (sq_le_sq₀ (norm_nonneg x)
        (mul_nonneg hM (norm_nonneg (π g⁻¹ x)))).mpr (hnorm g)
      nlinarith [hsqr]
    · simp)
  rw [map_sub, map_smul, mean_const m h1] at hpos
  simpa only [smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, sub_nonneg] using hpos.1

end Form

end DayDixmier
end Dixmier
end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier OAI.Dixmier.DayDixmier
open scoped BoundedContinuousFunction ComplexConjugate


theorem solution : type_of% @_root_.OAI.Dixmier.DayDixmier.averagedForm_lower := @_root_.OAI.Dixmier.DayDixmier.averagedForm_lower
