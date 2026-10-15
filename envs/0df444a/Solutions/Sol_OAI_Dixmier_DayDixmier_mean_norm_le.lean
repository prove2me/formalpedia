-- Prove2me | solution 1 for OAI.Dixmier.DayDixmier.mean_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:09:16.330978+00:00
-- url     : https://prove2.me/submissions/cbf5824e-9526-4dc3-bb76-ccd079fee4e4

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/MeanBounds.lean:L60-L85
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.DayDixmier.mean_norm_le. The node keeps its source
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

lemma mean_real_bound (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ)
    (h1 : m (BoundedContinuousFunction.const G 1) = 1)
    (hp : ∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0)
    (f : G →ᵇ ℂ) (C : ℝ) (hf : ∀ x, (f x).im = 0)
    (hC : ∀ x, |(f x).re| ≤ C) : (m f).im = 0 ∧ ‖m f‖ ≤ C := by
  have hplus := hp (BoundedContinuousFunction.const G (C : ℂ) + f) (by
    intro x
    simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.const_apply,
      Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, hf, add_zero]
    exact ⟨by have := (abs_le.mp (hC x)).1; linarith, trivial⟩)
  have hminus := hp (BoundedContinuousFunction.const G (C : ℂ) - f) (by
    intro x
    simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.const_apply,
      Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, hf, sub_zero]
    exact ⟨sub_nonneg.mpr (abs_le.mp (hC x)).2, trivial⟩)
  rw [map_add, mean_const m h1] at hplus
  rw [map_sub, mean_const m h1] at hminus
  have hi : (m f).im = 0 := by simpa using hplus.2
  refine ⟨hi, ?_⟩
  have hr : |(m f).re| ≤ C := by
    apply abs_le.mpr
    constructor <;> simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at * <;>
      linarith [hplus.1, hminus.1]
  have heq : m f = ((m f).re : ℂ) := by
    apply Complex.ext <;> simp [hi]
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  exact hr

variable [DiscreteTopology G]

lemma mean_norm_le (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ)
    (h1 : m (BoundedContinuousFunction.const G 1) = 1)
    (hp : ∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) (f : G →ᵇ ℂ) : ‖m f‖ ≤ 2 * ‖f‖ := by
  have hr : ‖m (realComponent f)‖ ≤ ‖f‖ :=
    (mean_real_bound m h1 hp _ ‖f‖ (fun _ => rfl)
      (fun g => by
        change |(f g).re| ≤ ‖f‖
        exact (Complex.abs_re_le_norm _).trans (f.norm_coe_le_norm g))).2
  have hi : ‖m (imagComponent f)‖ ≤ ‖f‖ :=
    (mean_real_bound m h1 hp _ ‖f‖ (fun _ => rfl)
      (fun g => by
        change |(f g).im| ≤ ‖f‖
        exact (Complex.abs_im_le_norm _).trans (f.norm_coe_le_norm g))).2
  have hf : f = realComponent f + Complex.I • imagComponent f := by
    ext g
    change f g = ((f g).re : ℂ) + Complex.I * ((f g).im : ℂ)
    apply Complex.ext <;> simp
  have hm := congrArg m hf
  rw [map_add, map_smul] at hm
  rw [hm]
  calc
    ‖m (realComponent f) + Complex.I • m (imagComponent f)‖ ≤
        ‖m (realComponent f)‖ + ‖Complex.I • m (imagComponent f)‖ := norm_add_le _ _
    _ ≤ ‖f‖ + ‖f‖ := by simpa using add_le_add hr hi
    _ = 2 * ‖f‖ := by ring

end DayDixmier
end Dixmier
end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier OAI.Dixmier.DayDixmier
open scoped BoundedContinuousFunction ComplexConjugate


theorem solution : type_of% @_root_.OAI.Dixmier.DayDixmier.mean_norm_le := @_root_.OAI.Dixmier.DayDixmier.mean_norm_le
