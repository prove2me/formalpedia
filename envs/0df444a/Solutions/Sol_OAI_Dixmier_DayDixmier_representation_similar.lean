-- Prove2me | solution 1 for OAI.Dixmier.DayDixmier.representation_similar
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:17:22.715988+00:00
-- url     : https://prove2.me/submissions/41243c1f-7973-4534-af08-fca9a56f26c7

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Amenable.lean:L12-L65
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.DayDixmier.representation_similar. The node keeps its source
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
import Theorems.Thm_OAI_Dixmier_DayDixmier_averagedForm_lower
import Theorems.Thm_OAI_Dixmier_DayDixmier_mean_norm_le

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

lemma coefficient_norm_le (x y : H) :
    ‖coefficient π hM hπ x y‖ ≤ M^2 * ‖x‖ * ‖y‖ := by
  unfold coefficient BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _

lemma coefficient_translate (h : G) (x y : H) :
    coefficient π hM hπ (π h x) (π h y) = leftTranslate h (coefficient π hM hπ x y) := by
  ext g
  simp [leftTranslate, coefficient, map_mul, mul_apply_eq_comp]

lemma averagedForm_bound (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ)
    (h1 : m (BoundedContinuousFunction.const G 1) = 1)
    (hp : ∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) (x y : H) :
    ‖averagedForm π hM hπ m x y‖ ≤ (2 * M^2) * ‖x‖ * ‖y‖ := by
  change ‖m (coefficient π hM hπ x y)‖ ≤ _
  calc
    _ ≤ 2 * ‖coefficient π hM hπ x y‖ := mean_norm_le m h1 hp _
    _ ≤ 2 * (M^2 * ‖x‖ * ‖y‖) := mul_le_mul_of_nonneg_left
      (coefficient_norm_le π hM hπ x y) (by norm_num)
    _ = _ := by ring

lemma averagedForm_nonneg (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ)
    (hp : ∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) (x : H) :
    0 ≤ (m (coefficient π hM hπ x x)).re ∧ (m (coefficient π hM hπ x x)).im = 0 := by
  apply hp
  intro g
  simpa only [coefficient_apply, RCLike.re_to_complex, RCLike.im_to_complex] using
    And.intro (inner_self_nonneg (𝕜 := ℂ) (x := π g⁻¹ x)) (inner_self_im (𝕜 := ℂ) (π g⁻¹ x))

end Form

end DayDixmier
end Dixmier
end

end OAI

-- ---- from OAI.Analysis.Unitarizability.Amenable ----
namespace OAI

noncomputable section
namespace Dixmier
namespace DayDixmier
open scoped BoundedContinuousFunction ComplexConjugate
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

theorem representation_similar {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (hG : Amenable G) (π : G →* (H →L[ℂ] H))
    (hb : ∃ C : ℝ, ∀ g, ‖π g‖ ≤ C) : SimilarToUnitary π := by
  obtain ⟨m, h1, hp, hinv⟩ := hG
  obtain ⟨C, hC⟩ := hb
  let M : ℝ := max C 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hπ : ∀ g, ‖π g‖ ≤ M := fun g => (hC g).trans (le_max_left _ _)
  let B : H →L⋆[ℂ] H →L[ℂ] ℂ := (averagedForm π hM.le hπ m).mkContinuous₂
    (2 * M^2) (averagedForm_bound π hM.le hπ m h1 hp)
  let Q : H →L[ℂ] H := InnerProductSpace.continuousLinearMapOfBilin B
  have hQ (x y : H) : inner ℂ (Q x) y = m (coefficient π hM.le hπ x y) := by
    exact InnerProductSpace.continuousLinearMapOfBilin_apply B x y
  have hQpos : Q.IsPositive := by
    rw [ContinuousLinearMap.isPositive_iff_complex]
    intro x
    rw [hQ]
    have h := averagedForm_nonneg π hM.le hπ m hp x
    refine ⟨?_, h.1⟩
    apply Complex.ext <;> simp [h.2]
  have hQnonneg : 0 ≤ Q := (ContinuousLinearMap.nonneg_iff_isPositive Q).mpr hQpos
  have hunit : IsUnit Q := by
    apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map Q
      (c := ⟨(M^2)⁻¹, inv_nonneg.mpr (sq_nonneg M)⟩)
        (by change (0 : ℝ) < (M^2)⁻¹; positivity)
    intro x
    change ‖x‖^2 * (M^2)⁻¹ ≤ _
    rw [hQ]
    calc
      ‖x‖^2 * (M^2)⁻¹ ≤ (m (coefficient π hM.le hπ x x)).re := by
        rw [← div_eq_mul_inv, div_le_iff₀ (sq_pos_of_pos hM)]
        simpa only [mul_comm] using averagedForm_lower π hM.le hπ m h1 hp x
      _ ≤ ‖m (coefficient π hM.le hπ x x)‖ := Complex.re_le_norm _
  obtain ⟨s, hs⟩ := (CFC.isUnit_sqrt_iff Q hQnonneg).mpr hunit
  let S : H ≃L[ℂ] H := ContinuousLinearEquiv.ofUnit s
  have hS (x : H) : S x = CFC.sqrt Q x := by
    change (s : H →L[ℂ] H) x = _
    rw [hs]
  have hSsymmetric := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (CFC.sqrt_nonneg Q)).isSymmetric
  have hdiag (x : H) : ‖S x‖^2 = (m (coefficient π hM.le hπ x x)).re := by
    rw [hS, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    have heq : inner ℂ (CFC.sqrt Q x) (CFC.sqrt Q x) = inner ℂ (Q x) x := by
      calc
        _ = inner ℂ (CFC.sqrt Q (CFC.sqrt Q x)) x := (hSsymmetric _ _).symm
        _ = inner ℂ (Q x) x := by
          congr 1
          exact congrArg (fun T : H →L[ℂ] H => T x) (CFC.sqrt_mul_sqrt_self Q hQnonneg)
    rw [heq, hQ, RCLike.re_to_complex]
  refine ⟨S, ?_⟩
  intro g x
  have hequal : ‖S (π g (S.symm x))‖^2 = ‖x‖^2 := by
    rw [hdiag, coefficient_translate, hinv, ← hdiag, S.apply_symm_apply]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hequal

end DayDixmier

universe v
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  
end Dixmier
end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier OAI.Dixmier.DayDixmier
open scoped BoundedContinuousFunction ComplexConjugate


theorem solution : type_of% @_root_.OAI.Dixmier.DayDixmier.representation_similar := @_root_.OAI.Dixmier.DayDixmier.representation_similar
