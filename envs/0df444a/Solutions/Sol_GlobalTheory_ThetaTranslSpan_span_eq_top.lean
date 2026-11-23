-- Prove2me | solution 1 for GlobalTheory.ThetaTranslSpan.span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:47.084205+00:00
-- url     : https://prove2.me/submissions/1c45acf7-e2d2-4216-8d0c-98e80cd31a3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependentThetaPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_exists_im_eq
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslSpan
variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
namespace GlobalTheory.ThetaTranslSpan
theorem _root_.solution (hH : Hm.PosDef) (Λ : AddSubgroup (Fin g → ℂ)) [DiscreteTopology Λ]
    (hΛ : ∀ v, (∀ a ∈ Λ, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = k) → v ∈ Λ) :
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨y, hy⟩ := exists_im_eq hH f
  have hmem : ∀ t : ℝ, t • y ∈ Λ := fun t => hΛ _ fun a ha => ⟨0, by
    rw [star_smul, smul_dotProduct, Complex.smul_im, hy,
      LinearMap.mem_ker.1 (hf (Submodule.subset_span ha))]
    simp⟩
  have hc : Continuous fun t : ℝ => (⟨t • y, hmem t⟩ : Λ) :=
    Continuous.subtype_mk (continuous_id.smul continuous_const) _
  have h := ((IsLocallyConstant.iff_continuous _).2 hc).apply_eq_of_preconnectedSpace 1 0
  have hy0 : y = 0 := by simpa using h
  apply hf0
  ext a
  all_goals simp [← hy, hy0]
end GlobalTheory.ThetaTranslSpan
