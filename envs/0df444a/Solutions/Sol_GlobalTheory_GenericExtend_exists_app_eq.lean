-- Prove2me | solution 1 for GlobalTheory.GenericExtend.exists_app_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:26:57.840236+00:00
-- url     : https://prove2.me/submissions/bf3e9d79-4ecd-4bae-a50f-8d11a94dc8eb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleGeneratorExtendingDensePart
import Theorems.Thm_GlobalTheory_GenericExtend_extAt_apply
import Theorems.Thm_GlobalTheory_bijective_resG_of_coheight_le_one
import Theorems.Thm_GlobalTheory_injective_appLE_of_eq
import Theorems.Thm_GlobalTheory_resG_resG
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenericExtend
namespace GlobalTheory.GenericExtend
theorem _root_.solution {Q Y : Scheme.{0}} [IsLocallyNoetherian Y] [GlobalTheory.IsNormalScheme Y]
    (J : Q ⟶ Y) [IsPreimmersion J] (hJ : ∀ V, Function.Injective (J.app V).hom) (W : Y.Opens)
    (f : Γ(Q, J ⁻¹ᵁ W)) (h : ∀ y ∈ W, Order.coheight y ≤ 1 → y ∉ Set.range J → ExtAt J W f y) :
    ∃ s : Γ(Y, W), (J.app W).hom s = f := by
  have h' : ∀ y : {y : Y // ExtAt J W f y}, ExtAt J W f y := fun y ↦ y.2
  choose V hV s hy hs using h'
  have hm : ∀ y, ExtAt J W f y → y ∈ iSup V := fun y hy' ↦ Opens.mem_iSup.2 ⟨⟨y, hy'⟩, hy _⟩
  have hW : iSup V ≤ W := iSup_le hV
  obtain ⟨s', hs', -⟩ := Y.sheaf.existsUnique_gluing' V (iSup V) (fun i ↦ homOfLE (le_iSup V i))
    le_rfl s fun a b ↦ by
      apply injective_appLE_of_eq J (W := J ⁻¹ᵁ (V a ⊓ V b)) rfl (hJ _)
      have h₁ := congrArg (resG Q (J.preimage_mono (inf_le_left : V a ⊓ V b ≤ _))) (hs a)
      have h₂ := congrArg (resG Q (J.preimage_mono (inf_le_right : V a ⊓ V b ≤ _))) (hs b)
      rw [resG_resG, res_appLE_apply] at h₁ h₂
      exact (appLE_res_apply J inf_le_left _ _).trans
        ((h₁.trans h₂.symm).trans (appLE_res_apply J inf_le_right _ _).symm)
  obtain ⟨s₀, hs₀⟩ := (bijective_resG_of_coheight_le_one hW fun y hy h1 ↦ hm y (by
    by_cases hr : y ∈ Set.range J
    · obtain ⟨q, rfl⟩ := hr
      exact extAt_apply J W f q hy
    · exact h y hy h1 hr)).2 s'
  refine ⟨s₀, Q.sheaf.eq_of_locally_eq' (fun i ↦ J ⁻¹ᵁ V i) (J ⁻¹ᵁ W)
    (fun i ↦ homOfLE (J.preimage_mono (hV i)))
    (fun q hq ↦ Opens.mem_iSup.2 ⟨⟨_, extAt_apply J W f q hq⟩, hy _⟩) _ _ fun i ↦ ?_⟩
  refine Eq.trans ?_ (hs i)
  have e : s i = resG Y (hV i) s₀ := by
    rw [← hs' i, ← hs₀]
    exact resG_resG hW (le_iSup V i) s₀
  rw [e, appLE_res_apply]
  rfl
end GlobalTheory.GenericExtend
