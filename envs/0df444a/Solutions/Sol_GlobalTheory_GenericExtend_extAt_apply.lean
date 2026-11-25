-- Prove2me | solution 1 for GlobalTheory.GenericExtend.extAt_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:04:05.643191+00:00
-- url     : https://prove2.me/submissions/6dec92e3-6360-4121-8d17-1bbd0425f84f

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
theorem _root_.solution {Q Y : Scheme.{0}} (J : Q ⟶ Y) [IsPreimmersion J] (W : Y.Opens)
    (f : Γ(Q, J ⁻¹ᵁ W)) (q : Q) (hq : J q ∈ W) : ExtAt J W f (J q) := by
  obtain ⟨σ, hσ⟩ := J.stalkMap_surjective q (Q.presheaf.germ (J ⁻¹ᵁ W) q hq f)
  obtain ⟨V, hV, s, rfl⟩ := Y.presheaf.exists_germ_eq σ
  rw [Scheme.Hom.germ_stalkMap_apply] at hσ
  obtain ⟨O, hO, i₁, i₂, hh⟩ := Q.presheaf.germ_eq q _ _ _ _ hσ
  obtain ⟨A, hA, hAO⟩ := J.isEmbedding.isInducing.isOpen_iff.1 O.isOpen
  let V' : Y.Opens := ⟨A, hA⟩ ⊓ V ⊓ W
  have hle : J ⁻¹ᵁ V' ≤ O := fun z hz ↦ by
    rw [← SetLike.mem_coe, ← hAO]; exact hz.1.1
  refine ⟨V', inf_le_right, resG Y (inf_le_left.trans inf_le_right) s,
    ⟨⟨by rw [← SetLike.mem_coe, ← hAO] at hO; exact hO, hV⟩, hq⟩, ?_⟩
  have := congrArg (resG Q hle) hh
  rw [appLE_res_apply]
  refine Eq.trans ?_ (this.trans (resG_resG i₂.le hle f))
  exact (resG_resG i₁.le hle _).symm
end GlobalTheory.GenericExtend
