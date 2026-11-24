-- Prove2me | solution 1 for GlobalTheory.isIso_stalkMap_genericPoint_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:04:54.065611+00:00
-- url     : https://prove2.me/submissions/3de6bdeb-d4e2-47e6-9ad2-a91668e9eef0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg
import Theorems.Thm_GlobalTheory_apply_genericPoint_of_isDominant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S T : Scheme.{0}} (f : S ⟶ T) [IsIntegral S]
    [IsIntegral T] [IsDominant f] (hf : Function.Injective f)
    (z : Spec T.functionField ⟶ S) (hz : z ≫ f = T.fromSpecStalk (genericPoint T)) :
    IsIso (f.stalkMap (genericPoint S)) := by
  have hs : z (IsLocalRing.closedPoint _) = genericPoint S := by
    apply hf
    rw [apply_genericPoint_of_isDominant f]
    refine (Scheme.Hom.comp_apply z f _).symm.trans ?_
    rw [hz]
    exact Scheme.fromSpecStalk_closedPoint
  have hF : IsField (S.presheaf.stalk (z (IsLocalRing.closedPoint _))) := by
    rw [hs]; exact Field.toIsField S.functionField
  rw [← hs]
  have h1 : IsIso (Scheme.stalkClosedPointTo (z ≫ f)) := by
    rw [hz, Scheme.stalkClosedPointTo_fromSpecStalk]
    infer_instance
  rw [Scheme.stalkClosedPointTo_comp] at h1
  have h2 : IsIso (Scheme.stalkClosedPointTo z) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · letI := hF.toField
      exact (Scheme.stalkClosedPointTo z).hom.injective
    · intro y
      obtain ⟨x, hx⟩ := (@ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ _ h1).2 y
      exact ⟨_, hx⟩
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (Scheme.stalkClosedPointTo z) h2 h1
end GlobalTheory
