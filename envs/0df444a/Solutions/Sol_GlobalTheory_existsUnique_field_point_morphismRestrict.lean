-- Prove2me | solution 1 for GlobalTheory.existsUnique_field_point_morphismRestrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:38:11.192669+00:00
-- url     : https://prove2.me/submissions/7a7052e5-7183-4406-ad08-4affafef0b2a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg

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
theorem _root_.solution {S T : Scheme.{0}} (f : S ⟶ T)
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) (V : T.Opens)
    (k : Type) [Field k] (w : Sp k ⟶ V) : ∃! z : Sp k ⟶ (f ⁻¹ᵁ V), z ≫ (f ∣_ V) = w := by
  obtain ⟨z, hz, hu⟩ := h k (w ≫ V.ι)
  have P := (isPullback_morphismRestrict f V).flip
  refine ⟨P.lift z w hz, P.lift_snd _ _ _, fun y hy ↦ ?_⟩
  apply P.hom_ext
  · rw [P.lift_fst]
    apply hu
    show (y ≫ _) ≫ f = _
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy]
  · rw [P.lift_snd]; exact hy
end GlobalTheory
