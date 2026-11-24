-- Prove2me | solution 1 for GlobalTheory.universallyClosed_of_closed_cover_in_universallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:41:19.106032+00:00
-- url     : https://prove2.me/submissions/0d08ce38-010c-44e7-8018-7e5291857bfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniversallyClosedOfClosedCoverInUniversallyClose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S X Y P : Scheme.{0}) (f : X ⟶ S) (π : Y ⟶ X) (q : Y ⟶ P) (s : P ⟶ S) (T : Set Y),
      UniversallyClosed s → IsImmersion q → q ≫ s = π ≫ f → IsClosed T → IsClosed (q '' T) →
        π '' T = Set.univ → UniversallyClosed f := by
  intro S X Y P f π q s T hs hq hcomm hT hqT hπT
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨T, hT⟩ : TopologicalSpace.Closeds Y)
  have hrange : Set.range I.subschemeι = T := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have hcl : IsClosedImmersion (I.subschemeι ≫ q) := by
    refine .of_isPreimmersion _ ?_
    have : Set.range (I.subschemeι ≫ q) = q '' T := by
      rw [← hrange, ← Set.range_comp]; rfl
    rw [this]; exact hqT
  have : UniversallyClosed ((I.subschemeι ≫ π) ≫ f) := by
    rw [Category.assoc, ← hcomm, ← Category.assoc]
    infer_instance
  have : Surjective (I.subschemeι ≫ π) := by
    constructor
    have : Set.range (I.subschemeι ≫ π) = π '' T := by
      rw [← hrange, ← Set.range_comp]; rfl
    rw [← Set.range_eq_univ, this]; exact hπT
  exact UniversallyClosed.of_comp_surjective (I.subschemeι ≫ π) f
end GlobalTheory
