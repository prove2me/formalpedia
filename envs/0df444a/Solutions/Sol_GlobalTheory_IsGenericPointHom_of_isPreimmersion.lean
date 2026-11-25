-- Prove2me | solution 1 for GlobalTheory.IsGenericPointHom.of_isPreimmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:21:26.019033+00:00
-- url     : https://prove2.me/submissions/07a68afe-a7b5-4661-a2ce-8195c0489b98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory
open ExtUnique
open GlobalTheory.IsGenericPointHom
namespace GlobalTheory.IsGenericPointHom
theorem _root_.solution {S : Scheme.{u}} [IsIntegral S] {K : Type u} [Field K] (j : Spec (.of K) ⟶ S)
    [IsPreimmersion j] [IsDominant j] : IsGenericPointHom j := by
  have hx : j (IsLocalRing.closedPoint K) = genericPoint S := by
    have hr : Set.range j = {j (IsLocalRing.closedPoint K)} := by
      ext y
      constructor
      · rintro ⟨u, rfl⟩
        rw [Subsingleton.elim u (IsLocalRing.closedPoint K)]
        rfl
      · rintro rfl
        exact ⟨_, rfl⟩
    have hg : IsGenericPoint (j (IsLocalRing.closedPoint K)) ⊤ := by
      show closure _ = Set.univ
      rw [← hr]
      exact j.denseRange.closure_range
    exact hg.eq (genericPoint_spec S)
  have hfield : IsField ↑(S.presheaf.stalk (j (IsLocalRing.closedPoint K))) := by
    rw [hx]
    exact Field.toIsField S.functionField
  let := hfield.toField
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo j) := by
    simp only [Scheme.stalkClosedPointTo, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (stalkClosedPointIso _).commRingCatIsoToRingEquiv.surjective.comp
      (j.stalkMap_surjective _)
  have hinj : Function.Injective (Scheme.stalkClosedPointTo j) :=
    (Scheme.stalkClosedPointTo j).hom.injective
  have : IsIso (Scheme.stalkClosedPointTo j) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  unfold IsGenericPointHom
  rw [← hx]
  exact ⟨asIso (Spec.map (Scheme.stalkClosedPointTo j)), Scheme.Spec_stalkClosedPointTo_fromSpecStalk j⟩
end GlobalTheory.IsGenericPointHom
