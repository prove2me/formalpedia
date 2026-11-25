-- Prove2me | solution 1 for GlobalTheory.IsGenericPointHom.range_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:20:56.591543+00:00
-- url     : https://prove2.me/submissions/dd078f29-3c06-40a3-b726-2b5c1428df28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback

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
variable {U S : Scheme.{u}} [IsIntegral S] {j : U ⟶ S}
namespace GlobalTheory.IsGenericPointHom
theorem _root_.solution (hj : IsGenericPointHom j) : Set.range j = {genericPoint S} := by
  obtain ⟨e, rfl⟩ := hj
  have hgen : ∀ y : S, y ⤳ genericPoint S → y = genericPoint S := fun y hy =>
    (hy.antisymm ((genericPoint_spec S).specializes trivial)).eq
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, rfl⟩
    apply hgen
    have hy : (e.hom ≫ S.fromSpecStalk (genericPoint S)) u ∈ Set.range (S.fromSpecStalk (genericPoint S)) :=
      ⟨e.hom u, by simp⟩
    rwa [Scheme.range_fromSpecStalk] at hy
  · rintro rfl
    have hη : genericPoint S ∈ Set.range (S.fromSpecStalk (genericPoint S)) := by
      rw [Scheme.range_fromSpecStalk]
      exact specializes_rfl
    obtain ⟨u, hu⟩ := hη
    exact ⟨e.inv u, by simp [hu]⟩
end GlobalTheory.IsGenericPointHom
