-- Prove2me | solution 1 for GlobalTheory.isIso_of_isOpenImmersion_of_geometricallyConnected
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:03:40.509243+00:00
-- url     : https://prove2.me/submissions/e88ad075-d474-4334-ada8-435b7c833999

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIsoOfIsOpenImmersionOfGeometricallyConnected
import Theorems.Thm_GlobalTheory_OpenSubgroupScheme_range_eq_univ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (Ga G : Over S) [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G), IsMonHom p →
      IsOpenImmersion p.left → LocallyOfFiniteType G.hom → GeometricallyConnected G.hom → IsIso p := by
  intro S Ga G _ _ p _ _ _ _
  have hsurj : Set.range p.left = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    let s : S := G.hom y
    let Ω : Type := AlgebraicClosure (S.residueField s)
    let t : Spec (CommRingCat.of Ω) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)) ≫ S.fromSpecResidueField s
    have ht : G.hom y = t (IsLocalRing.closedPoint Ω) :=
      (Scheme.fromSpecResidueField_apply s _).symm
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y _ ht
    have : IsOpenImmersion ((Over.pullback t).map p).left :=
      MorphismProperty.overPullbackMap _ _ ‹_›
    have : LocallyOfFiniteType ((Over.pullback t).obj G).hom := by
      show LocallyOfFiniteType (pullback.snd G.hom t); infer_instance
    have : ConnectedSpace ((Over.pullback t).obj G).left :=
      GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback G.hom t)
    have h := OpenSubgroupScheme.range_eq_univ ((Over.pullback t).map p)
    obtain ⟨w, hw⟩ : z ∈ Set.range ((Over.pullback t).map p).left := h ▸ Set.mem_univ _
    refine ⟨pullback.fst Ga.hom t w, ?_⟩
    have e : ((Over.pullback t).map p).left ≫ pullback.fst G.hom t = pullback.fst Ga.hom t ≫ p.left :=
      pullback.lift_fst _ _ _
    rw [← hz, ← hw, ← Scheme.Hom.comp_apply, ← e]
    rfl
  have : IsIso p.left := isIso_of_isOpenImmersion_of_opensRange_eq_top p.left (by
    ext1
    exact hsurj)
  have : IsIso ((Over.forget S).map p) := this
  exact isIso_of_reflects_iso p (Over.forget S)
end GlobalTheory
