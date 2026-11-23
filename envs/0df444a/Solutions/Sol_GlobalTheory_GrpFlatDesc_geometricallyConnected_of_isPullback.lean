-- Prove2me | solution 1 for GlobalTheory.GrpFlatDesc.geometricallyConnected_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:07:45.543162+00:00
-- url     : https://prove2.me/submissions/aa9e1ba7-bbcd-4807-b4a8-0e97d4b29ed1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupSchemeMorphismDescends

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GrpFlatDesc
open GrpDense MorphismProperty
variable {Z U : Scheme.{0}}
namespace GlobalTheory.GrpFlatDesc
theorem _root_.solution {A G : Scheme.{0}} {φ : A ⟶ G} {f : A ⟶ U} {g : G ⟶ Z} {j : U ⟶ Z}
    [Surjective j] (h : IsPullback φ f g j) [hf : GeometricallyConnected f] : GeometricallyConnected g := by
  refine ⟨fun K _ y W a b hW => ?_⟩

  obtain ⟨p, -⟩ := (pullback.fst y j).surjective (Classical.arbitrary _)
  let r := (Limits.pullback y j).fromSpecResidueField p
  let s := r ≫ pullback.fst y j
  let t := r ≫ pullback.snd y j
  have hst : t ≫ j = s ≫ y := by simp only [t, s, Category.assoc, pullback.condition]
  have hs : Surjective s := inferInstance

  have hc : ConnectedSpace ↥(Limits.pullback f t) := pullback_of_geometrically hf.1 _ t

  have hout : IsPullback (pullback.fst f t ≫ φ) (pullback.snd f t) g (s ≫ y) := by
    rw [← hst]
    exact (IsPullback.of_hasPullback f t).paste_horiz h
  let q : Limits.pullback f t ⟶ W :=
    hW.lift (pullback.fst f t ≫ φ) (pullback.snd f t ≫ s) (by simpa only [Category.assoc] using hout.w)
  have hq : IsPullback q (pullback.snd f t) b s :=
    IsPullback.of_right (by rwa [hW.lift_fst]) (hW.lift_snd _ _ _) hW
  have hqs : Surjective q := MorphismProperty.of_isPullback hq.flip hs
  exact hqs.surj.connectedSpace q.continuous
end GlobalTheory.GrpFlatDesc
