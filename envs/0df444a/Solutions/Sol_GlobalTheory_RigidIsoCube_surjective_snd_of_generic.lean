-- Prove2me | solution 1 for GlobalTheory.RigidIsoCube.surjective_snd_of_generic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:51.917249+00:00
-- url     : https://prove2.me/submissions/cfc0aef4-dddb-4544-99c2-5ac14e348263

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RigidifiedIsoRespectsCubeAndSymmetry
import Theorems.Thm_GlobalTheory_RigidIsoCube_surjective_appTop_of_baseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_snd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RigidIsoCube
namespace GlobalTheory.RigidIsoCube
theorem _root_.solution (hG : GlobalFnsSt) {S S' : Scheme.{0}} (k : S' ⟶ S) [QuasiCompact k]
    [IsSchemeTheoreticallyDominant k] (G : Over S) [GrpObj G] [Flat G.hom] {A : Over S'} [GrpObj A]
    (hA : IsAbelianScheme A) {g : A.left ⟶ G.left} (hg : IsPullback g A.hom G.hom k) (T : Over S) [Flat T.hom] :
    Function.Surjective (snd G T).left.appTop.hom := by
  let T' : Over S' := Over.mk (pullback.snd T.hom k)
  have : IsSchemeTheoreticallyDominant (pullback.fst T.hom k) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback T.hom k).flip
  have big : IsPullback (pullback.fst A.hom T'.hom ≫ g) (pullback.snd A.hom T'.hom) G.hom
      (pullback.fst T.hom k ≫ T.hom) := by
    rw [pullback.condition]
    exact (IsPullback.of_hasPullback A.hom T'.hom).paste_horiz hg
  have sq : IsPullback (pullback.lift (pullback.fst A.hom T'.hom ≫ g) (pullback.snd A.hom T'.hom ≫ pullback.fst T.hom k)
      (by rw [big.w, Category.assoc])) (pullback.snd A.hom T'.hom) (pullback.snd G.hom T.hom) (pullback.fst T.hom k) :=
    IsPullback.of_right (by rw [pullback.lift_fst]; exact big) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback G.hom T.hom)
  have : Flat (snd G T).left := inferInstanceAs (Flat (pullback.snd G.hom T.hom))
  refine surjective_appTop_of_baseChange (p := (snd G T).left) sq (lift (1 : T ⟶ G) (𝟙 T)).left ?_ (surj_snd hG hA T')
  exact congrArg (fun q => q.left) (lift_snd (1 : T ⟶ G) (𝟙 T))
end GlobalTheory.RigidIsoCube
