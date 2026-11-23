-- Prove2me | solution 1 for GlobalTheory.isAffineHom_of_flatQuotient_of_affine_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:45.54887+00:00
-- url     : https://prove2.me/submissions/bed57aff-95ba-478d-987d-536232b10c86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Theorems.Thm_GlobalTheory_isAffineHom_descendsAlong_fpqc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (G B T : Over S) [GrpObj G] [GrpObj B] [GrpObj T] (q : G ⟶ B) (i : T ⟶ G),
      IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left →
      IsPullback i (toUnit _) q (η[B]) → IsAffineHom T.hom → IsAffineHom q.left := by
  intro S G B T _ _ _ q i hq hi hfl hs hqc hker hT
  have hiq : i ≫ q = 1 := by rw [hker.w, Hom.one_def]
  have hw : fst G T ≫ q = (fst G T * (snd G T ≫ i)) ≫ q := by
    rw [mul_comp, Category.assoc, hiq, comp_one, _root_.mul_one]
  have hpb : IsPullback (fst G T) (fst G T * (snd G T ≫ i)) q q := by
    refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
      (fun s => lift s.fst (hker.lift (s.fst⁻¹ * s.snd) (toUnit _) (by
        rw [mul_comp, GrpObj.inv_comp, s.condition, inv_mul_cancel, Hom.one_def])))
      (fun s => lift_fst _ _) (fun s => ?_) (fun s m h1 h2 => ?_)⟩⟩
    · rw [comp_mul, lift_fst, ← Category.assoc, lift_snd, hker.lift_fst, mul_inv_cancel_left]
    · refine hom_ext _ _ (by rw [h1, lift_fst]) ?_
      rw [lift_snd]
      refine hker.hom_ext ?_ (toUnit_unique _ _)
      rw [hker.lift_fst, ← h1, ← h2, comp_mul, Category.assoc, inv_mul_cancel_left]
  have hfst : IsAffineHom (fst G T).left := by
    show IsAffineHom (pullback.fst G.hom T.hom)
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.hom T.hom).flip hT
  exact @MorphismProperty.of_isPullback_of_descendsAlong _ _ _ _ _ _ _ _ _ _ _ _
    _root_.GlobalTheory.isAffineHom_descendsAlong_fpqc (hpb.map (Over.forget S)) ⟨⟨hs, hfl⟩, hqc⟩ hfst
end _root_.GlobalTheory
end GlobalTheory
