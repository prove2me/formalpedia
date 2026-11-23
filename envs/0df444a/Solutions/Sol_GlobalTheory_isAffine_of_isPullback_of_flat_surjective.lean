-- Prove2me | solution 1 for GlobalTheory.isAffine_of_isPullback_of_flat_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:35.008156+00:00
-- url     : https://prove2.me/submissions/a7ac53d0-3a1d-4928-b006-bc2942c9adee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Theorems.Thm_GlobalTheory_quasiCompact_descendsAlong_fpqc
import Theorems.Thm_GlobalTheory_quasiSeparated_descendsAlong_fpqc
import Theorems.Thm_GlobalTheory_ProperFunctions_isPushout_appTop


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
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency.types false
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X}
    {p : X ⟶ S} {q : Y ⟶ T} (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [Flat f]
    [Surjective f] [IsAffine Y] : IsAffine X := by
  have hQf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) f :=
    ⟨⟨‹Surjective f›, ‹Flat f›⟩, inferInstance⟩
  have : QuasiCompact p :=
    @MorphismProperty.of_isPullback_of_descendsAlong _ _ _ _ _ _ _ _ _ _ _ _
      _root_.GlobalTheory.quasiCompact_descendsAlong_fpqc H.flip hQf (inferInstanceAs (QuasiCompact q))
  have : QuasiSeparated p :=
    @MorphismProperty.of_isPullback_of_descendsAlong _ _ _ _ _ _ _ _ _ _ _ _
      _root_.GlobalTheory.quasiSeparated_descendsAlong_fpqc H.flip hQf (inferInstanceAs (QuasiSeparated q))
  have hSpec : IsPullback (Spec.map g.appTop) (Spec.map q.appTop) (Spec.map p.appTop)
      (Spec.map f.appTop) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (_root_.GlobalTheory.ProperFunctions.isPushout_appTop H)
  have hfsq : IsPullback (inv T.toSpecΓ) (Spec.map f.appTop) f (inv S.toSpecΓ) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, Scheme.toSpecΓ_naturality]⟩
  have hQ' : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map g.appTop) :=
    MorphismProperty.of_isPullback hSpec.flip (MorphismProperty.of_isPullback hfsq hQf)
  have hiso : IsPullback T.toSpecΓ f (Spec.map f.appTop) S.toSpecΓ :=
    IsPullback.of_horiz_isIso ⟨(Scheme.toSpecΓ_naturality f).symm⟩
  have hbig : IsPullback (Y.toSpecΓ ≫ Spec.map q.appTop) g (Spec.map f.appTop)
      (X.toSpecΓ ≫ Spec.map p.appTop) := by
    rw [← Scheme.toSpecΓ_naturality, ← Scheme.toSpecΓ_naturality]
    exact H.flip.paste_horiz hiso
  have htop : IsPullback Y.toSpecΓ g (Spec.map g.appTop) X.toSpecΓ :=
    IsPullback.of_right hbig (Scheme.toSpecΓ_naturality g).symm hSpec.flip
  have : MorphismProperty.isomorphisms Scheme.{u} X.toSpecΓ :=
    MorphismProperty.of_isPullback_of_descendsAlong htop hQ'
      (MorphismProperty.isomorphisms.infer_property _)
  exact ⟨this⟩
end _root_.GlobalTheory
end GlobalTheory
