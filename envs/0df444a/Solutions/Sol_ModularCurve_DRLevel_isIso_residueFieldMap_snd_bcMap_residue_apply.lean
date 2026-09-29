-- Prove2me | solution 1 for ModularCurve.DRLevel.isIso_residueFieldMap_snd_bcMap_residue_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/cccd685d-f20d-5052-a6ed-c83ad12c85af

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRLevel_isIso_residueFieldMap_snd_bcMap_residue_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

namespace ECL_ResIso

private theorem isIso_residueFieldMap_of_isClosedImmersion {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    (x : X) : IsIso (f.residueFieldMap x) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  have hs : Function.Surjective (f.stalkMap x ≫ X.residue x).hom := by
    rw [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (X.residue_surjective x).comp (SurjectiveOnStalks.stalkMap_surjective f x)
  rw [← Scheme.residue_residueFieldMap, CommRingCat.hom_comp, RingHom.coe_comp] at hs
  exact Function.Surjective.of_comp hs

end ECL_ResIso

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    (O : Type) [CommRing O] [IsLocalRing O] (ρO : DRLevel.R q →+* O)
    (s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ DRLevel.fibre (N₀ := N₀) ((IsLocalRing.residue O).comp ρO))
    (hs : s ≫ pullback.snd _ _ = 𝟙 _) :
    IsIso ((DRLevel.XO.toBase (N₀ := N₀) ρO).residueFieldMap
      ((DRLevel.bcMap ρO (IsLocalRing.residue O)).base
        (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))))) := by

  haveI hsCI : IsClosedImmersion s :=
    isClosedImmersion_of_comp_eq_id (pullback.snd _ _) s hs
  haveI hρ : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  haveI hιCI : IsClosedImmersion (DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O)) := by
    rw [DRLevel.bcMap]
    exact MorphismProperty.pullbackMap (P := @IsClosedImmersion) (inferInstance : IsClosedImmersion (𝟙 _)) hρ
      (by rw [Category.id_comp]) (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])
  let ι := DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O)
  let π := DRLevel.XO.toBase (N₀ := N₀) ρO
  show IsIso (π.residueFieldMap (ι.base (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)))))

  have hιπ : ι ≫ π = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) := by
    show DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O) ≫ DRLevel.XO.toBase (N₀ := N₀) ρO = _
    rw [DRLevel.bcMap, pullback.map]
    exact pullback.lift_snd _ _ _
  have hcomp : (s ≫ ι) ≫ π = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) :=
    calc (s ≫ ι) ≫ π = s ≫ (ι ≫ π) := Category.assoc _ _ _
      _ = s ≫ (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) :=
          congrArg (fun t => s ≫ t) hιπ
      _ = (s ≫ pullback.snd _ _) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) :=
          (Category.assoc _ _ _).symm
      _ = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) :=
          congrArg (fun t => t ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) hs
      _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) := Category.id_comp _
  haveI hsι : IsClosedImmersion (s ≫ ι) :=
    MorphismProperty.IsStableUnderComposition.comp_mem (P := @IsClosedImmersion) s ι hsCI hιCI

  have h2 : IsIso ((s ≫ ι).residueFieldMap (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))) :=
    ECL_ResIso.isIso_residueFieldMap_of_isClosedImmersion _ _
  have h3 : IsIso (((s ≫ ι) ≫ π).residueFieldMap (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))) := by
    rw [Scheme.Hom.residueFieldMap_congr hcomp]
    haveI := ECL_ResIso.isIso_residueFieldMap_of_isClosedImmersion
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))
    infer_instance
  rw [Scheme.residueFieldMap_comp] at h3
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h2 h3

end S_ModularCurve_DRLevel_isIso_residueFieldMap_snd_bcMap_residue_apply
end P2MW
export P2MW.S_ModularCurve_DRLevel_isIso_residueFieldMap_snd_bcMap_residue_apply (solution)
