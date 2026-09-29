-- Prove2me | solution 1 for ModularCurve.DRLevel.isClosed_singleton_bcMap_residue_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/84b39498-1d63-57ff-a439-f07b867ed1ad

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRLevel_isClosed_singleton_bcMap_residue_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] [IsSeparated (DRLevel.toBase N₀ q)]
    (O : Type) [CommRing O] [IsLocalRing O] (ρO : DRLevel.R q →+* O)
    (s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ DRLevel.fibre (N₀ := N₀) ((IsLocalRing.residue O).comp ρO))
    (hs : s ≫ pullback.snd _ _ = 𝟙 _) :
    IsClosed ({(DRLevel.bcMap ρO (IsLocalRing.residue O)).base
        (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)))} :
      Set ↥(DRLevel.XO (N₀ := N₀) ρO)) := by
  classical

  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have hρι : Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ≫ Spec.map (CommRingCat.ofHom ρO) =
      Spec.map (CommRingCat.ofHom ((IsLocalRing.residue O).comp ρO)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hsq : IsPullback (DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O))
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue O).comp ρO))))
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) := by
    have h2 : DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O) ≫ pullback.snd (DRLevel.toBase N₀ q) _ =
        pullback.snd (DRLevel.toBase N₀ q) _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) := by
      rw [DRLevel.bcMap, pullback.map, pullback.lift_snd]
    refine IsPullback.of_right ?_ h2
      (IsPullback.of_hasPullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))
    have h1 : DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O) ≫ pullback.fst (DRLevel.toBase N₀ q) _ =
        pullback.fst (DRLevel.toBase N₀ q) _ := by
      rw [DRLevel.bcMap, pullback.map, pullback.lift_fst, Category.comp_id]
    rw [hρι]
    convert IsPullback.of_hasPullback (DRLevel.toBase N₀ q)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue O).comp ρO))) using 1
  haveI : IsClosedImmersion (DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O)) :=
    MorphismProperty.of_isPullback hsq.flip inferInstance

  haveI : IsClosedImmersion (s ≫ pullback.snd (DRLevel.toBase N₀ q) _) := by rw [hs]; infer_instance
  haveI : IsClosedImmersion s := IsClosedImmersion.of_comp s (pullback.snd (DRLevel.toBase N₀ q) _)

  have hrange : Set.range ⇑(s ≫ DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O)) =
      {(DRLevel.bcMap ρO (IsLocalRing.residue O)).base
        (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)))} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨q', rfl⟩
      rw [Subsingleton.elim q' (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))]
      rfl
    · rintro rfl
      exact ⟨_, rfl⟩
  haveI : IsClosedImmersion (s ≫ DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O)) :=
    MorphismProperty.comp_mem _ s _ ‹IsClosedImmersion s› ‹_›
  rw [← hrange]
  exact (s ≫ DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O)).isClosedEmbedding.isClosed_range

#print axioms solution

end S_ModularCurve_DRLevel_isClosed_singleton_bcMap_residue_apply
end P2MW
export P2MW.S_ModularCurve_DRLevel_isClosed_singleton_bcMap_residue_apply (solution)
