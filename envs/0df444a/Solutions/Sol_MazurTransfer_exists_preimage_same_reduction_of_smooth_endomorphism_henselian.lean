-- Prove2me | solution 1 for MazurTransfer.exists_preimage_same_reduction_of_smooth_endomorphism_henselian
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-16T14:49:44.18293+00:00
-- url     : https://prove2.me/submissions/92bb9891-e195-41b5-b2ef-33098f23802f

/- Copyright (c) 2026 Vas and contributors. Apache-2.0. Original formal-neighborhood lifting corollary of the official smooth henselian section theorem. Consumer: nineteen-divisibility for the original local Picard formal subgroup. -/
import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
universe u

theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (e x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (h : SchemeHomOver f f) [Smooth h.1]
    (heh : e.1 ≫ h.1 = e.1)
    (hred : Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) ≫ x.1 =
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) ≫ e.1) :
    ∃ z : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f,
      z.1 ≫ h.1 = x.1 ∧
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) ≫ z.1 =
        Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) ≫ e.1 := by
  let r := Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))
  let P := pullback h.1 x.1
  haveI : Smooth (pullback.snd h.1 x.1) :=
    MorphismProperty.of_isPullback (P := @Smooth.{u})
      (IsPullback.of_hasPullback h.1 x.1) inferInstance
  let k : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ P :=
    pullback.lift (r ≫ e.1) r (by rw [Category.assoc, heh]; exact hred.symm)
  have hk : k ≫ pullback.snd h.1 x.1 = r := pullback.lift_snd _ _ _
  obtain ⟨s, hs, hreds⟩ := AlgebraicGeometry.Smooth.exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing (pullback.snd h.1 x.1) k hk
  have hz : (s ≫ pullback.fst h.1 x.1) ≫ h.1 = x.1 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  have hzover : (s ≫ pullback.fst h.1 x.1) ≫ f = 𝟙 _ := by
    calc
      (s ≫ pullback.fst h.1 x.1) ≫ f =
          (s ≫ pullback.fst h.1 x.1) ≫ (h.1 ≫ f) :=
        congrArg (fun (a : X ⟶ Spec (CommRingCat.of R)) =>
          (s ≫ pullback.fst h.1 x.1) ≫ a) h.2.symm
      _ = ((s ≫ pullback.fst h.1 x.1) ≫ h.1) ≫ f := (Category.assoc _ _ _).symm
      _ = x.1 ≫ f := congrArg (fun a => a ≫ f) hz
      _ = 𝟙 _ := x.2
  refine ⟨⟨s ≫ pullback.fst h.1 x.1, hzover⟩, hz, ?_⟩
  change r ≫ (s ≫ pullback.fst h.1 x.1) = r ≫ e.1
  rw [← Category.assoc, hreds]
  exact pullback.lift_fst _ _ _

#print axioms solution
