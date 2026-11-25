-- Prove2me | solution 1 for GlobalTheory.VeryDenseFibres.mem_smoothLocus_of_smooth_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:39:14.420791+00:00
-- url     : https://prove2.me/submissions/c1c9ac13-5411-4eff-8249-db348d6fe2d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedGenericFibreOfDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionAndGeometricallyConnect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.VeryDenseFibres
namespace GlobalTheory.VeryDenseFibres
theorem _root_.solution {R : CommRingCat.{0}} {X : Scheme.{0}} (f : X ⟶ Spec R)
    [LocallyOfFinitePresentation f] [Flat f] (x : X)
    (h : Smooth (f.fiberToSpecResidueField (f x))) : x ∈ f.smoothLocus := by
  wlog hX : ∃ S, X = Spec S generalizing f X
  · obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
    have _ : Smooth (pullback.snd f ((Spec R).fromSpecResidueField
        ((X.affineCover.f i ≫ f) y))) := h
    have H := this (X.affineCover.f i ≫ f) y (by
      rw [Scheme.Hom.fiberToSpecResidueField, ← pullbackRightPullbackFstIso_inv_snd_snd]
      infer_instance) ⟨_, rfl⟩
    rwa [← Scheme.Hom.preimage_smoothLocus_eq] at H
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  letI := φ.hom.toAlgebra
  haveI : Algebra.FinitePresentation R S :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation) (φ := φ)).mp ‹_›
  haveI : Module.Flat R S :=
    (HasRingHomProperty.Spec_iff (P := @Flat) (φ := φ)).mp ‹_›
  haveI : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  let p : PrimeSpectrum R := Spec.map φ x
  haveI : x.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  haveI : Algebra.FormallySmooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
    rw [← RingHom.formallySmooth_algebraMap]
    refine RingHom.Smooth.formallySmooth ?_
    rw [← CommRingCat.hom_ofHom (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber ↑S)),
      ← HasRingHomProperty.Spec_iff (P := @Smooth),
      ← MorphismProperty.arrow_mk_iso_iff (P := @Smooth) (Spec.fiberToSpecResidueFieldIso R S p)]
    exact h
  haveI := Algebra.IsSmoothAt.of_formallySmooth_fiber (R := R) p.asIdeal x.asIdeal
  obtain ⟨g, hg, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R x.asIdeal
  let j : Spec (CommRingCat.of (Localization.Away g)) ⟶ Spec S :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))
  haveI : IsOpenImmersion j := IsOpenImmersion.of_isLocalization g
  haveI : Smooth (j ≫ Spec.map φ) := by
    rw [← Spec.map_comp, HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hsm
  obtain ⟨y, rfl⟩ : x ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ g]
    exact hg
  have := (j ≫ Spec.map φ).smoothLocus_eq_top.ge (Set.mem_univ y)
  rwa [← Scheme.Hom.preimage_smoothLocus_eq] at this
end GlobalTheory.VeryDenseFibres
