-- Prove2me | solution 1 for GlobalTheory.genericPart_dense_proOpen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:45.88291+00:00
-- url     : https://prove2.me/submissions/da952fa4-09be-492c-97c9-eb0f7afed373

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GenericPartDenseProOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isProper_str

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
namespace GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
private lemma comap_algebraMap_fractionRing_specializes (O F : Type) [CommRing O] [IsDomain O] [Field F]
    [Algebra O F] [IsFractionRing O F] (x : PrimeSpectrum F) (y : PrimeSpectrum O) :
    PrimeSpectrum.comap (algebraMap O F) x ⤳ y := by
  rw [← PrimeSpectrum.le_iff_specializes]
  intro a ha
  have h0 : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [PrimeSpectrum.comap_asIdeal, h0, ← RingHom.ker_eq_comap_bot,
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective O F)] at ha
  rw [Ideal.mem_bot.mp ha]
  exact zero_mem _
end GlobalTheory
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct Pointwise
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (O F : Type) [CommRing O] [IsDedekindDomain O] [Field F] [Algebra O F] [IsFractionRing O F] (X U : Scheme.{0}) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) (jQ : U ⟶ pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))), Flat s → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s → IsOpenImmersion jQ → Dense (Set.range jQ) → IsLocallyNoetherian X ∧ CompactSpace X ∧ X.IsSeparated ∧ IsPreimmersion (jQ ≫ pullback.fst _ _) ∧ Flat (jQ ≫ pullback.fst _ _) ∧ IsDominant (jQ ≫ pullback.fst _ _) ∧ QuasiCompact (jQ ≫ pullback.fst _ _) := by
  intro O F _ _ _ _ _ X U s jQ hflat hproj hopen hdense
  obtain ⟨N, i, hi, hsi⟩ := hproj
  have := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str O N
  have hprop : IsProper s := by rw [← hsi]; infer_instance
  have hnO : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hnF : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp F) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hcF : CompactSpace (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp F) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hcO : CompactSpace (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hsepO : IsSeparated (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O).toSpecΓ := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hpre : IsPreimmersion (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
    exact IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have hflg : Flat (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
    rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat F (nonZeroDivisors O)
  have hnP : IsLocallyNoetherian (pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)))
  have hcP : CompactSpace ↥(pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)))
  have : IsNoetherian (pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) := ⟨⟩
  have : TopologicalSpace.NoetherianSpace U := jQ.isOpenEmbedding.isInducing.noetherianSpace
  have hdomj : IsDominant jQ := ⟨hdense⟩
  have hdomf : IsDominant (pullback.fst s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) := by
    constructor
    intro x
    obtain ⟨p⟩ : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp F) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
    have hp : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F) p ⤳ s x := comap_algebraMap_fractionRing_specializes O F p (s x)
    obtain ⟨x', hx', hsx'⟩ := Flat.generalizingMap s hp
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := s) (g := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)) x' p hsx'
    exact closure_mono (show {x'} ⊆ Set.range _ from Set.singleton_subset_iff.mpr ⟨z, hz⟩)
      (specializes_iff_mem_closure.mp hx')
  refine ⟨LocallyOfFiniteType.isLocallyNoetherian s, QuasiCompact.compactSpace_of_compactSpace s,
    ?_, inferInstance, inferInstance, inferInstance, inferInstance⟩
  constructor
  rw [← terminal.comp_from s]
  infer_instance
end _root_.GlobalTheory
end GlobalTheory
