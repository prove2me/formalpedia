-- Prove2me | solution 1 for GlobalTheory.VeryDenseFibres.geometricallyConnected_of_veryDense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:43:15.334144+00:00
-- url     : https://prove2.me/submissions/ede1eef4-3696-45be-baed-d25873ede67f

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
import Theorems.Thm_GlobalTheory_VeryDenseFibres_geometricallyConnected_fiber_iff
import Theorems.Thm_GlobalTheory_geometricallyConnected_genericFibre_of_dense


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
theorem _root_.solution {R : Type} [CommRing R] [IsNoetherianRing R]
    {Z : Scheme.{0}} (s : Z ⟶ Sp R) [LocallyOfFiniteType s] [QuasiCompact s] (P : Set (Ideal R))
    (hP : ∀ (q₀ : Ideal R) (f₀ : R), q₀.IsPrime → f₀ ∉ q₀ →
      ∃ p₀ ∈ P, p₀.IsPrime ∧ q₀ ≤ p₀ ∧ f₀ ∉ p₀)
    (h : ∀ y : Sp R, y.asIdeal ∈ P → GeometricallyConnected (s.fiberToSpecResidueField y)) :
    GeometricallyConnected s := by
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro q
  have hq : q.asIdeal.IsPrime := PrimeSpectrum.isPrime q
  let t : Sp (R ⧸ q.asIdeal) ⟶ Sp R := spMap (Ideal.Quotient.mk q.asIdeal)
  have hd : Dense {y : Sp (R ⧸ q.asIdeal) | (t y).asIdeal ∈ P} := by
    refine (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R ⧸ q.asIdeal)).dense_iff.2 ?_
    rintro _ ⟨a, rfl⟩ ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha : a ∉ q.asIdeal := fun ha => hz (by
      rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]; exact Ideal.zero_mem _)
    obtain ⟨p, hp, hp', hle, hap⟩ := hP _ a hq ha
    obtain ⟨y, hy⟩ : (⟨p, hp'⟩ : PrimeSpectrum R) ∈
        Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk q.asIdeal)) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
      exact hle
    have hy' : Ideal.comap (Ideal.Quotient.mk q.asIdeal) y.asIdeal = p :=
      congrArg PrimeSpectrum.asIdeal hy
    refine ⟨y, fun hy2 => hap (hy' ▸ hy2), ?_⟩
    change Ideal.comap (Ideal.Quotient.mk q.asIdeal) y.asIdeal ∈ P
    rwa [hy']
  have H := GlobalTheory.geometricallyConnected_genericFibre_of_dense _ (Sp (R ⧸ q.asIdeal))
    (pullback.snd s t) _ hd fun y hy => (geometricallyConnected_fiber_iff s t y).2 (h _ hy)
  rw [geometricallyConnected_fiber_iff] at H
  have e : t (genericPoint (Sp (R ⧸ q.asIdeal))) = q := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext (Ideal.mk_ker (I := q.asIdeal))
  rwa [e] at H
end GlobalTheory.VeryDenseFibres
