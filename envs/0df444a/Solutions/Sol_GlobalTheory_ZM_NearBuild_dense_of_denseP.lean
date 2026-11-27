-- Prove2me | solution 1 for GlobalTheory.ZM.NearBuild.dense_of_denseP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:36:27.646098+00:00
-- url     : https://prove2.me/submissions/e01aca6e-f7ef-4a15-bbd3-9f9e834fbb4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP

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
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.NearBuild
variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {R R' : Type} [CommRing R] [CommRing R']
variable (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ)
  (β : o →+* R) (v : Ix g (N' ^ 2) → R)
variable {b Mat κ β v}
namespace GlobalTheory.ZM.NearBuild
theorem _root_.solution {P : Set (Ideal R)} (h : DenseP P) : Dense {p : Sp R | p.asIdeal ∈ P} := by
  have hv : PrimeSpectrum.vanishingIdeal {p : PrimeSpectrum R | p.asIdeal ∈ P} = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_bot]
    refine h a fun p hp hpr => ?_
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).1 ha ⟨p, hpr⟩ hp
  have hc : closure {p : PrimeSpectrum R | p.asIdeal ∈ P} = Set.univ := by
    rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hv]
    simp
  exact dense_iff_closure_eq.2 hc
end GlobalTheory.ZM.NearBuild
