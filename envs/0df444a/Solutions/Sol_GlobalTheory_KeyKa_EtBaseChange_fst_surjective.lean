-- Prove2me | solution 1 for GlobalTheory.KeyKa.EtBaseChange.fst_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:45:50.925333+00:00
-- url     : https://prove2.me/submissions/f196ae97-e584-40fc-89f1-7328dae03a32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.EtBaseChange
variable {T T' : Type} [CommRing T] [CommRing T'] {X Y : Scheme.{0}}
namespace GlobalTheory.KeyKa.EtBaseChange
theorem _root_.solution (R : Type) [CommRing R] :
    Function.Surjective (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  intro p
  have hs : Function.Surjective (TrivSqZeroExt.fstHom R R R).toRingHom := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have h : p ∈ PrimeSpectrum.zeroLocus (RingHom.ker (TrivSqZeroExt.fstHom R R R).toRingHom : Set (DualNumber R)) := by
    intro a ha
    have ha' : a.fst = 0 := ha
    refine (PrimeSpectrum.isPrime p).mem_of_pow_mem 2 ?_
    have : a ^ 2 = 0 := by
      ext <;> simp [sq, ha']
    rw [this]; exact Ideal.zero_mem _
  rw [← range_comap_of_surjective _ _ hs] at h
  exact h
end GlobalTheory.KeyKa.EtBaseChange
