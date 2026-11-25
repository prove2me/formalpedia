-- Prove2me | solution 1 for GlobalTheory.GermInterp.eq_of_comap_map_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:12:36.564451+00:00
-- url     : https://prove2.me/submissions/a45d9007-9b7f-45a6-875e-94ce21b63353

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsMaximalOfFinitePrimes

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
open GlobalTheory
open GlobalTheory GlobalTheory.GermInterp
namespace GlobalTheory.GermInterp
theorem _root_.solution {R : Type*} [CommRing R] (I : Ideal R)
    (hmax : ∀ Q : Ideal R, Q.IsPrime → I ≤ Q → Q.IsMaximal) (P : Ideal R) [hP : P.IsPrime] (hI : I ≤ P)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S P] (M : Ideal R) (hM : M.IsMaximal)
    (h : (I.map (algebraMap R S)).comap (algebraMap R S) ≤ M) : M = P := by
  by_contra hne
  have hMP : ¬ M ≤ P := fun hle => hne (hM.eq_of_le hP.ne_top hle)
  obtain ⟨m, hmM, hmP⟩ := Set.not_subset.1 hMP
  have hmeet : ¬ Disjoint (I : Set R) (↑(M.primeCompl ⊔ Submonoid.powers m) : Set R) := by
    intro hdis
    obtain ⟨Q, hQ, hIQ, hQdis⟩ := Ideal.exists_le_prime_disjoint I _ hdis
    have hQM : Q ≤ M := by
      intro x hx
      by_contra hxM
      exact Set.disjoint_left.1 hQdis hx
        (Submonoid.mem_sup_left (show x ∈ M.primeCompl from hxM))
    have hmQ : m ∉ Q := fun hm =>
      Set.disjoint_left.1 hQdis hm (Submonoid.mem_sup_right (Submonoid.mem_powers m))
    exact hmQ (((hmax Q hQ hIQ).eq_of_le hM.ne_top hQM) ▸ hmM)
  obtain ⟨w, hwI, hwW⟩ := Set.not_disjoint_iff.1 hmeet
  obtain ⟨v, hv, u, hu, rfl⟩ := Submonoid.mem_sup.1 hwW
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hu
  have hunit : IsUnit (algebraMap R S (m ^ k)) :=
    IsLocalization.map_units S (⟨m ^ k, fun h => hmP (hP.mem_of_pow_mem k h)⟩ : P.primeCompl)
  have hvmap : v ∈ (I.map (algebraMap R S)).comap (algebraMap R S) := by
    rw [Ideal.mem_comap]
    have hw := Ideal.mem_map_of_mem (algebraMap R S) hwI
    rw [map_mul] at hw
    exact (Ideal.mul_unit_mem_iff_mem _ hunit).1 hw
  exact hv (h hvmap)
end GlobalTheory.GermInterp
