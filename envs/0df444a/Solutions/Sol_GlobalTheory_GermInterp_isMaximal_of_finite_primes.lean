-- Prove2me | solution 1 for GlobalTheory.GermInterp.isMaximal_of_finite_primes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:57:59.1348+00:00
-- url     : https://prove2.me/submissions/2b4a6fbd-3c2e-4770-b951-fe8c7c790cd8

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
theorem _root_.solution {R : Type*} [CommRing R] [IsJacobsonRing R] (I : Ideal R)
    (hfin : {P : PrimeSpectrum R | I ≤ P.asIdeal}.Finite) (Q : Ideal R) (hQ : Q.IsPrime) (hI : I ≤ Q) :
    Q.IsMaximal := by
  have hT : {J : Ideal R | Q ≤ J ∧ J.IsMaximal}.Finite := by
    refine (hfin.image PrimeSpectrum.asIdeal).subset ?_
    rintro J ⟨hQJ, hJ⟩
    exact ⟨⟨J, hJ.isPrime⟩, le_trans hI hQJ, rfl⟩
  have hJac : Q.jacobson = Q := IsJacobsonRing.out inferInstance hQ.isRadical
  have hinf : hT.toFinset.inf id ≤ Q := by
    rw [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset]
    exact hJac.le
  obtain ⟨M, hM, hMQ⟩ := hQ.inf_le'.1 hinf
  rw [Set.Finite.mem_toFinset] at hM
  rw [show Q = M from le_antisymm hM.1 hMQ]
  exact hM.2
end GlobalTheory.GermInterp
