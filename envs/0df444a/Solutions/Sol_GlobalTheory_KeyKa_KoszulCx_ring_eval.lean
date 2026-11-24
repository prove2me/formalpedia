-- Prove2me | solution 1 for GlobalTheory.KeyKa.KoszulCx.ring_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:31:20.902572+00:00
-- url     : https://prove2.me/submissions/15eea999-146c-4c31-a74c-11e938a6eded

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignInsert

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
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KoszulCx
variable {R : Type} [CommRing R]
namespace GlobalTheory.KeyKa.KoszulCx
theorem _root_.solution {A S : Type} [CommRing A] [Fintype S] (φ : R →+* A) (v : A → R) (ψ : A →+* R) (hv : ∀ a, v a = ψ a)
    (hc : ∀ c, v (φ c) = c) (b : S → A) (u f : A) (c : S → R) (hu : v u = 0) (h : u * f = ∑ k, φ (c k) * b k) :
    ∑ k, v (b k) * c k = 0 := by
  obtain rfl : v = ψ := funext hv
  have e := congrArg ψ h
  rw [map_mul, map_sum, hu, zero_mul] at e
  simp only [map_mul, hc] at e
  exact Eq.trans (Finset.sum_congr rfl fun k' _ => mul_comm _ _) e.symm
end GlobalTheory.KeyKa.KoszulCx
