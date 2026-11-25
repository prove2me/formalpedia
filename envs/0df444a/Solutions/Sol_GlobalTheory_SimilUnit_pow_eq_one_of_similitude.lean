-- Prove2me | solution 1 for GlobalTheory.SimilUnit.pow_eq_one_of_similitude
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:26:54.22917+00:00
-- url     : https://prove2.me/submissions/d8bcc194-4a1b-4b1d-bf27-e5e1d10dbddf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNormalisingUnitSimilitudeOrigin

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
open GlobalTheory GlobalTheory.SimilUnit
namespace GlobalTheory.SimilUnit
theorem _root_.solution {A I : Type} [CommGroup A] [Fintype I] [DecidableEq I] (m : ℕ) (hm : m ≠ 0)
    (al : Matrix I I ℤ) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix I I ℤ)) (ξ : I → A)
    (hk : ∀ c, ∏ r, ξ r ^ al r c = 1) (r : I) : ξ r ^ m = 1 := by
  have hm' : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hm
  have hd : al.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hal
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, _root_.mul_one] at this
    exact pow_ne_zero _ hm' this.symm
  have h2 : al * al.transpose = (m : ℤ) • (1 : Matrix I I ℤ) := by
    have e : (al * al.transpose) * al = ((m : ℤ) • (1 : Matrix I I ℤ)) * al := by
      rw [Matrix.mul_assoc, hal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    have e' := congrArg (· * al.adjugate) e
    simp only [Matrix.mul_assoc (_ : Matrix I I ℤ) al al.adjugate, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at e'
    exact smul_right_injective _ hd e'
  have e : ∏ c, (∏ r', ξ r' ^ al r' c) ^ al r c = ξ r ^ m := by
    simp only [← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    have : ∀ r', ∏ c, ξ r' ^ (al r' c * al r c) = ξ r' ^ (if r' = r then (m : ℤ) else 0) := fun r' => by
      have := congrFun (congrFun h2 r') r
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        mul_ite, _root_.mul_one, mul_zero] at this
      rw [← this]
      exact (map_prod (zpowersHom A (ξ r')) (fun c => Multiplicative.ofAdd (al r' c * al r c)) Finset.univ).symm
    simp only [this, pow_ite, zpow_zero, Finset.prod_ite_eq', Finset.mem_univ, if_true, zpow_natCast]
  rw [← e]
  simp only [hk, one_zpow, Finset.prod_const_one]
end GlobalTheory.SimilUnit
