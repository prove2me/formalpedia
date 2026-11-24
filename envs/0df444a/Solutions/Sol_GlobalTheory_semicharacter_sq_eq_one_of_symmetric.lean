-- Prove2me | solution 1 for GlobalTheory.semicharacter_sq_eq_one_of_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:27:41.28193+00:00
-- url     : https://prove2.me/submissions/9fa54fac-d61c-4e46-bbe6-393b6deaaf08

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_valueRules
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_mul_neg_eq_one
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_neg_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open SymmetricSemicharacter
namespace GlobalTheory
theorem _root_.solution :
    ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ)
      (χ : u.Λ → ℂ), u.IsAH Hm χ → ∀ l, χ l ^ 2 = 1 := by
  intro P u Hm χ h l
  have h1 := mul_neg_eq_one u valueRules P.isLB h l
  rwa [neg_eq u valueRules P.isLB P.sym h l, ← sq] at h1
end GlobalTheory
