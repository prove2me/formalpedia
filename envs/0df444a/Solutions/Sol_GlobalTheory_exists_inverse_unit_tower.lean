-- Prove2me | solution 1 for GlobalTheory.exists_inverse_unit_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:47:47.877805+00:00
-- url     : https://prove2.me/submissions/693d99da-0894-4dc1-9420-d87984080d95

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TateIsoExistsLiftOfTwoData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsCompatibleNormTowerProfiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsInverseUnitTower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (ν : ℕ → ℤ) (h1 : ∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ))
    (h2 : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) :
    ∃ κ : ℕ → ℤ, (∀ n : ℕ, 0 < n → (n : ℤ) ∣ κ n * ν n - 1) ∧ (∀ n : ℕ, 0 < n → IsCoprime (κ n) (n : ℤ)) ∧
      ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ κ (n * m) - κ n := by
  have h : ∀ n : ℕ, ∃ x : ℤ, 0 < n → (n : ℤ) ∣ x * ν n - 1 := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨x, y, hxy⟩ := h1 n hn
      exact ⟨x, fun _ => ⟨-y, by linear_combination hxy⟩⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose κ hκ using h
  refine ⟨κ, hκ, fun n hn => ?_, fun n m hn hm => ?_⟩
  · obtain ⟨c, hc⟩ := hκ n hn
    exact ⟨ν n, -c, by linear_combination hc⟩
  · obtain ⟨c, hc⟩ := hκ n hn
    obtain ⟨c', hc'⟩ := hκ (n * m) (Nat.mul_pos hn hm)
    obtain ⟨d, hd⟩ := h2 n m hn hm
    push_cast at hc'
    refine ⟨κ n * m * c' - κ (n * m) * c - κ (n * m) * κ n * d, ?_⟩
    linear_combination κ n * hc' - κ (n * m) * hc - κ (n * m) * κ n * hd
end GlobalTheory
