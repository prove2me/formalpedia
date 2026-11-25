-- Prove2me | solution 1 for GlobalTheory.ExpUniqFamily.int_eq_of_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:42:30.943301+00:00
-- url     : https://prove2.me/submissions/9b0fd976-d2d7-4b1a-946e-d9a8b90347d1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueLinearLiftUniformisedFibresStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FamilyUnifExpUnique

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
open GlobalTheory.ExpUniqFamily
namespace GlobalTheory.ExpUniqFamily
theorem _root_.solution (n n' : ℤ)
    (h : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n' : ℂ) / k)) : n = n' := by
  have hk : 0 < (n' - n).natAbs + 1 := Nat.succ_pos _
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h _ hk)
  generalize hkk : (n' - n).natAbs + 1 = k at hk hm
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have h3 : ((n' - n : ℤ) : ℂ) = ((k * m : ℤ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ h2
    field_simp at hm ⊢
    linear_combination hm
  have h4 : n' - n = k * m := Int.cast_injective h3
  have h5 : n' - n = 0 := Int.eq_zero_of_abs_lt_dvd (m := k) ⟨m, h4⟩ (by
    rw [← hkk, Int.abs_eq_natAbs]; push_cast; omega)
  omega
end GlobalTheory.ExpUniqFamily
