-- Prove2me | solution 1 for GlobalTheory.LocLift.int_eq_of_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:29:48.335672+00:00
-- url     : https://prove2.me/submissions/b053d816-e98e-46e8-8987-a36540cec429

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolLinearLift

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
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}
namespace GlobalTheory.LocLift
theorem _root_.solution {a b : ℤ} (h : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (a : ℂ) / k) =
    Complex.exp (-(2 * Real.pi * Complex.I) * (b : ℂ) / k)) : a = b := by
  have hd : ∀ k : ℕ, 0 < k → (k : ℤ) ∣ b - a := fun k hk => by
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h k hk)
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    have hp := Complex.two_pi_I_ne_zero
    refine ⟨n, ?_⟩
    have : ((b : ℂ) - a) = k * n := by
      refine mul_left_cancel₀ hp ?_
      field_simp at hn
      linear_combination (2 * Real.pi * Complex.I) * hn
    exact_mod_cast this
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hd ((b - a).natAbs + 1) (Nat.succ_pos _)) (by
    rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega
end GlobalTheory.LocLift
