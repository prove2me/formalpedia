-- Prove2me | solution 1 for GlobalTheory.LevelLift.dvd_sub_of_exp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:10:06.542404+00:00
-- url     : https://prove2.me/submissions/2adcc892-f9dc-49f0-bf54-04d3b86ae5e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLatticeLiftOfLevelSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
open GlobalTheory GlobalTheory.LevelLift
namespace GlobalTheory.LevelLift
theorem _root_.solution (k : ℕ) (hk : 0 < k) (m n : ℤ)
    (h : Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : (k : ℤ) ∣ n - m := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  obtain ⟨c, hc⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  refine ⟨c, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have : ((n - m : ℤ) : ℂ) = ((k * c : ℤ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ h2
    field_simp at hc
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    first
      | linear_combination (2 * Real.pi * Complex.I) * hc
      | linear_combination -(2 * Real.pi * Complex.I) * hc
      | linear_combination hc
      | linear_combination -hc
  exact_mod_cast this
end GlobalTheory.LevelLift
