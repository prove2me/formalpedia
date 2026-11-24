-- Prove2me | solution 1 for GlobalTheory.FibreUnif.int_eq_of_exp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:53:46.726262+00:00
-- url     : https://prove2.me/submissions/73203726-cb7b-4a13-8adf-341175a5ae1b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_FamilyUniformisationFibreTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
open GlobalTheory
open GlobalTheory.FibreUnif
namespace GlobalTheory.FibreUnif
theorem _root_.solution {m n : ℤ} (h : ∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) :
    m = n := by
  have hd : ∀ k : ℕ, 0 < k → (k : ℤ) ∣ n - m := fun k hk => by
    obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h k hk)
    refine ⟨j, ?_⟩
    have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    have : ((n - m : ℤ) : ℂ) = ((k * j : ℤ) : ℂ) := by
      push_cast
      refine mul_left_cancel₀ h2 ?_
      field_simp at hj
      linear_combination (2 * Real.pi * Complex.I) * hj
    exact_mod_cast this
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hd ((n - m).natAbs + 1) (Nat.succ_pos _))
    (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega
end GlobalTheory.FibreUnif
