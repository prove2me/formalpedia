-- Prove2me | solution 1 for GlobalTheory.PeriodOnto.comm_sgnMat_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:52.869672+00:00
-- url     : https://prove2.me/submissions/08e935b0-7709-4f43-b7cc-25f1804adcfe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.PeriodOnto
namespace GlobalTheory.PeriodOnto
theorem _root_.solution {r q : ℕ} (X : Matrix (Fin r) (Fin r) ℂ) :
    sgnMat r q * X = X * sgnMat r q ↔
      ∀ a b : Fin r, ¬ (((a : ℕ) < q) ↔ ((b : ℕ) < q)) → X a b = 0 := by
  constructor
  · intro h a b hab
    have := congrFun (congrFun h a) b
    simp only [sgnMat, diagonal_mul, mul_diagonal, FD.sgn] at this
    by_cases ha : (a : ℕ) < q <;> by_cases hb : (b : ℕ) < q <;> simp [ha, hb] at hab this
    · linear_combination (1 / 2 : ℂ) * this
    · linear_combination (-1 / 2 : ℂ) * this
  · intro h
    ext a b
    simp only [sgnMat, diagonal_mul, mul_diagonal, FD.sgn]
    by_cases ha : (a : ℕ) < q <;> by_cases hb : (b : ℕ) < q
    · simp [ha, hb]
    · simp [h a b (by simp [ha, hb])]
    · simp [h a b (by simp [ha, hb])]
    · simp [ha, hb]
end GlobalTheory.PeriodOnto
