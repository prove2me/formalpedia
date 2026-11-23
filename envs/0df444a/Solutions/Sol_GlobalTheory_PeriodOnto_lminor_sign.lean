-- Prove2me | solution 1 for GlobalTheory.PeriodOnto.lminor_sign
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:02.688851+00:00
-- url     : https://prove2.me/submissions/05c835c8-9fa4-472c-9c8f-44730d453238

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
theorem _root_.solution {r q : ℕ} (X : Matrix (Fin r) (Fin r) ℂ) (h : (sgnMat r q * X).PosDef)
    (i : Fin (r + 1)) : 0 < FD.psgn q i * (FD.lminor X i).re := by
  have h1 := (h.submatrix (Fin.castLE_injective (Nat.le_of_lt_succ i.isLt))).det_pos
  have h2 : (sgnMat r q * X).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
      (Fin.castLE (Nat.le_of_lt_succ i.isLt)) =
      (Matrix.diagonal fun a : Fin i => ((FD.sgn q a : ℝ) : ℂ)) *
        X.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
          (Fin.castLE (Nat.le_of_lt_succ i.isLt)) := by
    ext a b
    simp [sgnMat, diagonal_mul]
  rw [h2, det_mul, det_diagonal] at h1
  have h3 : (∏ a : Fin i, ((FD.sgn q a : ℝ) : ℂ)) = ((FD.psgn q i : ℝ) : ℂ) := by
    rw [FD.psgn, ← Fin.prod_univ_eq_prod_range, Complex.ofReal_prod]
  rw [h3] at h1
  have := (Complex.pos_iff.mp h1).1
  simpa [FD.lminor] using this
end GlobalTheory.PeriodOnto
