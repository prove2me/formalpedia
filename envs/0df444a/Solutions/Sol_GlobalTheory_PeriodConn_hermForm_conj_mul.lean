-- Prove2me | solution 1 for GlobalTheory.PeriodConn.hermForm_conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:03.064376+00:00
-- url     : https://prove2.me/submissions/d17e0d13-3bea-42f8-8946-9881fa8ceee8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsPreconnectedBlockUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Matrix
open GlobalTheory GlobalTheory.PeriodConn
open NumberField Matrix
namespace GlobalTheory.PeriodConn
namespace _root_.GlobalTheory.PeriodConn
theorem _root_.solution {g : ℕ} (Hm N : Matrix (Fin g) (Fin g) ℂ)
    (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Nᵀ * Hm * N.map star) z w = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (N.mulVec z) (N.mulVec w) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  congr 2
  ext i
  simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
end _root_.GlobalTheory.PeriodConn
end GlobalTheory.PeriodConn
