-- Prove2me | solution 1 for GlobalTheory.BetaEx.cramer_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:01:27.947802+00:00
-- url     : https://prove2.me/submissions/0d1f8c3d-ffd5-449a-9a51-f449fd72072d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal

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
open GlobalTheory GlobalTheory.BetaEx
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
omit [NumberField E]
namespace GlobalTheory.BetaEx
theorem _root_.solution (v : Matrix (Fin n) (Fin n) E) (m : Fin n → E) :
    v.det • m = ∑ i, (v.updateRow i m).det • v i := by
  have h := Matrix.mulVec_cramer v.transpose m
  rw [Matrix.det_transpose] at h
  rw [← h]
  ext k
  simp [Matrix.mulVec, dotProduct, Matrix.cramer_transpose_apply, Finset.sum_apply, mul_comm]
end GlobalTheory.BetaEx
