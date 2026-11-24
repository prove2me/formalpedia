-- Prove2me | solution 1 for GordanGenProof.fm_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:28.885804+00:00
-- url     : https://prove2.me/submissions/22e321d8-87b7-4b25-a3e7-00b15c903cd1

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_GordanCones
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GordanIntegerMultiple_ExistsIntMultiple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GordanGenProof
open Finset
namespace GordanGenProof
theorem _root_.solution {n : ℕ} (a b : ℚ) (u v x : Fin n → ℚ) :
    (a • u - b • v) ⬝ᵥ x = a * (u ⬝ᵥ x) - b * (v ⬝ᵥ x) := by
  show ∑ i, (a • u - b • v) i * x i = a * ∑ i, u i * x i - b * ∑ i, v i * x i
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
end GordanGenProof
