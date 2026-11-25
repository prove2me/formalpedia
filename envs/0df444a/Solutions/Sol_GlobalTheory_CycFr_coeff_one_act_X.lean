-- Prove2me | solution 1 for GlobalTheory.CycFr.coeff_one_act_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:28:47.446934+00:00
-- url     : https://prove2.me/submissions/f7846bf0-eff5-43c6-8574-72ffa1589e8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Theorems.Thm_GlobalTheory_CycFr_act_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.CycFr
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
open PowerSeries
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
namespace GlobalTheory.CycFr
namespace _root_.GlobalTheory.CycFr
theorem _root_.solution (c : ℤ_[l]) : coeff 1 (_root_.GlobalTheory.CycFr.act O c X) = algebraMap ℤ_[l] O c := by
  rw [_root_.GlobalTheory.CycFr.act_X, map_sub, binomialSeries_coeff, Ring.choose_one_right,
    coeff_one, Algebra.smul_def, mul_one]
  simp
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
