-- Prove2me | solution 1 for GlobalTheory.CycFr.derivative_bin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:07:06.112204+00:00
-- url     : https://prove2.me/submissions/ee69ad48-d029-47eb-a105-42f49a7598fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin

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
theorem _root_.solution (c : ℤ_[l]) :
    derivative O (_root_.GlobalTheory.CycFr.bin O c) = C (algebraMap ℤ_[l] O c) * _root_.GlobalTheory.CycFr.bin O (c - 1) := by
  ext n
  have key : ((n : ℤ_[l]) + 1) * Ring.choose c (n + 1) = c * Ring.choose (c - 1) n := by
    have h := Ring.choose_smul_choose c (n := n + 1) (k := 1) (by omega)
    simpa [Ring.choose_one_right, nsmul_eq_mul] using h
  rw [coeff_derivative, coeff_C_mul, binomialSeries_coeff, binomialSeries_coeff, Algebra.smul_def,
    Algebra.smul_def, mul_one, mul_one, ← map_mul, ← key, map_mul, mul_comm]
  simp
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
