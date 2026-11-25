-- Prove2me | solution 1 for GlobalTheory.MomOne.Basic.mulS_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:02:24.77541+00:00
-- url     : https://prove2.me/submissions/0e31a51e-cd07-4774-9547-489f34b43317

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift

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
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.MomOne
variable {q : ℕ} [Fact q.Prime]
open GlobalTheory.MomOne.Basic
open Filter Topology
namespace GlobalTheory.MomOne.Basic
theorem _root_.solution (a : ℤ_[q]) :
    mulS a = PowerSeries.map ((algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom) (binomialSeries ℤ_[q] a) - 1 := by
  ext n
  rw [map_sub, coeff_map, binomialSeries_coeff, smul_eq_mul, mul_one, mulS, coeff_mk, coeff_one]
  rcases n with _ | n
  · simp
  · simp only [Nat.succ_ne_zero, if_false, sub_zero]; rfl
end GlobalTheory.MomOne.Basic
