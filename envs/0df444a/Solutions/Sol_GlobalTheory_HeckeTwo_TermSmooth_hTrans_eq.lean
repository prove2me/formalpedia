-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.TermSmooth.hTrans_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:41.581653+00:00
-- url     : https://prove2.me/submissions/d5de10ce-860c-4c9f-a9de-ab9c0bf07a5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermSmooth
namespace GlobalTheory.HeckeTwo.TermSmooth
theorem _root_.solution (σ : ℂ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) : hTrans σ ν y = intT σ ν 2 0 0 y := by
  unfold hTrans intT
  congr 1
  funext t
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have hnu : ‖(t : ℂ) + (y : ℂ) * I‖ = Real.sqrt (t ^ 2 + y ^ 2) := by
    rw [← Complex.normSq_add_mul_I, Complex.norm_def]
  unfold term phi
  rw [hnu]
  simp only [Nat.cast_zero, sub_zero, pow_zero, mul_one]
  congr 2
  have hs : 0 < Real.sqrt (t ^ 2 + y ^ 2) := Real.sqrt_pos.2 hQ
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hs.ne'), Complex.cpow_def_of_ne_zero (by exact_mod_cast hQ.ne'),
    ← Complex.ofReal_log hs.le, ← Complex.ofReal_log hQ.le, Real.log_sqrt hQ.le]
  congr 1
  push_cast
  ring
end GlobalTheory.HeckeTwo.TermSmooth
