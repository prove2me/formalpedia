-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.TermDecay.norm_qZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:23:12.828398+00:00
-- url     : https://prove2.me/submissions/da261eb4-69e9-4394-af67-b6163d1930f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntZEqFourier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableHeckeTermDecayIntegrand

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
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay
namespace GlobalTheory.HeckeTwo.TermDecay
theorem _root_.solution (σ : ℂ) (a : ℤ) (b m : ℕ) {y : ℝ} (hy : y ≠ 0) (t : ℝ) :
    ‖qZ σ a b m y t‖ = (t ^ 2 + y ^ 2) ^ (-((a : ℝ) / 2 + b + σ.re)) * |y| ^ m := by
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have hnu : ‖(t : ℂ) + (y : ℂ) * I‖ = Real.sqrt (t ^ 2 + y ^ 2) := by
    rw [← Complex.normSq_add_mul_I, Complex.norm_def]
  unfold qZ
  rw [norm_mul, norm_mul, norm_zpow, hnu, Complex.norm_cpow_eq_rpow_re_of_pos hQ,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, Real.sqrt_eq_rpow, ← Real.rpow_intCast,
    ← Real.rpow_mul hQ.le, ← Real.rpow_add hQ]
  congr 2
  simp
  ring
end GlobalTheory.HeckeTwo.TermDecay
