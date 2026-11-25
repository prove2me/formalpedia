-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan.aeval_dualPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:37:04.878103+00:00
-- url     : https://prove2.me/submissions/ef29e7ed-3ded-43a0-abe4-043f80f534a0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsAlgHomAdjoinInv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SndEqZeroOfSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan
open TrivSqZeroExt
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan
theorem _root_.solution {σ : Type} [Fintype σ] (t v : σ → ℂ) (G : MvPolynomial σ ℂ) :
    fst (aeval (dualPt t v) G) = eval t G ∧
      snd (aeval (dualPt t v) G) = ∑ q, v q * eval t (pderiv q G) := by
  classical
  induction G using MvPolynomial.induction_on with
  | C a => simp [algebraMap_eq_inl]
  | add p q hp hq =>
    refine ⟨by simp [hp.1, hq.1], ?_⟩
    simp [hp.2, hq.2, mul_add, Finset.sum_add_distrib]
  | mul_X p q hp =>
    refine ⟨by simp [hp.1, dualPt], ?_⟩
    simp only [map_mul, aeval_X, snd_mul, hp.1, hp.2, dualPt, fst_add, fst_inl, fst_inr, snd_add, snd_inl, snd_inr,
      Derivation.leibniz, pderiv_X, eval_mul, eval_X, smul_eq_mul, op_smul_eq_mul, add_zero, zero_add, map_add]
    simp [Pi.single_apply, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan
