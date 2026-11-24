-- Prove2me | solution 1 for GlobalTheory.Tw.CentralizerAdjoin.snd_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:14:34.874311+00:00
-- url     : https://prove2.me/submissions/f8ba7eb6-8e82-4ab3-8d50-abb744c30376

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_dm_snd
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_dm_one
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_dm_smul
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_dm_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.CentralizerAdjoin
variable {n : ℕ} {R : Type} [CommRing R]
namespace GlobalTheory.Tw.CentralizerAdjoin
theorem _root_.solution (N g : Matrix (Fin n) (Fin n) R) (hc : g * N = N * g) (P : (DualNumber R)[X]) :
    ∃ Q : R[X], (aeval (dm N g) P).map TrivSqZeroExt.snd =
      aeval N (derivative (P.map (TrivSqZeroExt.fstHom R R R).toRingHom)) * g + aeval N Q := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨Q1, h1⟩ := hp
    obtain ⟨Q2, h2⟩ := hq
    refine ⟨Q1 + Q2, ?_⟩
    rw [map_add, Matrix.map_add _ TrivSqZeroExt.snd_add, h1, h2, Polynomial.map_add, derivative_add,
      map_add, map_add, Matrix.add_mul]
    abel
  | monomial k a =>
    cases k with
    | zero =>
      refine ⟨C a.snd, ?_⟩
      rw [aeval_monomial, pow_zero, mul_one, Algebra.algebraMap_eq_smul_one, ← dm_one, dm_smul, dm_snd]
      simp [Algebra.algebraMap_eq_smul_one]
    | succ k =>
      refine ⟨monomial (k + 1) a.snd, ?_⟩
      rw [aeval_monomial, ← Algebra.smul_def, dm_pow N g hc, dm_smul, dm_snd, Polynomial.map_monomial,
        derivative_monomial, aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.fstHom_apply, add_tsub_cancel_right,
        smul_zero, zero_add, Matrix.smul_mul, smul_smul]
end GlobalTheory.Tw.CentralizerAdjoin
