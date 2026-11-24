-- Prove2me | solution 1 for GlobalTheory.SmoothForms.commutator_wordMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:19:27.720615+00:00
-- url     : https://prove2.me/submissions/e089c7ac-3bce-49e4-b668-97c693c2859e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutatorGlGeneratorTensorWordMapMatrixUnits
import Theorems.Thm_GlobalTheory_SmoothForms_commutator_word

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms
namespace GlobalTheory.SmoothForms
theorem _root_.solution : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A),
    Formalism.REAL.GlRel E → ∀ (d : ℕ) (a b : Fin n) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ),
    E a b * wordMap E d M - wordMap E d M * E a b =
      wordMap E d (polar n d a b * M - M * polar n d a b) := by
  intro A _ _ n E hE d a b M
  have hw : ∀ N, wordMap E d N = ∑ I, ∑ K, N I K • (List.ofFn fun q : Fin d => E (I q) (K q)).prod := fun _ => rfl
  have hl : wordMap E d (polar n d a b * M) =
      ∑ I, ∑ K, M I K • ∑ J, polar n d a b J I • (List.ofFn fun q => E (J q) (K q)).prod := by
    simp only [hw, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have hr : wordMap E d (M * polar n d a b) =
      ∑ I, ∑ K, M I K • ∑ J, polar n d a b K J • (List.ofFn fun q => E (I q) (J q)).prod := by
    simp only [hw, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_comm]
  rw [map_sub, hl, hr, hw, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [← smul_sub, ← commutator_word hE, smul_sub, mul_smul_comm, smul_mul_assoc]
end GlobalTheory.SmoothForms
