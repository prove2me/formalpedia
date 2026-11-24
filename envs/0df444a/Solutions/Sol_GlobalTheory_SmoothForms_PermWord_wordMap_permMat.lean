-- Prove2me | solution 1 for GlobalTheory.SmoothForms.PermWord.wordMap_permMat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:46.748825+00:00
-- url     : https://prove2.me/submissions/87c46b7e-7b6c-4fd0-b188-6aea1dab8d3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter

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
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.PermWord
namespace GlobalTheory.SmoothForms.PermWord
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (d : ℕ)
    (π : Equiv.Perm (Fin d)) :
    wordMap E d (permMat n d π) = ∑ K : Fin d → Fin n, (List.ofFn fun a => E (K (π a)) (K a)).prod := by
  simp only [wordMap, permMat, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [Finset.sum_eq_single (K ∘ π)]
  · simp
  · intro I _ hI; rw [if_neg hI, zero_smul]
  · simp
end GlobalTheory.SmoothForms.PermWord
