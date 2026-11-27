-- Prove2me | solution 1 for GlobalTheory.TraceGram.entry_mem_of_trace_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:34:42.129823+00:00
-- url     : https://prove2.me/submissions/2b561ba1-63c5-4133-a4d5-3421f313401d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntryMemSubringOfTraceGramUnit
import Theorems.Thm_GlobalTheory_TraceGram_pow_entry_mem
import Theorems.Thm_GlobalTheory_TraceGram_adjugate_entry_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.TraceGram
namespace GlobalTheory.TraceGram
theorem _root_.solution : ∀ {K : Type} [Field K] (O : Subring K) {n : ℕ} (g x : Matrix (Fin n) (Fin n) K) (c : Fin n → K),
    x = ∑ i, c i • g ^ (i : ℕ) → (∀ i j, g i j ∈ O) → (∀ j : Fin n, (x * g ^ (j : ℕ)).trace ∈ O) →
    (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det ≠ 0 →
    ((Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det)⁻¹ ∈ O → ∀ i j, x i j ∈ O := by
  intro K _ O n g x c hx hg htr hdet hinv
  set G : Matrix (Fin n) (Fin n) K := Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace with hGdef
  have hG : ∀ i j, G i j ∈ O := by
    intro i j
    simp only [hGdef, Matrix.of_apply, Matrix.trace, Matrix.diag_apply]
    exact O.sum_mem fun l _ => pow_entry_mem O g hg _ l l
  have hb : ∀ j, (c ᵥ* G) j ∈ O := by
    intro j
    have : (c ᵥ* G) j = (x * g ^ (j : ℕ)).trace := by
      rw [hx, Finset.sum_mul, Matrix.trace_sum]
      simp only [Matrix.vecMul, dotProduct, hGdef, Matrix.of_apply, smul_mul_assoc,
        Matrix.trace_smul, smul_eq_mul, pow_add]
    rw [this]; exact htr j
  have hc : ∀ i, c i ∈ O := by
    intro i
    have h1 : (c ᵥ* G) ᵥ* G.adjugate = G.det • c := by
      rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
    have h2 : c i = (G.det)⁻¹ * ((c ᵥ* G) ᵥ* G.adjugate) i := by
      rw [h1, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]
    rw [h2]
    refine O.mul_mem hinv ?_
    change ∑ l, (c ᵥ* G) l * G.adjugate l i ∈ O
    exact O.sum_mem fun l _ => O.mul_mem (hb l) (adjugate_entry_mem O G hG l i)
  intro i j
  rw [hx, Matrix.sum_apply]
  refine O.sum_mem fun l _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  exact O.mul_mem (hc l) (pow_entry_mem O g hg _ i j)
end GlobalTheory.TraceGram
