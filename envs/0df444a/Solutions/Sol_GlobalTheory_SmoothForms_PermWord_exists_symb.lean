-- Prove2me | solution 1 for GlobalTheory.SmoothForms.PermWord.exists_symb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:19:11.13619+00:00
-- url     : https://prove2.me/submissions/9400a247-cd34-4f33-b295-004fdaaf33d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_trace_pow_eq
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_perm_sum_mem
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_symb_mul
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_sum_mem_symb

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
    (π : Equiv.Perm (Fin d)) : ∃ c ∈ Algebra.adjoin ℂ (Set.range (gelfA E)),
      (∑ K : Fin d → Fin n, (List.ofFn fun a => gen n (K (π a)) (K a)).prod, c) ∈ symb E d := by
  have key := perm_sum_mem (Matrix.of (gen n))
    (fun j p => ∃ c ∈ Algebra.adjoin ℂ (Set.range (gelfA E)), (p, c) ∈ symb E j)
    ⟨1, one_mem _, Submodule.subset_span ⟨[], rfl, by simp [wd]⟩⟩
    (by
      rintro k j p ⟨c, hc, h⟩
      refine ⟨gelfA E k * c, mul_mem (Algebra.subset_adjoin ⟨k, rfl⟩) hc, ?_⟩
      rw [trace_pow_eq, ← Prod.mk_mul_mk]
      refine symb_mul E ?_ h
      unfold gelfA
      exact sum_mem_symb E (fun idx : Fin (k + 1) → Fin n => idx) fun idx a => idx (a + 1))
    d π (fun _ => 0)
  simp only [zero_add, pow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
    Matrix.of_apply] at key
  simp only [List.prod_ofFn]
  exact key
end GlobalTheory.SmoothForms.PermWord
