-- Prove2me | solution 1 for GlobalTheory.SmoothForms.GelfGen.exists_symb_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:51:37.514127+00:00
-- url     : https://prove2.me/submissions/ceac735e-8894-468a-bdee-fe8573acdbea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GelfAMemAdjoinLow
import Theorems.Thm_GlobalTheory_SmoothForms_GelfGen_trace_symb
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_perm_sum_mem
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_symb_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms
noncomputable section
open GlobalTheory.SmoothForms.PermWord
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.GelfGen
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace GlobalTheory.SmoothForms.GelfGen
theorem _root_.solution (E : Fin n → Fin n → A) (d : ℕ)
    (π : Equiv.Perm (Fin d)) : ∃ c ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val),
      (∑ K : Fin d → Fin n, (List.ofFn fun a => gen n (K (π a)) (K a)).prod, c) ∈ symb E d := by
  have key := perm_sum_mem (Matrix.of (gen n))
    (fun j p => ∃ c ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val), (p, c) ∈ symb E j)
    ⟨1, one_mem _, Submodule.subset_span ⟨[], rfl, by simp [wd]⟩⟩
    (by
      rintro k j p ⟨c, hc, h⟩
      obtain ⟨c', hc', h'⟩ := trace_symb E k
      exact ⟨c' * c, mul_mem hc' hc, by rw [← Prod.mk_mul_mk]; exact symb_mul E h' h⟩)
    d π (fun _ => 0)
  simp only [zero_add, pow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
    Matrix.of_apply] at key
  simp only [List.prod_ofFn]
  exact key
end GlobalTheory.SmoothForms.GelfGen
