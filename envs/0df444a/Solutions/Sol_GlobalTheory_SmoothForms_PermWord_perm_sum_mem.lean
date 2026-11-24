-- Prove2me | solution 1 for GlobalTheory.SmoothForms.PermWord.perm_sum_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:46.461798+00:00
-- url     : https://prove2.me/submissions/048e36fe-7154-4d73-8a8b-9059035dffdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_sum_cons_split

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
variable {S : Type} [CommRing S] {n : ℕ}
namespace GlobalTheory.SmoothForms.PermWord
theorem _root_.solution (X : Matrix (Fin n) (Fin n) S) (T : ℕ → S → Prop) (h0 : T 0 1)
    (hs : ∀ k j p, T j p → T (k + 1 + j) ((X ^ (k + 1)).trace * p)) (d : ℕ) :
    ∀ (π : Equiv.Perm (Fin d)) (m : Fin d → ℕ),
      T (∑ a, (m a + 1)) (∑ K : Fin d → Fin n, ∏ a, (X ^ (m a + 1)) (K (π a)) (K a)) := by
  induction d with
  | zero => intro π m; simpa using h0
  | succ d ih =>
    intro π m
    obtain ⟨⟨p, e⟩, rfl⟩ := Equiv.Perm.decomposeFin.symm.surjective π
    rw [sum_cons_split, Fin.sum_univ_succ]
    simp only [Fin.prod_univ_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
      Equiv.Perm.decomposeFin_symm_apply_succ, Fin.cons_succ, Fin.cons_zero]
    refine Fin.cases ?_ (fun q => ?_) p
    · have := hs (m 0) _ _ (ih e fun a => m a.succ)
      convert this using 1
      simp only [Equiv.swap_self, Equiv.refl_apply, Fin.cons_succ, Fin.cons_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl fun K _ => ?_
      rw [← Finset.sum_mul]; rfl
    · obtain ⟨x, rfl⟩ := e.surjective q
      have := ih e (Function.update (fun a => m a.succ) x (m 0 + 1 + m x.succ))
      convert this using 1
      · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), ← Finset.add_sum_erase _ _ (Finset.mem_univ x),
          Function.update_self, ← add_assoc, ← add_assoc]
        congr 1
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]
      · refine Finset.sum_congr rfl fun K _ => ?_
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ x), Function.update_self, add_assoc (m 0 + 1), pow_add X (m 0 + 1),
          Matrix.mul_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ x), Equiv.swap_apply_right, Fin.cons_succ, Fin.cons_zero,
          mul_assoc]
        congr 2
        refine Finset.prod_congr rfl fun a ha => ?_
        have hne := Finset.ne_of_mem_erase ha
        rw [Function.update_of_ne hne, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (by simpa using hne),
          Fin.cons_succ]
end GlobalTheory.SmoothForms.PermWord
