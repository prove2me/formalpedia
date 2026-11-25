-- Prove2me | solution 1 for GlobalTheory.truncMono_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:52:32.4618+00:00
-- url     : https://prove2.me/submissions/3cc6118b-8b79-4e5f-8b06-23b5de6db16b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedMonomialsLinearIndependentOverConstants
import Theorems.Thm_GlobalTheory_truncMono_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open MvPolynomial
namespace GlobalTheory
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] (d : ℕ) (x : Fin d → A) (E : Fin d → Derivation k A A), (∀ i j, E i (x j) = if i = j then 1 else 0) → ∀ B : Subalgebra k A, (∀ i, ∀ b ∈ B, E i b = 0) → LinearIndependent B (fun a : Fin d → Fin p => ∏ i, x i ^ (a i : ℕ)) := by
  intro p _ k A _ _ _ _ d x E hE B hB
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let toF : (Fin d → Fin p) → (Fin d →₀ ℕ) := fun a => Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))
  have hinj : Function.Injective toF := by
    intro a b hab
    funext i
    apply Fin.ext
    have := congrArg (fun f : Fin d →₀ ℕ => f i) hab
    simpa [toF] using this
  let F : MvPolynomial (Fin d) B := ∑ a, monomial (toF a) (g a)
  have hcoeff : ∀ m, coeff m F = ∑ a, if toF a = m then g a else 0 := by
    intro m
    simp only [F, coeff_sum, coeff_monomial]
  have hF : aeval x F = 0 := by
    rw [← hg]
    simp only [F, map_sum, aeval_monomial]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Subalgebra.smul_def]
    rfl
  have hF0 : F = 0 := by
    refine truncMono_eq_zero x E hE B hB (∑ _i : Fin d, p) F ?_ hF
    intro m hm
    rw [mem_support_iff, hcoeff] at hm
    obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    have hm' : toF a = m := by
      by_contra h
      exact ha (if_neg h)
    subst hm'
    refine ⟨fun i => by simp [toF], ?_⟩
    apply Finset.sum_le_sum
    intro i _
    simp [toF, (a i).isLt.le]
  intro a
  have := hcoeff (toF a)
  rw [hF0, coeff_zero] at this
  simp_rw [hinj.eq_iff] at this
  simpa using this.symm
end GlobalTheory
