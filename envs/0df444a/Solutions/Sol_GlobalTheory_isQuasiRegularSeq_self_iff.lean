-- Prove2me | solution 1 for GlobalTheory.isQuasiRegularSeq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:06:09.204998+00:00
-- url     : https://prove2.me/submissions/69e3bd31-c482-4bc1-a502-42dcba7e4c69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal

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
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {M}
namespace GlobalTheory
theorem _root_.solution (f : ι → R) :
    IsQuasiRegularSeq R f ↔ ∀ (a : ℕ) (p : MvPolynomial ι R), p.IsHomogeneous a →
      MvPolynomial.eval f p ∈ Ideal.span (Set.range f) ^ (a + 1) →
        ∀ α, p.coeff α ∈ Ideal.span (Set.range f) := by
  classical
  have key : ∀ (a : ℕ) (p : MvPolynomial ι R), p.IsHomogeneous a →
      MvPolynomial.eval f p = ∑ α : MonoDeg ι a, monoVal f α.1 • p.coeff α.1 := by
    intro a p hp
    have hs := Finset.sum_subtype (p := fun α : ι →₀ ℕ => α.degree = a) (F := MonoDeg.fintype ι a)
      (Finsupp.finite_of_degree_eq (σ := ι) a).toFinset (by simp)
      (fun α => monoVal f α • p.coeff α)
    rw [← hs, MvPolynomial.eval_eq]
    rw [Finset.sum_subset (s₂ := (Finsupp.finite_of_degree_eq (σ := ι) a).toFinset)]
    · exact Finset.sum_congr rfl fun α _ => mul_comm _ _
    · intro d hd
      have := hp (MvPolynomial.mem_support_iff.mp hd)
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      rwa [Finsupp.degree_eq_weight_one]
    · intro d _ hd
      simp [MvPolynomial.notMem_support_iff.mp hd]
  simp only [IsQuasiRegularSeq, smul_eq_mul, Ideal.mul_top] at key ⊢
  constructor
  · intro h a p hp hf α
    by_cases hα : α.degree = a
    · exact h a (fun β => p.coeff β.1) (key a p hp ▸ hf) ⟨α, hα⟩
    · rw [hp.coeff_eq_zero hα]
      exact zero_mem _
  · intro h a c hc α
    have hco : ∀ β : MonoDeg ι a,
        (∑ γ : MonoDeg ι a, MvPolynomial.monomial γ.1 (c γ)).coeff β.1 = c β := by
      intro β
      simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Subtype.val_inj]
    have hp : (∑ γ : MonoDeg ι a, MvPolynomial.monomial γ.1 (c γ)).IsHomogeneous a :=
      MvPolynomial.IsHomogeneous.sum _ _ _ fun γ _ => MvPolynomial.isHomogeneous_monomial _ γ.2
    rw [← hco α]
    refine h a _ hp ?_ _
    rw [key a _ hp]
    simpa only [hco] using hc
end GlobalTheory
