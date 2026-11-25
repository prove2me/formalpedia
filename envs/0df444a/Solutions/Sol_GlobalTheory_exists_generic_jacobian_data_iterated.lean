-- Prove2me | solution 1 for GlobalTheory.exists_generic_jacobian_data_iterated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:19:41.806798+00:00
-- url     : https://prove2.me/submissions/91c44c29-aac2-4b9e-b35f-d3c80d232903

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGenericJacobianDataOfPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGenericJacobianDataIterated
import Theorems.Thm_GlobalTheory_derivation_sumAlgEquiv_eq_pderiv
import Theorems.Thm_GlobalTheory_T_exists_local_generators_jacobian_det_not_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ τ : Type) [Finite σ] [Finite τ] (Q : Ideal (MvPolynomial τ (MvPolynomial σ Λ))) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C (MvPolynomial.C a) ∈ Q → a = 0) → ∀ d : τ ⊕ σ → Derivation ℤ (MvPolynomial τ (MvPolynomial σ Λ)) (MvPolynomial τ (MvPolynomial σ Λ)), (∀ t x, d (Sum.inl t) x = MvPolynomial.pderiv t x) → (∀ s x, d (Sum.inr s) (MvPolynomial.C x) = MvPolynomial.C (MvPolynomial.pderiv s x)) → (∀ s t, d (Sum.inr s) (MvPolynomial.X t) = 0) → ∃ (h : ℕ) (f : Fin h → MvPolynomial τ (MvPolynomial σ Λ)) (s : Fin h → τ ⊕ σ) (g : MvPolynomial τ (MvPolynomial σ Λ)), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ (Matrix.of fun i j => d (s i) (f j)).det ∉ Q := by
  intro Λ _ _ _ _ σ τ _ _ Q _ hQ d h1 h2 h3
  let e := MvPolynomial.sumAlgEquiv Λ τ σ
  have eC : ∀ a : Λ, e (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a) := fun a => by
    simp [e, MvPolynomial.sumAlgEquiv_C_inl]
  obtain ⟨h, f, s, g, hg, hf, hx, hdet⟩ := GlobalTheory.T.exists_local_generators_jacobian_det_not_mem Λ (τ ⊕ σ) (Q.comap e)
    (fun a ha => hQ a (by rw [← eC]; exact ha))
  refine ⟨h, fun j => e (f j), s, e g, hg, hf, fun x hxQ => ?_, ?_⟩
  · have h4 := hx (e.symm x) (by simpa [Ideal.mem_comap] using hxQ)
    have h5 := Ideal.mem_map_of_mem e h4
    rw [Ideal.map_span, ← Set.range_comp, map_mul, AlgEquiv.apply_symm_apply] at h5
    exact h5
  · intro hmem
    apply hdet
    rw [Ideal.mem_comap, AlgEquiv.map_det]
    convert hmem using 2
    ext i j : 1
    exact (derivation_sumAlgEquiv_eq_pderiv d h1 h2 h3 _ _).symm
end GlobalTheory
