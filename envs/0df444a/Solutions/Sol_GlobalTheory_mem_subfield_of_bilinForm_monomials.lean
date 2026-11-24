-- Prove2me | solution 1 for GlobalTheory.mem_subfield_of_bilinForm_monomials
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:34:47.618981+00:00
-- url     : https://prove2.me/submissions/1159672b-3cb4-4371-9650-fcb2e03150b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSubfieldOfBilinFormBasisMonomials
import Theorems.Thm_GlobalTheory_mem_monomialExponents
import Theorems.Thm_GlobalTheory_mem_monomialExponents_of_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X : Type) [AddCommGroup X] (S : Submodule ℤ (LinearMap.BilinForm ℤ X)) (I : Type) [Fintype I]
    (ε : Module.Basis I ℤ S) (K : Type) [Field K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (n : ℤ), n ≠ 0 →
    ∀ (t : I → Kˣ), (∀ a b : X, ((∏ k, t k ^ (n * (ε k : LinearMap.BilinForm ℤ X) a b) : Kˣ) : K) ∈ k₀) →
    ∀ k, (t k : K) ∈ k₀ := by
  intro X _ S I _ ε K _ k₀ hk n hn t h k
  classical
  set P := monomialExponents k₀ t with hP
  have hv : ∀ a b : X, (fun k => (ε k : LinearMap.BilinForm ℤ X) a b) ∈ P := fun a b =>
    mem_monomialExponents_of_smul k₀ t _ n hn (h a b)
  haveI : NoZeroSMulDivisors ℤ ((I → ℤ) ⧸ P) := by
    refine ⟨fun {c x} hx => ?_⟩
    obtain ⟨v, rfl⟩ := P.mkQ_surjective x
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [← map_smul] at hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx ⊢
      exact mem_monomialExponents_of_smul k₀ t v c hc hx
  haveI : Module.Free ℤ ((I → ℤ) ⧸ P) := Module.free_of_finite_type_torsion_free'
  have key : P.mkQ (Pi.single k 1) = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff ℤ]
    intro φ
    have hz : ∑ j, φ (P.mkQ (Pi.single j 1)) • ε j = 0 := by
      apply Subtype.ext
      ext a b
      have h0 : φ (P.mkQ (fun k => (ε k : LinearMap.BilinForm ℤ X) a b)) = 0 := by
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).mpr (hv a b), map_zero]
      have h1 : (fun k => (ε k : LinearMap.BilinForm ℤ X) a b)
          = ∑ j, (ε j : LinearMap.BilinForm ℤ X) a b • (Pi.single j 1 : I → ℤ) := by
        funext i
        simp [Finset.sum_apply, Pi.single_apply]
      rw [h1, map_sum, map_sum] at h0
      simp only [map_smul, smul_eq_mul] at h0
      simp only [AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero, LinearMap.zero_apply]
      rw [← h0]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact Fintype.linearIndependent_iff.mp ε.linearIndependent _ hz k
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hP, mem_monomialExponents] at key
  convert key using 2
  rw [Finset.prod_eq_single k]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp
end GlobalTheory
