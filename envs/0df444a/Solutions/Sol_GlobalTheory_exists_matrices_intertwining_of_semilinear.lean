-- Prove2me | solution 1 for GlobalTheory.exists_matrices_intertwining_of_semilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:12.506504+00:00
-- url     : https://prove2.me/submissions/f95b4e5a-32a5-46f2-9bf0-84010e906891

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatricesIntertwiningOfSemilinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (emb : O →+* PadicAlgCl l) (I M : Type) [AddCommGroup M] [Module O M] [Module (MvPolynomial I O) M] [IsScalarTower O (MvPolynomial I O) M], Module.Finite O M → (∀ (c : O) (x : M), c • x = 0 → c = 0 ∨ x = 0) → ∀ (V : Type) [AddCommGroup V] [Module (PadicAlgCl l) V] (j : M →ₛₗ[emb] V) (Tq : I → V →ₗ[PadicAlgCl l] V), (∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent (PadicAlgCl l) fun a => j (x a)) → (∀ i x, j ((MvPolynomial.X i : MvPolynomial I O) • x) = Tq i (j x)) → ∃ (n : ℕ) (σ : MvPolynomial I O →ₐ[O] Matrix (Fin n) (Fin n) O) (e : (Fin n → PadicAlgCl l) →ₗ[PadicAlgCl l] V), (∀ p, σ p = 0 → ∀ x : M, p • x = 0) ∧ Function.Injective e ∧ (∀ c, e c ∈ Submodule.span (PadicAlgCl l) (Set.range j)) ∧ ∀ i c, Tq i (e c) = e ((σ (MvPolynomial.X i)).map emb *ᵥ c) := by
  intro l _ O _ _ _ emb I M _ _ _ _ hfin htf V _ _ j Tq hli hX
  have : NoZeroSMulDivisors O M := ⟨fun {c x} h => htf c x h⟩
  have : Module.Free O M := Module.free_of_finite_type_torsion_free'
  let n := Module.finrank O M
  let b : Module.Basis (Fin n) O M := Module.finBasis O M
  let σ : MvPolynomial I O →ₐ[O] Matrix (Fin n) (Fin n) O :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (Algebra.lsmul O O M)
  let e : (Fin n → PadicAlgCl l) →ₗ[PadicAlgCl l] V :=
    ∑ a, (LinearMap.proj a : (Fin n → PadicAlgCl l) →ₗ[PadicAlgCl l] PadicAlgCl l).smulRight (j (b a))
  have he : ∀ c, e c = ∑ a, c a • j (b a) := by
    intro c
    simp [e, LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hσ : ∀ p a, p • b a = ∑ k, σ p k a • b k := by
    intro p a
    conv_lhs => rw [← b.sum_repr (p • b a)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp [σ, LinearMap.toMatrixAlgEquiv_apply]
  refine ⟨n, σ, e, ?_, ?_, ?_, ?_⟩
  · intro p hp x
    have h1 : (Algebra.lsmul O O M) p = 0 := by
      apply (LinearMap.toMatrixAlgEquiv b).injective
      simpa [σ] using hp
    simpa using LinearMap.congr_fun h1 x
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hl := Fintype.linearIndependent_iff.mp (hli n b b.linearIndependent) c (by rw [← he]; exact hc)
    funext a
    exact hl a
  · intro c
    rw [he]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b a, rfl⟩)
  · intro i c
    have key : ∀ a, Tq i (j (b a)) = ∑ k, emb (σ (MvPolynomial.X i) k a) • j (b k) := by
      intro a
      rw [← hX, hσ, map_sum]
      simp [LinearMap.map_smulₛₗ]
    rw [he, he, map_sum]
    simp_rw [LinearMap.map_smul, key, Finset.smul_sum, smul_smul]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]
end GlobalTheory
