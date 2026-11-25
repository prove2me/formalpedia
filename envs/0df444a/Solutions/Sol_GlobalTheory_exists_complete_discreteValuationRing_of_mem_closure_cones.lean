-- Prove2me | solution 1 for GlobalTheory.exists_complete_discreteValuationRing_of_mem_closure_cones
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:50:42.563476+00:00
-- url     : https://prove2.me/submissions/b04f9722-948c-4658-bdab-02249a1c0272

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDiscreteValuationRingOfMemClosureC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDiscreteValuationRingOfMemClosureCones
import Theorems.Thm_GlobalTheory_eval_eq_zero_of_aeval_tmul_eq_zero
import Theorems.Thm_GlobalTheory_exists_complete_discreteValuationRing_of_mem_closure_cone


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (F K J ι : Type) [Field F] [Field K] [Algebra F K] [Fintype J] [Finite ι] (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)], (∀ i, Algebra.FiniteType F (A i)) → ∀ (w : ∀ i, J → A i) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J F) (d : ℕ), G.IsHomogeneous d → (∀ i, MvPolynomial.aeval (w i) G = 0) → MvPolynomial.aeval v G = 0) → ∃ (i : ι) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A i →+* FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ (∀ x : F, f (algebraMap F (A i) x) = algebraMap W (FractionRing W) (algebraMap K W (algebraMap F K x))) ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w i j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W := by
  intro F K J ι _ _ _ _ _ A _ _ hA w v hv h
  classical
  have hN : ∀ i, IsNoetherianRing (K ⊗[F] A i) := fun i =>
    Algebra.FiniteType.isNoetherianRing K _
  by_cases hex : ∃ (i : ι) (P : Ideal (K ⊗[F] A i)), P ∈ minimalPrimes (K ⊗[F] A i) ∧
      ∀ (G : MvPolynomial J K) (d : ℕ), G.IsHomogeneous d →
        MvPolynomial.aeval (fun j => Ideal.Quotient.mk P ((1 : K) ⊗ₜ[F] w i j)) G = 0 →
        MvPolynomial.eval v G = 0
  · obtain ⟨i, P, hP, hG⟩ := hex
    have : P.IsPrime := hP.1.1
    obtain ⟨W, _, _, _, _, f, s, w', h1, h2, h3⟩ :=
      exists_complete_discreteValuationRing_of_mem_closure_cone K ((K ⊗[F] A i) ⧸ P) J
        inferInstance _ v hv hG
    refine ⟨i, W, inferInstance, inferInstance, inferInstance, inferInstance,
      f.toRingHom.comp ((Ideal.Quotient.mk P).comp
        (Algebra.TensorProduct.includeRight (R := F) (A := K) (B := A i)).toRingHom),
      s, w', h1, h2, fun x => ?_, h3⟩
    rw [← IsScalarTower.algebraMap_apply K W (FractionRing W), ← f.commutes]
    change f (Ideal.Quotient.mk P (Algebra.TensorProduct.includeRight (R := F) (A := K)
      (algebraMap F (A i) x))) = f (Ideal.Quotient.mk P (algebraMap K _ (algebraMap F K x)))
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  · exfalso
    push_neg at hex
    choose G d hG hG0 hGv using hex
    have : ∀ i, Finite (minimalPrimes (K ⊗[F] A i)) := fun i =>
      (minimalPrimes.finite_of_isNoetherianRing _).to_subtype
    letI : Fintype (Σ i, minimalPrimes (K ⊗[F] A i)) := Fintype.ofFinite _
    let H : MvPolynomial J K := ∏ x : Σ i, minimalPrimes (K ⊗[F] A i), G x.1 x.2.1 x.2.2
    have hH : H.IsHomogeneous (∑ x : Σ i, minimalPrimes (K ⊗[F] A i), d x.1 x.2.1 x.2.2) :=
      MvPolynomial.IsHomogeneous.prod _ _ _ fun x _ => hG _ _ _
    have hHv : MvPolynomial.eval v H ≠ 0 := by
      rw [map_prod]
      exact Finset.prod_ne_zero_iff.mpr fun x _ => hGv _ _ _
    have hnil : ∀ i, IsNilpotent (MvPolynomial.aeval (fun j => (1 : K) ⊗ₜ[F] w i j) H) := by
      intro i
      rw [nilpotent_iff_mem_prime]
      intro Q hQ
      obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := Q) bot_le
      refine hPQ ?_
      rw [map_prod]
      refine Ideal.prod_mem P (Finset.mem_univ
        (⟨i, P, hP⟩ : Σ i, minimalPrimes (K ⊗[F] A i))) ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hG0 i P hP]
      exact MvPolynomial.comp_aeval_apply _ (Ideal.Quotient.mkₐ K P) _
    choose n hn using hnil
    letI : Fintype ι := Fintype.ofFinite ι
    refine pow_ne_zero (∑ i, n i) hHv ?_
    rw [← map_pow]
    refine eval_eq_zero_of_aeval_tmul_eq_zero A w v h _ _ (hH.pow _) fun i => ?_
    rw [map_pow]
    exact pow_eq_zero_of_le (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)) (hn i)
end GlobalTheory
