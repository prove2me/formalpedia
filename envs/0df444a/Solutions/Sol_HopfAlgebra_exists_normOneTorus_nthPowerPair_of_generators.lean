-- Prove2me | solution 1 for HopfAlgebra.exists_normOneTorus_nthPowerPair_of_generators
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c99c7367-a10a-5b52-9bfa-b3ed79f4c2c8

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_normOneTorus_nthPowerPair_of_generators

open scoped TensorProduct

set_option maxHeartbeats 12000000 in
theorem solution
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c)
    (B₀ : Type) [CommRing B₀] [HopfAlgebra K B₀] (hcc₀ : Coalgebra.IsCocomm K B₀)
    (u₀ v₀ : B₀)
    (hgen₀ : Algebra.adjoin K {u₀, v₀} = ⊤)
    (hrel₀ : u₀ ^ 2 - algebraMap K B₀ c * v₀ ^ 2 = 1)
    (hcu₀ : Coalgebra.comul (R := K) u₀ = u₀ ⊗ₜ[K] u₀ + c • (v₀ ⊗ₜ[K] v₀))
    (hcv₀ : Coalgebra.comul (R := K) v₀ = u₀ ⊗ₜ[K] v₀ + v₀ ⊗ₜ[K] u₀)
    (hlift₀ : ∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      ∃! g : B₀ →ₐ[K] AlgebraicClosure K, g u₀ = w ∧ g v₀ = z) :
    ∃ (P Q : B₀),
      (P ^ 2 - algebraMap K B₀ c * Q ^ 2 = 1) ∧
      (Coalgebra.comul (R := K) P = P ⊗ₜ[K] P + c • (Q ⊗ₜ[K] Q)) ∧
      (Coalgebra.comul (R := K) Q = P ⊗ₜ[K] Q + Q ⊗ₜ[K] P) ∧
      (Coalgebra.counit (R := K) P = 1) ∧
      (Coalgebra.counit (R := K) Q = 0) ∧
      (∀ f : B₀ →ₐ[K] AlgebraicClosure K,
        f P + f Q * δ = (f u₀ + f v₀ * δ) ^ n ∧
        f P - f Q * δ = (f u₀ - f v₀ * δ) ^ n) := by
  classical
  set ε : B₀ →ₐ[K] K := Bialgebra.counitAlgHom K B₀ with hε_def
  set Δ : B₀ →ₐ[K] B₀ ⊗[K] B₀ := Bialgebra.comulAlgHom K B₀ with hΔ_def
  have hε_eq : ∀ x, Coalgebra.counit (R := K) x = ε x := fun x => rfl
  have hΔ_eq : ∀ x, Coalgebra.comul (R := K) x = Δ x := fun x => rfl

  have hεuv : ε u₀ = 1 ∧ ε v₀ = 0 := by
    obtain ⟨g₁, ⟨hgu, hgv⟩, -⟩ := hlift₀ 1 0 (by ring)
    have ax : ∀ x : B₀, (TensorProduct.lid K B₀)
        ((Coalgebra.counit (R := K)).rTensor B₀ (Coalgebra.comul (R := K) x)) = x := by
      intro x; rw [Coalgebra.rTensor_counit_comul]; simp
    have eq1 : (ε u₀) • u₀ + (c * ε v₀) • v₀ = u₀ := by
      have := ax u₀; rw [hcu₀] at this
      simpa only [map_add, map_smul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
        hε_eq, smul_smul] using this
    have eq2 : (ε v₀) • u₀ + (ε u₀) • v₀ = v₀ := by
      have := ax v₀; rw [hcv₀] at this
      have h := this
      simp only [map_add, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hε_eq] at h
      linear_combination (norm := module) h
    have inj : Function.Injective (algebraMap K (AlgebraicClosure K)) :=
      FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)
    constructor
    · apply inj
      have := congrArg g₁ eq1
      simp only [map_add, map_smul, hgu, hgv, smul_zero, add_zero] at this
      rw [Algebra.smul_def, mul_one] at this
      simpa using this
    · apply inj
      have := congrArg g₁ eq2
      simp only [map_add, map_smul, hgu, hgv, smul_zero, add_zero] at this
      rw [Algebra.smul_def, mul_one] at this
      simpa using this
  obtain ⟨hεu₀, hεv₀⟩ := hεuv

  set cB : B₀ := algebraMap K B₀ c with hcB
  let PQ : ℕ → B₀ × B₀ := fun k =>
    Nat.rec (1, 0) (fun _ pq => (u₀ * pq.1 + cB * v₀ * pq.2, u₀ * pq.2 + v₀ * pq.1)) k
  let P : ℕ → B₀ := fun k => (PQ k).1
  let Q : ℕ → B₀ := fun k => (PQ k).2
  have hP0 : P 0 = 1 := rfl
  have hQ0 : Q 0 = 0 := rfl
  have hPsucc : ∀ k, P (k+1) = u₀ * P k + cB * v₀ * Q k := fun k => rfl
  have hQsucc : ∀ k, Q (k+1) = u₀ * Q k + v₀ * P k := fun k => rfl

  let L : B₀ →ₐ[K] B₀ ⊗[K] B₀ := Algebra.TensorProduct.includeLeft
  let R : B₀ →ₐ[K] B₀ ⊗[K] B₀ := Algebra.TensorProduct.includeRight
  have hLR : ∀ x y : B₀, x ⊗ₜ[K] y = L x * R y := by
    intro x y
    simp only [L, R, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hLcB : L cB = algebraMap K (B₀ ⊗[K] B₀) c := by rw [hcB]; exact L.commutes c
  have hRcB : R cB = algebraMap K (B₀ ⊗[K] B₀) c := by rw [hcB]; exact R.commutes c
  have hΔc : Δ cB = algebraMap K (B₀ ⊗[K] B₀) c := by rw [hcB]; exact Δ.commutes c

  have main : ∀ k,
      (P k ^ 2 - cB * Q k ^ 2 = 1) ∧
      (Δ (P k) = P k ⊗ₜ[K] P k + c • (Q k ⊗ₜ[K] Q k)) ∧
      (Δ (Q k) = P k ⊗ₜ[K] Q k + Q k ⊗ₜ[K] P k) ∧
      (ε (P k) = 1) ∧ (ε (Q k) = 0) ∧
      (∀ f : B₀ →ₐ[K] AlgebraicClosure K,
        f (P k) + f (Q k) * δ = (f u₀ + f v₀ * δ) ^ k ∧
        f (P k) - f (Q k) * δ = (f u₀ - f v₀ * δ) ^ k) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hP0, hQ0]; ring
      · rw [hP0, hQ0]; simp [map_one, Algebra.TensorProduct.one_def]
      · rw [hP0, hQ0]; simp [map_zero]
      · rw [hP0]; exact map_one ε
      · rw [hQ0]; exact map_zero ε
      · intro f; rw [hP0, hQ0]; simp [map_one, map_zero, pow_zero]
    | succ k ih =>
      obtain ⟨ihrel, ihcP, ihcQ, ihεP, ihεQ, ihpow⟩ := ih
      have hrel₀' : u₀ * u₀ - cB * (v₀ * v₀) = 1 := by linear_combination hrel₀
      have hΔu : Δ u₀ = u₀ ⊗ₜ[K] u₀ + c • (v₀ ⊗ₜ[K] v₀) := hcu₀
      have hΔv : Δ v₀ = u₀ ⊗ₜ[K] v₀ + v₀ ⊗ₜ[K] u₀ := hcv₀
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hPsucc, hQsucc]
        linear_combination (P k ^ 2 - cB * Q k ^ 2) * hrel₀' + ihrel
      · rw [hPsucc, hQsucc]
        simp only [map_add, map_mul, ihcP, ihcQ, hΔu, hΔv, hΔc, hLR, Algebra.smul_def,
          hLcB, hRcB, map_one]
        ring
      · rw [hPsucc, hQsucc]
        simp only [map_add, map_mul, ihcP, ihcQ, hΔu, hΔv, hΔc, hLR, Algebra.smul_def,
          hLcB, hRcB, map_one]
        ring
      · simp only [hPsucc, map_add, map_mul, ihεP, ihεQ, hεu₀, hεv₀, hcB, AlgHom.commutes,
          mul_zero, mul_one, add_zero]
      · simp only [hQsucc, map_add, map_mul, ihεP, ihεQ, hεu₀, hεv₀, mul_zero, zero_mul,
          mul_one, one_mul, add_zero, zero_add]
      · intro f
        obtain ⟨ihpow1, ihpow2⟩ := ihpow f
        have hfcB : f cB = algebraMap K (AlgebraicClosure K) c := by rw [hcB]; exact f.commutes c
        have key1 : f (P (k+1)) + f (Q (k+1)) * δ
            = (f u₀ + f v₀ * δ) * (f (P k) + f (Q k) * δ) := by
          simp only [hPsucc, hQsucc, map_add, map_mul, hfcB, ← hδ]; ring
        have key2 : f (P (k+1)) - f (Q (k+1)) * δ
            = (f u₀ - f v₀ * δ) * (f (P k) - f (Q k) * δ) := by
          simp only [hPsucc, hQsucc, map_add, map_mul, hfcB, ← hδ]; ring
        exact ⟨by rw [key1, ihpow1]; ring, by rw [key2, ihpow2]; ring⟩

  obtain ⟨hrelPQ, hcP, hcQ, hεP, hεQ, hpow⟩ := main n
  exact ⟨P n, Q n, hcB ▸ hrelPQ, hΔ_eq _ ▸ hcP, hΔ_eq _ ▸ hcQ,
    hε_eq _ ▸ hεP, hε_eq _ ▸ hεQ, hpow⟩

end S_HopfAlgebra_exists_normOneTorus_nthPowerPair_of_generators
end P2MW
export P2MW.S_HopfAlgebra_exists_normOneTorus_nthPowerPair_of_generators (solution)
