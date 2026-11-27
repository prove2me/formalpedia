-- Prove2me | solution 1 for GlobalTheory.complex_matrix_descends_of_rational_on_tuple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:38:03.236746+00:00
-- url     : https://prove2.me/submissions/bf05f73c-597e-44db-a42b-dc41fb7a686d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexMatrixDescendsOfRationalOnTuple

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
theorem _root_.solution : ∀ {K : Type} [Field K] (σ : K →+* ℂ) {T : Type} (n D : ℕ) (dQ nV : T → ℕ) (ι : ∀ t, Matrix (Fin D) (Fin (dQ t)) K) (Pq : ∀ t, Matrix (Fin (dQ t)) (Fin (nV t)) K) (V : ∀ t, Matrix (Fin n) (Fin (nV t)) K) (r : T → K) (U : Set T) (t0 : T) (Ψc : Matrix (Fin n) (Fin D) ℂ), t0 ∈ U → Function.Bijective (ι t0).mulVec → Function.Surjective (Pq t0).mulVec → (∀ t ∈ U, Ψc * (ι t * Pq t).map σ = ((r t)⁻¹ • V t).map σ) → (∃ Ψ : Matrix (Fin n) (Fin D) K, Ψ.map σ = Ψc ∧ ∀ t ∈ U, Ψ * ι t * Pq t = (r t)⁻¹ • V t) ∧ (Function.Injective Ψc.mulVec → r t0 = 1 → LinearMap.ker (V t0).mulVecLin = LinearMap.ker (Pq t0).mulVecLin) := by
  intro K _ σ T n D dQ nV ι Pq V r U t0 Ψc ht0 hι hP h
  have hσ : Function.Injective σ := σ.injective
  have hsurj : Function.Surjective (ι t0 * Pq t0).mulVec := by
    intro y
    obtain ⟨x, rfl⟩ := hι.2 y
    obtain ⟨z, rfl⟩ := hP x
    exact ⟨z, (Matrix.mulVec_mulVec _ _ _).symm⟩
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1 hsurj
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Matrix (Fin n) (Fin D) K, Ψ = ((r t0)⁻¹ • V t0) * R := ⟨_, rfl⟩
  have hΨc : Ψ.map σ = Ψc := by
    calc Ψ.map σ = ((r t0)⁻¹ • V t0).map σ * R.map σ := by rw [hΨ, Matrix.map_mul]
      _ = Ψc * (ι t0 * Pq t0).map σ * R.map σ := by rw [h t0 ht0]
      _ = Ψc * ((ι t0 * Pq t0) * R).map σ := by rw [Matrix.map_mul (M := R), Matrix.mul_assoc]
      _ = Ψc := by rw [hR, Matrix.map_one σ σ.map_zero σ.map_one, Matrix.mul_one]
  have hall : ∀ t ∈ U, Ψ * ι t * Pq t = (r t)⁻¹ • V t := by
    intro t ht
    apply Matrix.map_injective hσ
    show (Ψ * ι t * Pq t).map σ = ((r t)⁻¹ • V t).map σ
    rw [Matrix.mul_assoc, Matrix.map_mul, hΨc, h t ht]
  refine ⟨⟨Ψ, hΨc, hall⟩, fun hinj hr => ?_⟩
  have key : Ψ * ι t0 * Pq t0 = V t0 := by
    rw [hall t0 ht0, hr, inv_one, one_smul]
  have hΨinj : Function.Injective Ψ.mulVec := by
    intro x y hxy
    have hc : Ψc.mulVec (fun j => σ (x j)) = Ψc.mulVec (fun j => σ (y j)) := by
      funext i
      change (Ψc).mulVec (σ ∘ x) i = (Ψc).mulVec (σ ∘ y) i
      rw [← hΨc, ← RingHom.map_mulVec, ← RingHom.map_mulVec, hxy]
    funext j
    exact hσ (congrFun (hinj hc) j)
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hv
    rw [← key, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hv
    have h1 : (ι t0).mulVec ((Pq t0).mulVec v) = 0 := hΨinj (hv.trans (Matrix.mulVec_zero Ψ).symm)
    exact hι.1 (h1.trans (Matrix.mulVec_zero (ι t0)).symm)
  · intro hv
    rw [← key, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
end GlobalTheory
