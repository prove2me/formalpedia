-- Prove2me | solution 1 for HopfAlgebra.exists_withConv_equiv_rootsOfUnity_of_comul_gens_quadraticTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a12d66c2-10cc-5a35-9b42-d2e12cd73087

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_withConv_equiv_rootsOfUnity_of_comul_gens_quadraticTwist

set_option maxHeartbeats 16000000

open scoped TensorProduct in
theorem solution
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c)
    (A : Type) [CommRing A] [HopfAlgebra K A] (u v : A)
    (hrel : u ^ 2 - algebraMap K A c * v ^ 2 = 1)
    (hcu : Coalgebra.comul (R := K) u = u ⊗ₜ[K] u + c • (v ⊗ₜ[K] v))
    (hcv : Coalgebra.comul (R := K) v = u ⊗ₜ[K] v + v ⊗ₜ[K] u)
    (hn : ∀ f : A →ₐ[K] AlgebraicClosure K, (f u + f v * δ) ^ n = 1)
    (hlift : ∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      (w + z * δ) ^ n = 1 →
      ∃! f : A →ₐ[K] AlgebraicClosure K, f u = w ∧ f v = z) :
    ∃ eμ : WithConv (A →ₐ[K] AlgebraicClosure K) ≃ rootsOfUnity n (AlgebraicClosure K),
      (∀ f g, eμ (f * g) = eμ f * eμ g) ∧
      ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
        (f g : WithConv (A →ₐ[K] AlgebraicClosure K)),
        (∀ a : A, g a = σ (f a)) →
        (σ δ = δ →
          ((eμ g : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
          = σ ((eμ f : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ∧
        (σ δ = -δ →
          ((eμ g : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
          * σ ((eμ f : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = 1) := by
  have hδne : δ ≠ 0 := fun h => hc ((algebraMap K (AlgebraicClosure K)).injective
    (by rw [← hδ, h, mul_zero, map_zero]))
  have h2ne : (2 : AlgebraicClosure K) ≠ 0 := two_ne_zero
  let raw : WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K :=
    fun f => f.ofConv u + f.ofConv v * δ
  have hrel_φ : ∀ (φ : A →ₐ[K] AlgebraicClosure K),
      φ u ^ 2 - algebraMap K (AlgebraicClosure K) c * φ v ^ 2 = 1 := fun φ => by
    have := congrArg φ hrel
    simp only [map_sub, map_mul, map_pow, map_one, AlgHom.commutes] at this
    exact this
  have hprod : ∀ f, raw f * (f.ofConv u - f.ofConv v * δ) = 1 := fun f => by
    show (f.ofConv u + f.ofConv v * δ) * (f.ofConv u - f.ofConv v * δ) = 1
    have h1 := hrel_φ f.ofConv
    linear_combination h1 - f.ofConv v ^ 2 * hδ
  have hraw_ne : ∀ f, raw f ≠ 0 := fun f h => by
    have := hprod f; rw [h, zero_mul] at this; exact one_ne_zero this.symm
  have hraw_pow : ∀ f, (raw f) ^ n = 1 := fun f => hn f.ofConv
  let toR : WithConv (A →ₐ[K] AlgebraicClosure K) → rootsOfUnity n (AlgebraicClosure K) :=
    fun f => ⟨Units.mk0 _ (hraw_ne f), by
      rw [mem_rootsOfUnity]; ext; push_cast; exact hraw_pow f⟩
  have htoR_coe : ∀ f, ((toR f : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = raw f :=
    fun _ => rfl

  have hconv_u : ∀ f g : WithConv (A →ₐ[K] AlgebraicClosure K),
      (f * g).ofConv u = f.ofConv u * g.ofConv u
        + algebraMap K (AlgebraicClosure K) c * (f.ofConv v * g.ofConv v) := by
    intro f g
    show LinearMap.mul' K (AlgebraicClosure K)
        (TensorProduct.map f.ofConv.toLinearMap g.ofConv.toLinearMap
          (Coalgebra.comul (R := K) u)) = _
    rw [hcu]
    simp only [map_add, LinearMap.map_smul, TensorProduct.map_tmul,
      LinearMap.mul'_apply, AlgHom.toLinearMap_apply]
    rw [Algebra.smul_def]
  have hconv_v : ∀ f g : WithConv (A →ₐ[K] AlgebraicClosure K),
      (f * g).ofConv v = f.ofConv u * g.ofConv v + f.ofConv v * g.ofConv u := by
    intro f g
    show LinearMap.mul' K (AlgebraicClosure K)
        (TensorProduct.map f.ofConv.toLinearMap g.ofConv.toLinearMap
          (Coalgebra.comul (R := K) v)) = _
    rw [hcv]
    simp only [map_add, TensorProduct.map_tmul, LinearMap.mul'_apply,
      AlgHom.toLinearMap_apply]
  have htoR_mul : ∀ f g, toR (f * g) = toR f * toR g := fun f g => by
    refine Subtype.ext (Units.ext ?_)
    push_cast
    show (f * g).ofConv u + (f * g).ofConv v * δ
      = (f.ofConv u + f.ofConv v * δ) * (g.ofConv u + g.ofConv v * δ)
    rw [hconv_u f g, hconv_v f g, ← hδ]; ring

  have htoR_inj : Function.Injective toR := by
    intro f g h
    have hraw : raw f = raw g := by
      have : ((toR f : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
           = ((toR g : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) := by rw [h]
      exact this
    have hrawc : f.ofConv u - f.ofConv v * δ = g.ofConv u - g.ofConv v * δ :=
      mul_left_cancel₀ (hraw_ne g) ((hraw ▸ hprod f).trans (hprod g).symm)
    have hu : f.ofConv u = g.ofConv u := by
      have heq : 2 * f.ofConv u = 2 * g.ofConv u := by
        have h' := congrArg₂ (· + ·) hraw hrawc
        simp only [raw] at h'; linear_combination h'
      exact mul_left_cancel₀ h2ne heq
    have hv : f.ofConv v = g.ofConv v := by
      have h2δ : (2 : AlgebraicClosure K) * δ ≠ 0 := mul_ne_zero h2ne hδne
      have heq : (2 * δ) * f.ofConv v = (2 * δ) * g.ofConv v := by
        have h' := congrArg₂ (· - ·) hraw hrawc
        simp only [raw] at h'; linear_combination h'
      exact mul_left_cancel₀ h2δ heq
    obtain ⟨f₀, _, huniq⟩ := hlift (f.ofConv u) (f.ofConv v) (hrel_φ f.ofConv) (hn f.ofConv)
    have hf := huniq f.ofConv ⟨rfl, rfl⟩
    have hg := huniq g.ofConv ⟨hu.symm, hv.symm⟩
    calc f = WithConv.toConv f.ofConv := rfl
      _ = WithConv.toConv g.ofConv := by rw [hf, hg]
      _ = g := rfl

  have htoR_surj : Function.Surjective toR := by
    intro ζ
    set ζv : AlgebraicClosure K := ((ζ : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
    set ζi : AlgebraicClosure K := (((ζ : (AlgebraicClosure K)ˣ)⁻¹
      : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
    have hζinv : ζv * ζi = 1 := by
      simp only [ζv, ζi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hζpow : ζv ^ n = 1 := by
      have hmem := (mem_rootsOfUnity n (ζ : (AlgebraicClosure K)ˣ)).mp ζ.2
      calc ζv ^ n = (((ζ:(AlgebraicClosure K)ˣ)^n : (AlgebraicClosure K)ˣ)
            : AlgebraicClosure K) := by push_cast; ring
        _ = 1 := by rw [hmem, Units.val_one]
    let w : AlgebraicClosure K := (ζv + ζi) / 2
    let z : AlgebraicClosure K := (ζv - ζi) / (2 * δ)
    have hwz_sum : w + z * δ = ζv := by
      show (ζv + ζi) / 2 + (ζv - ζi) / (2 * δ) * δ = ζv
      field_simp; ring
    have hwz_diff : w - z * δ = ζi := by
      show (ζv + ζi) / 2 - (ζv - ζi) / (2 * δ) * δ = ζi
      field_simp; ring
    have hwz_rel : w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 := by
      rw [← hδ]
      calc w^2 - (δ*δ)*z^2 = (w+z*δ)*(w-z*δ) := by ring
        _ = ζv * ζi := by rw [hwz_sum, hwz_diff]
        _ = 1 := hζinv
    obtain ⟨f₀, ⟨hfu, hfv⟩, _⟩ := hlift w z hwz_rel (by rw [hwz_sum]; exact hζpow)
    refine ⟨WithConv.toConv f₀, Subtype.ext (Units.ext ?_)⟩
    show f₀ u + f₀ v * δ = ζv
    rw [hfu, hfv, hwz_sum]

  refine ⟨Equiv.ofBijective toR ⟨htoR_inj, htoR_surj⟩, htoR_mul, fun σ f g hfg => ?_⟩
  refine ⟨fun hσ => ?_, fun hσ => ?_⟩
  · show g.ofConv u + g.ofConv v * δ = σ (f.ofConv u + f.ofConv v * δ)
    rw [hfg u, hfg v, map_add, map_mul, hσ]
  · show (g.ofConv u + g.ofConv v * δ) * σ (f.ofConv u + f.ofConv v * δ) = 1
    rw [hfg u, hfg v, map_add, map_mul, hσ]
    have hσrel : (σ (f.ofConv u))^2
        - algebraMap K (AlgebraicClosure K) c * (σ (f.ofConv v))^2 = 1 := by
      have := congrArg σ (hrel_φ f.ofConv)
      simp only [map_sub, map_mul, map_pow, map_one, AlgEquiv.commutes] at this
      exact this
    linear_combination hσrel - (σ (f.ofConv v))^2 * hδ

end S_HopfAlgebra_exists_withConv_equiv_rootsOfUnity_of_comul_gens_quadraticTwist
end P2MW
export P2MW.S_HopfAlgebra_exists_withConv_equiv_rootsOfUnity_of_comul_gens_quadraticTwist (solution)
