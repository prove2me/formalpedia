-- Prove2me | solution 1 for ModularCurve.det_eq_natCast_of_forall_rootsOfUnity_of_det_frobenius_eq_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/76ed797a-8777-5bb6-9e8e-2e345a3620ef

import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_GaloisRep_det_eq_cycloChar_pow_of_det_frobenius_eq_pow
import Theorems.Thm_AlgebraicClosure_exists_cycloChar_family
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_det_eq_natCast_of_forall_rootsOfUnity_of_det_frobenius_eq_natCast
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"
set_option autoImplicit false
open ModularCurve

private theorem natCast_eq_of_forall_rootsOfUnity (p : ℕ) [hp : Fact p.Prime]
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod p)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ p = 1 → σ μ = μ ^ ((cyc σ : ZMod p)).val)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ℕ)
    (ha : ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) :
    (a : ZMod p) = (cyc σ : ZMod p) := by
  have hpp : p.Prime := hp.out
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  haveI : NeZero ((p : ℕ) : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hpp.ne_zero⟩
  obtain ⟨ζ, hζr⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p (AlgebraicClosure ℚ))
    (ne_of_gt (Polynomial.degree_cyclotomic_pos p _ hpp.pos))
  have hζ : IsPrimitiveRoot ζ p := Polynomial.isRoot_cyclotomic_iff.mp hζr
  have h1 : σ ζ = ζ ^ a := ha ζ hζ.pow_eq_one
  have h2 : σ ζ = ζ ^ ((cyc σ : ZMod p)).val := hcyc σ ζ hζ.pow_eq_one
  have h3 : ζ ^ (a % p) = ζ ^ ((cyc σ : ZMod p)).val := by
    have h4 : ζ ^ a = ζ ^ (a % p) := by
      conv_lhs => rw [← Nat.div_add_mod a p, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
    rw [← h4, ← h1, h2]
  have h5 : a % p = ((cyc σ : ZMod p)).val := hζ.pow_inj (Nat.mod_lt a hpp.pos) (ZMod.val_lt _) h3
  rw [← ZMod.natCast_zmod_val (cyc σ : ZMod p), ZMod.natCast_eq_natCast_iff', ← h5,
    Nat.mod_eq_of_lt (Nat.mod_lt a hpp.pos)]

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (S : Finset ℕ)
    (hdet : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρ σ).det) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) → (ρ σ).det = (a : HeckeAlg ⧸ 𝔪) := by
  intro σ a ha
  obtain ⟨cyc, hcyc⟩ := AlgebraicClosure.exists_cycloChar_family
  have hpp : p.Prime := Fact.out
  letI : Field (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : CharP (HeckeAlg ⧸ 𝔪) p := (CharP.charP_iff_prime_eq_zero hpp).mpr (by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr hp
    rwa [map_natCast] at h)
  have hfin' : GaloisFactorsThroughFiniteLevel ρ.toHomUnits := by
    obtain ⟨L, hL, hLρ⟩ := hfin
    exact ⟨L, hL, fun τ hτ => Units.ext (by rw [MonoidHom.coe_toHomUnits, hLρ τ hτ, Units.val_one])⟩
  have key := GaloisRep.det_eq_cycloChar_pow_of_det_frobenius_eq_pow p (F := HeckeAlg ⧸ 𝔪) (cyc p)
    (hcyc p hpp) 1 (S : Set ℕ) S.finite_toSet 1 ρ.toHomUnits hfin'
    (fun ℓ hℓ _ hℓS _ A hA τ hτ => by
      rw [pow_one, MonoidHom.coe_toHomUnits, ← hdet ℓ hℓ (by exact_mod_cast hℓS) A hA τ hτ, map_natCast])
    σ
  rw [pow_one, MonoidHom.coe_toHomUnits] at key
  rw [key, ← natCast_eq_of_forall_rootsOfUnity p (cyc p) (hcyc p hpp) σ a ha, map_natCast]

end S_ModularCurve_det_eq_natCast_of_forall_rootsOfUnity_of_det_frobenius_eq_natCast
end P2MW
export P2MW.S_ModularCurve_det_eq_natCast_of_forall_rootsOfUnity_of_det_frobenius_eq_natCast (solution)
