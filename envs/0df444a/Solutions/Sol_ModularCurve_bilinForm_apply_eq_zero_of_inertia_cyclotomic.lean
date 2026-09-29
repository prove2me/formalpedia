-- Prove2me | solution 1 for ModularCurve.bilinForm_apply_eq_zero_of_inertia_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/63902a96-6797-58cd-93d7-1814690348ca

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_apply_eq_pow_and_apply_eq_self_of_mem_inertiaSubgroupIn_and_exists_mem_inertiaSubgroupIn_of_not_dvd
import Theorems.Thm_ModularCurve_diamondHBar_apply_eq_self_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_bilinForm_apply_eq_zero_of_inertia_cyclotomic
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one"

set_option autoImplicit false
open scoped MatrixGroups

set_option maxHeartbeats 6400000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (b : LinearMap.BilinForm (ZMod p) ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p))
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
      ∀ (x y x' y' : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
        (x' : ModularCurve.JH M H) = ModularCurve.diamondHBar M H (ZMod.unitOfCoprime c hc) (σ • (x : ModularCurve.JH M H)) →
        (y' : ModularCurve.JH M H) = σ • (y : ModularCurve.JH M H) →
          b x' y' = (c : ZMod p) • b x y)
    (x y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) (hx : (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ c : ℕ, (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) → σ • (x : ModularCurve.JH M H) = c • (x : ModularCurve.JH M H))) (hy : (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ c : ℕ, (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) → σ • (y : ModularCurve.JH M H) = c • (y : ModularCurve.JH M H))) :
    b x y = 0 := by
  have hp : p.Prime := Fact.out

  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = M / p := ⟨_, rfl⟩
  have hMpm : M = p * m := by rw [hm]; exact (Nat.mul_div_cancel' hpM).symm
  have hpm : ¬ p ∣ m := by
    intro h
    apply hpM2
    rw [pow_two, hMpm]
    exact Nat.mul_dvd_mul_left p h
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  have hM0 : M ≠ 0 := NeZero.ne M
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hMpm; exact hM0 hMpm

  have h2p : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    apply h2p
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    exact (ZMod.natCast_eq_zero_iff _ _).1 h'
  have h2unit : IsUnit ((2 : ℕ) : ZMod (p ^ 1)) := by
    rw [pow_one]
    exact isUnit_iff_ne_zero.2 (by exact_mod_cast h2ne)
  obtain ⟨u2, hu2⟩ := h2unit

  obtain ⟨-, hsurj⟩ :=
    ValuationSubring.exists_apply_eq_pow_and_apply_eq_self_of_mem_inertiaSubgroupIn_and_exists_mem_inertiaSubgroupIn_of_not_dvd
      p hp 1 m hpm Pl hPl
  obtain ⟨σ, hσI, hσp, hσm⟩ := hsurj u2
  obtain ⟨e, he⟩ : ∃ e : ℕ, e = ((u2 : ZMod (p ^ 1))).val := ⟨_, rfl⟩
  have he2 : e ≡ 2 [MOD p] := by
    have h : ((e : ℕ) : ZMod (p ^ 1)) = ((2 : ℕ) : ZMod (p ^ 1)) := by rw [he, ZMod.natCast_zmod_val, hu2]
    have := (ZMod.natCast_eq_natCast_iff _ _ _).1 h
    rwa [pow_one] at this

  obtain ⟨c, hcp, hcm⟩ := Nat.chineseRemainder hcop e 1
  have hc2 : c ≡ 2 [MOD p] := hcp.trans he2
  have hcM : c.Coprime M := by
    rw [hMpm]
    apply Nat.Coprime.mul_right
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      exact h2p (Nat.modEq_zero_iff_dvd.1 (hc2.symm.trans (Nat.modEq_zero_iff_dvd.2 h)))
    · show Nat.gcd c m = 1
      rw [Nat.ModEq.gcd_eq hcm, Nat.gcd_one_left]

  have powmod : ∀ {w : AlgebraicClosure ℚ} {n a a' : ℕ}, w ^ n = 1 → a ≡ a' [MOD n] → w ^ a = w ^ a' := by
    intro w n a a' hw h
    rw [← Nat.div_add_mod a n, ← Nat.div_add_mod a' n, pow_add, pow_add, pow_mul, pow_mul, hw, one_pow, one_pow,
      one_mul, one_mul, (h : a % n = a' % n)]

  have hσp' : ∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c := by
    intro ζ hζ
    rw [hσp ζ (by rw [pow_one]; exact hζ), ← he]
    exact powmod hζ (hcp.symm).symm.symm

  have hσM : ∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c := by
    intro ζ hζ
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow hM0] at hζ
      exact zero_ne_one hζ
    have hpm1 : ζ ^ (p * m) = 1 := by rw [← hMpm, hζ]
    have hmp1 : ζ ^ (m * p) = 1 := by rw [mul_comm, hpm1]

    have h1 : σ (ζ ^ m) = (ζ ^ m) ^ c := by
      rw [hσp (ζ ^ m) (by rw [← pow_mul, pow_one, hmp1]), ← he]
      exact powmod (by rw [← pow_mul, hmp1]) hcp.symm
    have h2 : σ (ζ ^ p) = (ζ ^ p) ^ c := by
      rw [hσm (ζ ^ p) (by rw [← pow_mul, hpm1])]
      conv_lhs => rw [← pow_one (ζ ^ p)]
      exact powmod (by rw [← pow_mul, hpm1]) hcm.symm

    have hc0 : ζ ^ c ≠ 0 := pow_ne_zero _ hζ0
    have hum : (σ ζ * (ζ ^ c)⁻¹) ^ m = 1 := by
      rw [mul_pow, ← map_pow, h1, inv_pow, ← pow_mul, ← pow_mul, mul_comm c m, mul_inv_cancel₀ (pow_ne_zero _ hζ0)]
    have hup : (σ ζ * (ζ ^ c)⁻¹) ^ p = 1 := by
      rw [mul_pow, ← map_pow, h2, inv_pow, ← pow_mul, ← pow_mul, mul_comm c p, mul_inv_cancel₀ (pow_ne_zero _ hζ0)]
    have hu : σ ζ * (ζ ^ c)⁻¹ = 1 := (pow_eq_one_iff_of_coprime hcop.symm).1 ⟨hum, hup⟩
    rwa [mul_inv_eq_one₀ hc0] at hu

  have hcH : ZMod.unitOfCoprime c hcM ∈ H := by
    apply hHp
    apply Units.ext
    rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.coe_unitOfCoprime, ZMod.castHom_apply,
      ZMod.cast_natCast (Nat.div_dvd_of_dvd hpM), Units.val_one]
    have h := (ZMod.natCast_eq_natCast_iff c 1 (M / p)).2 (by rw [← hm]; exact hcm)
    rwa [Nat.cast_one] at h
  have hdia : ∀ z : ModularCurve.JH M H, ModularCurve.diamondHBar M H (ZMod.unitOfCoprime c hcM) z = z :=
    fun z => ModularCurve.diamondHBar_apply_eq_self_of_mem M H _ hcH z

  have hxσ := hx σ hσI c hσp'
  have hyσ := hy σ hσI c hσp'
  have key := hgal σ c hcM hσM x y (c • x) (c • y)
    ((AddSubmonoidClass.coe_nsmul x c).trans (hxσ.symm.trans (hdia _).symm))
    ((AddSubmonoidClass.coe_nsmul y c).trans hyσ.symm)
  rw [← Nat.cast_smul_eq_nsmul (ZMod p) c x, ← Nat.cast_smul_eq_nsmul (ZMod p) c y, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right, smul_eq_mul, (ZMod.natCast_eq_natCast_iff c 2 p).2 hc2, Nat.cast_ofNat] at key
  have h2b : (2 : ZMod p) * b x y = 0 := by linear_combination key
  exact (mul_eq_zero.1 h2b).resolve_left h2ne

end S_ModularCurve_bilinForm_apply_eq_zero_of_inertia_cyclotomic
end P2MW
export P2MW.S_ModularCurve_bilinForm_apply_eq_zero_of_inertia_cyclotomic (solution)
