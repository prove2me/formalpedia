-- Prove2me | solution 1 for ModularCurve.ofAlgAut_smul_galois_smul_eq_of_mem_inertiaSubgroupIn_of_frickeGaloisTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/173c1b54-328c-5ea4-9fce-ef853d3f555f

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_FLTPrelim_Ramification

import Theorems.Thm_ValuationSubring_exists_apply_eq_pow_and_apply_eq_self_of_mem_inertiaSubgroupIn_and_exists_mem_inertiaSubgroupIn_of_not_dvd
import Theorems.Thm_ModularCurve_diamondHBar_apply_eq_self_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ofAlgAut_smul_galois_smul_eq_of_mem_inertiaSubgroupIn_of_frickeGaloisTwist
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace WCommInertia

theorem exists_modEq_and_forall_pow_eq_one_apply_eq_pow
    {F K : Type*} [Field F] [Field K] [Algebra F K] (σ : K ≃ₐ[F] K)
    (p N' a : ℕ) (hcop : p.Coprime N') (hpN : p * N' ≠ 0)
    (h1 : ∀ μ : K, μ ^ p = 1 → σ μ = μ ^ a) (h2 : ∀ μ : K, μ ^ N' = 1 → σ μ = μ) :
    ∃ c : ℕ, c ≡ a [MOD p] ∧ c ≡ 1 [MOD N'] ∧ ∀ ζ : K, ζ ^ (p * N') = 1 → σ ζ = ζ ^ c := by
  obtain ⟨c, hc₁, hc₂⟩ := Nat.chineseRemainder hcop a 1
  refine ⟨c, hc₁, hc₂, fun ζ hζ => ?_⟩
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hpN] at hζ
    exact zero_ne_one hζ

  have hbez : (N' : ℤ) * Nat.gcdA N' p + (p : ℤ) * Nat.gcdB N' p = 1 := by
    have h := Nat.gcd_eq_gcd_ab N' p
    rw [Nat.Coprime.gcd_eq_one hcop.symm] at h
    exact_mod_cast h.symm
  set s : ℤ := Nat.gcdA N' p with hs
  set t : ℤ := Nat.gcdB N' p with ht
  have hζ₁ : (ζ ^ N') ^ p = 1 := by rw [← pow_mul, mul_comm, hζ]
  have hζ₂ : (ζ ^ p) ^ N' = 1 := by rw [← pow_mul, hζ]
  have hdec : ζ = (ζ ^ N') ^ s * (ζ ^ p) ^ t := by
    rw [← zpow_natCast ζ N', ← zpow_natCast ζ p, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0, hbez, zpow_one]

  have hc₁' : (ζ ^ N') ^ c = (ζ ^ N') ^ a := by
    rw [pow_eq_pow_mod c hζ₁, pow_eq_pow_mod a hζ₁, hc₁]
  have hc₂' : (ζ ^ p) ^ c = ζ ^ p := by
    conv_rhs => rw [← pow_one (ζ ^ p)]
    rw [pow_eq_pow_mod c hζ₂, pow_eq_pow_mod 1 hζ₂, hc₂]
  calc σ ζ = σ ((ζ ^ N') ^ s * (ζ ^ p) ^ t) := by rw [← hdec]
    _ = (σ (ζ ^ N')) ^ s * (σ (ζ ^ p)) ^ t := by rw [map_mul, map_zpow₀, map_zpow₀]
    _ = ((ζ ^ N') ^ a) ^ s * (ζ ^ p) ^ t := by rw [h1 _ hζ₁, h2 _ hζ₂]
    _ = ((ζ ^ N') ^ c) ^ s * ((ζ ^ p) ^ c) ^ t := by rw [hc₁', hc₂']
    _ = ((ζ ^ N') ^ s * (ζ ^ p) ^ t) ^ c := by
      rw [mul_pow, ← zpow_natCast ((ζ ^ N') ^ s) c, ← zpow_natCast ((ζ ^ p) ^ t) c, ← zpow_mul, ← zpow_mul,
        ← zpow_natCast (ζ ^ N') c, ← zpow_natCast (ζ ^ p) c, ← zpow_mul, ← zpow_mul, mul_comm s, mul_comm t]
    _ = ζ ^ c := by rw [← hdec]

end WCommInertia

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (w : ModularCurve.xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] ModularCurve.xHFunctionFieldBar M H)

    (hw4 : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ x : ModularCurve.JH M H,
          AlgebraicCurve.SemilinearAut.ofAlgAut w • (σ • x)
            = σ • ModularCurve.diamondHBar M H (ZMod.unitOfCoprime c hc) (AlgebraicCurve.SemilinearAut.ofAlgAut w • x))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ Pl.inertiaSubgroupIn ℚ) (x : ModularCurve.JH M H) :
    AlgebraicCurve.SemilinearAut.ofAlgAut w • (σ • x) = σ • (AlgebraicCurve.SemilinearAut.ofAlgAut w • x) := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨N', hN'⟩ := hpM
  have hN'p : ¬ p ∣ N' := fun h => hpM2 (by rw [hN', pow_two]; exact Nat.mul_dvd_mul_left p h)
  have hcop : p.Coprime N' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hN'p
  have hM0 : p * N' ≠ 0 := by rw [← hN']; exact NeZero.ne M
  obtain ⟨h8, -⟩ :=
    ValuationSubring.exists_apply_eq_pow_and_apply_eq_self_of_mem_inertiaSubgroupIn_and_exists_mem_inertiaSubgroupIn_of_not_dvd
      p hp 1 N' hN'p Pl hPl
  obtain ⟨u, hu1, hu2⟩ := h8 σ hσ
  obtain ⟨c, hca, hc1, hζc⟩ := WCommInertia.exists_modEq_and_forall_pow_eq_one_apply_eq_pow σ p N'
    ((u : ZMod (p ^ 1)).val) hcop hM0 (fun μ hμ => hu1 μ (by rw [pow_one]; exact hμ)) hu2

  have hcM : c.Coprime M := by
    rw [hN']
    refine Nat.Coprime.mul_right ?_ ?_
    · have hu := (ZMod.val_coe_unit_coprime u).coprime_dvd_right (dvd_pow_self p one_ne_zero)
      unfold Nat.Coprime at hu ⊢
      rw [hca.gcd_eq]
      exact hu
    · unfold Nat.Coprime
      rw [hc1.gcd_eq]
      exact Nat.gcd_one_left N'
  have hζ : ∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c := fun ζ h => hζc ζ (by rw [← hN']; exact h)
  rw [hw4 σ c hcM hζ x, ModularCurve.diamondHBar_apply_eq_self_of_mem]

  apply hHp
  have hdiv : M / p = N' := by rw [hN']; exact Nat.mul_div_cancel_left N' hp.pos
  have hc1' : c ≡ 1 [MOD M / p] := hdiv ▸ hc1
  ext
  rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.coe_unitOfCoprime, ZMod.castHom_apply, ZMod.cast_natCast (Nat.div_dvd_of_dvd ⟨N', hN'⟩),
    Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
  exact hc1'

#print axioms solution

end S_ModularCurve_ofAlgAut_smul_galois_smul_eq_of_mem_inertiaSubgroupIn_of_frickeGaloisTwist
end P2MW
export P2MW.S_ModularCurve_ofAlgAut_smul_galois_smul_eq_of_mem_inertiaSubgroupIn_of_frickeGaloisTwist (solution)
