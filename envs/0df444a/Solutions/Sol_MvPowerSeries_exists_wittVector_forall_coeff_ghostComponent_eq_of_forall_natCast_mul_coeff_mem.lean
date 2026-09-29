-- Prove2me | solution 1 for MvPowerSeries.exists_wittVector_forall_coeff_ghostComponent_eq_of_forall_natCast_mul_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/801897d2-c75c-5a56-b97d-8e3bb790c8d9

import Mathlib
import Theorems.Thm_WittVector_exists_forall_ghostComponent_eq_of_sub_frobeniusLift_mem
import Theorems.Thm_MvPowerSeries_expand_sub_pow_mem_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_wittVector_forall_coeff_ghostComponent_eq_of_forall_natCast_mul_coeff_mem

set_option autoImplicit false

universe u v

namespace MvPowerSeries
p2m_export "MvPowerSeries" "coeff C coeff_mul_C X coeff_expand_smul expand coeff_expand_of_not_dvd ext expand_sub_pow_mem_span_natCast"
namespace D1Dwork
p2m_open "MvPowerSeries"

p2m_open "MvPowerSeries P2MW.S_MvPowerSeries_exists_wittVector_forall_coeff_ghostComponent_eq_of_forall_natCast_mul_coeff_mem.MvPowerSeries"

variable {𝓞 : Type*} [CommRing 𝓞] {p : ℕ}

private theorem mem_span_pow_of_forall_coeff_mem {σ : Type*} {g : MvPowerSeries σ 𝓞} (e : ℕ)
    (h : ∀ m, coeff m g ∈ Ideal.span {(p : 𝓞) ^ e}) : g ∈ Ideal.span {(p : MvPowerSeries σ 𝓞) ^ e} := by
  choose b hb using fun m => Ideal.mem_span_singleton'.1 (h m)
  refine Ideal.mem_span_singleton'.2 ⟨(fun m => b m : MvPowerSeries σ 𝓞), ?_⟩
  ext m
  rw [← map_natCast (C (σ := σ) (R := 𝓞)) p, ← map_pow, coeff_mul_C, ← hb m]
  rfl

private theorem mem_span_pow_of_pow_mul_mem (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞) {a : 𝓞} {K e : ℕ}
    (hKe : K ≤ e) (h : (p : 𝓞) ^ K * a ∈ Ideal.span {(p : 𝓞) ^ e}) :
    a ∈ Ideal.span {(p : 𝓞) ^ (e - K)} := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h
  refine Ideal.mem_span_singleton'.2 ⟨b, ?_⟩
  have h0 : (p : 𝓞) ^ K * (b * (p : 𝓞) ^ (e - K) - a) = 0 := by
    rw [mul_sub, sub_eq_zero, ← hb, mul_comm ((p : 𝓞) ^ K), mul_assoc, ← pow_add,
      Nat.sub_add_cancel hKe]
  exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 (pow_mem hpR K)).1 _ h0)

private theorem mem_span_pow_of_natCast_mul_mem [hp : Fact p.Prime] {u : ℕ} (hu : ¬ p ∣ u) {a : 𝓞}
    {e : ℕ} (h : (u : 𝓞) * a ∈ Ideal.span {(p : 𝓞) ^ e}) : a ∈ Ideal.span {(p : 𝓞) ^ e} := by
  have hcop : IsCoprime (u : ℤ) ((p : ℤ) ^ e) :=
    Nat.isCoprime_iff_coprime.2
      (Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hu).symm)
  obtain ⟨x, y, hxy⟩ := hcop
  have h1 : ((x : 𝓞) * (u : 𝓞) + (y : 𝓞) * (p : 𝓞) ^ e) = 1 := by
    have := congrArg (Int.castRingHom 𝓞) hxy
    simpa using this
  have : a = (x : 𝓞) * ((u : 𝓞) * a) + (p : 𝓞) ^ e * ((y : 𝓞) * a) := by
    calc a = ((x : 𝓞) * (u : 𝓞) + (y : 𝓞) * (p : 𝓞) ^ e) * a := by rw [h1, one_mul]
      _ = _ := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h)
    (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

variable {τ : Type*}

private theorem coeff_smul_mem [hp : Fact p.Prime] (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (M : ℕ)
    (H : MvPowerSeries τ 𝓞)
    (hH : ∀ (μ : τ →₀ ℕ) (t : τ), ((μ t : ℕ) : 𝓞) * coeff μ H ∈ Ideal.span {(p : 𝓞) ^ (M - 1)})
    (K : ℕ) (hK : K ≤ M - 1) (μ : τ →₀ ℕ) (t : τ) (ht : ¬ p ∣ μ t) :
    coeff (p ^ K • μ) H ∈ Ideal.span {(p : 𝓞) ^ (M - 1 - K)} := by
  have h := hH (p ^ K • μ) t
  rw [Finsupp.smul_apply, smul_eq_mul, Nat.cast_mul, Nat.cast_pow, mul_assoc] at h
  exact mem_span_pow_of_natCast_mul_mem ht (mem_span_pow_of_pow_mul_mem hpR hK h)

private noncomputable def gam (M : ℕ) (H : MvPowerSeries τ 𝓞) (k : ℕ) : MvPowerSeries τ 𝓞 :=
  fun μ' => coeff (p ^ (M - 1 - k) • μ') H

private theorem coeff_gam (M : ℕ) (H : MvPowerSeries τ 𝓞) (k : ℕ) (μ' : τ →₀ ℕ) :
    coeff μ' (gam (p := p) M H k) = coeff (p ^ (M - 1 - k) • μ') H := rfl

private theorem gam_succ_sub_expand_mem [hp : Fact p.Prime] (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (M : ℕ)
    (H : MvPowerSeries τ 𝓞)
    (hH : ∀ (μ : τ →₀ ℕ) (t : τ), ((μ t : ℕ) : 𝓞) * coeff μ H ∈ Ideal.span {(p : 𝓞) ^ (M - 1)})
    (k : ℕ) (hk : k + 1 < M) :
    gam (p := p) M H (k + 1) - expand p hp.out.ne_zero (gam (p := p) M H k) ∈
      Ideal.span {(p : MvPowerSeries τ 𝓞) ^ (k + 1)} := by
  apply mem_span_pow_of_forall_coeff_mem
  intro m
  rw [map_sub, coeff_gam]
  by_cases hdiv : ∀ i, p ∣ m i
  ·
    obtain ⟨m₀, rfl⟩ : ∃ m₀ : τ →₀ ℕ, m = p • m₀ :=
      ⟨m.mapRange (fun a => a / p) (by simp), by ext i; simp [Nat.mul_div_cancel' (hdiv i)]⟩
    rw [coeff_expand_smul, coeff_gam, smul_smul, ← pow_succ,
      show M - 1 - (k + 1) + 1 = M - 1 - k by omega, sub_self]
    exact Ideal.zero_mem _
  · obtain ⟨i, hi⟩ := not_forall.1 hdiv
    rw [coeff_expand_of_not_dvd p hp.out.ne_zero _ hi, sub_zero]
    have h := coeff_smul_mem hpR M H hH (M - 1 - (k + 1)) (by omega) m i hi
    rwa [show M - 1 - (M - 1 - (k + 1)) = k + 1 by omega] at h

end MvPowerSeries.D1Dwork

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hfrob : ∀ c : 𝓞, c ^ p - c ∈ Ideal.span {(p : 𝓞)})
    {τ : Type v} [Fintype τ] (M : ℕ) (H : MvPowerSeries τ 𝓞)
    (hH : ∀ (μ : τ →₀ ℕ) (t : τ), ((μ t : ℕ) : 𝓞) * MvPowerSeries.coeff μ H ∈ Ideal.span {(p : 𝓞) ^ (M - 1)}) :
    ∃ ℓ : WittVector p (MvPowerSeries τ 𝓞), ∀ n : ℕ, n < M → ∀ μ' : τ →₀ ℕ,
      MvPowerSeries.coeff μ' (WittVector.ghostComponent n ℓ) = MvPowerSeries.coeff (p ^ (M - 1 - n) • μ') H := by
  classical
  obtain ⟨ℓ, hℓ⟩ := WittVector.exists_forall_ghostComponent_eq_of_sub_frobeniusLift_mem
    (R := MvPowerSeries τ 𝓞) p (MvPowerSeries.expand p (Fact.out : p.Prime).ne_zero).toRingHom
    (fun f => MvPowerSeries.expand_sub_pow_mem_span_natCast p hfrob f) M
    (MvPowerSeries.D1Dwork.gam (p := p) M H)
    (fun k hk => MvPowerSeries.D1Dwork.gam_succ_sub_expand_mem hp M H hH k hk)
  exact ⟨ℓ, fun n hn μ' => by rw [hℓ n hn]; rfl⟩

end S_MvPowerSeries_exists_wittVector_forall_coeff_ghostComponent_eq_of_forall_natCast_mul_coeff_mem
end P2MW
export P2MW.S_MvPowerSeries_exists_wittVector_forall_coeff_ghostComponent_eq_of_forall_natCast_mul_coeff_mem (solution)
