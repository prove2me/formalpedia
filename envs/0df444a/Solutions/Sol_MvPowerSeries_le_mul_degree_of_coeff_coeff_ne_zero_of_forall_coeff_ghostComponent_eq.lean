-- Prove2me | solution 1 for MvPowerSeries.le_mul_degree_of_coeff_coeff_ne_zero_of_forall_coeff_ghostComponent_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/4dcb5858-1f5f-570b-a84b-de853a2f41df

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_le_mul_degree_of_coeff_coeff_ne_zero_of_forall_coeff_ghostComponent_eq

set_option autoImplicit false

universe u v

namespace MvPowerSeries
p2m_export "MvPowerSeries" "coeff C X monomial coeff_zero coeff_C_mul coeff_mul"
namespace D2Dwork
p2m_open "MvPowerSeries"

p2m_open "MvPowerSeries P2MW.S_MvPowerSeries_le_mul_degree_of_coeff_coeff_ne_zero_of_forall_coeff_ghostComponent_eq.MvPowerSeries Finset"

variable {𝓞 : Type*} [CommRing 𝓞] {τ : Type*}

private def WOrd (c L : ℕ) (f : MvPowerSeries τ 𝓞) : Prop :=
  ∀ μ : τ →₀ ℕ, coeff μ f ≠ 0 → L ≤ c * μ.degree

private theorem word_zero (c L : ℕ) : WOrd c L (0 : MvPowerSeries τ 𝓞) :=
  fun μ h => absurd (coeff_zero μ) h

private theorem word_add {c L : ℕ} {f g : MvPowerSeries τ 𝓞} (hf : WOrd c L f) (hg : WOrd c L g) :
    WOrd c L (f + g) := by
  intro μ h
  rw [map_add] at h
  by_cases hfμ : coeff μ f = 0
  · rw [hfμ, zero_add] at h
    exact hg μ h
  · exact hf μ hfμ

private theorem word_neg {c L : ℕ} {f : MvPowerSeries τ 𝓞} (hf : WOrd c L f) : WOrd c L (-f) := by
  intro μ h
  rw [map_neg, neg_ne_zero] at h
  exact hf μ h

private theorem word_sub {c L : ℕ} {f g : MvPowerSeries τ 𝓞} (hf : WOrd c L f) (hg : WOrd c L g) :
    WOrd c L (f - g) := by
  rw [sub_eq_add_neg]
  exact word_add hf (word_neg hg)

private theorem word_sum {c L : ℕ} {ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries τ 𝓞)
    (h : ∀ i ∈ s, WOrd c L (f i)) : WOrd c L (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty]; exact word_zero c L
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact word_add (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

private theorem word_mul {c L₁ L₂ : ℕ} {f g : MvPowerSeries τ 𝓞} (hf : WOrd c L₁ f) (hg : WOrd c L₂ g) :
    WOrd c (L₁ + L₂) (f * g) := by
  classical
  intro μ h
  rw [coeff_mul] at h
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [HasAntidiagonal.mem_antidiagonal] at hx
  have h1 : coeff x.1 f ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
  have h2 : coeff x.2 g ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
  have := add_le_add (hf _ h1) (hg _ h2)
  rwa [← mul_add, ← map_add, hx] at this

private theorem word_pow {c L : ℕ} {f : MvPowerSeries τ 𝓞} (hf : WOrd c L f) :
    ∀ N : ℕ, WOrd c (N * L) (f ^ N)
  | 0 => fun μ _ => by rw [zero_mul]; exact Nat.zero_le _
  | N + 1 => by
    rw [pow_succ, Nat.succ_mul]
    exact word_mul (word_pow hf N) hf

private theorem word_of_mul {a c L : ℕ} (ha : 0 < a) {f : MvPowerSeries τ 𝓞} (hf : WOrd (a * c) (a * L) f) :
    WOrd c L f := fun μ h =>
  Nat.le_of_mul_le_mul_left (by simpa [mul_assoc] using hf μ h) ha

private theorem word_C_mul {c L : ℕ} (r : 𝓞) {f : MvPowerSeries τ 𝓞} (hf : WOrd c L f) :
    WOrd c L (C r * f) := by
  intro μ h
  rw [coeff_C_mul] at h
  exact hf μ (right_ne_zero_of_mul h)

private theorem word_of_C_mul {c L : ℕ} {r : 𝓞} (hr : r ∈ nonZeroDivisors 𝓞) {f : MvPowerSeries τ 𝓞}
    (hf : WOrd c L (C r * f)) : WOrd c L f := by
  intro μ h
  refine hf μ ?_
  rw [coeff_C_mul]
  exact fun h0 => h ((mem_nonZeroDivisors_iff.1 hr).1 _ h0)

end MvPowerSeries.D2Dwork

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {τ : Type v} [Fintype τ] (M L : ℕ) (H : MvPowerSeries τ 𝓞)
    (hL : ∀ μ : τ →₀ ℕ, MvPowerSeries.coeff μ H ≠ 0 → L ≤ μ.degree)
    (ℓ : WittVector p (MvPowerSeries τ 𝓞))
    (hℓ : ∀ n : ℕ, n < M → ∀ μ' : τ →₀ ℕ,
      MvPowerSeries.coeff μ' (WittVector.ghostComponent n ℓ) = MvPowerSeries.coeff (p ^ (M - 1 - n) • μ') H)
    (j : ℕ) (hj : j < M) (μ' : τ →₀ ℕ) (hμ' : MvPowerSeries.coeff μ' (ℓ.coeff j) ≠ 0) :
    L ≤ p ^ (M - 1 - j) * μ'.degree := by
  classical

  suffices key : ∀ j : ℕ, j < M → MvPowerSeries.D2Dwork.WOrd (p ^ (M - 1 - j)) L (ℓ.coeff j) from
    key j hj μ' hμ'
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hjM
  have hp0 : 0 < p := (Fact.out : p.Prime).pos

  have hghost : MvPowerSeries.D2Dwork.WOrd (p ^ (M - 1 - j)) L (WittVector.ghostComponent j ℓ) := by
    intro μ hμ
    rw [hℓ j hjM] at hμ
    have h := hL _ hμ
    rwa [map_nsmul, smul_eq_mul] at h

  have hlow : ∀ i ∈ Finset.range j, MvPowerSeries.D2Dwork.WOrd (p ^ (M - 1 - j)) L
      ((p : MvPowerSeries τ 𝓞) ^ i * (ℓ.coeff i) ^ p ^ (j - i)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [← map_natCast (MvPowerSeries.C (σ := τ) (R := 𝓞)) p, ← map_pow]
    refine MvPowerSeries.D2Dwork.word_C_mul _ ?_
    refine MvPowerSeries.D2Dwork.word_of_mul (pow_pos hp0 (j - i)) ?_
    rw [← pow_add, show j - i + (M - 1 - j) = M - 1 - i by omega]
    exact MvPowerSeries.D2Dwork.word_pow (ih i hi (by omega)) _

  have hrec : (p : MvPowerSeries τ 𝓞) ^ j * ℓ.coeff j =
      WittVector.ghostComponent j ℓ -
        ∑ i ∈ Finset.range j, (p : MvPowerSeries τ 𝓞) ^ i * (ℓ.coeff i) ^ p ^ (j - i) := by
    rw [WittVector.ghostComponent_apply, aeval_wittPolynomial, Finset.sum_range_succ, Nat.sub_self,
      pow_zero, pow_one, add_sub_cancel_left]
  have hpj : MvPowerSeries.D2Dwork.WOrd (p ^ (M - 1 - j)) L ((p : MvPowerSeries τ 𝓞) ^ j * ℓ.coeff j) := by
    rw [hrec]
    exact MvPowerSeries.D2Dwork.word_sub hghost (MvPowerSeries.D2Dwork.word_sum _ _ hlow)
  rw [← map_natCast (MvPowerSeries.C (σ := τ) (R := 𝓞)) p, ← map_pow] at hpj
  exact MvPowerSeries.D2Dwork.word_of_C_mul (pow_mem hp j) hpj

end S_MvPowerSeries_le_mul_degree_of_coeff_coeff_ne_zero_of_forall_coeff_ghostComponent_eq
end P2MW
export P2MW.S_MvPowerSeries_le_mul_degree_of_coeff_coeff_ne_zero_of_forall_coeff_ghostComponent_eq (solution)
