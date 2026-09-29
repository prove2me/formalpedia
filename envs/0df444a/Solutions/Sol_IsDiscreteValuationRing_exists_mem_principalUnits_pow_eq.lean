-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_mem_principalUnits_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7ef9ca61-3af3-5217-91f8-daef9cdb17bf

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_mem_principalUnits_pow_eq

set_option autoImplicit false
open IsLocalRing

namespace Ws26U8

theorem exists_add_pow_succ_eq_quadratic {R : Type*} [CommRing R] (a h : R) (n : ℕ) :
    ∃ d : R, (a + h) ^ (n + 1) = a ^ (n + 1) + (n + 1 : R) * a ^ n * h + h ^ 2 * d := by
  induction n with
  | zero => exact ⟨0, by ring⟩
  | succ n ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨(n + 1 : R) * a ^ n + d * (a + h), ?_⟩
    rw [pow_succ, hd]
    push_cast
    ring

end Ws26U8

open IsLocalRing Ws26U8 in
theorem solution {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {n : ℕ} (hn : 0 < n) {e : ℕ} (hne : Ideal.span {(n : R)} = IsLocalRing.maximalIdeal R ^ e)
    {k : ℕ} (hk : e < k) {w : Rˣ} (hw : w ∈ principalUnits R (k + e)) :
    ∃ u ∈ principalUnits R k, u ^ n = w := by
  set I := IsLocalRing.maximalIdeal R with hI
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hmax : I = Ideal.span {π} := hπ.maximalIdeal_eq
  have hpow : ∀ n : ℕ, I ^ n = Ideal.span {π ^ n} := fun n => by rw [hmax, Ideal.span_singleton_pow]

  have hne' := hne
  rw [hpow, Ideal.span_singleton_eq_span_singleton] at hne'
  obtain ⟨c, hc⟩ := hne'.symm
  obtain ⟨l, hl⟩ : ∃ l : ℕ, n = l + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩

  have unit_of : ∀ a : R, a - 1 ∈ I ^ k → IsUnit a := fun a ha => by
    have ha' : a - 1 ∈ I := Ideal.pow_le_self (by omega) ha
    have h := isUnit_one_sub_self_of_mem_nonunits (-(a - 1)) (I.neg_mem ha')
    rwa [sub_neg_eq_add, add_sub_cancel] at h

  have step : ∀ (M : ℕ) (a : R), k ≤ M → a - 1 ∈ I ^ k → a ^ n - w ∈ I ^ (M + e) →
      ∃ b : R, b - a ∈ I ^ M ∧ b - 1 ∈ I ^ k ∧ b ^ n - w ∈ I ^ (2 * M) := by
    intro M a hkM ha1 haw
    have ha_unit : IsUnit a := unit_of a ha1
    obtain ⟨t, ht⟩ : π ^ (M + e) ∣ a ^ n - w := by rw [← Ideal.mem_span_singleton, ← hpow]; exact haw
    have hq : IsUnit ((c : R) * a ^ l) := c.isUnit.mul (ha_unit.pow l)
    obtain ⟨q', hq'⟩ := hq.exists_right_inv
    set h : R := -(π ^ M * t * q') with hh
    have hhM : h ∈ I ^ M := by
      rw [hpow, Ideal.mem_span_singleton, hh]
      exact (dvd_mul_right _ _).mul_right _ |>.neg_right
    refine ⟨a + h, by rwa [add_sub_cancel_left], ?_, ?_⟩
    · rw [add_sub_right_comm]
      exact Ideal.add_mem _ ha1 (Ideal.pow_le_pow_right hkM hhM)
    · obtain ⟨d, hd⟩ := exists_add_pow_succ_eq_quadratic a h l
      have hlin : a ^ n + (n : R) * a ^ l * h - w = 0 := by
        have e1 : a ^ n = w + π ^ (M + e) * t := by rw [← ht]; ring
        rw [e1, ← hc, hh, pow_add]
        linear_combination (-(π ^ M * π ^ e * t)) * hq'
      have hkey : (a + h) ^ n - w = h ^ 2 * d := by
        rw [hl, hd, ← hl]
        have : ((l : R) + 1) = (n : R) := by rw [hl]; push_cast; ring
        rw [this]
        linear_combination hlin
      rw [hkey, two_mul, pow_add, pow_two]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hhM hhM)

  let S := {q : R × ℕ // k ≤ q.2 ∧ q.1 - 1 ∈ I ^ k ∧ q.1 ^ n - (w : R) ∈ I ^ (q.2 + e)}
  have next : ∀ s : S, ∃ s' : S, s'.1.2 = 2 * s.1.2 - e ∧ s'.1.1 - s.1.1 ∈ I ^ s.1.2 := by
    rintro ⟨⟨a, M⟩, hkM, ha1, haw⟩
    obtain ⟨b, hba, hb1, hbw⟩ := step M a hkM ha1 haw
    have h2M : 2 * M - e + e = 2 * M := by omega
    exact ⟨⟨(b, 2 * M - e), by dsimp only; omega, hb1, by rw [h2M]; exact hbw⟩, rfl, hba⟩
  choose nxt hnxt_M hnxt_sub using next
  have hw0 : (1 : R) ^ n - (w : R) ∈ I ^ (k + e) := by
    rw [one_pow, ← neg_sub]; exact (I ^ (k + e)).neg_mem hw
  let s0 : S := ⟨((1 : R), k), le_rfl, by simp, hw0⟩
  let seq : ℕ → S := fun m => nxt^[m] s0
  have seq_succ : ∀ m, seq (m + 1) = nxt (seq m) := fun m => Function.iterate_succ_apply' nxt m s0
  set f : ℕ → R := fun m => (seq m).1.1 with hf
  set Mx : ℕ → ℕ := fun m => (seq m).1.2 with hMx
  have hM : ∀ m, k + m ≤ Mx m := by
    intro m
    induction m with
    | zero => show k + 0 ≤ k; omega
    | succ m ih =>
      have h1 : Mx (m + 1) = 2 * Mx m - e := by
        show (seq (m + 1)).1.2 = 2 * (seq m).1.2 - e; rw [seq_succ]; exact hnxt_M _
      omega
  have hsub : ∀ m, f (m + 1) - f m ∈ I ^ m := by
    intro m
    have h1 : f (m + 1) - f m ∈ I ^ Mx m := by
      show (seq (m + 1)).1.1 - (seq m).1.1 ∈ I ^ (seq m).1.2; rw [seq_succ]; exact hnxt_sub _
    exact Ideal.pow_le_pow_right ((Nat.le_add_left m k).trans (hM m)) h1
  have hcauchy : ∀ m l, m ≤ l → f l - f m ∈ I ^ m := by
    intro m l hml
    induction l, hml using Nat.le_induction with
    | base => rw [sub_self]; exact Ideal.zero_mem _
    | succ l hml ih =>
      have : f (l + 1) - f m = (f (l + 1) - f l) + (f l - f m) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.pow_le_pow_right hml (hsub l)) ih

  have hprec : ∀ {m l : ℕ}, m ≤ l → f m ≡ f l [SMOD I ^ m • (⊤ : Submodule R R)] := by
    intro m l hml
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub]
    exact (I ^ m).neg_mem (hcauchy m l hml)
  have hpc : IsPrecomplete I R := by rw [hI]; infer_instance
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hpc hprec
  have hL' : ∀ m, f m - L ∈ I ^ m := fun m => by
    have := hL m; rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this

  have hL1 : L - 1 ∈ I ^ k := by
    have h1 : f k - 1 ∈ I ^ k := (seq k).2.2.1
    have : L - 1 = (f k - 1) - (f k - L) := by ring
    rw [this]; exact Ideal.sub_mem _ h1 (hL' k)

  have hLp : L ^ n - w = 0 := by
    have hhd : IsHausdorff I R := by rw [hI]; infer_instance
    refine IsHausdorff.haus hhd _ fun m => ?_
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    have h1 : (f m) ^ n - w ∈ I ^ m :=
      Ideal.pow_le_pow_right ((Nat.le_add_left m k).trans ((hM m).trans (Nat.le_add_right _ e))) (seq m).2.2.2
    have h2 : L ^ n - (f m) ^ n ∈ I ^ m := by
      obtain ⟨r, hr⟩ := sub_dvd_pow_sub_pow L (f m) n
      rw [hr, ← neg_sub, neg_mul]
      exact (I ^ m).neg_mem (Ideal.mul_mem_right _ _ (hL' m))
    have : L ^ n - w = (L ^ n - (f m) ^ n) + ((f m) ^ n - w) := by ring
    rw [this]; exact Ideal.add_mem _ h2 h1

  have hLu : IsUnit L := unit_of L hL1
  refine ⟨hLu.unit, by rw [mem_principalUnits_iff, IsUnit.unit_spec]; exact hL1, ?_⟩
  ext
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  exact sub_eq_zero.mp hLp

end S_IsDiscreteValuationRing_exists_mem_principalUnits_pow_eq
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_mem_principalUnits_pow_eq (solution)
