-- Prove2me | solution 1 for GlobalTheory.CycFr.eq_act_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:14:20.677357+00:00
-- url     : https://prove2.me/submissions/0c70a354-1411-49bb-90d3-3465d8a47c5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfAlgHomEqMul
import Theorems.Thm_GlobalTheory_CycFr_X_dvd_act_X
import Theorems.Thm_GlobalTheory_CycFr_act_comm
import Theorems.Thm_GlobalTheory_CycFr_act_nat_X
import Theorems.Thm_GlobalTheory_CycFr_algHom_ext_X
import Theorems.Thm_GlobalTheory_CycFr_coeff_one_act_X
import Theorems.Thm_GlobalTheory_CycFr_constantCoeff_algHom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries GlobalTheory.CycFr
open GlobalTheory GlobalTheory.CycFr
open PowerSeries
namespace GlobalTheory.CycFr
namespace _root_.GlobalTheory.CycFr
theorem _root_.solution {l : ℕ} [Fact l.Prime] {O : Type}
    [CommRing O] [IsDomain O] [CharZero O]
    [Algebra ℤ_[l] O] (φ₀ g : O⟦X⟧ →ₐ[O] O⟦X⟧) (c : ℤ_[l]) (hφ : φ₀ X = (1 + X) ^ l - 1)
    (hc : ∀ a, φ₀ (g a) = g (φ₀ a)) (h0 : constantCoeff (g X) = 0)
    (h1 : coeff 1 (g X) = algebraMap ℤ_[l] O c) :
    g = _root_.GlobalTheory.CycFr.act O c := by
  set A := _root_.GlobalTheory.CycFr.act O c X with hAdef
  set G := g X with hGdef
  set P : O⟦X⟧ := ∑ i ∈ Finset.range l, (1 + X) ^ i with hPdef
  have hP : (1 + X : O⟦X⟧) ^ l - 1 = X * P := by
    rw [← geom_sum_mul, add_sub_cancel_left, mul_comm]
  have hPc : constantCoeff P = (l : O) := by simp [P]
  have hXφ : X ∣ φ₀ X := by rw [hφ, hP]; exact dvd_mul_right _ _
  have hφact : φ₀ = _root_.GlobalTheory.CycFr.act O (l : ℤ_[l]) := by
    apply _root_.GlobalTheory.CycFr.algHom_ext_X _ _ hXφ
    rw [hφ, _root_.GlobalTheory.CycFr.act_nat_X]
  have hA0 : constantCoeff A = 0 :=
    PowerSeries.X_dvd_iff.mp (_root_.GlobalTheory.CycFr.X_dvd_act_X c)
  have hG : φ₀ G = (1 + G) ^ l - 1 := by
    rw [hGdef, hc, hφ]; simp [map_sub, map_pow, map_add, map_one]
  have hA : φ₀ A = (1 + A) ^ l - 1 := by
    rw [hAdef, hφact, _root_.GlobalTheory.CycFr.act_comm, ← hφact, hφ]
    simp [map_sub, map_pow, map_add, map_one]
  have hstep : ∀ n, 2 ≤ n → ∀ E : O⟦X⟧, G - A = X ^ n * E → constantCoeff E = 0 := by
    intro n hn E hE
    set S : O⟦X⟧ := ∑ i ∈ Finset.range l, (1 + G) ^ i * (1 + A) ^ (l - 1 - i) with hSdef
    have hSc : constantCoeff S = (l : O) := by simp [S, hA0, h0]
    have hD : φ₀ (G - A) = (G - A) * S := by
      have hgs := geom_sum₂_mul (1 + G) (1 + A) l
      rw [add_sub_add_left_eq_sub] at hgs
      rw [map_sub, hG, hA, mul_comm, hgs]; ring
    rw [hE, map_mul, map_pow, hφ, hP, mul_pow, mul_assoc, mul_assoc] at hD
    have hcancel := mul_left_cancel₀ (pow_ne_zero n PowerSeries.X_ne_zero) hD
    have hcc := congrArg constantCoeff hcancel
    rw [map_mul, map_mul, map_pow, hPc, hSc,
      _root_.GlobalTheory.CycFr.constantCoeff_algHom φ₀ hXφ E] at hcc
    have hne : ((l : O) ^ n) ≠ (l : O) := by
      rw [← Nat.cast_pow, Ne, Nat.cast_inj]
      intro h
      have h2 : 2 ≤ l := (Fact.out : l.Prime).two_le
      have := Nat.pow_right_injective h2 (h.trans (pow_one l).symm)
      omega
    have : constantCoeff E * ((l : O) ^ n - l) = 0 := by linear_combination hcc
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  have hdvd : ∀ n, X ^ (n + 2) ∣ G - A := by
    intro n
    induction n with
    | zero =>
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      interval_cases m
      · simp [hA0, h0]
      · rw [map_sub, h1, hAdef, _root_.GlobalTheory.CycFr.coeff_one_act_X, sub_self]
    | succ k ih =>
      obtain ⟨E, hE⟩ := ih
      have he := hstep (k + 2) (by omega) E hE
      obtain ⟨F, hF⟩ := PowerSeries.X_dvd_iff.mpr he
      exact ⟨F, by rw [hE, hF]; ring⟩
  have hGA : G = A := by
    rw [← sub_eq_zero]
    ext m
    have := PowerSeries.X_pow_dvd_iff.mp (hdvd m) m (by omega)
    simpa using this
  exact _root_.GlobalTheory.CycFr.algHom_ext_X _ _ (PowerSeries.X_dvd_iff.mpr h0) hGA
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
