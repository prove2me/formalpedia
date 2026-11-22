-- Prove2me | solution 1 for LamLitt.omega_integrality_iff_first_coeffs
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T23:26:20.626189+00:00
-- url     : https://prove2.me/submissions/19a5429d-1682-44f3-b5c4-93fdad4677b1

import Definitions.Def_LamLitt_Defs
import Mathlib

namespace LamLittAuxB

open LamLitt

/-- The set of `m ≤ p` whose threshold `P₀ m` is at most `p`. -/
noncomputable def S (P₀ : ℕ → ℕ) (p : ℕ) : Finset ℕ :=
  (Finset.range (p + 1)).filter (fun m => P₀ m ≤ p)

/-- The largest `m ≤ p` with `P₀ m ≤ p` (or `0` if there is none). -/
noncomputable def M (P₀ : ℕ → ℕ) (p : ℕ) : ℕ := (S P₀ p).sup id

lemma M_mem_of_ne_zero (P₀ : ℕ → ℕ) (p : ℕ) (h : M P₀ p ≠ 0) : P₀ (M P₀ p) ≤ p := by
  have hne : (S P₀ p).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    apply h
    simp [M, he]
  obtain ⟨m, hm, hmeq⟩ := Finset.exists_mem_eq_sup (S P₀ p) hne id
  have hm' : P₀ m ≤ p := (Finset.mem_filter.mp hm).2
  have : M P₀ p = m := hmeq
  rw [this]
  exact hm'

lemma le_M (P₀ : ℕ → ℕ) (p m : ℕ) (h1 : m ≤ p) (h2 : P₀ m ≤ p) : m ≤ M P₀ p := by
  have hm : m ∈ S P₀ p := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, h2⟩
  exact Finset.le_sup (f := id) hm

/-- Forward direction. -/
lemma forward (a : ℕ → ℚ) (ω : Nat.Primes → ℤ) (hs : omegaSuperlinear ω)
    (hi : omegaIntegral ω a) (m : ℕ) :
    ∃ P₀ : ℕ, ∀ p : Nat.Primes, P₀ ≤ (p : ℕ) →
      ∀ k : ℕ, k < m * (p : ℕ) → Nat.Coprime (a k).den p := by
  have hev := hs.eventually_ge_atTop (m : ℝ)
  rw [Filter.eventually_comap, Filter.eventually_atTop] at hev
  obtain ⟨P₀, hP₀⟩ := hev
  refine ⟨P₀, fun p hp k hk => ?_⟩
  have h1 : (m : ℝ) ≤ (ω p : ℝ) / ((p : ℕ) : ℝ) := hP₀ (p : ℕ) hp p rfl
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
  rw [le_div_iff₀ hp0] at h1
  have h2 : ((m * (p : ℕ) : ℕ) : ℤ) ≤ ω p := by
    have : (((m * (p : ℕ) : ℕ) : ℤ) : ℝ) ≤ ((ω p : ℤ) : ℝ) := by
      push_cast
      exact h1
    exact_mod_cast this
  apply hi p k
  have h3 : (k : ℤ) < ((m * (p : ℕ) : ℕ) : ℤ) := by exact_mod_cast hk
  omega

/-- Backward direction. -/
lemma backward (a : ℕ → ℚ)
    (h : ∀ m : ℕ, ∃ P₀ : ℕ, ∀ p : Nat.Primes, P₀ ≤ (p : ℕ) →
      ∀ k : ℕ, k < m * (p : ℕ) → Nat.Coprime (a k).den p) :
    ∃ ω : Nat.Primes → ℤ, omegaSuperlinear ω ∧ omegaIntegral ω a := by
  choose P₀ hP₀ using h
  refine ⟨fun p => (M P₀ (p : ℕ) : ℤ) * ((p : ℕ) : ℤ) - 1, ?_, ?_⟩
  · unfold omegaSuperlinear
    rw [Filter.tendsto_atTop]
    intro B
    rw [Filter.eventually_comap]
    filter_upwards [Filter.eventually_ge_atTop (max (P₀ (⌈B⌉₊ + 1)) (⌈B⌉₊ + 1))] with n hn p hpn
    subst hpn
    have hle : ⌈B⌉₊ + 1 ≤ M P₀ (p : ℕ) :=
      le_M P₀ (p : ℕ) _ (le_trans (le_max_right _ _) hn) (le_trans (le_max_left _ _) hn)
    have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
    have hB : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
    have hM : (⌈B⌉₊ : ℝ) + 1 ≤ (M P₀ (p : ℕ) : ℝ) := by exact_mod_cast hle
    rw [le_div_iff₀ hp0]
    push_cast
    have hB0 : (0 : ℝ) ≤ (⌈B⌉₊ : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hM hp0.le, mul_le_mul_of_nonneg_right hB hp0.le,
      mul_nonneg hB0 (sub_nonneg.mpr hp1)]
  · intro p j hj
    have hj' : (j : ℤ) ≤ (M P₀ (p : ℕ) : ℤ) * ((p : ℕ) : ℤ) - 1 := hj
    have hlt : j < M P₀ (p : ℕ) * (p : ℕ) := by
      have : (j : ℤ) < ((M P₀ (p : ℕ) * (p : ℕ) : ℕ) : ℤ) := by
        push_cast
        omega
      exact_mod_cast this
    have hne : M P₀ (p : ℕ) ≠ 0 := by
      intro h0
      rw [h0] at hlt
      omega
    exact hP₀ (M P₀ (p : ℕ)) p (M_mem_of_ne_zero P₀ (p : ℕ) hne) j hlt

end LamLittAuxB

open LamLitt PowerSeries in
theorem solution (a : ℕ → ℚ) :
    (∃ ω : Nat.Primes → ℤ, omegaSuperlinear ω ∧ omegaIntegral ω a) ↔
      ∀ m : ℕ, ∃ P₀ : ℕ, ∀ p : Nat.Primes, P₀ ≤ (p : ℕ) →
        ∀ k : ℕ, k < m * (p : ℕ) → Nat.Coprime (a k).den p := by
  constructor
  · rintro ⟨ω, hs, hi⟩ m
    exact LamLittAuxB.forward a ω hs hi m
  · intro h
    exact LamLittAuxB.backward a h
