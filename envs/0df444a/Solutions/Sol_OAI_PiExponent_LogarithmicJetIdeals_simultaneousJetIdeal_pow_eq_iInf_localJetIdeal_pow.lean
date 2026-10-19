-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.simultaneousJetIdeal_pow_eq_iInf_localJetIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:25:43.596341+00:00
-- url     : https://prove2.me/submissions/516f36bf-d39f-465b-be29-cf809047e6a5

import Mathlib
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets

open OAI.PiExponent OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem pie_local_coprime {m : ℕ} (c c' : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (i : Fin m) (hi : c i ≠ c' i) :
    IsCoprime (localJetIdeal c T e) (localJetIdeal c' T e) := by
  set a := jetCoordinate c T i.succ
  set b := jetCoordinate c' T i.succ
  have hab : IsCoprime a b := by
    have hsub : a - b = MvPolynomial.C (c' i - c i) := by
      simp [a, b, jetCoordinate, map_sub]
    have hne : c' i - c i ≠ 0 := sub_ne_zero.mpr (Ne.symm hi)
    refine ⟨MvPolynomial.C (c' i - c i)⁻¹, -MvPolynomial.C (c' i - c i)⁻¹, ?_⟩
    have : MvPolynomial.C (c' i - c i)⁻¹ * (a - b) = 1 := by
      rw [hsub, ← map_mul, inv_mul_cancel₀ hne, map_one]
    linear_combination this
  have hpow : IsCoprime (a ^ e i.succ) (b ^ e i.succ) := hab.pow
  rw [← Ideal.isCoprime_span_singleton_iff] at hpow
  rw [Ideal.isCoprime_iff_sup_eq] at hpow ⊢
  rw [eq_top_iff, ← hpow]
  apply sup_le_sup
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span ⟨i.succ, rfl⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span ⟨i.succ, rfl⟩

theorem solution
    {m : ℕ} (K : ℕ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ)
    (hr : ∃ i, r i ≠ 0) (he : ∀ i, 0 < e i)
    (k : ℕ) :
    (simultaneousJetIdeal K r T e) ^ k =
      ⨅ j : Fin K,
        (localJetIdeal (fun i => (j.val : ℂ) * r i) T e) ^ k := by
  obtain ⟨i, hi⟩ := hr
  set L : Fin K → Ideal (MvPolynomial (Fin (m + 1)) ℂ) :=
    fun j => localJetIdeal (fun i => (j.val : ℂ) * r i) T e
  have hcop : ∀ j j' : Fin K, j ≠ j' → IsCoprime (L j) (L j') := by
    intro j j' hjj
    apply pie_local_coprime _ _ T e i
    intro h
    apply hjj
    have := mul_right_cancel₀ hi h
    exact Fin.ext (by exact_mod_cast this)
  have h1 : simultaneousJetIdeal K r T e = ∏ j, L j := by
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ)
      (fun j _ j' _ hjj => hcop j j' hjj)]
    simp [simultaneousJetIdeal, L]
  have h2 : (∏ j, L j ^ k) = ⨅ j, L j ^ k := by
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ)
      (fun j _ j' _ hjj => (hcop j j' hjj).pow)]
    simp
  rw [h1, ← Finset.prod_pow, h2]
