-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.localJetIdeal_pairwise_isCoprime
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:08:36.563552+00:00
-- url     : https://prove2.me/submissions/44123b96-af04-4336-add0-bb89ef4cf708

import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m K : ℕ} (c : Fin K → Fin m → ℂ) (T : Fin m → ℕ)
    (b : Fin (m + 1) → ℕ) (hb : ∀ i, 0 < b i)
    (hc : Function.Injective c) :
    Pairwise (fun j l : Fin K =>
      IsCoprime (localJetIdeal (c j) T b) (localJetIdeal (c l) T b)) := by
  classical
  intro j l hjl
  have hcenters : c j ≠ c l := by
    intro h
    exact hjl (hc h)
  obtain ⟨i, hi⟩ : ∃ i, c j i ≠ c l i := by
    by_contra h
    apply hcenters
    funext i
    by_contra hne
    exact h ⟨i, hne⟩
  let f := jetCoordinate (c j) T i.succ
  let g := jetCoordinate (c l) T i.succ
  have hdelta : c l i - c j i ≠ 0 := sub_ne_zero.mpr hi.symm
  have hdiff : f - g = MvPolynomial.C (c l i - c j i) := by
    dsimp [f, g]
    simp only [jetCoordinate, Fin.cases_succ, map_sub]
    ring
  have hfg : IsCoprime f g := by
    refine ⟨MvPolynomial.C ((c l i - c j i)⁻¹),
      -MvPolynomial.C ((c l i - c j i)⁻¹), ?_⟩
    calc
      _ = MvPolynomial.C ((c l i - c j i)⁻¹) * (f - g) := by ring
      _ = MvPolynomial.C ((c l i - c j i)⁻¹) *
          MvPolynomial.C (c l i - c j i) := by rw [hdiff]
      _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hdelta, map_one]
  have hf : f ^ b i.succ ∈ localJetIdeal (c j) T b := by
    apply Ideal.subset_span
    exact ⟨i.succ, rfl⟩
  have hg : g ^ b i.succ ∈ localJetIdeal (c l) T b := by
    apply Ideal.subset_span
    exact ⟨i.succ, rfl⟩
  obtain ⟨u, v, huv⟩ := hfg.pow (m := b i.succ) (n := b i.succ)
  apply Ideal.isCoprime_iff_exists.mpr
  exact ⟨u * f ^ b i.succ, (localJetIdeal (c j) T b).mul_mem_left u hf,
    v * g ^ b i.succ, (localJetIdeal (c l) T b).mul_mem_left v hg, huv⟩