-- Prove2me | solution 1 for InvShareComp.Exog.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:51:06.099683+00:00
-- url     : https://prove2.me/submissions/196dec91-3313-4129-8382-708f83baa7cc

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model
import Theorems.Thm_InvShareComp_Exog_lemma_3a_uniqueness
import Theorems.Thm_InvShareComp_Exog_lemma_2a
import Theorems.Thm_InvShareComp_Exog_central_identity
import Theorems.Thm_InvShareComp_Exog_proposition_1a
import Theorems.Thm_InvShareComp_Exog_proposition_1c

open MeasureTheory Classical

open InvShareComp.Exog in
theorem solution (P : Params) (hP : P.Standing) (ν : Measure (ℝ × ℝ))
    (hν : IsDemandLaw ν) (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1)
    (hS0 : 0 < SVal P ν (P.cbar - P.δ) I) :
    (∀ t ∈ Set.Icc 0 (P.cbar - P.δ), ∀ s s' : ℝ,
        IsSymEqShare P ν t I s → IsSymEqShare P ν (P.cbar - P.δ) I s' →
        profitShare1 P ν t I I s s ≤ profitShare1 P ν (P.cbar - P.δ) I I s' s' ∧
        profitShare2 P ν t I I s s ≤ profitShare2 P ν (P.cbar - P.δ) I I s' s') ∧
    (∀ s' sN : ℝ, IsSymEqShare P ν (P.cbar - P.δ) I s' → IsSymEqNoShare P ν I sN →
        profitNo1 P ν I I sN sN ≤ profitShare1 P ν (P.cbar - P.δ) I I s' s' ∧
        profitNo2 P ν I I sN sN ≤ profitShare2 P ν (P.cbar - P.δ) I I s' s') ∧
    (0 < P.β → ∀ t ∈ Set.Icc 0 (P.cbar - P.δ), ∀ s : ℝ, IsSymEqShare P ν t I s →
        profitShare1 P ν t I I s s < centralProfit P ν I I / 2 ∧
        profitShare2 P ν t I I s s < centralProfit P ν I I / 2 ∧ s ≠ 0) := by
  obtain ⟨hc0, hccb, hcbp, hk, hβ, hδ0, hδ⟩ := hP
  -- swap symmetry of the two retailers' profits at symmetric profiles
  have hswap : ∀ g : ℝ × ℝ → ℝ, ∫ ω, g (ω.2, ω.1) ∂ν = ∫ ω, g ω ∂ν := by
    intro g
    have h := integral_map_equiv (μ := ν) (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)) g
    have hm : Measure.map (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)) ν = ν := by
      exact hν.exch
    rw [hm] at h
    rw [h]; rfl
  have hsym2 : ∀ t s : ℝ, profitShare2 P ν t I I s s = profitShare1 P ν t I I s s := by
    intro t s
    unfold profitShare1 profitShare2
    rw [hswap (fun ω => payShare P t I I (dDet P.β s s) (dDet P.β s s) ω.1 ω.2)]
  have hsymN : ∀ s : ℝ, profitNo2 P ν I I s s = profitNo1 P ν I I s s := by
    intro s
    unfold profitNo1 profitNo2
    rw [hswap (fun ω => payNo P I (dDet P.β s s) ω.1)]
  have hP' : P.Standing := ⟨hc0, hccb, hcbp, hk, hβ, hδ0, hδ⟩
  have htop : P.cbar - P.δ ∈ Set.Icc 0 (P.cbar - P.δ) := ⟨by linarith, le_refl _⟩
  -- the closed-form service level at the top transfer price is non-negative
  have hsTop : 0 ≤ sHat P ν (P.cbar - P.δ) I := by
    unfold sHat
    apply div_nonneg (mul_nonneg hβ hS0.le) (by linarith)
  -- ŝ(t) ≥ ŝ(c̄ − δ) for t in range
  have hmono : ∀ t ∈ Set.Icc 0 (P.cbar - P.δ),
      sHat P ν (P.cbar - P.δ) I ≤ sHat P ν t I := by
    intro t ht
    obtain ⟨h1, h2, -⟩ := proposition_1a P hP' ν hν I hI t ht
    obtain ⟨h1', -, -⟩ := proposition_1a P hP' ν hν I hI (P.cbar - P.δ) htop
    have hk2 : 0 < 2 * P.k := by linarith
    have : sHat P ν t I - sHat P ν (P.cbar - P.δ) I
        = (2 * (P.cbar - P.δ - t)) * P.β * Wval ν I / (2 * P.k) := by
      have e : sHat P ν t I - sHat P ν (P.cbar - P.δ) I
          = (sHat P ν t I - sHatN P ν I) - (sHat P ν (P.cbar - P.δ) I - sHatN P ν I) := by ring
      rw [e, h1, h1']; field_simp; ring
    have : 0 ≤ (2 * (P.cbar - P.δ - t)) * P.β * Wval ν I / (2 * P.k) := by
      apply div_nonneg _ hk2.le
      apply mul_nonneg (mul_nonneg _ hβ) h2
      linarith [ht.2]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro t ht s s' hs hs'
    have e1 := lemma_3a_uniqueness P hP' ν hν I hI t ht s hs
    have e2 := lemma_3a_uniqueness P hP' ν hν I hI (P.cbar - P.δ) htop s' hs'
    have hle : P.k * s' ^ 2 ≤ P.k * s ^ 2 := by
      rw [e1, e2]
      have := hmono t ht
      have : sHat P ν (P.cbar - P.δ) I ^ 2 ≤ sHat P ν t I ^ 2 := by
        apply pow_le_pow_left₀ hsTop this
      nlinarith
    have c1 := central_identity P hP' ν hν I hI t ht s
    have c2 := central_identity P hP' ν hν I hI (P.cbar - P.δ) htop s'
    refine ⟨?_, ?_⟩
    · rw [c1, c2]; linarith
    · rw [hsym2, hsym2, c1, c2]; linarith
  · intro s' sN hs' hsN
    have e2 := lemma_3a_uniqueness P hP' ν hν I hI (P.cbar - P.δ) htop s' hs'
    have eN := (lemma_2a P hP' ν hν I hI sN).1 hsN
    have hc := proposition_1c P hP' ν hν I hI (P.cbar - P.δ)
      ⟨by linarith, le_refl _⟩ hS0.le
    unfold piHatN piHat at hc
    rw [← e2, ← eN] at hc
    exact ⟨hc, by rw [hsymN, hsym2]; exact hc⟩
  · intro hβpos t ht s hs
    have e1 := lemma_3a_uniqueness P hP' ν hν I hI t ht s hs
    have hpos : 0 < sHat P ν (P.cbar - P.δ) I := by
      unfold sHat
      apply div_pos (mul_pos hβpos hS0) (by linarith)
    have hspos : 0 < s := by rw [e1]; linarith [hmono t ht]
    have c1 := central_identity P hP' ν hν I hI t ht s
    have hks : 0 < P.k * s ^ 2 := by positivity
    refine ⟨?_, ?_, hspos.ne'⟩
    · rw [c1]; linarith
    · rw [hsym2, c1]; linarith
