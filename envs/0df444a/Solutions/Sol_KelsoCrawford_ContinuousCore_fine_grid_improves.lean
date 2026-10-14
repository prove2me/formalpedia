-- Prove2me | solution 1 for KelsoCrawford.ContinuousCore.fine_grid_improves
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:01:16.395977+00:00
-- url     : https://prove2.me/submissions/bca3458d-4964-448f-9d63-0e0ae6ab1813

import Mathlib
import Definitions.Def_KelsoCrawford_ContinuousCore_Model



namespace KelsoCrawford.ContinuousCore

theorem fg_core {W F : Type}
    [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (hu : M.UtilityRegular)
    (hres : M.ReservationSalaries)
    (H : ℝ)
    (hgain : ∀ A : Allocation W F, M.IsIR A →
      ∃ (j : F) (C : Finset W) (r : W → ℝ),
        (∀ i ∈ C, M.u i (A.assign i) (A.sal i) ≤ M.u i j (r i)) ∧
        KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal + H ≤ KelsoCrawford.Process.profit (M.y j) C r)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < H / ((Fintype.card W : ℝ) + 1))
    (A : Allocation W F) (hIR : M.IsIR A) :
    M.CanStrictlyImprove (M.grid δ) A := by
  obtain ⟨j, C, r, hC, hP⟩ := hgain A hIR
  have hge : ∀ i ∈ C, M.σ i j ≤ r i := by
    intro i hi
    have h1 := hC i hi
    have h2 : M.u i (A.assign i) (M.σ i (A.assign i)) ≤ M.u i (A.assign i) (A.sal i) :=
      (hu i (A.assign i)).1.monotone (hIR.1 i)
    rw [hres i (A.assign i) j] at h2
    exact (hu i j).1.le_iff_le.mp (h2.trans h1)
  let r' : W → ℝ := fun i => M.σ i j + ((⌊(r i - M.σ i j) / δ⌋.toNat : ℕ) + 1 : ℕ) * δ
  have hr' : ∀ i ∈ C, r i < r' i ∧ r' i ≤ r i + δ := by
    intro i hi
    have h0 : 0 ≤ (r i - M.σ i j) / δ := div_nonneg (by linarith [hge i hi]) hδ.le
    have hfl : (0:ℤ) ≤ ⌊(r i - M.σ i j) / δ⌋ := Int.floor_nonneg.mpr h0
    have hcast : ((⌊(r i - M.σ i j) / δ⌋.toNat : ℕ) : ℝ) = (⌊(r i - M.σ i j) / δ⌋ : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hfl]
    have a1 := Int.floor_le ((r i - M.σ i j) / δ)
    have a2 := Int.lt_floor_add_one ((r i - M.σ i j) / δ)
    have e : (r i - M.σ i j) / δ * δ = r i - M.σ i j := div_mul_cancel₀ _ hδ.ne'
    simp only [r', Nat.cast_add, Nat.cast_one, hcast]
    constructor
    · nlinarith
    · nlinarith
  refine ⟨j, C, r', ?_, ?_, ?_⟩
  · intro i _; exact ⟨_, rfl⟩
  · intro i hi
    exact lt_of_le_of_lt (hC i hi) ((hu i j).1 (hr' i hi).1)
  · unfold KelsoCrawford.Process.profit at *
    have hsum : ∑ i ∈ C, r' i ≤ ∑ i ∈ C, r i + C.card * δ := by
      have : ∑ i ∈ C, r' i ≤ ∑ i ∈ C, (r i + δ) := Finset.sum_le_sum (fun i hi => (hr' i hi).2)
      have e2 : ∑ i ∈ C, (r i + δ) = ∑ i ∈ C, r i + C.card * δ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      linarith
    have hcard : (C.card : ℝ) ≤ Fintype.card W := by exact_mod_cast Finset.card_le_univ C
    have hpos : (0:ℝ) < (Fintype.card W : ℝ) + 1 := by positivity
    have hH : δ * ((Fintype.card W : ℝ) + 1) < H := (lt_div_iff₀ hpos).mp hδsmall
    nlinarith
end KelsoCrawford.ContinuousCore

open KelsoCrawford.ContinuousCore


theorem solution {W F : Type}
    [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hres : M.ReservationSalaries)
    (hGS : ∀ j, KelsoCrawford.Process.GrossSubstitutesOn (M.y j) Set.univ)
    (H : ℝ) (hH : 0 < H)
    (hgain : ∀ A : Allocation W F, M.IsIR A →
      ∃ (j : F) (C : Finset W) (r : W → ℝ),
        (∀ i ∈ C, M.u i (A.assign i) (A.sal i) ≤ M.u i j (r i)) ∧
        KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal + H ≤ KelsoCrawford.Process.profit (M.y j) C r)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < H / ((Fintype.card W : ℝ) + 1))
    (A : Allocation W F) (hIR : M.IsIR A)
    (hgrid : ∀ i, A.sal i ∈ M.grid δ i (A.assign i)) :
    M.CanStrictlyImprove (M.grid δ) A := by
  exact fg_core M hu hres H hgain δ hδ hδsmall A hIR
