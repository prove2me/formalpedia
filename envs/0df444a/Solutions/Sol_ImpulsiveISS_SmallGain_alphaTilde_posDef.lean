-- Prove2me | solution 1 for ImpulsiveISS.SmallGain.alphaTilde_posDef
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:49:40.156586+00:00
-- url     : https://prove2.me/submissions/816374e2-c015-4c09-90c0-e262e59c6f00

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
import Definitions.Def_ImpulsiveISS_SmallGain_System
import Definitions.Def_ImpulsiveISS_SmallGain_Interconnection
open scoped NNReal
open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria

open ImpulsiveISS.SmallGain in
theorem solution {n : ℕ} (hn : 0 < n) (α : Fin n → ℝ≥0 → ℝ≥0)
    (hα : ∀ i, IsPosDef (α i))
    (T : (Fin n → ℝ≥0) → (Fin n → ℝ≥0)) (σ : ℝ≥0 → Fin n → ℝ≥0) (τ : Fin n → ℝ≥0 → ℝ≥0)
    (hσ : IsOmegaPath T σ τ) :
    IsPosDef (alphaTilde σ τ α) := by
  obtain ⟨hσc, hK, hInv, -, -, -⟩ := hσ
  have hmono : ∀ i, StrictMono (fun r => σ r i) := fun i => (hK i).1.2.1
  have hzero : ∀ i, σ 0 i = 0 := fun i => (hK i).1.2.2
  have hsurj : ∀ i, Function.Surjective (fun r => σ r i) :=
    fun i x => ⟨τ i x, (hInv i).2 x⟩
  have hτc : ∀ i, Continuous (τ i) := by
    intro i
    let e := StrictMono.orderIsoOfSurjective (fun r => σ r i) (hmono i) (hsurj i)
    have he : (e.symm : ℝ≥0 → ℝ≥0) = τ i := by
      funext x
      have h1 : e (τ i x) = x := (hInv i).2 x
      rw [← h1, e.symm_apply_apply]
      rw [h1]
    rw [← he]
    exact e.symm.continuous
  have hσi : ∀ i, Continuous (fun r => σ r i) := fun i => (continuous_apply i).comp hσc
  have hterm : ∀ i r, τ i (α i (σ r i)) = 0 ↔ r = 0 := by
    intro i r
    have hτ0 : τ i 0 = 0 := by
      have := (hInv i).1 0
      simp only [hzero i] at this
      exact this
    constructor
    · intro h
      have h1 : α i (σ r i) = 0 := by
        have h' : σ (τ i (α i (σ r i))) i = α i (σ r i) := (hInv i).2 (α i (σ r i))
        rw [h, hzero i] at h'
        exact h'.symm
      have h2 : σ r i = 0 := ((hα i).2 _).mp h1
      rw [← hzero i] at h2
      exact (hmono i).injective h2
    · rintro rfl
      rw [hzero i, ((hα i).2 0).mpr rfl, hτ0]
  refine ⟨?_, fun r => ?_⟩
  · unfold alphaTilde
    apply Continuous.finset_sup_apply
    intro i _
    exact (hτc i).comp (((hα i).1).comp (hσi i))
  · unfold alphaTilde
    constructor
    · intro h
      have h0 := (Finset.sup_eq_bot_iff _ _).mp h ⟨0, hn⟩ (Finset.mem_univ _)
      exact (hterm _ r).mp h0
    · rintro rfl
      apply (Finset.sup_eq_bot_iff _ _).mpr
      intro i _
      exact (hterm i 0).mpr rfl
