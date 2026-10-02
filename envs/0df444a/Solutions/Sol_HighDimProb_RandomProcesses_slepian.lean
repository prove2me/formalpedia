-- Prove2me | solution 1 for HighDimProb.RandomProcesses.slepian
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T08:05:59.063396+00:00
-- url     : https://prove2.me/submissions/c26e70cb-6c24-46d2-a12f-6f3e170a8642

import Mathlib
import Theorems.Thm_HighDimProb_RandomProcesses_slepian_finite_dim_all_thresholds

import Definitions.Def_HighDimProb_RandomProcesses_ProcessESup
import Definitions.Def_HighDimProb_RandomProcesses_ProcessTailProb

open MeasureTheory ProbabilityTheory HighDimProb.RandomProcesses

namespace SlepianProof

abbrev FiniteSlepian : Prop :=
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {ι : Type} [Fintype ι] [Nonempty ι] (X Y : ι → Ω → ℝ)
      (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
      (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
      (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P = ∫ ω, (Y i ω) ^ 2 ∂P)
      (hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤ ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P)
      (τ : ℝ),
      (P.real {ω | Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ≥ τ} ≤
        P.real {ω | Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) ≥ τ}) ∧
      ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂P ≤
        ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) ∂P

theorem slepian_of_finite (hfinite : FiniteSlepian) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {T : Type} [Nonempty T] (X Y : T → Ω → ℝ)
      (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
      (hXmean : ∀ t, ∫ ω, X t ω ∂P = 0) (hYmean : ∀ t, ∫ ω, Y t ω ∂P = 0)
      (hvar : ∀ t, ∫ ω, (X t ω) ^ 2 ∂P = ∫ ω, (Y t ω) ^ 2 ∂P)
      (hinc : ∀ t s, ∫ ω, (X t ω - X s ω) ^ 2 ∂P ≤ ∫ ω, (Y t ω - Y s ω) ^ 2 ∂P),
      (∀ τ : ℝ, processTailProb P X τ ≤ processTailProb P Y τ) ∧
      processESup P X ≤ processESup P Y := by
  intro Ω _ P _ T _ X Y hXG hYG hXmean hYmean hvar hinc
  classical
  have hsub (s : Finset T) (hs : s.Nonempty) : Nonempty s := by
    obtain ⟨t, ht⟩ := hs
    exact ⟨⟨t, ht⟩⟩
  have hmax (s : Finset T) (hs : s.Nonempty) (Z : T → Ω → ℝ) (ω : Ω) :
      Finset.univ.sup' (@Finset.univ_nonempty s _ (hsub s hs)) (fun t : s => Z t ω) =
        s.sup' hs (fun t => Z t ω) := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro t _
      exact Finset.le_sup' (f := fun t => Z t ω) t.property
    · apply Finset.sup'_le
      intro t ht
      exact Finset.le_sup' (f := fun t : s => Z t ω) (Finset.mem_univ ⟨t, ht⟩)
  have hf (s : {s : Finset T // s.Nonempty}) (τ : ℝ) :
      P.real {ω | ∃ t ∈ s.1, X t ω ≥ τ} ≤ P.real {ω | ∃ t ∈ s.1, Y t ω ≥ τ} ∧
      (∫ ω, s.1.sup' s.2 (fun t => X t ω) ∂P) ≤
        ∫ ω, s.1.sup' s.2 (fun t => Y t ω) ∂P := by
    letI := hsub s.1 s.2
    have h := hfinite P (fun t : s.1 => X t) (fun t : s.1 => Y t)
      (hXG.comp_right Subtype.val) (hYG.comp_right Subtype.val)
      (fun t => hXmean t) (fun t => hYmean t) (fun t => hvar t)
      (fun t u => hinc t u) τ
    simp_rw [hmax s.1 s.2] at h
    have hevent (Z : T → Ω → ℝ) :
        {ω | s.1.sup' s.2 (fun t => Z t ω) ≥ τ} =
          {ω | ∃ t ∈ s.1, Z t ω ≥ τ} := by
      ext ω
      exact Finset.le_sup'_iff (H := s.2) (f := fun t => Z t ω)
    simpa only [hevent X, hevent Y] using h
  refine ⟨fun τ => ?_, ?_⟩
  · unfold processTailProb
    apply csSup_le
    · obtain ⟨t⟩ := ‹Nonempty T›
      exact ⟨P.real {ω | ∃ u ∈ ({t} : Finset T), X u ω ≥ τ},
        ⟨⟨{t}, Finset.singleton_nonempty t⟩, rfl⟩⟩
    · rintro p ⟨s, rfl⟩
      apply le_trans (hf s τ).1
      apply le_csSup
      · exact ⟨1, by rintro p ⟨s, rfl⟩; exact measureReal_le_one⟩
      · exact ⟨s, rfl⟩
  · unfold processESup
    apply iSup_mono
    intro s
    exact EReal.coe_le_coe_iff.mpr (hf s 0).2

end SlepianProof

theorem solution :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {T : Type} [Nonempty T] (X Y : T → Ω → ℝ)
      (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
      (hXmean : ∀ t, ∫ ω, X t ω ∂P = 0) (hYmean : ∀ t, ∫ ω, Y t ω ∂P = 0)
      (hvar : ∀ t, ∫ ω, (X t ω) ^ 2 ∂P = ∫ ω, (Y t ω) ^ 2 ∂P)
      (hinc : ∀ t s, ∫ ω, (X t ω - X s ω) ^ 2 ∂P ≤ ∫ ω, (Y t ω - Y s ω) ^ 2 ∂P),
      (∀ τ : ℝ, processTailProb P X τ ≤ processTailProb P Y τ) ∧
      processESup P X ≤ processESup P Y  := by
  exact SlepianProof.slepian_of_finite
    HighDimProb.RandomProcesses.slepian_finite_dim_all_thresholds
