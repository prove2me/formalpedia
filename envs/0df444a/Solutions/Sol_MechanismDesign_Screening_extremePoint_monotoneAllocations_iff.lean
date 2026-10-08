-- Prove2me | solution 1 for MechanismDesign.Screening.extremePoint_monotoneAllocations_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:09:59.902517+00:00
-- url     : https://prove2.me/submissions/26e779dd-27f9-40cf-8968-2c3263ac422b

import Mathlib
import Definitions.Def_MechanismDesign_Screening_ExtremePoints

open MeasureTheory

namespace MechanismDesign.Screening

lemma psi_plus_mono : Monotone (fun s : ℝ => s + min s (1 - s) / 2) := by
  intro a b hab
  simp only [min_def]; split_ifs <;> linarith

lemma psi_minus_mono : Monotone (fun s : ℝ => s - min s (1 - s) / 2) := by
  intro a b hab
  simp only [min_def]; split_ifs <;> linarith

instance typeMeasure_finite (θlo θhi : ℝ) : IsFiniteMeasure (typeMeasure θlo θhi) :=
  isFiniteMeasure_restrict.2 (by simp)

theorem extremePoint_monotoneAllocations_iff_core {θlo θhi : ℝ}
    (g : L1Space θlo θhi) (hg : g ∈ monotoneAllocations θlo θhi) :
    IsExtremePoint (monotoneAllocations θlo θhi) g ↔
      ∀ᵐ x ∂(typeMeasure θlo θhi), (g : ℝ → ℝ) x = 0 ∨ (g : ℝ → ℝ) x = 1 := by
  set μ := typeMeasure θlo θhi
  have hmemIcc : ∀ᵐ x ∂μ, x ∈ Set.Icc θlo θhi := ae_restrict_mem measurableSet_Icc
  -- members of M take values in [0,1] a.e.
  have hval : ∀ h ∈ monotoneAllocations θlo θhi, ∀ᵐ x ∂μ, (h : ℝ → ℝ) x ∈ Set.Icc (0:ℝ) 1 := by
    rintro h ⟨q, _, hq01, hq⟩
    filter_upwards [hq, hmemIcc] with x hx hxI
    rw [hx]; exact hq01 x hxI
  constructor
  · intro hext
    by_contra hnot
    obtain ⟨q, hqm, hq01, hgq⟩ := hg
    set φ : ℝ → ℝ := fun s => min s (1 - s) / 2 with hφ
    have hφc : Continuous φ := by fun_prop
    have hqae : AEStronglyMeasurable q μ := (Lp.aestronglyMeasurable g).congr hgq
    have hφq : AEStronglyMeasurable (fun x => φ (q x)) μ := hφc.comp_aestronglyMeasurable hqae
    have hmem : MemLp (fun x => φ (q x)) 1 μ := by
      refine MemLp.of_bound hφq 1 ?_
      filter_upwards [hmemIcc] with x hx
      have := hq01 x hx
      simp only [hφ, Real.norm_eq_abs]
      rw [abs_le]; constructor
      · have : -1 ≤ min (q x) (1 - q x) := le_min (by linarith [this.1]) (by linarith [this.2])
        linarith
      · have : min (q x) (1 - q x) ≤ q x := min_le_left _ _
        linarith [(hq01 x hx).2]
    set y : L1Space θlo θhi := hmem.toLp _ with hy
    have hyae : (y : ℝ → ℝ) =ᵐ[μ] fun x => φ (q x) := MemLp.coeFn_toLp hmem
    have hyne : y ≠ 0 := by
      intro h0
      apply hnot
      have h0' : (y : ℝ → ℝ) =ᵐ[μ] 0 := Lp.eq_zero_iff_ae_eq_zero.1 h0
      filter_upwards [h0', hyae, hgq, hmemIcc] with x h1 h2 h3 hx
      rw [h2] at h1
      simp only [Pi.zero_apply, hφ] at h1
      rw [h3]
      have := hq01 x hx
      rcases min_choice (q x) (1 - q x) with h | h
      · left; rw [h] at h1; linarith
      · right; rw [h] at h1; linarith
    rcases hext.2 y hyne with h | h
    · apply h
      refine ⟨fun x => q x + φ (q x), psi_plus_mono.comp_monotoneOn hqm, ?_, ?_⟩
      · intro x hx
        have := hq01 x hx
        simp only [hφ, min_def]
        constructor <;> split_ifs <;> linarith [this.1, this.2]
      · filter_upwards [Lp.coeFn_add g y, hgq, hyae] with x h1 h2 h3
        rw [h1, Pi.add_apply, h2, h3]
    · apply h
      refine ⟨fun x => q x - φ (q x), psi_minus_mono.comp_monotoneOn hqm, ?_, ?_⟩
      · intro x hx
        have := hq01 x hx
        simp only [hφ, min_def]
        constructor <;> split_ifs <;> linarith [this.1, this.2]
      · filter_upwards [Lp.coeFn_sub g y, hgq, hyae] with x h1 h2 h3
        rw [h1, Pi.sub_apply, h2, h3]
  · intro h01
    refine ⟨hg, fun y hy => ?_⟩
    by_contra hboth
    push_neg at hboth
    obtain ⟨hp, hm⟩ := hboth
    apply hy
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hval _ hp, hval _ hm, Lp.coeFn_add g y, Lp.coeFn_sub g y, h01]
      with x h1 h2 h3 h4 h5
    rw [h3, Pi.add_apply] at h1
    rw [h4, Pi.sub_apply] at h2
    simp only [Pi.zero_apply]
    rcases h5 with h | h <;> rw [h] at h1 h2 <;>
      linarith [h1.1, h1.2, h2.1, h2.2]

end MechanismDesign.Screening

open MechanismDesign.Screening


theorem solution {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi)
    (g : L1Space θlo θhi) (hg : g ∈ monotoneAllocations θlo θhi) :
    IsExtremePoint (monotoneAllocations θlo θhi) g ↔
      ∀ᵐ x ∂(typeMeasure θlo θhi), (g : ℝ → ℝ) x = 0 ∨ (g : ℝ → ℝ) x = 1 := by
  exact extremePoint_monotoneAllocations_iff_core g hg
