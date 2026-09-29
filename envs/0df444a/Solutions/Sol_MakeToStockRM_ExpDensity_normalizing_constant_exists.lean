-- Prove2me | solution 1 for MakeToStockRM.ExpDensity.normalizing_constant_exists
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:53:56.043091+00:00
-- url     : https://prove2.me/submissions/effa452d-80bb-4dd5-b912-959afcd405f4

import Mathlib
import Definitions.Def_MakeToStockRM_ExpDensity_expDensity
import Definitions.Def_MakeToStockRM_ExpDensity_region

namespace MakeToStockRM.ExpDensity

theorem aux_ncE_cont (θ σ δ ϱ : ℝ) : Continuous (expDensity θ σ δ ϱ) := by
  unfold expDensity
  fun_prop

theorem aux_ncE_open (η ξ : ℝ → ℝ) (ymin ymax : ℝ) (hη : Continuous η) (hξ : Continuous ξ) :
    IsOpen (region η ξ ymin ymax) := by
  unfold region
  refine IsOpen.inter (isOpen_lt continuous_const continuous_snd) ?_
  refine IsOpen.inter (isOpen_lt continuous_snd continuous_const) ?_
  refine IsOpen.inter (isOpen_lt (hη.comp continuous_snd) continuous_fst) ?_
  exact isOpen_lt continuous_fst (hξ.comp continuous_snd)

theorem aux_ncE_nonempty (η ξ : ℝ → ℝ) (ymin ymax : ℝ) (hy : ymin < ymax)
    (hlt : ∀ y ∈ Set.Icc ymin ymax, η y < ξ y) :
    (region η ξ ymin ymax).Nonempty := by
  set y0 := (ymin + ymax) / 2
  have h1 : ymin < y0 := by simp only [y0]; linarith
  have h2 : y0 < ymax := by simp only [y0]; linarith
  have h3 := hlt y0 ⟨h1.le, h2.le⟩
  refine ⟨((η y0 + ξ y0) / 2, y0), h1, h2, ?_, ?_⟩
  · show η y0 < (η y0 + ξ y0) / 2; linarith
  · show (η y0 + ξ y0) / 2 < ξ y0; linarith

theorem aux_ncE_integrable (θ σ δ ϱ ymin ymax : ℝ) (η ξ : ℝ → ℝ)
    (hη : Continuous η) (hξ : Continuous ξ) :
    MeasureTheory.IntegrableOn (expDensity θ σ δ ϱ) (region η ξ ymin ymax) := by
  obtain ⟨a, ha⟩ := (isCompact_Icc (a := ymin) (b := ymax)).bddBelow_image hη.continuousOn
  obtain ⟨b, hb⟩ := (isCompact_Icc (a := ymin) (b := ymax)).bddAbove_image hξ.continuousOn
  have hsub : region η ξ ymin ymax ⊆ Set.Icc a b ×ˢ Set.Icc ymin ymax := by
    intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    have hz2 : z.2 ∈ Set.Icc ymin ymax := ⟨h1.le, h2.le⟩
    have hA : a ≤ η z.2 := ha ⟨z.2, hz2, rfl⟩
    have hB : ξ z.2 ≤ b := hb ⟨z.2, hz2, rfl⟩
    exact ⟨⟨by linarith, by linarith⟩, hz2⟩
  have hc : IsCompact (Set.Icc a b ×ˢ Set.Icc ymin ymax) := isCompact_Icc.prod isCompact_Icc
  exact ((aux_ncE_cont θ σ δ ϱ).continuousOn.integrableOn_compact hc).mono_set hsub

end MakeToStockRM.ExpDensity

open MakeToStockRM.ExpDensity

theorem solution (θ σ δ ϱ ymin ymax : ℝ) (η ξ : ℝ → ℝ)
    (hy : ymin < ymax) (hη : Continuous η) (hξ : Continuous ξ)
    (hlt : ∀ y ∈ Set.Icc ymin ymax, η y < ξ y) :
    MeasureTheory.IntegrableOn (expDensity θ σ δ ϱ) (region η ξ ymin ymax) ∧
      ∃! K : ℝ, 0 < K ∧ ∫ z in region η ξ ymin ymax, K * expDensity θ σ δ ϱ z = 1 := by
  have hint := aux_ncE_integrable θ σ δ ϱ ymin ymax η ξ hη hξ
  refine ⟨hint, ?_⟩
  set I := ∫ z in region η ξ ymin ymax, expDensity θ σ δ ϱ z with hI
  have hpos : 0 < I := by
    rw [hI, MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae _ hint]
    · have hsupp : Function.support (expDensity θ σ δ ϱ) = Set.univ := by
        ext z
        simp [expDensity, (Real.exp_pos _).ne']
      rw [hsupp, Set.univ_inter]
      exact (aux_ncE_open η ξ ymin ymax hη hξ).measure_pos _
        (aux_ncE_nonempty η ξ ymin ymax hy hlt)
    · exact Filter.Eventually.of_forall (fun z => (Real.exp_pos _).le)
  have hmul : ∀ K : ℝ, ∫ z in region η ξ ymin ymax, K * expDensity θ σ δ ϱ z = K * I := by
    intro K
    rw [hI, MeasureTheory.integral_const_mul]
  refine ⟨1 / I, ⟨by positivity, ?_⟩, ?_⟩
  · rw [hmul]; field_simp
  · rintro K ⟨_, hK⟩
    rw [hmul] at hK
    field_simp
    linarith
