-- Prove2me | solution 1 for HairerSPDE.cameronMartinNorm_ne_top_iff_forall_submodule
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T10:26:39.224993+00:00
-- url     : https://prove2.me/submissions/159f7d40-03f5-4064-bd56-c99a148997de

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin
import Theorems.Thm_HairerSPDE_map_add_null_iff
import Theorems.Thm_HairerSPDE_cameronMartinNorm_eq_top
import Theorems.Thm_HairerSPDE_exists_fullMeasure_submodule_notMem

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

-- The remote wrapper looks up an unqualified top-level `solution`, so the
-- target namespace is opened rather than entered.
open HairerSPDE

theorem solution {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B) :
    cameronMartinNorm μ h ≠ ∞
      ↔ ∀ V : Submodule ℝ B, MeasurableSet (V : Set B) → μ V = 1 → h ∈ V := by
  constructor
  · -- Forward: a finite-norm shift preserves null sets. The translate `V + h` then has
    -- full measure, while `h ∉ V` would make it disjoint from the full-measure `V`.
    intro hh V hVmeas hV1
    by_contra hhV
    set S : Set B := (fun x : B => x + h) '' (V : Set B) with hS
    have hS_meas : MeasurableSet S :=
      MeasurableEmbedding.measurableSet_image' (measurableEmbedding_addRight h) hVmeas
    have hpre : (fun x : B => x + h) ⁻¹' S = (V : Set B) := by
      rw [hS]
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨y, hyV, hyx⟩
        have h1 : y + h = x + h := hyx
        have hxy : y = x := add_right_cancel h1
        rwa [← hxy]
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hcompl_pre : (fun x : B => x + h) ⁻¹' Sᶜ = (V : Set B)ᶜ := by
      rw [Set.preimage_compl, hpre]
    have hSfull : μ S = 1 := by
      have hmapcompl : (μ.map (fun x : B => x + h)) Sᶜ = 0 := by
        rw [Measure.map_apply (measurable_add_const h) hS_meas.compl, hcompl_pre]
        rw [measure_compl hVmeas (measure_ne_top μ _), hV1, measure_univ, tsub_self]
      have hcompl_zero : μ Sᶜ = 0 := (map_add_null_iff μ hμ h hh Sᶜ hS_meas.compl).mp hmapcompl
      have htop : μ Set.univ = μ S + μ Sᶜ := (measure_add_measure_compl hS_meas).symm
      rw [measure_univ] at htop
      rw [hcompl_zero, add_zero] at htop
      exact htop.symm
    have hdisj : Disjoint (V : Set B) S := by
      rw [Set.disjoint_left]
      intro x hxV hxS
      obtain ⟨y, hyV, hyx⟩ := hxS
      refine hhV ?_
      have hsub : x - y ∈ V := (V : Submodule ℝ B).sub_mem hxV hyV
      have hxy : h = x - y := by
        have hy : y + h = x := hyx
        rw [← hy]
        abel
      rwa [hxy]
    have hVcompl_zero : μ (V : Set B)ᶜ = 0 := by
      rw [measure_compl hVmeas (measure_ne_top μ _), hV1, measure_univ, tsub_self]
    have hSzero : μ S = 0 :=
      measure_mono_null (Set.disjoint_right.mp hdisj) hVcompl_zero
    rw [hSfull] at hSzero
    exact one_ne_zero hSzero
  · -- Converse: an infinite-norm point is missed by a constructed full-measure subspace.
    intro hV
    by_contra hfin
    have htop : cameronMartinNorm μ h = ∞ := by
      rcases eq_or_ne (cameronMartinNorm μ h) ∞ with h1 | h1
      · exact h1
      · exact absurd hfin h1
    obtain ⟨L, hL, hLh⟩ := cameronMartinNorm_eq_top μ hμ h htop
    obtain ⟨V, hVmeas, hV1, hhV⟩ :=
      exists_fullMeasure_submodule_notMem μ hμ h L hL hLh
    exact hhV (hV V hVmeas hV1)
