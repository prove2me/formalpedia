-- Prove2me | solution 1 for NahmiasPerishable.Inventory.m11
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T12:12:05.828622+00:00
-- url     : https://prove2.me/submissions/259fec54-bbe6-4878-8c13-aaa941da20cb

import Definitions.Def_NahmiasPerishable_Inventory_Stationary

open MeasureTheory Set
open scoped ENNReal
open NahmiasPerishable.Inventory

private noncomputable def u01Law : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

private instance : IsProbabilityMeasure u01Law := by
  constructor
  dsimp [u01Law]
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

private noncomputable def u01Demand : Demand where
  law := u01Law
  prob := inferInstance
  nonneg := by
    dsimp [u01Law]
    rw [ae_restrict_iff' measurableSet_Icc]
    exact ae_of_all _ (fun d hd => hd.1)
  density := (Icc (0 : ℝ) 1).indicator 1
  measurable_density := measurable_one.indicator measurableSet_Icc
  law_density := (withDensity_indicator_one measurableSet_Icc).symm

private lemma u01_apply_Icc : u01Demand.law (Icc (0 : ℝ) 1) = 1 := by
  change (volume.restrict (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) = 1
  rw [Measure.restrict_apply measurableSet_Icc, inter_self, Real.volume_Icc]
  norm_num

private lemma cdf_u01_one : cdf u01Demand.law 1 = 1 := by
  unfold cdf
  change ((volume.restrict (Icc (0 : ℝ) 1)) (Iic 1)).toReal = 1
  rw [Measure.restrict_apply measurableSet_Iic,
    inter_eq_self_of_subset_right (fun x hx => hx.2), Real.volume_Icc]
  norm_num

private lemma shockInvariant_dirac_one :
    ShockInvariant u01Demand.law (fun a d => max d (2 - a)) (Measure.dirac (1 : ℝ)) := by
  refine ⟨inferInstance, ?_⟩
  let μ := (Measure.dirac (1 : ℝ)).prod u01Demand.law
  let A : Set (ℝ × ℝ) := ({1} : Set ℝ) ×ˢ Icc (0 : ℝ) 1
  have hAmeas : MeasurableSet A :=
    (measurableSet_singleton (1 : ℝ)).prod measurableSet_Icc
  have hμA : μ A = 1 := by
    dsimp [μ, A]
    rw [Measure.prod_prod, Measure.dirac_apply' _ (measurableSet_singleton (1 : ℝ)),
      Set.indicator_of_mem (Set.mem_singleton (1 : ℝ)), Pi.one_apply, u01_apply_Icc, mul_one]
  have haeA : ∀ᵐ xd ∂μ, xd ∈ A := by
    rw [ae_iff]
    change μ Aᶜ = 0
    rw [prob_compl_eq_zero_iff hAmeas]
    exact hμA
  have hae_eq : (fun xd : ℝ × ℝ => max xd.2 (2 - xd.1)) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
    filter_upwards [haeA] with xd hxd
    rcases hxd with ⟨h1, h2⟩
    have hx1 : xd.1 = 1 := h1
    rw [hx1]
    have h21 : (2 : ℝ) - 1 = 1 := by norm_num
    rw [h21]
    exact max_eq_right h2.2
  rw [Measure.map_congr hae_eq, Measure.map_const, measure_univ, one_smul]

set_option linter.unusedVariables false in
theorem solution : ¬ (∀ (D : Demand) (S : ℝ) (hS : 0 ≤ S) (ν : Measure ℝ)
    (hν : ShockInvariant D.law (fun a d => max d (S-a)) ν)
    (hnonneg : ν (Ici 0) = 1),
    ∀ y : ℝ, 0 ≤ y →
      1-cdf D.law y*cdf D.law (S-y) ≠ 0 ∧
      cdf ν y = cdf D.law y*(1-cdf D.law (S-y))/(1-cdf D.law y*cdf D.law (S-y))) := by
  intro h
  have hnonneg : (Measure.dirac (1 : ℝ)) (Ici (0 : ℝ)) = 1 := by
    rw [Measure.dirac_apply' _ measurableSet_Ici,
      Set.indicator_of_mem (by norm_num : (1 : ℝ) ∈ Ici (0 : ℝ)), Pi.one_apply]
  have h1 := (h u01Demand 2 (by norm_num) (Measure.dirac (1 : ℝ))
    shockInvariant_dirac_one hnonneg 1 (by norm_num)).1
  have hsub : (2 : ℝ) - 1 = 1 := by norm_num
  rw [hsub, cdf_u01_one] at h1
  norm_num at h1
