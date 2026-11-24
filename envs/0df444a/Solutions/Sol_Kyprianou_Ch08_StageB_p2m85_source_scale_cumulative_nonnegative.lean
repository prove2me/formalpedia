-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m85_source_scale_cumulative_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T18:46:00.042266+00:00
-- url     : https://prove2.me/submissions/f5564fd7-6eb8-41ea-8529-09270bce6732

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_tilted_descending_potential
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_tilted_cumulative_continuous
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_tilted_cumulative_laplace
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    ∃ ν : Measure ℝ, ν (Iio (0 : ℝ)) = 0 ∧
      (∀ r : ℝ, ν (Iic r) < ⊤) ∧
      (∀ s : ℝ, 0 < s → (∫⁻ y, ENNReal.ofReal (Real.exp (-s*y)) ∂ν) =
        ENNReal.ofReal (s / (ψ (Phi ψ q + s) - q))) ∧
      (∀ r : ℝ, Real.exp (-(Phi ψ q) * r) * W q r = (ν (Iic r)).toReal) := by
  obtain ⟨F, X, hpath, hexp⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
  have hnegative : ¬ (∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => X.X t ω)) := by
    intro h
    apply D.excludesNegativeSubordinator
    filter_upwards [hpath, h] with ω heq ha
    intro s t hst
    simpa only [heq] using ha hst
  obtain ⟨hr, ν, hs, hfin, hatom, hlap⟩ :=
    source_result81_tilted_descending_potential X hnegative q hq
  have hf (r : ℝ) : ν (Iic r) < ⊤ :=
    (measure_mono (Iic_subset_Iic.mpr (le_max_left r 0))).trans_lt
      (hfin (max r 0) (le_max_right r 0))
  have hsets : RightRootSet ψ q = RightRootSet X.ψ q := by
    ext β
    change (0 ≤ β ∧ ψ β = q) ↔ (0 ≤ β ∧ X.ψ β = q)
    exact ⟨fun ⟨hn, he⟩ => ⟨hn, (hexp β hn).trans he⟩,
      fun ⟨hn, he⟩ => ⟨hn, (hexp β hn).symm.trans he⟩⟩
  have hPhi : Phi ψ q = Phi X.ψ q := congrArg sSup hsets
  have hroot : IsScaleTransformDomainBridge ψ q := ⟨(hW q hq).1,
    fun β hb => by rw [hPhi, ← hexp β hb]; exact hr.2 β hb⟩
  have hl (s : ℝ) (hs' : 0 < s) :
      (∫⁻ y, ENNReal.ofReal (Real.exp (-s*y)) ∂ν) =
        ENNReal.ofReal (s / (ψ (Phi ψ q + s) - q)) := by
    rw [hPhi, ← hexp _ (add_nonneg hr.1.2.1.1 hs'.le)]
    exact hlap s hs'
  let g (r : ℝ) := Real.exp (Phi ψ q * r) * (ν (Iic r)).toReal
  have hc : ContinuousOn g (Ici 0) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (source_result81_tilted_cumulative_continuous ν hs hf hatom)
  have hw := hW q hq
  have he : ∀ r : ℝ, 0 < r → W q r = g r :=
    AvramDividend.Classical.continuousOn_Ioi_eq_of_laplace_eq (W q) g (Phi ψ q)
      (hw.2.2.2.1.mono Ioi_subset_Ici_self) (hc.mono Ioi_subset_Ici_self)
      (fun r _ => hw.2.2.1 r) (fun r _ => mul_nonneg (Real.exp_nonneg _) ENNReal.toReal_nonneg)
      (fun β hb => by
        have hb0 := hroot.1.2.1.1.trans hb.le
        obtain ⟨h1, e1⟩ := hw.2.2.2.2.2 β hb0 hb
        obtain ⟨h2, e2⟩ := source_result81_tilted_cumulative_laplace ψ q hroot ν hs hf hl β hb0 hb
        exact ⟨h1, h2, e1.trans e2.symm⟩)
  have he0 : W q 0 = g 0 := by
    let l := 𝓝[Ioi (0 : ℝ)] (0 : ℝ)
    haveI : NeBot l := nhdsWithin_Ioi_neBot (le_refl (0 : ℝ))
    have h1 : Tendsto (W q) l (𝓝 (W q 0)) :=
      (hw.2.2.2.1 0 (Set.mem_Ici.mpr (le_refl (0 : ℝ)))).mono Ioi_subset_Ici_self
    have h2 : Tendsto g l (𝓝 (g 0)) :=
      (hc 0 (Set.mem_Ici.mpr (le_refl (0 : ℝ)))).mono Ioi_subset_Ici_self
    have hEq : W q =ᶠ[l] g := Filter.Eventually.mono self_mem_nhdsWithin fun r hr => he r hr
    exact tendsto_nhds_unique (h1.congr' hEq) h2
  refine ⟨ν, hs, hf, hl, fun r => ?_⟩
  by_cases h : r < 0
  · rw [hw.2.1 r h, mul_zero]
    have hz : ν (Iic r) = 0 := measure_mono_null (fun y hy => hy.trans_lt h) hs
    simp [hz]
  · have hEq : W q r = g r := (le_of_not_gt h).eq_or_lt.elim
      (fun hr => by simpa [← hr] using he0) (he r)
    rw [hEq]
    simp only [g, ← mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, one_mul]
