-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_halfline_density_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T01:46:41.676972+00:00
-- url     : https://prove2.me/submissions/08f1e98e-49c7-4dc3-9a83-ab442c41787a

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_tilted_descending_potential
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_tilted_cumulative_laplace
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_tilted_cumulative_continuous
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq
import Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_kernel_nonneg_full_halfline
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open AvramDividend.Classical

theorem p2m87_qpos_halfline_density_nonneg_core :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q x y : ℝ), 0 < q → 0 ≤ x → 0 ≤ y →
      0 ≤ killedHalflineDensity ψ q (W q) x y := by
  intro Ω mΩ P hP D ψ W hψ hW q x y hq hx hy
  have hq0 : 0 ≤ q := le_of_lt hq
  have hWq : IsQScale ψ q (W q) := hW q hq0
  obtain ⟨F, A, hae, hexp⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
  have hnotneg : ¬ (∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => A.X t ω)) := by
    intro ha
    have hd : ∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => D.X t ω) := by
      filter_upwards [hae, ha] with ω h h'
      intro s t hst
      simpa [h s, h t] using h' hst
    exact D.excludesNegativeSubordinator hd
  obtain ⟨hBA, ν, hsupp, hfin0, hatom, hlapA⟩ :=
    source_result81_tilted_descending_potential A hnotneg q hq0
  have hΦA0 : 0 ≤ Phi A.ψ q := hBA.1.2.1.1
  have hrs : RightRootSet A.ψ q = RightRootSet ψ q := by
    ext β; constructor
    · intro h; change 0 ≤ β ∧ A.ψ β = q at h
      exact ⟨h.1, by simpa [hexp β h.1] using h.2⟩
    · intro h; change 0 ≤ β ∧ ψ β = q at h
      exact ⟨h.1, by simpa [hexp β h.1] using h.2⟩
  have hΦ : Phi A.ψ q = Phi ψ q := by simp [Phi, hrs]
  have hBψ : IsScaleTransformDomainBridge ψ q := ⟨hWq.1, fun β hβ => by
    rw [← hΦ, ← hexp β hβ]; exact hBA.2 β hβ⟩
  have hfin : ∀ z, ν (Iic z) < ⊤ := by
    intro z; by_cases hz : 0 ≤ z
    · exact hfin0 z hz
    · calc ν (Iic z) ≤ ν (Iio 0) := measure_mono (by intro w hw; exact lt_of_le_of_lt hw (lt_of_not_ge hz))
           _ = 0 := hsupp
           _ < ⊤ := by simp
  have hlapν : ∀ s, 0 < s →
      (∫⁻ z, ENNReal.ofReal (Real.exp (-s * z)) ∂ν) =
        ENNReal.ofReal (s / (ψ (Phi ψ q + s) - q)) := by
    intro s hs
    have h0 : 0 ≤ Phi A.ψ q + s := add_nonneg hΦA0 (le_of_lt hs)
    have h0' : 0 ≤ Phi ψ q + s := by simpa [← hΦ] using h0
    simpa [hΦ, hexp (Phi ψ q + s) h0'] using hlapA s hs
  have hlag := source_result81_tilted_cumulative_laplace ψ q hBψ ν hsupp hfin hlapν
  have hcontν := source_result81_tilted_cumulative_continuous ν hsupp hfin hatom
  have hWc : ContinuousOn (W q) (Ioi 0) := ContinuousOn.mono hWq.2.2.2.1 (by intro z hz; exact le_of_lt (show (0 : ℝ) < z from hz))
  have hgc : ContinuousOn (fun z => Real.exp (Phi ψ q * z) * (ν (Iic z)).toReal) (Ioi 0) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul (ContinuousOn.mono hcontν (by intro z hz; exact le_of_lt (show (0 : ℝ) < z from hz)))
  have hrep : ∀ z, 0 < z → W q z = Real.exp (Phi ψ q * z) * (ν (Iic z)).toReal := by
    intro z hz
    refine AvramDividend.Classical.continuousOn_Ioi_eq_of_laplace_eq (W q)
      (fun z => Real.exp (Phi ψ q * z) * (ν (Iic z)).toReal)
      (max 0 (Phi ψ q)) hWc hgc (fun z _ => hWq.2.2.1 z) (fun z _ => mul_nonneg (le_of_lt (Real.exp_pos _)) ENNReal.toReal_nonneg) ?_ z hz
    intro θ hθ
    have h0 : 0 ≤ θ := le_of_lt (lt_of_le_of_lt (le_max_left 0 (Phi ψ q)) hθ)
    have hP : Phi ψ q < θ := lt_of_le_of_lt (le_max_right 0 (Phi ψ q)) hθ
    have hw := hWq.2.2.2.2.2 θ h0 hP
    have hg := hlag θ h0 hP
    exact ⟨hw.1, hg.1, hw.2.trans hg.2.symm⟩
  have hΦ0 : 0 ≤ Phi ψ q := hWq.1.2.1.1
  have hcancel : ∀ z, Real.exp (-(Phi ψ q * z)) *
      (Real.exp (Phi ψ q * z) * (ν (Iic z)).toReal) = (ν (Iic z)).toReal := by
    intro z; rw [← mul_assoc, ← Real.exp_add]; have : -(Phi ψ q * z) + Phi ψ q * z = 0 := by ring
    rw [this, Real.exp_zero, one_mul]
  have hmonoIoi : MonotoneOn (fun z => Real.exp (-(Phi ψ q * z)) * W q z) (Ioi 0) := by
    intro u hu v hv huv
    change Real.exp (-(Phi ψ q * u)) * W q u ≤ Real.exp (-(Phi ψ q * v)) * W q v
    rw [hrep u hu, hrep v hv, hcancel u, hcancel v]
    have hc : (ν (Iic u)).toReal ≤ (ν (Iic v)).toReal :=
      ENNReal.toReal_mono (hfin v).ne (measure_mono (by intro w hw; exact le_trans hw huv))
    exact hc
  have htc : ContinuousOn (fun z => Real.exp (-(Phi ψ q * z)) * W q z) (Ici 0) :=
    ((Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).continuousOn).mul
      hWq.2.2.2.1
  have hcl : ClusterPt (0 : ℝ) (𝓟 (Ioi (0 : ℝ))) := by
    rw [← mem_closure_iff_clusterPt]; simp
  have hmono : MonotoneOn (fun z => Real.exp (-(Phi ψ q * z)) * W q z) (Ici 0) := by
    have hi := hmonoIoi.insert_of_continuousWithinAt hcl
      (ContinuousWithinAt.mono (htc.continuousWithinAt (by simp)) (by intro z hz; exact le_of_lt (show (0 : ℝ) < z from hz)))
    have hs : insert (0 : ℝ) (Ioi 0) = Ici 0 := by
      ext z; simp only [mem_insert_iff, mem_Ioi, mem_Ici]
      constructor
      · intro hz; rcases hz with hz | hz
        · subst hz; exact le_rfl
        · exact le_of_lt hz
      · intro hz; rcases eq_or_lt_of_le hz with h | h <;> simp [h]
    simpa [hs] using hi
  simpa [killedHalflineDensity, neg_mul] using
    chat04_killed_resolvent_kernel_nonneg_full_halfline (Phi ψ q) (W q) hmono (fun z _ => hWq.2.2.1 z) hWq.2.1 x y hx hy

theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q x y : ℝ), 0 < q → 0 ≤ x → 0 ≤ y →
      0 ≤ killedHalflineDensity ψ q (W q) x y := by
  intro Ω mΩ P hP D ψ W hψ hW q x y hq hx hy
  exact p2m87_qpos_halfline_density_nonneg_core Ω P D ψ W hψ hW q x y hq hx hy
