-- Prove2me | solution 1 for GlobalTheory.SchwartzDiv.hasFDerivAt_integral_smul_param
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:17.207049+00:00
-- url     : https://prove2.me/submissions/aea0ef28-734d-4b9e-ade2-050cb5c59c53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory Set Filter Topology Metric
noncomputable section
open GlobalTheory GlobalTheory.SchwartzDiv
variable {H : Type} [MeasurableSpace H] {ν : Measure H} {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X] {c : H → X} {S : Set X} {φ : H → ℂ}
namespace GlobalTheory.SchwartzDiv
theorem _root_.solution (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W}
    (hΘ : ContDiff ℝ ∞ Θ) (t₀ : P) :
    HasFDerivAt (fun t => ∫ y, φ y • Θ (t, c y) ∂ν) (∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t₀ ∂ν) t₀ := by
  have hΘs : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1 :=
    ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst)
      (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl
  have hΘ' := hΘs.continuous
  have hK : IsCompact (closedBall t₀ 1 ×ˢ S) := (isCompact_closedBall t₀ 1).prod hS
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΘ'.continuousOn
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hΘ.continuous.continuousOn
  have hm : ∀ t, AEStronglyMeasurable (fun y => φ y • Θ (t, c y)) ν := fun t =>
    hφ.1.smul ((hΘ.continuous.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F' := fun t y => φ y • fderiv ℝ (fun s => Θ (s, c y)) t) (bound := fun y => ‖φ y‖ * C)
    (ball_mem_nhds t₀ one_pos) (.of_forall hm) ?_ ?_ ?_ (hφ.norm.mul_const C) ?_
  · refine Integrable.mono' (hφ.norm.mul_const C₀) (hm t₀) ?_
    filter_upwards [hcS] with y hy
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC₀ _ ⟨mem_closedBall_self zero_le_one, hy⟩) (norm_nonneg _)
  · exact hφ.1.smul ((hΘ'.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)
  · filter_upwards [hcS] with y hy t ht
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC (t, c y) ⟨ball_subset_closedBall ht, hy⟩) (norm_nonneg _)
  · refine .of_forall fun y t _ => ?_
    have hd : ContDiff ℝ ∞ fun s => Θ (s, c y) := hΘ.comp (contDiff_id.prodMk contDiff_const)
    exact ((hd.differentiable (by simp)) t).hasFDerivAt.const_smul (φ y)
end GlobalTheory.SchwartzDiv
