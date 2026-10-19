-- Prove2me | solution 1 for OAI.Brennan.univalent_growth_upper
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T20:22:18.212292+00:00
-- url     : https://prove2.me/submissions/6946fef2-4954-4173-ae8c-e1f4d97cc96c

import Mathlib
import Definitions.Def_Brennan
import Definitions.Def_OAIQWBRNK000
import Theorems.Thm_OAI_StrictInverseFirstPower_derivative_distortion

section
-- module Solutions.OAIQW_BrennanCore.Distortion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma schlicht_deriv_bounds {f : ℂ → ℂ} (hf : Schlicht f) {z : ℂ} (hz : z ∈ disk) :
    (1-‖z‖)/(1+‖z‖)^3 ≤ ‖deriv f z‖ ∧
      ‖deriv f z‖ ≤ (1+‖z‖)/(1-‖z‖)^3 :=
  OAI.StrictInverseFirstPower.derivative_distortion hf.1.1 hf.1.2 hf.2.2
    (by simpa [disk, Metric.mem_ball, dist_zero_right] using hz)

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_BrennanCore.TraceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

lemma radial_growth_upper {f : ℂ → ℂ} (hf : Schlicht f) {r : ℝ} (hr : 0 ≤ r)
    (hr1 : r < 1) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖f ((r:ℂ)*ζ)‖ ≤ r/(1-r)^2 := by
  let B : ℝ → ℝ := fun t => (1+t)/(1-t)^3
  let G : ℝ → ℝ := fun t => t/(1-t)^2
  have hn (t : ℝ) (ht : t ∈ Icc 0 r) : ‖(t:ℂ)*ζ‖ = t := by
    simp [hζ,abs_of_nonneg ht.1]
  have hm (t : ℝ) (ht : t ∈ Icc 0 r) : (t:ℂ)*ζ ∈ disk := by
    simp only [disk,Metric.mem_ball,dist_zero_right,hn t ht]
    exact ht.2.trans_lt hr1
  have hd (t : ℝ) (ht : t ∈ Icc 0 r) :
      HasDerivAt (fun t : ℝ => f ((t:ℂ)*ζ)) (deriv f ((t:ℂ)*ζ)*ζ) t := by
    have hdf := ((hf.1.1 _ (hm t ht)).differentiableAt (Metric.isOpen_ball.mem_nhds (hm t ht))).hasDerivAt
    have hl : HasDerivAt (fun t : ℝ => (t:ℂ)*ζ) ζ t := by
      simpa using (Complex.ofRealCLM.hasDerivAt.mul_const ζ :
        HasDerivAt (fun t : ℝ => Complex.ofRealCLM t*ζ) ((Complex.ofRealCLM (1:ℝ))*ζ) t)
    convert HasDerivAt.comp (𝕜 := ℝ) t hdf hl using 1 <;> rfl
  have hB : ContinuousOn B (Icc 0 r) := by
    unfold B
    exact (continuous_const.add continuous_id).continuousOn.div ((continuous_const.sub continuous_id).pow 3).continuousOn
      (fun t ht => pow_ne_zero 3 (by linarith [ht.2]))
  have hG (t : ℝ) (ht : t ∈ Icc 0 r) : HasDerivAt G (B t) t := by
    have hnz : 1-t ≠ 0 := by linarith [ht.2]
    have hd := (hasDerivAt_id t).div (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow 2) (pow_ne_zero 2 hnz)
    convert hd using 1 <;> try rfl
    dsimp [G,B]
    field_simp [hnz]
    ring
  have hb := norm_sub_le_integral_of_norm_deriv_le_of_le hr
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t ⟨ht.1.le,ht.2.le⟩).differentiableAt.differentiableWithinAt)
    (Eventually.of_forall (fun t ht => show ‖deriv (fun t : ℝ => f ((t:ℂ)*ζ)) t‖ ≤ B t from by
      rw [(hd t ⟨ht.1.le,ht.2.le⟩).deriv,norm_mul,hζ,mul_one]
      simpa only [B,hn t ⟨ht.1.le,ht.2.le⟩] using (schlicht_deriv_bounds hf (hm t ⟨ht.1.le,ht.2.le⟩)).2))
    (hB.intervalIntegrable_of_Icc hr)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hG t (by simpa [uIcc_of_le hr] using ht))
    (hB.intervalIntegrable_of_Icc hr)
  rw [hi] at hb
  simpa [G,hf.2.1] using hb

lemma schlicht_growth_upper {f : ℂ → ℂ} (hf : Schlicht f) {z : ℂ} (hz : z ∈ disk) :
    ‖f z‖ ≤ ‖z‖/(1-‖z‖)^2 := by
  by_cases hzero : z = 0
  · simp [hzero,hf.2.1]
  have hn := norm_pos_iff.mpr hzero
  have hζ : ‖z/(‖z‖:ℂ)‖ = 1 := by
    simp [div_self hn.ne']
  have he : (‖z‖:ℂ)*(z/(‖z‖:ℂ)) = z := by
    field_simp [show (‖z‖:ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hn.ne']
  simpa [he] using radial_growth_upper hf hn.le (by simpa [disk] using hz) hζ

theorem univalent_growth_upper_oai {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (Metric.ball 0 1)) (hi : Set.InjOn f (Metric.ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖f z‖ ≤ ‖z‖ / (1 - ‖z‖) ^ 2 :=
  schlicht_growth_upper ⟨⟨hd, hi⟩, h0, h1⟩
    (by simpa [disk, Metric.mem_ball, dist_zero_right] using hz)

end Brennan

end

end OAI
end

theorem solution : type_of% @OAI.Brennan.univalent_growth_upper_oai := @OAI.Brennan.univalent_growth_upper_oai
