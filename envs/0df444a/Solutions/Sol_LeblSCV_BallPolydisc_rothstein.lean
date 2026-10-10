-- Prove2me | solution 1 for LeblSCV.BallPolydisc.rothstein
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-10T02:16:53.066601+00:00
-- url     : https://prove2.me/submissions/11267689-0684-4954-b943-b0e58a4f9dad

/-
SPDX-License-Identifier: Apache-2.0
Complete proof of Rothstein: no proper holomorphic bidisc-to-ball map.
All custom proof bodies are included; only canonical definitions and Mathlib
are imported. The quantitative Cauchy variance and properness argument is reconstructed.
-/
import Definitions.Def_LeblSCV_BallPolydisc_IsProperMapOn
import Definitions.Def_LeblSCV_BallPolydisc_unitPolydisc
import Definitions.Def_LeblSCV_BallPolydisc_unitBall
import Mathlib

/- Complete module: ProperCollar -/
section

open Set Metric

namespace LeblSCV.BallPolydisc.Proof

noncomputable def energy (z : Fin 2 → ℂ) : ℝ := ∑ j, ‖z j‖ ^ 2

lemma energy_nonneg (z : Fin 2 → ℂ) : 0 ≤ energy z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma continuous_energy : Continuous energy := by
  unfold energy
  fun_prop

lemma compact_energy_sublevel {c : ℝ} (hc : c < 1) :
    IsCompact {z : Fin 2 → ℂ | energy z ≤ c} := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le continuous_energy continuous_const) ?_
  refine (isBounded_iff_forall_norm_le).2 ⟨1, fun z hz => ?_⟩
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
  intro j
  have hj : ‖z j‖ ^ 2 ≤ energy z :=
    Finset.single_le_sum (fun i _ => sq_nonneg ‖z i‖) (Finset.mem_univ j)
  have hn := norm_nonneg (z j)
  change energy z ≤ c at hz
  nlinarith

lemma proper_collar {f : (Fin 2 → ℂ) → (Fin 2 → ℂ)}
    (hp : IsProperMapOn f (unitPolydisc 2) (unitBall 2))
    {c : ℝ} (hc : c < 1) (j : Fin 2) :
    ∃ R : ℝ, 0 ≤ R ∧ R < 1 ∧
      ∀ z ∈ unitPolydisc 2, R < ‖z j‖ → c < energy (f z) := by
  let K := {v : Fin 2 → ℂ | energy v ≤ c}
  have hK : K ⊆ unitBall 2 := fun v hv => lt_of_le_of_lt hv hc
  have hcomp := hp.2.2 K hK (compact_energy_sublevel hc)
  let P := unitPolydisc 2 ∩ f ⁻¹' K
  by_cases hne : P.Nonempty
  · obtain ⟨z, hz, hmax⟩ := hcomp.exists_isMaxOn hne
      ((continuous_apply j).norm.continuousOn)
    refine ⟨‖z j‖, norm_nonneg _, hz.1 j, ?_⟩
    intro w hw hR
    by_contra hn
    have hwP : w ∈ P := ⟨hw, le_of_not_gt hn⟩
    exact (not_le_of_gt hR) (hmax hwP)
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    intro z hz _
    by_contra hn
    exact hne ⟨z, hz, le_of_not_gt hn⟩

end LeblSCV.BallPolydisc.Proof

end

/- Complete module: BidiscSlices -/
section

open Set Metric

namespace LeblSCV.BallPolydisc.Proof

noncomputable def pair (z w : ℂ) : Fin 2 → ℂ := ![z, w]

@[simp] lemma pair_zero (z w : ℂ) : pair z w 0 = z := rfl
@[simp] lemma pair_one (z w : ℂ) : pair z w 1 = w := rfl

lemma pair_mem {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    pair z w ∈ unitPolydisc 2 := by
  intro j
  fin_cases j <;> simp_all

lemma pair_left_differentiable (w : ℂ) : Differentiable ℂ (fun z => pair z w) := by
  apply differentiable_pi.mpr
  intro j
  fin_cases j
  · exact differentiable_id
  · exact differentiable_const w

lemma pair_right_differentiable (z : ℂ) : Differentiable ℂ (pair z) := by
  apply differentiable_pi.mpr
  intro j
  fin_cases j
  · exact differentiable_const z
  · exact differentiable_id

lemma slice_left_differentiable {f : (Fin 2 → ℂ) → (Fin 2 → ℂ)}
    (hf : DifferentiableOn ℂ f (unitPolydisc 2)) {w : ℂ} (hw : ‖w‖ < 1) :
    DifferentiableOn ℂ (fun z => f (pair z w)) (ball 0 1) := by
  exact hf.comp (pair_left_differentiable w).differentiableOn
    (fun z hz => pair_mem (by simpa using hz) hw)

lemma slice_right_differentiable {f : (Fin 2 → ℂ) → (Fin 2 → ℂ)}
    (hf : DifferentiableOn ℂ f (unitPolydisc 2)) {z : ℂ} (hz : ‖z‖ < 1)
    (j : Fin 2) :
    DifferentiableOn ℂ (fun w => f (pair z w) j) (ball 0 1) := by
  have h : DifferentiableOn ℂ (fun w => f (pair z w)) (ball 0 1) := hf.comp (pair_right_differentiable z).differentiableOn
    (fun w hw => pair_mem hz (by simpa using hw))
  exact (differentiable_apply j).differentiableOn.comp h (fun _ _ => Set.mem_univ _)

end LeblSCV.BallPolydisc.Proof

end

/- Complete module: DiskBoundaryVanishing -/
section

open Set Metric

namespace LeblSCV.BallPolydisc.Proof

lemma disk_boundary_vanishing {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 1))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R < 1 ∧
      ∀ w : ℂ, R < ‖w‖ → ‖w‖ < 1 → ‖h w‖ ≤ ε) :
    ∀ w ∈ ball (0 : ℂ) 1, h w = 0 := by
  intro w hw
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨R, hR, hsmallR⟩ := hsmall ε hε
  have hw1 : ‖w‖ < 1 := by simpa using hw
  obtain ⟨r, hrlo, hrhi⟩ := exists_between (max_lt hR hw1)
  have hrw : ‖w‖ < r := (le_max_right R ‖w‖).trans_lt hrlo
  have hrR : R < r := (le_max_left R ‖w‖).trans_lt hrlo
  have hr : 0 < r := (norm_nonneg w).trans_lt hrw
  have hd : DiffContOnCl ℂ h (ball 0 r) := hh.diffContOnCl_ball (by
    intro z hz
    have hz' : ‖z‖ ≤ r := by simpa using hz
    simpa using hz'.trans_lt hrhi)
  have hb : ∀ z ∈ frontier (ball (0 : ℂ) r), ‖h z‖ ≤ ε := by
    intro z hz
    rw [frontier_ball 0 (ne_of_gt hr)] at hz
    have hz' : ‖z‖ = r := by simpa using hz
    exact hsmallR z (hz' ▸ hrR) (hz' ▸ hrhi)
  have hout := Complex.norm_le_of_forall_mem_frontier_norm_le
    isBounded_ball hd hb (subset_closure (by simpa using hrw))
  simpa using hout

end LeblSCV.BallPolydisc.Proof

end

/- Complete module: OscillationCollapse -/
section

open Set Metric

namespace LeblSCV.BallPolydisc.Proof

lemma proper_slice_constant {f : (Fin 2 → ℂ) → (Fin 2 → ℂ)}
    (hf : DifferentiableOn ℂ f (unitPolydisc 2))
    (hp : IsProperMapOn f (unitPolydisc 2) (unitBall 2))
    (hestimate : ∀ z : ℂ, ‖z‖ < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ w : ℂ, ‖w‖ < 1 → ∀ j : Fin 2,
        ‖f (pair z w) j - f (pair 0 w) j‖ ^ 2 ≤
          C * (1 - energy (f (pair 0 w)))) :
    ∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 → f (pair z w) = f (pair 0 w) := by
  intro z w hz hw
  obtain ⟨C, hC, hest⟩ := hestimate z hz
  funext j
  apply sub_eq_zero.mp
  apply disk_boundary_vanishing
    ((slice_right_differentiable hf hz j).sub
      (slice_right_differentiable hf (by simp : ‖(0 : ℂ)‖ < 1) j)) _ w
    (by simpa using hw)
  intro ε hε
  have hpos : 0 < ε ^ 2 / C := div_pos (sq_pos_of_pos hε) hC
  obtain ⟨R, _, hR, hcollar⟩ := proper_collar hp (by linarith : 1 - ε ^ 2 / C < 1) 1
  refine ⟨R, hR, ?_⟩
  intro v hRv hv
  have hen := hcollar (pair 0 v) (pair_mem (by simp) hv) (by simpa using hRv)
  have he := hest v hv j
  have hmul : C * (ε ^ 2 / C) = ε ^ 2 := by field_simp
  have hn := norm_nonneg (f (pair z v) j - f (pair 0 v) j)
  have hh : C * (1 - energy (f (pair 0 v))) < ε ^ 2 := by nlinarith
  change ‖f (pair z v) j - f (pair 0 v) j‖ ≤ ε
  nlinarith

lemma not_proper_of_slice_constant {f : (Fin 2 → ℂ) → (Fin 2 → ℂ)}
    (hp : IsProperMapOn f (unitPolydisc 2) (unitBall 2))
    (hc : ∀ z : ℂ, ‖z‖ < 1 → f (pair z 0) = f (pair 0 0)) : False := by
  have hzero : pair 0 0 ∈ unitPolydisc 2 := pair_mem (by simp) (by simp)
  have he : energy (f (pair 0 0)) < 1 := hp.1 hzero
  obtain ⟨R, hR0, hR1, hcollar⟩ := proper_collar hp he 0
  obtain ⟨t, hRt, ht1⟩ := exists_between hR1
  have ht0 : 0 ≤ t := hR0.trans (le_of_lt hRt)
  have htn : ‖(t : ℂ)‖ = t := by simp [abs_of_nonneg ht0]
  have hmem := pair_mem (z := (t : ℂ)) (w := 0) (by simpa only [htn] using ht1) (by simp)
  have hlt := hcollar (pair (t : ℂ) 0) hmem (by simpa only [pair_zero, htn] using hRt)
  rw [hc (t : ℂ) (by simpa only [htn] using ht1)] at hlt
  exact lt_irrefl _ hlt

end LeblSCV.BallPolydisc.Proof

end

/- Complete module: CircleVariance -/
section

open MeasureTheory Metric Real

namespace LeblSCV.BallPolydisc.Proof

lemma circle_variance (f : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hf : ContinuousOn f (sphere c |R|)) (a : ℂ) :
    circleAverage (fun z => ‖f z - a‖ ^ 2) c R =
      circleAverage (fun z => ‖f z‖ ^ 2) c R -
        2 * inner ℝ a (circleAverage f c R) + ‖a‖ ^ 2 := by
  have hn : CircleIntegrable (fun z => ‖f z‖ ^ 2) c R := (hf.norm.pow 2).circleIntegrable'
  have hi : ContinuousOn (fun z => inner ℝ a (f z)) (sphere c |R|) :=
    (innerSL ℝ a).continuous.comp_continuousOn hf
  have him : circleAverage (fun z => inner ℝ a (f z)) c R =
      inner ℝ a (circleAverage f c R) :=
    (innerSL ℝ a).circleAverage_comp_comm hf.circleIntegrable'
  conv_lhs => congr; ext z; rw [norm_sub_sq_real, real_inner_comm]
  have htwo : CircleIntegrable (fun z => 2 * inner ℝ a (f z)) c R :=
    (continuousOn_const.mul hi).circleIntegrable'
  have hsub : CircleIntegrable (fun z => ‖f z‖ ^ 2 - 2 * inner ℝ a (f z)) c R := hn.sub htwo
  rw [circleAverage_fun_add hsub (circleIntegrable_const (‖a‖ ^ 2) c R),
    circleAverage_fun_sub hn htwo, circleAverage_const]
  have hmul : circleAverage (fun z => 2 * inner ℝ a (f z)) c R =
      2 * circleAverage (fun z => inner ℝ a (f z)) c R := by
    simpa only [smul_eq_mul] using
      (circleAverage_fun_smul (a := (2 : ℝ)) (f := fun z => inner ℝ a (f z)) (c := c) (R := R))
  rw [hmul, him]

lemma circle_average_sq_le (f : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hf : ContinuousOn f (sphere c |R|)) :
    ‖circleAverage f c R‖ ^ 2 ≤ circleAverage (fun z => ‖f z‖ ^ 2) c R := by
  have hn := circleAverage_nonneg_of_nonneg (c := c) (R := R)
    (fun z _ => sq_nonneg ‖f z - circleAverage f c R‖)
  rw [circle_variance f c R hf, real_inner_self_eq_norm_sq] at hn
  linarith

lemma circle_weighted_sq_le (f k : ℂ → ℂ) (c : ℂ) (R M : ℝ)
    (hf : ContinuousOn f (sphere c |R|)) (hk : ContinuousOn k (sphere c |R|))
    (hb : ∀ z ∈ sphere c |R|, ‖k z‖ ≤ M) :
    ‖circleAverage (fun z => k z * f z) c R‖ ^ 2 ≤
      M ^ 2 * circleAverage (fun z => ‖f z‖ ^ 2) c R := by
  apply (circle_average_sq_le _ c R (hk.mul hf)).trans
  have h := circleAverage_mono ((hk.mul hf).norm.pow 2).circleIntegrable'
    (continuousOn_const.mul (hf.norm.pow 2)).circleIntegrable'
    (fun z hz => show ‖k z * f z‖ ^ 2 ≤ M ^ 2 * ‖f z‖ ^ 2 by
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb z hz) 2)
        (sq_nonneg _))
  have he : circleAverage (fun z => M ^ 2 * ‖f z‖ ^ 2) c R =
      M ^ 2 * circleAverage (fun z => ‖f z‖ ^ 2) c R := by
    simpa only [smul_eq_mul] using
      (circleAverage_fun_smul (a := M ^ 2) (f := fun z => ‖f z‖ ^ 2) (c := c) (R := R))
  change circleAverage (fun z => ‖k z * f z‖ ^ 2) c R ≤
    circleAverage (fun z => M ^ 2 * ‖f z‖ ^ 2) c R at h
  rwa [he] at h

end LeblSCV.BallPolydisc.Proof

end

/- Complete module: CauchyOscillation -/
section

open MeasureTheory Metric Real Set

namespace LeblSCV.BallPolydisc.Proof

lemma disk_diffContOnCl (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (R : ℝ) (hR : 0 < R) (hR1 : R < 1) : DiffContOnCl ℂ f (ball 0 |R|) := by
  apply DifferentiableOn.diffContOnCl
  apply hf.mono
  intro z hz
  have hz' := closure_ball_subset_closedBall hz
  rw [mem_closedBall_zero_iff, abs_of_pos hR] at hz'
  exact mem_ball_zero_iff.mpr (hz'.trans_lt hR1)

lemma cauchy_kernel_bound (R : ℝ) (hR : 0 < R) (z : ℂ) (hz : ‖z‖ < R) :
    ContinuousOn (fun u : ℂ => u / (u - z)) (sphere 0 |R|) ∧
      ∀ u ∈ sphere 0 |R|, ‖u / (u - z)‖ ≤ R / (R - ‖z‖) := by
  have hu (u : ℂ) (hu : u ∈ sphere 0 |R|) : ‖u‖ = R := by
    simpa [mem_sphere_zero_iff_norm, abs_of_pos hR] using hu
  have hne (u : ℂ) (hu' : u ∈ sphere 0 |R|) : u - z ≠ 0 := by
    intro h
    have := hu u hu'
    rw [sub_eq_zero.mp h] at this
    linarith
  refine ⟨continuousOn_id.div (continuousOn_id.sub continuousOn_const) hne, ?_⟩
  intro u hu'
  rw [norm_div, hu u hu']
  apply div_le_div_of_nonneg_left hR.le (sub_pos.mpr hz)
  have := norm_sub_norm_le u z
  rw [hu u hu'] at this
  exact this

lemma scalar_disk_oscillation (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (R : ℝ) (hR : 0 < R) (hR1 : R < 1) (z : ℂ) (hz : ‖z‖ < R) :
    ‖f z - f 0‖ ^ 2 ≤ (R / (R - ‖z‖)) ^ 2 *
      (circleAverage (fun u => ‖f u‖ ^ 2) 0 R - ‖f 0‖ ^ 2) := by
  have hd := disk_diffContOnCl f hf R hR hR1
  have hc : ContinuousOn f (sphere 0 |R|) := hd.continuousOn_ball.mono sphere_subset_closedBall
  have hcs : ContinuousOn (fun u => f u - f 0) (sphere 0 |R|) := hc.sub continuousOn_const
  have hds : DiffContOnCl ℂ (fun u => f u - f 0) (ball 0 |R|) := hd.sub diffContOnCl_const
  have hm : circleAverage f 0 R = f 0 := hd.circleAverage
  have he := hds.circleAverage_smul_div
    (show z ∈ ball 0 |R| by simpa [mem_ball_zero_iff, abs_of_pos hR] using hz)
  simp only [sub_zero, smul_eq_mul] at he
  obtain ⟨hk, hb⟩ := cauchy_kernel_bound R hR z hz
  have h := circle_weighted_sq_le (fun u => f u - f 0) (fun u => u / (u - z))
    0 R (R / (R - ‖z‖)) hcs hk hb
  rw [he, circle_variance f 0 R hc (f 0), hm, real_inner_self_eq_norm_sq] at h
  nlinarith

end LeblSCV.BallPolydisc.Proof

end

/- Complete module: DiskOscillation -/
section

open MeasureTheory Metric Real Set

namespace LeblSCV.BallPolydisc.Proof

lemma circle_coordinate_deficit (g : ℂ → (Fin 2 → ℂ))
    (hg : DifferentiableOn ℂ g (ball 0 1))
    (hb : ∀ u ∈ ball (0 : ℂ) 1, ∑ j : Fin 2, ‖g u j‖ ^ 2 < 1)
    (R : ℝ) (hR : 0 < R) (hR1 : R < 1) (j : Fin 2) :
    circleAverage (fun u => ‖g u j‖ ^ 2) 0 R - ‖g 0 j‖ ^ 2 ≤
      1 - ∑ i : Fin 2, ‖g 0 i‖ ^ 2 := by
  have hd (i : Fin 2) := disk_diffContOnCl (fun u => g u i)
    (differentiableOn_pi.mp hg i) R hR hR1
  have hc (i : Fin 2) : ContinuousOn (fun u => g u i) (sphere 0 |R|) :=
    (hd i).continuousOn_ball.mono sphere_subset_closedBall
  have hm (i : Fin 2) : circleAverage (fun u => g u i) 0 R = g 0 i := (hd i).circleAverage
  have hn (i : Fin 2) : 0 ≤ circleAverage (fun u => ‖g u i‖ ^ 2) 0 R - ‖g 0 i‖ ^ 2 := by
    have h := circle_average_sq_le (fun u => g u i) 0 R (hc i)
    rw [hm] at h
    linarith
  have hs : circleAverage (fun u => ∑ i : Fin 2, ‖g u i‖ ^ 2) 0 R =
      ∑ i : Fin 2, circleAverage (fun u => ‖g u i‖ ^ 2) 0 R := by
    exact circleAverage_fun_sum (s := Finset.univ) (f := fun i u => ‖g u i‖ ^ 2)
      (fun i _ => ((hc i).norm.pow 2).circleIntegrable')
  have hsum : CircleIntegrable (fun u => ∑ i : Fin 2, ‖g u i‖ ^ 2) 0 R := by
    apply ContinuousOn.circleIntegrable'
    exact continuousOn_finsetSum _ (fun i _ => (hc i).norm.pow 2)
  have hbound := circleAverage_mono_on_of_le_circle hsum (fun u hu => by
    apply le_of_lt (hb u ?_)
    have hu' : ‖u‖ = R := by simpa [mem_sphere_zero_iff_norm, abs_of_pos hR] using hu
    simpa [mem_ball_zero_iff, hu'] using hR1)
  rw [hs] at hbound
  have hj := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 2))) => hn i)
    (Finset.mem_univ j)
  rw [Finset.sum_sub_distrib] at hj
  linarith

lemma disk_oscillation_bound (z : ℂ) (hz : ‖z‖ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℂ → (Fin 2 → ℂ),
      DifferentiableOn ℂ g (ball 0 1) →
      (∀ u ∈ ball (0 : ℂ) 1, ∑ j : Fin 2, ‖g u j‖ ^ 2 < 1) →
      ∀ j : Fin 2, ‖g z j - g 0 j‖ ^ 2 ≤ C * (1 - ∑ i : Fin 2, ‖g 0 i‖ ^ 2) := by
  let R : ℝ := (1 + ‖z‖) / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hzR : ‖z‖ < R := by dsimp [R]; linarith
  refine ⟨(R / (R - ‖z‖)) ^ 2, by positivity, ?_⟩
  intro g hg hb j
  apply (scalar_disk_oscillation (fun u => g u j) (differentiableOn_pi.mp hg j)
    R hR hR1 z hzR).trans
  exact mul_le_mul_of_nonneg_left (circle_coordinate_deficit g hg hb R hR hR1 j) (sq_nonneg _)

end LeblSCV.BallPolydisc.Proof

end

/- Complete module: RothsteinRoot -/
section

namespace LeblSCV.BallPolydisc

/-- Theorem 1.4.4 (Rothstein 1935; Lebl, p. 33). There exists no proper holomorphic mapping of
the unit bidisc `𝔻² ⊆ ℂ²` to the (Euclidean) unit ball `𝔹₂ ⊆ ℂ²`. -/
theorem rothstein :
    ¬ ∃ f : (Fin 2 → ℂ) → (Fin 2 → ℂ),
        DifferentiableOn ℂ f (unitPolydisc 2) ∧
          IsProperMapOn f (unitPolydisc 2) (unitBall 2) := by
  rintro ⟨f, hf, hp⟩
  apply Proof.not_proper_of_slice_constant hp
  have hest : ∀ z : ℂ, ‖z‖ < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ w : ℂ, ‖w‖ < 1 → ∀ j : Fin 2,
        ‖f (Proof.pair z w) j - f (Proof.pair 0 w) j‖ ^ 2 ≤
          C * (1 - Proof.energy (f (Proof.pair 0 w))) := by
    intro z hz
    obtain ⟨C, hC, hb⟩ := Proof.disk_oscillation_bound z hz
    refine ⟨C, hC, ?_⟩
    intro w hw j
    apply hb (fun u => f (Proof.pair u w)) (Proof.slice_left_differentiable hf hw)
    intro u hu
    apply hp.1 (Proof.pair_mem (by simpa using hu) hw)
  intro z hz
  exact Proof.proper_slice_constant hf hp hest z 0 hz (by simp)

end LeblSCV.BallPolydisc

 theorem solution :
    ¬ ∃ f : (Fin 2 → ℂ) → (Fin 2 → ℂ),
        DifferentiableOn ℂ f (LeblSCV.BallPolydisc.unitPolydisc 2) ∧
          LeblSCV.BallPolydisc.IsProperMapOn f (LeblSCV.BallPolydisc.unitPolydisc 2)
            (LeblSCV.BallPolydisc.unitBall 2) :=
  LeblSCV.BallPolydisc.rothstein

end
