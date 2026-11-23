-- Prove2me | solution 1 for NoHair.rescaled_ball_mass_recovers_total_source
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:28:00.470535+00:00
-- url     : https://prove2.me/submissions/662904d9-b2b0-427b-a512-68c90c0e0bef

import Theorems.Thm_NoHair_translated_ball_source_uniform_bound
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped ContDiff Topology

private abbrev X := ADMPoint
local instance : (cocompact X).IsCountablyGenerated := by
  rw [←Metric.cobounded_eq_cocompact,←comap_norm_atTop]
  infer_instance
local instance : NeZero admSurfaceMeasure := ⟨(volume : Measure X).toSphere_ne_zero⟩

private lemma mass_measurable {q : X → ℝ} (hi : Integrable q) (x : X) :
    Measurable (fun t : ℝ => (∫ z in ball x (t*‖x‖),q z)/t^2) := by
  have mono (f : X → ℝ) (hf : Integrable f) (hn : ∀ z, 0≤f z) :
      Monotone (fun t : ℝ => ∫ z in ball x (t*‖x‖), f z) := by
    intro a b hab
    apply setIntegral_mono_set hf.integrableOn (ae_of_all _ hn)
    exact ae_of_all _ (fun z hz => ball_subset_ball (mul_le_mul_of_nonneg_right hab (norm_nonneg x)) hz)
  let a:=fun z => |q z|
  let b:=fun z => |q z|-q z
  have ha : Integrable a := hi.abs
  have hb : Integrable b := hi.abs.sub hi
  have he (t : ℝ) : (∫ z in ball x (t*‖x‖),a z)-(∫ z in ball x (t*‖x‖),b z)=
      ∫ z in ball x (t*‖x‖),q z := by
    rw [←integral_sub ha.integrableOn hb.integrableOn]
    simp [a,b]
  apply Measurable.div _ (measurable_id.pow_const 2)
  have hm := (mono a ha (fun z => abs_nonneg _)).measurable.sub
    (mono b hb (fun z => sub_nonneg.mpr (le_abs_self _))).measurable
  change Measurable (fun t : ℝ => (∫ z in ball x (t*‖x‖),a z)-(∫ z in ball x (t*‖x‖),b z)) at hm
  simpa only [he] using hm

private lemma majorant_int (K : ℝ) : IntegrableOn (fun t : ℝ => K/(t+1)^2) (Ioi 0) := by
  have e:=integrableOn_add_rpow_Ioi_of_lt (a:=(-2:ℝ)) (c:=0) (m:=1) (by norm_num) (by norm_num)
  apply (e.const_mul K).congr
  filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=(0:ℝ)))] with t ht
  change K*(t+1)^(-2:ℝ)=K/(t+1)^2
  simp only [Real.rpow_neg (by linarith [mem_Ioi.mp ht] : 0≤t+1) (2:ℝ),Real.rpow_two,div_eq_mul_inv]

private lemma ball_real' (x : X) {r : ℝ} (hr : 0<r) :
    volume.real (ball x r)=r^3*volume.real (ball (0:X) 1) := by
  rw [measureReal_def,volume.addHaar_ball_of_pos x hr,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]
  simp [measureReal_def,finrank_euclideanSpace]

private lemma fixed_scale {q : X → ℝ} (hi : Integrable q) (t : ℝ) (ht : t≠1) :
    Tendsto (fun x : X => ∫ z in ball x (t*‖x‖),q z) (cocompact X)
      (𝓝 (if 1<t then ∫ z,q z else 0)) := by
  let G:= fun (x z : X) => (ball x (t*‖x‖)).indicator q z
  let g:= fun z => if 1<t then q z else 0
  have hmeas (x : X) : AEStronglyMeasurable (G x) volume := hi.aestronglyMeasurable.indicator measurableSet_ball
  have hb (x z : X) : ‖G x z‖ ≤ |q z| := by
    by_cases hz : z∈ball x (t*‖x‖) <;> simp [G,hz]
  have hlim (z : X) : Tendsto (fun x : X => G x z) (cocompact X) (𝓝 (g z)) := by
    apply tendsto_const_nhds.congr'
    rcases lt_or_gt_of_ne ht with lo|hi'
    · filter_upwards [(tendsto_norm_cocompact_atTop (E:=X)).eventually_gt_atTop (‖z‖/(1-t))] with x hx
      have hx' := (div_lt_iff₀ (sub_pos.mpr lo)).mp hx
      have hd : ¬z∈ball x (t*‖x‖) := by
        rw [mem_ball,not_lt]
        have e : ‖x‖ ≤ dist z x+‖z‖ := by simpa [dist_comm x z] using dist_triangle x z 0
        linarith only [hx',e]
      simp [G,g,not_lt_of_ge lo.le,hd]
    · filter_upwards [(tendsto_norm_cocompact_atTop (E:=X)).eventually_gt_atTop (‖z‖/(t-1))] with x hx
      have hx' := (div_lt_iff₀ (sub_pos.mpr hi')).mp hx
      have hd : z∈ball x (t*‖x‖) := by
        rw [mem_ball]
        have e : dist z x ≤ ‖z‖+‖x‖ := by simpa using dist_triangle z 0 x
        linarith only [hx',e]
      simp [G,g,hi',hd]
  have e:=tendsto_integral_filter_of_dominated_convergence (μ:=volume) (fun z => |q z|)
    (Eventually.of_forall hmeas) (Eventually.of_forall fun x => ae_of_all _ (hb x)) hi.abs (ae_of_all _ hlim)
  have eq (x : X) : (∫ z,G x z)=∫ z in ball x (t*‖x‖),q z := integral_indicator measurableSet_ball
  simp_rw [eq] at e
  by_cases h : 1<t <;> simpa [g,h] using e

theorem solution (q : ADMPoint → ℝ) (hi : Integrable q)
    (hd : ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ z : ADMPoint, R < ‖z‖ → |q z| ≤ C/‖z‖^4) :
    Tendsto (fun x : ADMPoint => (∫ t : ℝ in Ioi 0, (∫ z in ball x (t*‖x‖), q z)/t^2)) (cocompact ADMPoint) (𝓝 (∫ z, q z)) := by
  let F := fun (x : X) (t : ℝ) => (∫ z in ball x (t*‖x‖),q z)/t^2
  let f := fun t : ℝ => if 1<t then (∫ z,q z)/t^2 else 0
  obtain ⟨K,R,hK,hR,hb⟩ := translated_ball_source_uniform_bound q hi hd
  have hm : ∀ᶠ x : X in cocompact X, AEStronglyMeasurable (F x) (volume.restrict (Ioi (0:ℝ))) :=
    Eventually.of_forall fun x => (mass_measurable hi x).aestronglyMeasurable
  have hb' : ∀ᶠ x : X in cocompact X, ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), ‖F x t‖ ≤ K/(t+1)^2 := by
    filter_upwards [(tendsto_norm_cocompact_atTop (E:=X)).eventually_gt_atTop R] with x hx
    exact (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => hb x hx t ht)
  have hl : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), Tendsto (fun x : X => F x t) (cocompact X) (𝓝 (f t)) := by
    filter_upwards [ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 1)] with t ht
    have e := (fixed_scale hi t ht).div_const (t^2)
    by_cases h : 1<t <;> simpa [F,f,h] using e
  have e := tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => K/(t+1)^2)
    hm hb' (majorant_int K) hl
  have g (t : ℝ) : f t=(Ioi (1:ℝ)).indicator (fun s => (∫ z,q z)/s^2) t := by rfl
  have tail : (∫ t : ℝ in Ioi 1, t^(-2:ℝ))=1 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) (by norm_num)]
    norm_num
  have fl : (∫ t in Ioi (0:ℝ),f t)=(∫ z,q z) := by
    simp_rw [g]
    rw [setIntegral_indicator measurableSet_Ioi]
    rw [show Ioi (0:ℝ) ∩ Ioi 1 = Ioi 1 from inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num))]
    calc
      _ = ∫ t : ℝ in Ioi 1, (∫ z,q z)*t^(-2:ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change (∫ z,q z)/t^2=(∫ z,q z)*t^(-2:ℝ)
        simp only [Real.rpow_neg (by linarith [mem_Ioi.mp ht] : 0≤t) (2:ℝ),Real.rpow_two,div_eq_mul_inv]
      _ = _ := by rw [integral_const_mul,tail,mul_one]
  rw [fl] at e
  exact e
