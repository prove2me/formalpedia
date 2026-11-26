-- Prove2me | solution 1 for LogLogJam.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:27:11.658103+00:00
-- url     : https://prove2.me/submissions/b6862c08-c874-4cd9-9f06-d296b5628b95

import Definitions.Def_LogLogJam_GaussProtocol
import Theorems.Thm_LogLogJam_history_reference_density

import Theorems.Thm_LogLogJam_lemma_5_3
import Theorems.Thm_LogLogJam_lemma_5_5

open MeasureTheory Filter LogLogJam
open scoped ENNReal Topology

private theorem derivMeasurable {X : Type*} [MeasurableSpace X] (q : ℝ → X → ℝ)
    (hC : ∀ x, ContDiff ℝ 1 (fun t => q t x)) (hm : ∀ t, Measurable (q t)) :
    Measurable (fun z : ℝ × X => deriv (fun t => q t z.2) z.1) := by
  apply measurable_uncurry_of_continuous_of_measurable (fun x => (hC x).continuous_deriv_one)
  intro t
  let d (n : ℕ) : ℝ := 1 / (n+1 : ℝ)
  have hlim : Tendsto d atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall fun n => by change 0 < 1 / (n+1 : ℝ); positivity⟩
  apply measurable_of_tendsto_metrizable (f := fun (n : ℕ) x => (d n)⁻¹ * (q (t+d n) x - q t x))
    (fun n => measurable_const.mul ((hm _).sub (hm _)))
  apply tendsto_pi_nhds.mpr
  intro x
  exact ((hC x).differentiable_one t).hasDerivAt.tendsto_slope_zero_right.comp hlim

private theorem measurableDistance (l : ℝ) : Measurable (fun z : ℝ × ℝ => trDist l z.1 z.2) := by
  simp [trDist, Vsq, rot, Matrix.det_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    Matrix.transpose_apply]
  fun_prop

private theorem measEvent {Y : Type*} [MeasurableSpace Y] (l e : ℝ) (v w : Y → ℝ)
    (hv : Measurable v) (hw : Measurable w) : MeasurableSet {y | trDist l (v y) (w y) ≤ e} := by
  let g : Y → ℝ × ℝ := fun y => (v y, w y)
  have hg : Measurable g := hv.prodMk hw
  let f : ℝ × ℝ → ℝ := fun z => trDist l z.1 z.2
  have hf : Measurable f := measurableDistance l
  exact (measurableSet_le (f := f ∘ g) (g := fun _ : Y => e) (hf.comp hg) measurable_const)

set_option maxHeartbeats 330000 in
private theorem angleIntegral {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (q : ℝ → X → ℝ) (hq : Measurable (Function.uncurry q)) (a : X → ℝ) (ha : Measurable a)
    (l e : ℝ) (hl : 1 < l) (hE : 1 < energy l) (he : 0 < e) (he' : e < 1/2) :
    (∫⁻ t in Set.Ico 0 Real.pi, ∫⁻ x, ENNReal.ofReal (q t x) *
      ({z | trDist l (a z) t ≤ e} : Set X).indicator 1 x ∂μ) ≤
      ENNReal.ofReal (2 * Real.pi * e / energy l) * (∫⁻ x, ⨆ t, ENNReal.ofReal (q t x) ∂μ) := by
  classical
  let f (t : ℝ) (x : X) := ENNReal.ofReal (q t x) *
    ({z | trDist l (a z) t ≤ e} : Set X).indicator (1 : X → ℝ≥0∞) x
  let A := {z : ℝ × X | trDist l (a z.2) z.1 ≤ e}
  have hA : MeasurableSet A := measEvent l e (fun z : ℝ × X => a z.2) Prod.fst (ha.comp measurable_snd) measurable_fst
  have hf : Measurable (Function.uncurry f) := by
    have hfun : Function.uncurry f = fun z : ℝ × X => ENNReal.ofReal (q z.1 z.2) *
        A.indicator (fun _ => (1 : ℝ≥0∞)) z := by
      funext z; by_cases hz : trDist l (a z.2) z.1 ≤ e <;> simp [f, A, hz, Function.uncurry]
    rw [hfun]
    exact hq.ennreal_ofReal.mul (measurable_const.indicator hA)
  change (∫⁻ t in Set.Ico 0 Real.pi, ∫⁻ x, f t x ∂μ) ≤ _
  rw [lintegral_lintegral_swap hf.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  let U := {t : ℝ | trDist l t (a x) ≤ e}
  let M := ⨆ t, ENNReal.ofReal (q t x)
  have hU : MeasurableSet U := measEvent l e id (fun _ => a x) measurable_id measurable_const
  calc
    _ ≤ ∫⁻ t in Set.Ico 0 Real.pi, U.indicator (fun _ => M) t := by
      apply lintegral_mono
      intro t
      have hsym : trDist l (a x) t = trDist l t (a x) := by simp [trDist, add_comm]
      by_cases hx : trDist l t (a x) ≤ e
      · simpa [f,U,hsym,hx] using (le_iSup (fun t => ENNReal.ofReal (q t x)) t)
      · simp [f,U,hsym,hx]
    _ = M * volume (Set.Ico 0 Real.pi ∩ U) := by
      rw [lintegral_indicator hU, setLIntegral_const, Measure.restrict_apply hU, Set.inter_comm U]
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul_left (lemma_5_3 l e (a x) hl hE he he') _

theorem solution {T : ℕ} (P : GaussProtocol T) (lam ε : ℝ) (hlam : 1 < lam)
    (hE : 1 < energy lam) (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    succProb lam ε P ≤ ENNReal.ofReal (2 * ε / energy lam) *
      (1 + ENNReal.ofReal Real.pi * (Jbar lam P T) ^ (1 / 2 : ℝ)) := by
  let G := {H : Hist T // ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)}
  obtain ⟨μ, hs, hc⟩ := history_reference_density P T le_rfl
  let _ := hs
  obtain ⟨hpos, hper, hC, hm, hn, hrep⟩ := hc lam hlam
  let q (t : ℝ) (H : G) := histDens lam t H.1
  let a (H : G) := P.out H.1
  have ha : Measurable a := P.measurable_out.comp measurable_subtype_coe
  have hqm : Measurable (Function.uncurry q) :=
    measurable_uncurry_of_continuous_of_measurable (fun H => (hC H).continuous) hm
  have hj (t : ℝ) : protoFisher lam P T t = fisherInfo μ q t := by
    unfold protoFisher
    apply hrep
    have qlog := derivMeasurable (fun t x => Real.log (q t x))
      (fun H => (hC H).log (fun t => (hpos t H).ne')) (fun t => (hm t).log)
    exact ((qlog.comp (measurable_const.prodMk measurable_id)).pow_const 2).ennreal_ofReal
  have hsu (t : ℝ) : histInt lam t P T (Set.indicator {H | trDist lam (P.out H) t ≤ ε} 1) =
      ∫⁻ H, ENNReal.ofReal (q t H) * ({z | trDist lam (a z) t ≤ ε} : Set G).indicator 1 H ∂μ := by
    have hmEvent : MeasurableSet {H : Hist T | trDist lam (P.out H) t ≤ ε} :=
      measEvent lam ε P.out (fun _ => t) P.measurable_out measurable_const
    have kev := (measurable_const.indicator hmEvent : Measurable
      (({H : Hist T | trDist lam (P.out H) t ≤ ε} : Set (Hist T)).indicator (1 : Hist T → ℝ≥0∞))).comp
      (measurable_subtype_coe (p := fun H : Hist T => ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)))
    rw [hrep t (Set.indicator {H : Hist T | trDist lam (P.out H) t ≤ ε} (1 : Hist T → ℝ≥0∞)) kev]
    apply lintegral_congr
    intro H
    by_cases h : trDist lam (P.out H.1) t ≤ ε <;> simp [q,a,h]
  have hb := (angleIntegral μ q hqm a ha lam ε hlam hE hε hε2).trans
    (mul_le_mul_right (lemma_5_5 μ q hpos hper hC hm hn) _)
  unfold succProb Jbar
  simp_rw [hsu, hj]
  have hcoeff : ENNReal.ofReal (1/Real.pi) * ENNReal.ofReal (2*Real.pi*ε/energy lam) =
      ENNReal.ofReal (2*ε/energy lam) := by
    rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp [Real.pi_ne_zero]
  simpa only [←mul_assoc, hcoeff] using mul_le_mul_right hb (ENNReal.ofReal (1/Real.pi))
