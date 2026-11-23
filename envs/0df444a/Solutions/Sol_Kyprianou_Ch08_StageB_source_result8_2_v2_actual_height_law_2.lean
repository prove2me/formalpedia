-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.source_result8_2_v2_actual_height_law
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T00:05:48.890796+00:00
-- url     : https://prove2.me/submissions/8bfd4cc2-23ed-4ca8-9cd0-ebedaa04ea7f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_exists_pos_tail_measure_of_log_stieltjes_link
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_regularity_left_continuous
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_bounds
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_multiplicative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

private theorem p2m_tendsto_log_Iio (y : ℝ) (hy : 0 < y) :
    Tendsto Real.log (𝓝[<] y) (𝓝[<] Real.log y) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (Real.continuousAt_log (ne_of_gt hy)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] y ≤ 𝓝 y)
  · filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds hy),
      (self_mem_nhdsWithin : ∀ᶠ s in 𝓝[<] y, s ∈ Set.Iio y)] with s hs_pos hs_lt
    exact Real.log_lt_log hs_pos hs_lt

private theorem p2m_tendsto_exp_Iio_log (y : ℝ) (hy : 0 < y) :
    Tendsto Real.exp (𝓝[<] Real.log y) (𝓝[<] y) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · simpa [Real.exp_log hy] using
      (Real.continuous_exp.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[<] Real.log y ≤ 𝓝 (Real.log y)))
  · filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t in 𝓝[<] Real.log y, t ∈ Set.Iio (Real.log y))] with t ht
    simpa [Real.exp_log hy] using Real.exp_strictMono ht

private theorem p2m_continuous_neg_rightLim_log {f : ℝ → ℝ} (hf : Monotone f)
    (h₀ : ℝ) (hh₀ : 0 < h₀) :
    ContinuousWithinAt (fun h : ℝ => -Function.rightLim f (Real.log h)) (Set.Ici h₀) h₀ := by
  have hg : (hf.stieltjesFunction : ℝ → ℝ) = fun t => Function.rightLim f t := by
    funext t
    exact Monotone.stieltjesFunction_eq hf t
  have hright : ContinuousWithinAt (fun t : ℝ => Function.rightLim f t) (Set.Ici (Real.log h₀)) (Real.log h₀) := by
    simpa [hg] using (hf.stieltjesFunction).right_continuous (Real.log h₀)
  exact (hright.comp (Real.continuousAt_log (ne_of_gt hh₀)).continuousWithinAt
    (fun s hs => Real.log_le_log hh₀ (Set.mem_Ici.mp hs))).neg

private theorem p2m_tendsto_neg_comp_exp {g : ℝ → ℝ} {y : ℝ} (hy : 0 < y)
    (hg : Tendsto (fun s : ℝ => -g s) (𝓝[<] y) (nhds (-g y))) :
    Tendsto (fun t : ℝ => -g (Real.exp t)) (𝓝[<] Real.log y) (nhds (-g y)) := by
  simpa [Function.comp_def] using hg.comp (p2m_tendsto_exp_Iio_log y hy)

private theorem p2m_tendsto_rightLim_log_left {f : ℝ → ℝ} (hf : Monotone f) {y A : ℝ}
    (hlogLeft : Tendsto Real.log (𝓝[<] y) (𝓝[<] Real.log y))
    (hA : Function.leftLim (Function.rightLim f) (Real.log y) = A) :
    Tendsto (fun s : ℝ => Function.rightLim f (Real.log s)) (𝓝[<] y) (nhds A) := by
  simpa [Function.comp_def, hA] using ((Monotone.rightLim hf).tendsto_leftLim (Real.log y)).comp hlogLeft

private theorem p2m_log_stieltjes_left_link {F f : ℝ → ℝ}
    (hfdef : f = fun t => -F (Real.exp t)) (hfmono : Monotone f)
    (hFlink : ∀ y : ℝ, 0 < y → Tendsto (fun s : ℝ => -F s) (𝓝[<] y) (nhds (-F y))) :
    ∀ y : ℝ, 0 < y → Tendsto (fun s : ℝ => -(-Function.rightLim f (Real.log s))) (𝓝[<] y) (nhds (-F y)) := by
  intro y hy
  have hf_left_tendsto : Tendsto f (𝓝[<] Real.log y) (nhds (-F y)) := by
    rw [hfdef]
    exact p2m_tendsto_neg_comp_exp hy (hFlink y hy)
  have hleft_f : Function.leftLim f (Real.log y) = -F y := leftLim_eq_of_tendsto hf_left_tendsto
  have hleft_rl : Function.leftLim (Function.rightLim f) (Real.log y) = -F y := by
    simpa [hleft_f] using leftLim_rightLim (hfmono.tendsto_leftLim (Real.log y))
  simpa [hleft_rl] using p2m_tendsto_rightLim_log_left hfmono (p2m_tendsto_log_Iio y hy) hleft_rl

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ n : Measure ℝ, HasActualQExcursionHeightLaw P D ψ q n := by
  let S : ℝ → ℝ → ℝ := fun a h => ∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X a h ω}, Real.exp (Phi ψ q * a) * discountedAt q (tauPlus D.X a ω) ∂P
  let F : ℝ → ℝ := fun h => -Real.log (S 1 h)
  let f : ℝ → ℝ := fun t => -F (Real.exp t)
  let G : ℝ → ℝ := fun h => -Function.rightLim f (Real.log h)
  let hPhi : PhiIsLargestRoot ψ q := (hW q hq).1
  let hB := actual_height_tail_bounds P D ψ W hψ hW q hq
  let hR := Kyprianou.Ch08.StageB.actual_height_tail_regularity_left_continuous
    P D ψ W hψ hW q hq
  let hM := actual_height_tail_multiplicative P D ψ W hψ hW q hq
  let hFanti := hR.1
  let hFtop := hR.2.2.1
  let hFlink := hR.2.2.2
  let hfmono : Monotone f := fun t₁ t₂ ht => neg_le_neg (by simpa [F, S] using hFanti (Set.mem_Ioi.mpr (Real.exp_pos t₁)) (Set.mem_Ioi.mpr (Real.exp_pos t₂)) (Real.exp_strictMono.monotone ht))
  let hGanti : AntitoneOn G (Set.Ioi 0) := fun x hx y hy hxy => by
    simpa [G] using neg_le_neg ((Monotone.rightLim hfmono) (Real.log_le_log hx hxy))
  let hGcont : ∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt G (Set.Ici h₀) h₀ := fun h₀ hh₀ => by simpa [G] using p2m_continuous_neg_rightLim_log hfmono h₀ hh₀
  let hFtop' : Tendsto F atTop (nhds 0) := by simpa [F, S] using hFtop
  let hftop : Tendsto f atTop (nhds 0) := by simpa [f] using (hFtop'.comp Real.tendsto_exp_atTop).neg
  let hright_top : Tendsto (fun t : ℝ => Function.rightLim f t) atTop (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hftop (hftop.comp (Filter.tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)) (Filter.Eventually.of_forall fun t => hfmono.le_rightLim le_rfl) (Filter.Eventually.of_forall fun t => hfmono.rightLim_le (lt_add_of_pos_right t zero_lt_one))
  let hGtop : Tendsto G atTop (nhds 0) := by simpa [G] using (hright_top.comp Real.tendsto_log_atTop).neg
  let hGlink : ∀ y : ℝ, 0 < y → Tendsto (fun s => -G s) (𝓝[<] y) (nhds (-F y)) := by simpa [G] using p2m_log_stieltjes_left_link (F := F) (f := f) rfl hfmono (fun y hy => by simpa [F, S] using hFlink y hy)
  obtain ⟨mu, htail, hfin⟩ := exists_pos_tail_measure_of_log_stieltjes_link G F hGanti hGcont hGtop hGlink
  refine ⟨mu, hPhi, ?_⟩
  intro a h ha hh
  let hnn : 0 ≤ F h := by
    let hlog : Real.log (S 1 h) ≤ 0 := by simpa [S] using Real.log_nonpos (hB h hh).1.le (hB h hh).2
    simpa [F] using (neg_nonneg.mpr hlog)
  let hTR : (mu (Set.Ici h)).toReal = F h := by simpa [htail h hh] using ENNReal.toReal_ofReal hnn
  constructor
  · exact hfin h hh
  · simpa [F, S, hTR] using hM a h ha hh
