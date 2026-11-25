-- Prove2me | solution 1 for GlobalTheory.exists_density_origin_of_almost_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:14.733347+00:00
-- url     : https://prove2.me/submissions/bf2daf3e-7c3b-48d9-9e48-78c024097d80

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsDensityOriginOfAlmostHomogeneous
import Theorems.Thm_GlobalTheory_densHom_scale
import Theorems.Thm_GlobalTheory_densHom_tendsto_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
namespace GlobalTheory
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
end
open MeasureTheory Filter Topology Matrix in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
private theorem closedBall_smul_div_ball_eq_ofReal_pow_mul (l ν : Measure V) [l.IsAddHaarMeasure] (x : V)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    ν (Metric.closedBall x (s * r)) / l (Metric.ball 0 r) =
      ENNReal.ofReal (s ^ Module.finrank ℝ V) *
        (ν (Metric.closedBall x (s * r)) / l (Metric.closedBall x (s * r))) := by
  rw [_root_.GlobalTheory.densHom_scale l x hs hr, ← mul_div_assoc,
    ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_pos.2 (pow_pos hs _)).ne' ENNReal.ofReal_ne_top]
open MeasureTheory Filter Topology Matrix in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
private theorem ofReal_pow_mul_le_liminf_ball_ratio (l ν : Measure V) [l.IsAddHaarMeasure] {x : V} {s : ℝ}
    (hs : 0 < s) {D : ENNReal}
    (hD : Tendsto (fun r => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) (𝓝[>] 0) (𝓝 D))
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν (Metric.closedBall x (s * r)) ≤ ν (Metric.ball 0 r)) :
    ENNReal.ofReal (s ^ Module.finrank ℝ V) * D ≤
      liminf (fun r => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) := by
  have htend : Tendsto (fun r => ENNReal.ofReal (s ^ Module.finrank ℝ V) *
      (ν (Metric.closedBall x (s * r)) / l (Metric.closedBall x (s * r)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (s ^ Module.finrank ℝ V) * D)) :=
    ENNReal.Tendsto.const_mul (hD.comp (_root_.GlobalTheory.densHom_tendsto_mul hs))
      (Or.inr ENNReal.ofReal_ne_top)
  refine (le_of_eq htend.liminf_eq.symm).trans (Filter.liminf_le_liminf ?_)
  filter_upwards [h, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
  rw [← closedBall_smul_div_ball_eq_ofReal_pow_mul l ν x hs hr0]
  exact ENNReal.div_le_div_right hr _
open MeasureTheory Filter Topology Matrix in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
private theorem limsup_ball_ratio_le_ofReal_pow_mul (l ν : Measure V) [l.IsAddHaarMeasure] {x : V} {s : ℝ}
    (hs : 0 < s) {D : ENNReal}
    (hD : Tendsto (fun r => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) (𝓝[>] 0) (𝓝 D))
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν (Metric.ball 0 r) ≤ ν (Metric.closedBall x (s * r))) :
    limsup (fun r => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) ≤
      ENNReal.ofReal (s ^ Module.finrank ℝ V) * D := by
  have htend : Tendsto (fun r => ENNReal.ofReal (s ^ Module.finrank ℝ V) *
      (ν (Metric.closedBall x (s * r)) / l (Metric.closedBall x (s * r)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (s ^ Module.finrank ℝ V) * D)) :=
    ENNReal.Tendsto.const_mul (hD.comp (_root_.GlobalTheory.densHom_tendsto_mul hs))
      (Or.inr ENNReal.ofReal_ne_top)
  refine (Filter.limsup_le_limsup ?_).trans (le_of_eq htend.limsup_eq)
  filter_upwards [h, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
  rw [← closedBall_smul_div_ball_eq_ofReal_pow_mul l ν x hs hr0]
  exact ENNReal.div_le_div_right hr _
end GlobalTheory
end

set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open GlobalTheory
open MeasureTheory Filter Topology Matrix
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V)
    [l.IsAddHaarMeasure] [IsLocallyFiniteMeasure ν], (∀ r : ℝ, 0 < r → ν (Metric.ball 0 r) ≠ 0) →
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ x : V, ‖x‖ < δ →
      ∀ᶠ r in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * r)) ≤ ν (Metric.ball 0 r) ∧
        ν (Metric.ball 0 r) ≤ ν (Metric.ball x ((1 + ε) * r))) →
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      Tendsto (fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c) := by
  intro V _ _ _ _ _ l ν _ _ hpos halmost
  set ρ := fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r) with hρ
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ D : ENNReal, D < ⊤ ∧
      ENNReal.ofReal ((1 - 2 * ε) ^ Module.finrank ℝ V) * D ≤ liminf ρ (𝓝[>] 0) ∧
      limsup ρ (𝓝[>] 0) ≤ ENNReal.ofReal ((1 + ε) ^ Module.finrank ℝ V) * D := by
    intro ε hε hε2
    obtain ⟨δ, hδ, hx⟩ := halmost ε hε (by linarith)
    obtain ⟨x, hxmem, hxD, hxfin⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (Metric.measure_ball_pos l (0 : V) hδ).ne'
      (ae_restrict_of_ae ((Besicovitch.ae_tendsto_rnDeriv ν l).and (Measure.rnDeriv_lt_top ν l)))
    have hxr := hx x (mem_ball_zero_iff.1 hxmem)
    refine ⟨_, hxfin, ofReal_pow_mul_le_liminf_ball_ratio l ν (by linarith) hxD ?_,
      limsup_ball_ratio_le_ofReal_pow_mul l ν (by linarith) hxD ?_⟩
    · filter_upwards [hxr, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
      exact (measure_mono (Metric.closedBall_subset_ball (by nlinarith))).trans hr.1
    · filter_upwards [hxr] with r hr
      exact hr.2.trans (measure_mono Metric.ball_subset_closedBall)
  have hML : liminf ρ (𝓝[>] 0) ≤ limsup ρ (𝓝[>] 0) := liminf_le_limsup
  have hLtop : limsup ρ (𝓝[>] 0) < ⊤ := by
    obtain ⟨D, hD, -, hup⟩ := key (1 / 4) (by norm_num) (by norm_num)
    exact hup.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD)
  have hLM : limsup ρ (𝓝[>] 0) ≤ liminf ρ (𝓝[>] 0) := by
    have hK : Tendsto (fun ε : ℝ => ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V))
        (𝓝 0) (𝓝 1) := by
      have hc : ContinuousAt (fun ε : ℝ =>
          ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V)) 0 :=
        ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)
      simpa using hc.tendsto
    have hT : Tendsto (fun ε : ℝ => ENNReal.ofReal
        ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V) * liminf ρ (𝓝[>] 0))
        (𝓝[>] 0) (𝓝 (liminf ρ (𝓝[>] 0))) := by
      have h1 := ENNReal.Tendsto.mul_const (b := liminf ρ (𝓝[>] 0)) (ENNReal.tendsto_ofReal hK)
        (Or.inr (hML.trans_lt hLtop).ne)
      simpa using h1.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hT ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
    obtain ⟨D, -, hlow, hup⟩ := key ε hε.1 hε.2
    have hb : 0 < (1 - 2 * ε) ^ Module.finrank ℝ V := pow_pos (by linarith [hε.2]) _
    refine hup.trans ?_
    calc ENNReal.ofReal ((1 + ε) ^ Module.finrank ℝ V) * D
        = ENNReal.ofReal ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V) *
          (ENNReal.ofReal ((1 - 2 * ε) ^ Module.finrank ℝ V) * D) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg (pow_nonneg (by linarith [hε.1]) _) hb.le),
            div_mul_cancel₀ _ hb.ne']
      _ ≤ _ := by gcongr
  have htend : Tendsto ρ (𝓝[>] 0) (𝓝 (limsup ρ (𝓝[>] 0))) :=
    tendsto_of_liminf_eq_limsup (le_antisymm hML hLM) rfl
  refine ⟨limsup ρ (𝓝[>] 0), ?_, hLtop.ne, htend⟩
  intro hL0
  rw [hL0] at htend
  obtain ⟨δ, hδ, hx⟩ := halmost (1 / 2) (by norm_num) (by norm_num)
  have hs_le : ∀ t : NNReal, 0 < t → ν (Metric.ball 0 δ) ≤ t * l (Metric.ball 0 δ) := by
    intro t ht
    have hle := VitaliFamily.measure_le_of_frequently_le (Besicovitch.vitaliFamily ν) (t • l)
      (Measure.AbsolutelyContinuous.refl ν) (Metric.ball (0 : V) δ) ?_
    · rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hle
      exact hle
    intro x hxs
    apply ((Besicovitch.tendsto_filterAt ν x).comp
      (_root_.GlobalTheory.densHom_tendsto_mul (show (0 : ℝ) < 1 / 4 by norm_num))).frequently
    refine Filter.Eventually.frequently ?_
    have hpos' : (0 : ENNReal) < t * ENNReal.ofReal ((1 / 4) ^ Module.finrank ℝ V) :=
      ENNReal.mul_pos (by exact_mod_cast ht.ne') (ENNReal.ofReal_pos.2 (by positivity)).ne'
    filter_upwards [(tendsto_order.1 htend).2 _ hpos', hx x (mem_ball_zero_iff.1 hxs),
      self_mem_nhdsWithin] with r hr hxr (hr0 : 0 < r)
    show ν (Metric.closedBall x (1 / 4 * r)) ≤ (t • l) (Metric.closedBall x (1 / 4 * r))
    have hlt : ν (Metric.ball 0 r) <
        t * ENNReal.ofReal ((1 / 4) ^ Module.finrank ℝ V) * l (Metric.ball 0 r) :=
      (ENNReal.div_lt_iff (Or.inl (Metric.measure_ball_pos l 0 hr0).ne')
        (Or.inl measure_ball_lt_top.ne)).1 hr
    rw [mul_assoc, ← _root_.GlobalTheory.densHom_scale l x (by norm_num) hr0] at hlt
    have hsub : Metric.closedBall x (1 / 4 * r) ⊆ Metric.ball x ((1 - 1 / 2) * r) :=
      Metric.closedBall_subset_ball (by linarith)
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ((measure_mono hsub).trans hxr.1).trans hlt.le
  have hzero : ν (Metric.ball 0 δ) = 0 := by
    have hT : Tendsto (fun t : NNReal => (t : ENNReal) * l (Metric.ball 0 δ)) (𝓝[>] 0) (𝓝 0) := by
      have h1 := ENNReal.Tendsto.mul_const (b := l (Metric.ball 0 δ))
        (ENNReal.tendsto_coe.2 (tendsto_id (x := 𝓝 (0 : NNReal)))) (Or.inr measure_ball_lt_top.ne)
      simpa using h1.mono_left nhdsWithin_le_nhds
    exact le_antisymm (ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun t ht => hs_le t ht))
      bot_le
  exact hpos δ hδ hzero
end _root_.GlobalTheory
end GlobalTheory
