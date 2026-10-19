-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.Resolvent.scalar_entropy_integral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:31:46.267581+00:00
-- url     : https://prove2.me/submissions/d427ad80-0c16-4b41-bf5e-accdf4531134

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/Resolvent.lean:L189-L234
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.Resolvent.scalar_entropy_integral. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent

-- ---- from OAI.Probability.EntangledGames.Resolvent ----
namespace OAI

universe u_n u_J

open scoped BigOperators ComplexOrder

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace ThresholdParallelRepetition.Resolvent

variable {n : Type u_n} [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.Resolvent

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace ThresholdParallelRepetition.Resolvent

lemma scalar_entropy_integral {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IntegrableOn (fun s : ℝ => t / (1 + s) - t / (t + s)) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, t / (1 + s) - t / (t + s)) = t * Real.log t := by
  rcases eq_or_lt_of_le ht0 with rfl | ht
  · simp
  have hd (s : ℝ) (hs : s ∈ Ici (0 : ℝ)) :
      HasDerivAt (fun u : ℝ => t * (Real.log (1 + u) - Real.log (t + u)))
        (t / (1 + s) - t / (t + s)) s := by
    have h₁ := ((hasDerivAt_id s).const_add (1 : ℝ)).log
      (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one hs))
    have h₂ := ((hasDerivAt_id s).const_add t).log
      (ne_of_gt (add_pos_of_pos_of_nonneg ht hs))
    convert! (h₁.sub h₂).const_mul t using 1
    simp only [id_eq]
    ring
  have htop : Tendsto (fun s : ℝ => t + s) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop (b - t)] with s hs
    linarith
  have hratio : Tendsto (fun s : ℝ => (1 + s) / (t + s)) atTop (𝓝 1) := by
    have hh := (htop.const_div_atTop (1 - t)).const_add (1 : ℝ)
    rw [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    have ht' : t + s ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg ht hs)
    field_simp
    ring
  have hlog : Tendsto (fun s : ℝ => Real.log ((1 + s) / (t + s))) atTop (𝓝 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hl : Tendsto (fun s : ℝ => t * (Real.log (1 + s) - Real.log (t + s)))
      atTop (𝓝 0) := by
    have hh := hlog.const_mul t
    rw [mul_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    rw [Real.log_div (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one hs))
      (ne_of_gt (add_pos_of_pos_of_nonneg ht hs))]
  have hneg (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      t / (1 + s) - t / (t + s) ≤ 0 := by
    apply sub_nonpos.mpr
    apply div_le_div_of_nonneg_left ht.le (add_pos ht hs)
    linarith
  refine ⟨integrableOn_Ioi_deriv_of_nonpos' hd hneg hl, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonpos' hd hneg hl]
  simp

end ThresholdParallelRepetition.Resolvent

end
end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.Resolvent
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology


theorem solution : type_of% @_root_.OAI.ThresholdParallelRepetition.Resolvent.scalar_entropy_integral := @_root_.OAI.ThresholdParallelRepetition.Resolvent.scalar_entropy_integral
