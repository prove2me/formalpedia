-- Prove2me | solution 1 for MasulloRH.complex_window_trace_error_controlled_by_reference_deficit
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T03:24:47.893795+00:00
-- url     : https://prove2.me/submissions/512273c1-6d3f-4012-88b3-5aa3783c7b5e

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_resolvent_kernel_bound_at_every_point_right_of_one
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_reference_real_resolvent_sandwich
import Mathlib.Tactic.Linarith

open MasulloRH Set

theorem solution (α : ℝ) (s : ℂ) (hs : 1 < s.re) :
    let W := ∑' z : ZetaZerosInTraceStrip (1 / 2),
      if α ≤ |z.val.re - 1 / 2| then zeroDecayWeight (1 / 2) z else 0
    let D := (regularizedTraceRHS (1 / 2) 3).re - (regularizedTraceRHS α 3).re
    W / 4 ≤ D ∧ D ≤ W / 2 ∧
      ‖regularizedTraceRHS (1 / 2) s - regularizedTraceRHS α s‖ ≤
        ‖s - 5 / 2‖ * (1 + ‖s - 5 / 2‖ / (s.re - 1)) * W := by
  classical
  let Z := ZetaZerosInTraceStrip (1 / 2)
  let inside : Set Z := {z | |z.val.re - 1/2| < α}
  let w := zeroDecayWeight (1/2)
  let c := fun t : ℂ => ‖t-5/2‖ * (1+‖t-5/2‖/(t.re-1))
  have hw : Summable w := weighted_zero_summability _ (by norm_num)
  have hext : Summable (fun z : (insideᶜ : Set Z) => w z.val) := hw.subtype (· ∈ insideᶜ)
  have hmass : (∑' z : (insideᶜ : Set Z), w z.val) =
      ∑' z : Z, if α ≤ |z.val.re-1/2| then w z else 0 := by
    rw [tsum_subtype]
    congr 1
    funext z
    simp [Set.indicator, inside]
  have hwc (t : ℂ) : Summable (fun z : Z => c t * w z) := hw.mul_left _
  have hf (t : ℂ) (ht : 1 < t.re) : Summable (zeroResolventTerm (1/2) t) :=
    (hwc t).of_norm_bounded (fun z => resolvent_kernel_bound_at_every_point_right_of_one t ht z)
  let e : ZetaZerosInTraceStrip α ≃ inside :=
    { toFun := fun r => ⟨⟨r.val, r.prop.1, r.prop.2.1, r.prop.2.2.1, abs_lt.mpr
        ⟨by linarith [r.prop.2.1], by linarith [r.prop.2.2.1]⟩⟩, r.prop.2.2.2⟩
      invFun := fun r => ⟨r.val.val, r.val.prop.1, r.val.prop.2.1, r.val.prop.2.2.1, r.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hdiff (t : ℂ) (ht : 1 < t.re) :
      regularizedTraceRHS (1/2) t - regularizedTraceRHS α t =
      ∑' z : (insideᶜ : Set Z), zeroResolventTerm (1/2) t z.val := by
    have hsum := (hf t ht).tsum_subtype_add_tsum_subtype_compl inside
    rw [← e.tsum_eq (fun z => zeroResolventTerm (1/2) t z.val)] at hsum
    change regularizedSpectral α t + _ = regularizedSpectral (1/2) t at hsum
    unfold regularizedTraceRHS
    rw [← hsum]
    abel
  have ht : (1:ℝ) < (3:ℂ).re := by norm_num
  have hex3 : Summable (fun z : (insideᶜ : Set Z) => zeroResolventTerm (1/2) 3 z.val) := (hf 3 ht).subtype (· ∈ insideᶜ)
  have hr := (Complex.hasSum_re hex3.hasSum).summable
  have hd : (regularizedTraceRHS (1/2) 3).re - (regularizedTraceRHS α 3).re =
      ∑' z : (insideᶜ : Set Z), (zeroResolventTerm (1/2) 3 z.val).re := by
    rw [← Complex.sub_re, hdiff 3 ht, Complex.re_tsum hex3]
  dsimp only
  rw [← hmass, hd, hdiff s hs]
  constructor
  · rw [← tsum_div_const]
    exact (hext.div_const 4).tsum_le_tsum (fun z => (reference_real_resolvent_sandwich z.val).1) hr
  constructor
  · rw [← tsum_div_const]
    exact hr.tsum_le_tsum (fun z => (reference_real_resolvent_sandwich z.val).2) (hext.div_const 2)
  · exact tsum_of_norm_bounded (hext.hasSum.mul_left (c s))
      (fun z => resolvent_kernel_bound_at_every_point_right_of_one s hs z.val)
