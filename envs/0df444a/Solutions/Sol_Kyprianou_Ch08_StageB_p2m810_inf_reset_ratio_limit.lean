-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_inf_reset_ratio_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:20:30.672555+00:00
-- url     : https://prove2.me/submissions/03c77ccc-14ff-46dc-9e4d-c94573f6fd4a

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_reset_delta_limit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_zscale_ge_one
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_zscale_continuous
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
/-- Continuous small-reset ratio. -/
theorem solution :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      (∀ b : ℝ, 0 < b → 0 < W q b) →
      let R := fun (ε b : ℝ) => ((Zscale q (W q) (x+ε) -
        W q (x+ε) * ((Zscale q (W q) ε - 1) / W q ε)) /
      (Zscale q (W q) (b+ε) -
        W q (b+ε) * ((Zscale q (W q) ε - 1) / W q ε)))
      Tendsto (fun ε => R ε a) (nhdsWithin 0 (Ioi 0))
        (nhds (Zscale q (W q) x / Zscale q (W q) a)) ∧
      Tendsto (fun ε => R ε (a-ε)) (nhdsWithin 0 (Ioi 0))
        (nhds (Zscale q (W q) x / Zscale q (W q) a)) := by
  intro ψ W hW q x a hq ha hx hxa hp
  dsimp only
  let δ : ℝ → ℝ := fun e => (Zscale q (W q) e - 1) / W q e
  let Z := Zscale q (W q)
  let f := W q
  have hc : ContinuousOn f (Ici (0 : ℝ)) := (hW q hq).2.2.2.1
  have hz : ContinuousOn Z (Ici (0 : ℝ)) := p2m810_zscale_continuous ψ W hW q hq
  have hδ : Tendsto δ (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    p2m810_inf_reset_delta_limit ψ W hW q hq hp
  have hlim (t : ℝ) (ht : 0 ≤ t) :
      Tendsto (fun e => Z (t+e) - f (t+e) * δ e)
        (nhdsWithin 0 (Ioi 0)) (nhds (Z t)) := by
    have harg : Tendsto (fun e : ℝ => t+e) (nhdsWithin 0 (Ioi 0))
        (nhdsWithin t (Ici 0)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · simpa using (tendsto_const_nhds (x := t)).add
          (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun e : ℝ => e)
            (nhdsWithin 0 (Ioi 0)) (nhds 0))
      · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with e he
        exact add_nonneg ht (le_of_lt he)
    simpa using ((hz t ht).tendsto.comp harg).sub
      (((hc t ht).tendsto.comp harg).mul hδ)
  have hd : Z a ≠ 0 := by
    have h := source_zscale_ge_one ψ W hW q a hq ha.le
    change 1 ≤ Z a at h
    linarith
  have hconst : Tendsto (fun e : ℝ => Z a - f a * δ e)
      (nhdsWithin 0 (Ioi 0)) (nhds (Z a)) := by
    simpa using (tendsto_const_nhds (x := Z a)).sub
      ((tendsto_const_nhds (x := f a)).mul hδ)
  constructor
  · exact (hlim x hx).div (hlim a ha.le) hd
  · have h := (hlim x hx).div hconst hd
    change Tendsto (fun e : ℝ => (Z (x+e) - f (x+e) * δ e) /
        (Z a - f a * δ e)) (nhdsWithin 0 (Ioi 0)) (nhds (Z x / Z a)) at h
    change Tendsto (fun e : ℝ => (Z (x+e) - f (x+e) * δ e) /
        (Z (a-e+e) - f (a-e+e) * δ e)) (nhdsWithin 0 (Ioi 0)) (nhds (Z x / Z a))
    simpa only [sub_add_cancel] using h
