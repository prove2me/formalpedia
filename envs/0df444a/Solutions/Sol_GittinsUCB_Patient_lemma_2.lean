-- Prove2me | solution 1 for GittinsUCB.Patient.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T06:08:55.379711+00:00
-- url     : https://prove2.me/submissions/33c5732b-00ae-4786-bbfa-fb14f102e0c4

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal

theorem gu_sqrt_diff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    |Real.sqrt a - Real.sqrt b| ≤ |a - b| / Real.sqrt b := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  rw [le_div_iff₀ hsb]
  have key : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
    have := Real.sq_sqrt ha; have := Real.sq_sqrt hb.le; nlinarith
  calc |Real.sqrt a - Real.sqrt b| * Real.sqrt b
      ≤ |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = |a - b| := by
        rw [← key, abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.sqrt a + Real.sqrt b)]

theorem solution (f : ℝ → ℝ)
    (hf : (fun x : ℝ => |f x|) =o[atTop] Real.sqrt) :
    Tendsto (fun x : ℝ => Real.sqrt (x + f x) - Real.sqrt x) atTop (nhds 0) := by
  have h1 : Tendsto (fun x => |f x| / Real.sqrt x) atTop (nhds 0) :=
    hf.tendsto_div_nhds_zero
  have hev : ∀ᶠ x in atTop, |Real.sqrt (x + f x) - Real.sqrt x| ≤ |f x| / Real.sqrt x := by
    filter_upwards [h1.eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1)),
      eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    have hfx : |f x| ≤ Real.sqrt x := by rwa [div_le_one hsx] at hx
    have hsxx : Real.sqrt x ≤ x := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hpos : 0 ≤ x + f x := by
      have := neg_abs_le (f x); linarith
    have := gu_sqrt_diff hpos (by linarith : (0:ℝ) < x)
    simpa using this
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _) hev h1
