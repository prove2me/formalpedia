-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_dyadic_passage_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:18:29.35164+00:00
-- url     : https://prove2.me/submissions/d6d070d1-982e-4950-943a-ecedb3391a98

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_before
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_contact
import Theorems.Thm_Kyprianou_Ch04_cor412_dyadic_reward_eq
import Theorems.Thm_Kyprianou_Ch04_cor412_infimum_decomp
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The exponential infimum reward factors pathwise at a finite downward passage. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (w : Ω) (t : NNReal)
    (ht : Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w = (t : WithTop NNReal))
    (hb : BddBelow (range (fun s : NNReal => L.X s w)))
    (β : ℝ) (hβ : 0 ≤ β) :
    let R : (NNReal → ℝ) → ℝ≥0∞ := fun f =>
      ⨅ q : ℕ × ℕ, ENNReal.ofReal (Real.exp (β * f ((q.1 : NNReal) / 2 ^ q.2)))
    R (fun s => L.X s w) =
      ENNReal.ofReal (Real.exp (β * L.X t w)) *
        R (fun u => L.X (t + u) w - L.X t w) := by
  intro R
  let f : NNReal → ℝ := fun s => L.X s w
  let g : NNReal → ℝ := fun u => f (t + u) - f t
  have hgb : BddBelow (range g) := by
    obtain ⟨a,ha⟩ := hb
    refine ⟨a - f t, ?_⟩
    rintro y ⟨u,rfl⟩
    exact sub_le_sub_right (ha ⟨t + u,rfl⟩) _
  have hgrc (u : NNReal) : ContinuousWithinAt g (Ici u) u := by
    have h := (L.rightCont w (t + u)).comp
      (continuous_const.add continuous_id).continuousWithinAt
      (show MapsTo (fun s : NNReal => t + s) (Ici u) (Ici (t + u)) from
        fun s hs => add_le_add_right hs t)
    exact h.sub continuousWithinAt_const
  have h1 := Kyprianou.Ch04.cor412_dyadic_reward_eq f (L.rightCont w) hb β hβ
  have h2 := Kyprianou.Ch04.cor412_dyadic_reward_eq g hgrc hgb β hβ
  have hd := Kyprianou.Ch04.cor412_infimum_decomp f t
    (Kyprianou.Ch04.cor412_lower_before P F L w t ht)
    (Kyprianou.Ch04.cor412_lower_contact P F L w t ht) hb
  change R f = ENNReal.ofReal (Real.exp (β * f t)) * R g
  change R f = _ at h1
  change R g = _ at h2
  rw [h1,h2,hd,mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
