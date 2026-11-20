-- Prove2me | solution 1 for LogitRankDistill.lemma_5_3
-- status  : ACCEPTED   (disprove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T16:27:05.942353+00:00
-- url     : https://prove2.me/submissions/a9c3e529-734d-4614-9153-e7c1d565752d

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_LogitRankDistill_Models

open LogitRankDistill

theorem solution : ¬ (∀ {Tok : Type} [Fintype Tok] [DecidableEq Tok] (L L' : Tok → ℝ),
    IsingLTL.BeliefProp.tvDist (softmax L) (softmax L') ≤ (1 / 4) * ⨆ y, |L y - L' y|) := by
  intro h
  let L : ULift.{0} Bool → ℝ := fun y => if y.down then 1 else -1
  have hb := h L (fun _ => 0)
  have hsup : (⨆ y : ULift.{0} Bool, |L y - 0|) = 1 := by
    have : (fun y : ULift.{0} Bool => |L y - 0|) = fun _ => 1 := by
      funext y; simp only [L]; split_ifs <;> norm_num
    rw [this, ciSup_const]
  rw [hsup] at hb
  have hsum : ∀ f : ULift.{0} Bool → ℝ, ∑ y, f y = f ⟨true⟩ + f ⟨false⟩ := by
    intro f
    rw [← (Equiv.ulift.{0, 0} (α := Bool)).symm.sum_comp]
    simp [Fintype.sum_bool, Equiv.ulift]
  simp only [IsingLTL.BeliefProp.tvDist, softmax, hsum, L] at hb
  norm_num at hb
  have he := Real.exp_one_gt_d9
  have hpos : 0 < Real.exp 1 + Real.exp (-1) := by positivity
  have hinv : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  rw [hinv] at hb hpos
  set e := Real.exp 1 with he'
  have he0 : 0 < e := Real.exp_pos 1
  have h1 : e / (e + e⁻¹) - 1 / 2 = (e ^ 2 - 1) / (2 * (e ^ 2 + 1)) := by field_simp; ring
  have h2 : e⁻¹ / (e + e⁻¹) - 1 / 2 = -((e ^ 2 - 1) / (2 * (e ^ 2 + 1))) := by field_simp; ring
  rw [h1, h2, abs_neg, abs_of_pos (by apply div_pos <;> nlinarith)] at hb
  have hq : (e ^ 2 - 1) / (2 * (e ^ 2 + 1)) ≤ 1 / 4 := by linarith
  rw [div_le_iff₀ (by positivity)] at hq
  nlinarith
