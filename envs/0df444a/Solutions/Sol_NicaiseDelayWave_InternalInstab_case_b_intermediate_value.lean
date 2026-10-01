-- Prove2me | solution 1 for NicaiseDelayWave.InternalInstab.case_b_intermediate_value
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:21:12.35265+00:00
-- url     : https://prove2.me/submissions/5aa7e3d1-c478-409b-a5cf-c46cf11eba99

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

theorem solution (μ₁ μ₂ Λ : ℝ) (l : ℕ) (hμ₁ : 0 < μ₁) (hμ : μ₁ < μ₂)
    (hΛ : 0 < Λ) :
    ∃ α : ℝ, 0 < α ∧ α < (μ₂-μ₁)/2 ∧
      0 < Real.log (μ₂/(μ₁+2*α))/α ∧
      μ₂*Real.exp (-α*(Real.log (μ₂/(μ₁+2*α))/α))=2*α+μ₁ ∧
      α^2+(2*l+1)^2*Real.pi^2/(Real.log (μ₂/(μ₁+2*α))/α)^2=Λ^2 := by
  let b := (μ₂-μ₁)/2
  let f : ℝ → ℝ := fun a => (a^2-Λ^2)*(Real.log (μ₂/(μ₁+2*a)))^2+(2*l+1)^2*Real.pi^2*a^2
  have hb : 0 < b := by dsimp [b]; linarith
  have hμ₂ : 0 < μ₂ := lt_trans hμ₁ hμ
  have hd : ∀ a ∈ Set.Icc 0 b, 0 < μ₁+2*a := by
    intro a ha
    linarith [ha.1]
  have hlog : ContinuousOn (fun a : ℝ => Real.log (μ₂/(μ₁+2*a))) (Set.Icc 0 b) := by
    apply ContinuousOn.log
    · exact continuousOn_const.div (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) (fun a ha => ne_of_gt (hd a ha))
    · exact fun a ha => ne_of_gt (div_pos hμ₂ (hd a ha))
  have hf : ContinuousOn f (Set.Icc 0 b) := by
    exact ((continuousOn_id.pow 2).sub continuousOn_const).mul (hlog.pow 2) |>.add
      (continuousOn_const.mul (continuousOn_id.pow 2))
  have hf0 : f 0 < 0 := by
    have hlog0 : 0 < Real.log (μ₂/μ₁) := Real.log_pos ((one_lt_div hμ₁).mpr hμ)
    dsimp [f]
    simp only [zero_pow (by decide : 2 ≠ 0),zero_sub,mul_zero,add_zero,zero_add]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hΛ)) (sq_pos_of_pos hlog0)
  have hfb : 0 < f b := by
    have hd' : μ₁+2*b=μ₂ := by dsimp [b]; ring
    dsimp [f]
    rw [hd',div_self (ne_of_gt hμ₂),Real.log_one]
    simp only [zero_pow (by decide : 2 ≠ 0),mul_zero,zero_add]
    positivity
  obtain ⟨a,ha,hfa⟩ := intermediate_value_Icc (le_of_lt hb) hf ⟨hf0.le,hfb.le⟩
  have ha0 : 0 < a := by
    by_contra hh
    have he : a=0 := le_antisymm (le_of_not_gt hh) ha.1
    subst a
    linarith
  have hab : a < b := by
    by_contra hh
    have he : a=b := le_antisymm ha.2 (le_of_not_gt hh)
    subst a
    linarith
  have hda : 0 < μ₁+2*a := hd a ha
  have hla : 0 < Real.log (μ₂/(μ₁+2*a)) := by
    apply Real.log_pos
    apply (one_lt_div hda).mpr
    dsimp [b] at hab
    linarith
  refine ⟨a,ha0,hab,div_pos hla ha0,?_,?_⟩
  · rw [show -a*(Real.log (μ₂/(μ₁+2*a))/a) = -Real.log (μ₂/(μ₁+2*a)) by field_simp]
    rw [Real.exp_neg,Real.exp_log (div_pos hμ₂ hda)]
    field_simp
    ring
  · dsimp [f] at hfa
    have hz : (Real.log (μ₂/(μ₁+2*a))/a)^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (div_pos hla ha0))
    have he : (2*l+1)^2*Real.pi^2/(Real.log (μ₂/(μ₁+2*a))/a)^2=Λ^2-a^2 := by
      apply (div_eq_iff hz).mpr
      field_simp [ne_of_gt ha0]
      nlinarith [hfa]
    linarith
