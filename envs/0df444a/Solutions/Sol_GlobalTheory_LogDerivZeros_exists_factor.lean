-- Prove2me | solution 1 for GlobalTheory.LogDerivZeros.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:19:01.312653+00:00
-- url     : https://prove2.me/submissions/99419a10-d1c7-4c7c-a5b4-8688630675bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsFactorOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Theorems.Thm_GlobalTheory_LogDerivZeros_exists_factor_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.LogDerivZeros
namespace GlobalTheory.LogDerivZeros
theorem _root_.solution {U : Set ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (S : Finset ℂ)
    (hS : ∀ w ∈ S, w ∈ U) (ho : ∀ w ∈ S, analyticOrderAt f w ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      (∀ z, f z = (∏ w ∈ S, (z - w) ^ (analyticOrderNatAt f w)) * g z) ∧ ∀ w ∈ S, g w ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨f, hf, by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨g, hg, hfg, hg0⟩ := ih (fun w hw => hS w (Finset.mem_insert_of_mem hw))
      (fun w hw => ho w (Finset.mem_insert_of_mem hw))
    have haU : a ∈ U := hS a (Finset.mem_insert_self _ _)
    have hP : AnalyticAt ℂ (fun z : ℂ => ∏ w ∈ S, (z - w) ^ (analyticOrderNatAt f w)) a := by
      fun_prop
    have hP0 : (∏ w ∈ S, (a - w) ^ (analyticOrderNatAt f w)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun w hw => pow_ne_zero _ (sub_ne_zero.2 (by rintro rfl; exact ha hw))
    have hord : analyticOrderAt f a = analyticOrderAt g a := by
      have e : f = (fun z : ℂ => ∏ w ∈ S, (z - w) ^ (analyticOrderNatAt f w)) * g := funext hfg
      have := analyticOrderAt_mul hP (hg a haU)
      rw [← e, hP.analyticOrderAt_eq_zero.2 hP0, zero_add] at this
      exact this
    have hordn : analyticOrderNatAt g a = analyticOrderNatAt f a := by
      simp [analyticOrderNatAt, hord]
    obtain ⟨h, hh, hgh, hh0⟩ := exists_factor_one hg haU (hord ▸ ho a (Finset.mem_insert_self _ _))
    refine ⟨h, hh, fun z => ?_, fun w hw => ?_⟩
    · rw [Finset.prod_insert ha, hfg z, hgh z, hordn]; ring
    · rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hh0
      · intro h0
        exact hg0 w hw (by rw [hgh w, h0, mul_zero])
end GlobalTheory.LogDerivZeros
