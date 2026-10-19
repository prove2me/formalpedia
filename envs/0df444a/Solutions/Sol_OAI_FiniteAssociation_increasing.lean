-- Prove2me | solution 1 for OAI.FiniteAssociation.increasing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:53:12.697324+00:00
-- url     : https://prove2.me/submissions/55482226-7e87-4273-bd70-e99b5cd85265

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder

open OAI OAI.FiniteAssociation
universe uE uF uI
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
universe u
variable {E : Type u}
theorem hc_fa_singleton {E : Type*} [Fintype E] (p : E → Set.Icc (0 : ℝ) 1) (ω : E → Bool) :
    (OAI.FiniteAssociation.law p).real {ω} = ∏ e, (if ω e then (p e : ℝ) else 1 - (p e : ℝ)) := by
  have hs : ({ω} : Set (E → Bool)) = Set.univ.pi (fun e => {ω e}) := by
    ext η; simp [funext_iff]
  rw [hs, measureReal_def, OAI.FiniteAssociation.law, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  cases h : ω e
  · rw [← measureReal_def, bernoulliMeasure_real_apply_of_notMem_of_mem _ (measurableSet_singleton _) (by simp) (by simp)]
    simp
  · rw [← measureReal_def, bernoulliMeasure_real_apply_of_mem_of_notMem _ (measurableSet_singleton _) (by simp) (by simp)]
    simp

theorem hc_fa_harris {E : Type*} [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (f g : (E → Bool) → ℝ) (hf : Monotone f) (hg : Monotone g) :
    OAI.FiniteAssociation.mean p f * OAI.FiniteAssociation.mean p g ≤
      OAI.FiniteAssociation.mean p (fun ω => f ω * g ω) := by
  let μ : (E → Bool) → ℝ := fun ω => (OAI.FiniteAssociation.law p).real {ω}
  have hmean : ∀ h : (E → Bool) → ℝ, OAI.FiniteAssociation.mean p h = ∑ ω, μ ω * h ω := by
    intro h
    unfold OAI.FiniteAssociation.mean
    rw [integral_fintype Integrable.of_finite]
    rfl
  have hS1 : ∑ ω, μ ω = 1 := by
    have := hmean (fun _ => 1)
    simp only [OAI.FiniteAssociation.mean, integral_const, mul_one] at this
    rw [← this]; simp
  have hμ0 : 0 ≤ μ := fun ω => measureReal_nonneg
  have hμ : ∀ a b, μ a * μ b ≤ μ (a ⊓ b) * μ (a ⊔ b) := by
    intro a b
    simp only [μ, hc_fa_singleton, ← Finset.prod_mul_distrib]
    refine le_of_eq (Finset.prod_congr rfl (fun e _ => ?_))
    simp only [Pi.inf_apply, Pi.sup_apply]
    by_cases ha : a e <;> by_cases hb : b e <;> simp [ha, hb] <;> ring
  let cf : ℝ := - ∑ ω, |f ω|
  let cg : ℝ := - ∑ ω, |g ω|
  have hcf : ∀ ω, cf ≤ f ω := fun ω => by
    have := Finset.single_le_sum (f := fun ω => |f ω|) (fun ω _ => abs_nonneg _) (Finset.mem_univ ω)
    simp only [cf]; linarith [neg_abs_le (f ω)]
  have hcg : ∀ ω, cg ≤ g ω := fun ω => by
    have := Finset.single_le_sum (f := fun ω => |g ω|) (fun ω _ => abs_nonneg _) (Finset.mem_univ ω)
    simp only [cg]; linarith [neg_abs_le (g ω)]
  have key := fkg (μ := μ) (f := fun ω => f ω - cf) (g := fun ω => g ω - cg) hμ0
    (fun ω => sub_nonneg.mpr (hcf ω)) (fun ω => sub_nonneg.mpr (hcg ω))
    (fun a b hab => sub_le_sub_right (hf hab) _) (fun a b hab => sub_le_sub_right (hg hab) _) hμ
  rw [hmean, hmean, hmean]
  have e1 : ∑ a, μ a * (f a - cf) = (∑ a, μ a * f a) - cf * ∑ a, μ a := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun a _ => by ring)
  have e2 : ∑ a, μ a * (g a - cg) = (∑ a, μ a * g a) - cg * ∑ a, μ a := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun a _ => by ring)
  have e3 : ∑ a, μ a * ((f a - cf) * (g a - cg)) = (∑ a, μ a * (f a * g a)) - cg * (∑ a, μ a * f a)
      - cf * (∑ a, μ a * g a) + cf * cg * ∑ a, μ a := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  rw [e1, e2, e3, hS1] at key
  nlinarith

theorem solution [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (f g : (E → Bool) → ℝ) (hf : Monotone f) (hg : Monotone g) :
    mean p f * mean p g ≤ mean p (fun ω => f ω * g ω) := by
  exact hc_fa_harris p f g hf hg

