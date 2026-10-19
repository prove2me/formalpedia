-- Prove2me | solution 1 for OAI.ProductCylinder.decreasing_forall
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:56:07.443414+00:00
-- url     : https://prove2.me/submissions/a399b02b-85f8-4d1d-94c3-38f711bcacf4

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder

open OAI OAI.ProductCylinder
universe uE uF uI
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
variable {E : Type uE}
theorem hc_cyl_eq {E : Type*} (J : Finset E) (A : Set (E → Bool))
    (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) :
    A = (J.restrict) ⁻¹' {ξ | OAI.ProductCylinder.extend J ξ ∈ A} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  exact (hA ω _ (fun e he => by simp [OAI.ProductCylinder.extend, he])).symm

theorem hc_cyl_real {E : Type*} (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1) (A : Set (E → Bool))
    (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) :
    (OAI.ProductCylinder.law p).real A =
      (OAI.ProductCylinder.finiteLaw J p).real {ξ | OAI.ProductCylinder.extend J ξ ∈ A} := by
  conv_lhs => rw [hc_cyl_eq J A hA]
  rw [← map_measureReal_apply (Finset.measurable_restrict J) (MeasurableSet.of_discrete)]
  unfold OAI.ProductCylinder.law OAI.ProductCylinder.finiteLaw
  rw [Measure.infinitePi_map_restrict]

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
theorem hc_fa_harris_anti {E : Type*} [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (f g : (E → Bool) → ℝ) (hf : Antitone f) (hg : Antitone g) :
    OAI.FiniteAssociation.mean p f * OAI.FiniteAssociation.mean p g ≤
      OAI.FiniteAssociation.mean p (fun ω => f ω * g ω) := by
  have := hc_fa_harris p (fun ω => - f ω) (fun ω => - g ω) (fun a b h => neg_le_neg (hf h))
    (fun a b h => neg_le_neg (hg h))
  simpa [OAI.FiniteAssociation.mean, integral_neg] using this

theorem hc_ind_anti {E : Type*} (Q : (E → Bool) → Prop) (hQ : Antitone Q) :
    Antitone (fun ω => if Q ω then (1:ℝ) else 0) := by
  intro a b hab
  by_cases hb : Q b
  · have : Q a := hQ hab hb
    simp [hb, this]
  · by_cases ha : Q a <;> simp [ha, hb]

theorem hc_fa_prob_forall {E : Type*} [Fintype E] {I : Type*} (p : E → Set.Icc (0 : ℝ) 1)
    (s : Finset I) (P : I → (E → Bool) → Prop) (hP : ∀ i ∈ s, Antitone (P i)) :
    (∏ i ∈ s, OAI.FiniteAssociation.prob p (P i)) ≤
      OAI.FiniteAssociation.prob p (fun ω => ∀ i ∈ s, P i ω) := by
  induction s using Finset.induction_on with
  | empty =>
    simp [OAI.FiniteAssociation.prob, OAI.FiniteAssociation.mean]
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    have hA : Antitone (fun ω => ∀ i ∈ s, P i ω) := fun a b hab h i hi =>
      hP i (Finset.mem_insert_of_mem hi) hab (h i hi)
    have h0 : 0 ≤ OAI.FiniteAssociation.prob p (P j) :=
      integral_nonneg (fun ω => by dsimp only; split_ifs <;> norm_num)
    have hh := hc_fa_harris_anti p _ _ (hc_ind_anti (P j) (hP j (Finset.mem_insert_self j s)))
      (hc_ind_anti _ hA)
    calc OAI.FiniteAssociation.prob p (P j) * ∏ i ∈ s, OAI.FiniteAssociation.prob p (P i)
        ≤ OAI.FiniteAssociation.prob p (P j) * OAI.FiniteAssociation.prob p (fun ω => ∀ i ∈ s, P i ω) :=
          mul_le_mul_of_nonneg_left (ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))) h0
      _ ≤ _ := hh
      _ = _ := by
        unfold OAI.FiniteAssociation.prob
        congr 1; funext ω
        by_cases h1 : P j ω <;> by_cases h2 : ∀ i ∈ s, P i ω <;> simp [h1, h2, Finset.forall_mem_insert]

theorem hc_pc_decreasing {E : Type*} {I : Type*} [Fintype I] (J : Finset E)
    (p : E → Set.Icc (0 : ℝ) 1) (A : I → Set (E → Bool))
    (hA : ∀ i ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A i ↔ ω ∈ A i))
    (hmono : ∀ i, Antitone (fun ω => ω ∈ A i)) :
    (∏ i, (OAI.ProductCylinder.law p).real (A i)) ≤ (OAI.ProductCylinder.law p).real (⋂ i, A i) := by
  have hI : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ ⋂ i, A i ↔ ω ∈ ⋂ i, A i) := by
    intro ω ω' h
    simp only [Set.mem_iInter]
    exact forall_congr' (fun i => hA i ω ω' h)
  rw [hc_cyl_real J p _ hI]
  simp only [hc_cyl_real J p _ (hA _)]
  let q : J → Set.Icc (0 : ℝ) 1 := fun e => p e
  have hprob : ∀ B : Set (J → Bool), (OAI.ProductCylinder.finiteLaw J p).real B =
      OAI.FiniteAssociation.prob q (fun ξ => ξ ∈ B) := by
    intro B
    unfold OAI.FiniteAssociation.prob OAI.FiniteAssociation.mean
    have : (fun ξ : J → Bool => if ξ ∈ B then (1:ℝ) else 0) = B.indicator 1 := by
      funext ξ; simp [Set.indicator_apply]
    rw [this, integral_indicator_one MeasurableSet.of_discrete]
    rfl
  simp only [hprob]
  have hmon : ∀ ξ ξ' : J → Bool, ξ ≤ ξ' → OAI.ProductCylinder.extend J ξ ≤ OAI.ProductCylinder.extend J ξ' := by
    intro ξ ξ' h e
    unfold OAI.ProductCylinder.extend
    split_ifs with he
    · exact h _
    · exact le_rfl
  have := hc_fa_prob_forall q Finset.univ (fun i ξ => OAI.ProductCylinder.extend J ξ ∈ A i)
    (fun i _ ξ ξ' h => hmono i (hmon ξ ξ' h))
  convert this using 2
  · simp
  · simp

theorem solution {I : Type uI} [Fintype I] (J : Finset E)
    (p : E → Set.Icc (0 : ℝ) 1) (A : I → Set (E → Bool))
    (hA : ∀ i ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A i ↔ ω ∈ A i))
    (hmono : ∀ i, Antitone (fun ω => ω ∈ A i)) :
    (∏ i, (law p).real (A i)) ≤ (law p).real (⋂ i, A i) := by
  exact hc_pc_decreasing J p A hA hmono

