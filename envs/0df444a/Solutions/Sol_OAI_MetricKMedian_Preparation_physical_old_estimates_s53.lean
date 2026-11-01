-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.physical_old_estimates_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:20:18.275034+00:00
-- url     : https://prove2.me/submissions/d078fe4f-6c29-49d8-9550-cc55439562d4

import Mathlib
import Definitions.Def_OAIQ053K032
import Definitions.Def_OAIQ053K036

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

omit [Fintype Ξ] in
theorem variance_const (μ : FiniteLaw Ω) (c : ℝ) : μ.variance (fun _ => c)=0 := by
  rw [variance_eq, expect_const, expect_const, sub_self]

end MetricKMedian.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_FilteredMoments
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

theorem restricted_moments (μ : FiniteLaw Ω) (Y : Ω → I → ℝ) (q : I → ℝ)
    (A : Finset I) {g : ℝ} (hm : ∀ i, μ.expect (fun ω => Y ω i)=q i)
    (hv : ∀ i, μ.variance (fun ω => Y ω i) ≤ g*q i)
    (hp : ∀ i j, i ≠ j → μ.expect (fun ω => Y ω i*Y ω j) ≤ q i*q j) :
    μ.expect (fun ω => ∑ i ∈ A, Y ω i)=(∑ i ∈ A, q i) ∧
    μ.variance (fun ω => ∑ i ∈ A, Y ω i) ≤ g*(∑ i ∈ A, q i) := by
  let X := fun i ω => if i ∈ A then Y ω i else 0
  let m := fun i => if i ∈ A then q i else 0
  have hm' : ∀ i, μ.expect (X i)=m i := by
    intro i
    by_cases hi : i ∈ A
    · simpa only [X,m,ite_eq_left hi] using hm i
    · simp only [X,m,ite_eq_right hi,expect_const]
  have hv' : ∀ i, μ.variance (X i) ≤ g*m i := by
    intro i
    by_cases hi : i ∈ A
    · simpa only [X,m,ite_eq_left hi] using hv i
    · simp only [X,m,ite_eq_right hi,mul_zero,variance_eq,expect_const,zero_pow (by decide : 2 ≠ 0),sub_zero,le_refl]
  have hp' : ∀ i j, i ≠ j → μ.expect (fun ω => X i ω*X j ω) ≤ m i*m j := by
    intro i j hij
    by_cases hi : i ∈ A <;> by_cases hj : j ∈ A
    · simpa only [X,m,ite_eq_left hi,ite_eq_left hj] using hp i j hij
    all_goals simp only [X,m,hi,hj,ite_true,ite_false,mul_zero,zero_mul,expect_const,le_refl]
  have he := μ.variance_sum_le X m (fun i => g*m i) hm' hv' hp'
  simp only [X,m,sum_ite_mem,univ_inter,← mul_sum] at he
  refine ⟨?_,he⟩
  rw [expect_sum]
  simp only [hm]

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteJoint
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

theorem expect_joint (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) (f : Ω × Ξ → ℝ) :
    (joint μ κ).expect f=μ.expect (fun ω => (κ ω).expect (fun ξ => f (ω, ξ))) := by
  simp only [expect, joint, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparationInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

omit [Fintype I] [Fintype T] [DecidableEq T] in

theorem rescaled_subset_mean {Ξ : Type} [Fintype Ξ] (μ : FiniteLaw Ξ)
    (Y : Ξ → T × I → ℝ) (P : T → Finset I) (y : I → ℝ) (p p' : T → ℝ)
    (hm : ∀ t i, μ.expect (fun ξ => Y ξ (t,i))=if i ∈ P t then p' t*y i/p t else 0)
    (F : Finset I) (d : I → ℝ) (t : T) :
    μ.expect (fun ξ => ∑ i ∈ F, Y ξ (t,i)*d i)=
      (p' t/p t)*(∑ i ∈ F ∩ P t, y i*d i) := by
  rw [FiniteLaw.expect_sum]
  simp_rw [FiniteLaw.expect_mul_right,hm]
  have he : ∀ i, (if i ∈ P t then p' t*y i/p t else 0)*d i=
      if i ∈ P t then (p' t/p t)*(y i*d i) else 0 := by
    intro i
    split_ifs <;> ring
  simp_rw [he]
  rw [sum_ite_mem,mul_sum]

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparationOldCost
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T Ω Ξ : Type} [Fintype I] [DecidableEq I]
  [Fintype T] [DecidableEq T] [Fintype Ω] [Fintype Ξ]

omit [DecidableEq T] in

theorem preparation_old_cost (ν : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ)
    (P : T → Finset I) (y d : I → ℝ) (p : T → ℝ) (p' : Ω → T → ℝ)
    (U : Ω → I → ℝ) (Y : Ω → Ξ → T × I → ℝ) (F : Finset I) {p₀ : ℝ}
    (hy : ∀ i, 0 ≤ y i) (hd : ∀ i, 0 ≤ d i) (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (hp : ∀ t, p₀ ≤ p t) (hcap : ∀ ω t, p' ω t ≤ 1)
    (hUm : ∀ i, ν.expect (fun ω => U ω i)=y i)
    (hYm : ∀ ω t i, (κ ω).expect (fun ξ => Y ω ξ (t,i))=
      if i ∈ P t then p' ω t*y i/p t else 0) :
    (ν.joint κ).expect (fun z =>
      (∑ i ∈ F ∩ SupplierStars.outside P, U z.1 i*d i)+
      (∑ t, ∑ i ∈ F, Y z.1 z.2 (t,i)*d i)) ≤ (∑ i ∈ F, y i*d i)/p₀ := by
  let a := fun t => ∑ i ∈ F ∩ P t, y i*d i
  let u := ∑ i ∈ F ∩ SupplierStars.outside P, y i*d i
  have ha : ∀ t, 0 ≤ a t := fun t => sum_nonneg (fun i _ => mul_nonneg (hy i) (hd i))
  have hu : 0 ≤ u := sum_nonneg (fun i _ => mul_nonneg (hy i) (hd i))
  have hpart : u+(∑ t, a t)=∑ i ∈ F, y i*d i := SupplierStars.mass_partition (fun i => y i*d i) P hP F
  have hinner : ∀ ω, (κ ω).expect (fun ξ => ∑ t, ∑ i ∈ F, Y ω ξ (t,i)*d i)=
      ∑ t, (p' ω t/p t)*a t := by
    intro ω
    rw [FiniteLaw.expect_sum]
    exact sum_congr rfl (fun t _ => rescaled_subset_mean (κ ω) (Y ω) P y p (p' ω) (hYm ω) F d t)
  have hbound : ∀ ω, (∑ t, (p' ω t/p t)*a t) ≤ (∑ t, a t)/p₀ := by
    intro ω
    rw [sum_div]
    apply sum_le_sum
    intro t _
    have hpp : 0 < p t := hp₀.trans_le (hp t)
    calc
      (p' ω t/p t)*a t ≤ (1/p t)*a t := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hcap ω t) hpp.le) (ha t)
      _ ≤ (1/p₀)*a t := mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hp₀ (hp t)) (ha t)
      _ = a t/p₀ := by ring
  have hout : ν.expect (fun ω => ∑ i ∈ F ∩ SupplierStars.outside P, U ω i*d i)=u := by
    rw [FiniteLaw.expect_sum]
    simp only [FiniteLaw.expect_mul_right,hUm,u]
  rw [FiniteLaw.expect_joint]
  simp only [FiniteLaw.expect_add,FiniteLaw.expect_const,hinner]
  rw [hout]
  have he := (ν.expect_mono hbound).trans_eq (ν.expect_const _)
  have hue : u ≤ u/p₀ := (le_div_iff₀ hp₀).mpr (mul_le_of_le_one_right hu hp₀1)
  calc
    _ ≤ u/p₀+(∑ t, a t)/p₀ := add_le_add hue he
    _ = (u+∑ t, a t)/p₀ := (add_div _ _ _).symm
    _ = _ := by rw [hpart]

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparationNoise
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]

theorem conditional_shortfall (ν : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ)
    (U B : Ω → ℝ) (P : Ω → Ξ → ℝ) {u b g v A : ℝ}
    (hab : u+b=1) (hU : ν.expect U=u) (hUv : ν.variance U ≤ g)
    (hPm : ∀ ω, (κ ω).expect (P ω)=B ω)
    (hPv : ∀ ω, (κ ω).variance (P ω) ≤ v)
    (hB : ν.expect (fun ω => |B ω-b|) ≤ A) :
    (ν.joint κ).expect (fun z => max (1-U z.1-P z.1 z.2) 0) ≤
      Real.sqrt g+Real.sqrt v+A := by
  have hpoint : ∀ z : Ω × Ξ, max (1-U z.1-P z.1 z.2) 0 ≤
      |U z.1-u|+|P z.1 z.2-B z.1|+|B z.1-b| := by
    intro z
    apply max_le
    · have he : 1-U z.1-P z.1 z.2= -(U z.1-u)-(P z.1 z.2-B z.1)-(B z.1-b) := by
        linarith only [hab]
      rw [he]
      have h1 := neg_le_abs (U z.1-u)
      have h2 := neg_le_abs (P z.1 z.2-B z.1)
      have h3 := neg_le_abs (B z.1-b)
      linarith only [h1,h2,h3]
    · positivity
  have hu : ν.expect (fun ω => |U ω-u|) ≤ Real.sqrt g := by
    rw [← hU]
    exact (ν.expect_abs_centered_le_sqrt U).trans (Real.sqrt_le_sqrt hUv)
  have hp : ∀ ω, (κ ω).expect (fun ξ => |P ω ξ-B ω|) ≤ Real.sqrt v := by
    intro ω
    rw [← hPm ω]
    exact ((κ ω).expect_abs_centered_le_sqrt (P ω)).trans (Real.sqrt_le_sqrt (hPv ω))
  have he := (ν.joint κ).expect_mono hpoint
  simp only [FiniteLaw.expect_joint,FiniteLaw.expect_add,FiniteLaw.expect_const] at he
  have hp' : ν.expect (fun ω => (κ ω).expect (fun ξ => |P ω ξ-B ω|)) ≤ Real.sqrt v :=
    (ν.expect_mono hp).trans_eq (ν.expect_const _)
  rw [FiniteLaw.expect_joint]
  exact he.trans (add_le_add (add_le_add hu hp') hB)

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparationRescaling
attribute [-simp] _root_.OAI.MetricKMedian.RationalLaw.real_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {T Ω : Type*} [Fintype T] [Fintype Ω]

theorem rescaling_total_noise (μ : FiniteLaw Ω) (a p : T → ℝ)
    (p' : Ω → T → ℝ) {p₀ A : ℝ} (hp₀ : 0 < p₀)
    (ha : ∀ t, 0 ≤ a t) (has : ∑ t, a t ≤ 1) (hp : ∀ t, p₀ ≤ p t)
    (hA : 0 ≤ A) (hdev : ∀ t, μ.expect (fun ω => |p' ω t-p t|) ≤ A) :
    μ.expect (fun ω => |(∑ t, a t*p' ω t/p t)-(∑ t, a t)|) ≤ A/p₀ := by
  have hpp : ∀ t, 0 < p t := fun t => hp₀.trans_le (hp t)
  have hpoint : ∀ ω, |(∑ t, a t*p' ω t/p t)-(∑ t, a t)| ≤
      ∑ t, (a t/p t)*|p' ω t-p t| := by
    intro ω
    have he : (∑ t, a t*p' ω t/p t)-(∑ t, a t)=∑ t, (a t/p t)*(p' ω t-p t) := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro t _
      field_simp [(hpp t).ne']
    rw [he]
    apply (abs_sum_le_sum_abs _ _).trans_eq
    apply sum_congr rfl
    intro t _
    rw [abs_mul,abs_of_nonneg (div_nonneg (ha t) (hpp t).le)]
  have he := μ.expect_mono hpoint
  rw [FiniteLaw.expect_sum] at he
  simp only [FiniteLaw.expect_mul] at he
  have hs : (∑ t, (a t/p t)*μ.expect (fun ω => |p' ω t-p t|)) ≤ (∑ t, a t)*(A/p₀) := by
    rw [sum_mul]
    apply sum_le_sum
    intro t _
    calc
      _ ≤ (a t/p t)*A := mul_le_mul_of_nonneg_left (hdev t) (div_nonneg (ha t) (hpp t).le)
      _ ≤ (a t/p₀)*A := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (ha t) hp₀ (hp t)) hA
      _ = _ := by ring
  exact (he.trans hs).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right has (div_nonneg hA hp₀.le))

theorem rescaled_mass_bound (a p p' : T → ℝ) {p₀ : ℝ} (hp₀ : 0 < p₀)
    (ha : ∀ t, 0 ≤ a t) (has : ∑ t, a t ≤ 1) (hp : ∀ t, p₀ ≤ p t)
    (hp' : ∀ t, p' t ≤ 1) : (∑ t, a t*p' t/p t) ≤ 1/p₀ := by
  calc
    _ ≤ ∑ t, a t/p₀ := by
      apply sum_le_sum
      intro t _
      calc
        a t*p' t/p t ≤ a t/p t := div_le_div_of_nonneg_right
          ((mul_le_mul_of_nonneg_left (hp' t) (ha t)).trans_eq (mul_one _)) (hp₀.trans_le (hp t)).le
        _ ≤ a t/p₀ := div_le_div_of_nonneg_left (ha t) hp₀ (hp t)
    _ = (∑ t, a t)/p₀ := (sum_div _ _ _).symm
    _ ≤ 1/p₀ := div_le_div_of_nonneg_right has hp₀.le

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparationSubsetNoise
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T Ω Ξ : Type} [Fintype I] [DecidableEq I]
  [Fintype T] [DecidableEq T] [Fintype Ω] [Fintype Ξ]

omit [Fintype Ω] in

theorem bundle_subset_moments (μ : FiniteLaw Ξ) (Y : Ξ → T × I → ℝ)
    (P : T → Finset I) (y : I → ℝ) (p p' : T → ℝ) (F : Finset I) (g : ℝ)
    (hm : ∀ t i, μ.expect (fun ξ => Y ξ (t,i))=if i ∈ P t then p' t*y i/p t else 0)
    (hv : ∀ a, μ.variance (fun ξ => Y ξ a) ≤ g*(if a.2 ∈ P a.1 then p' a.1*y a.2/p a.1 else 0))
    (hc : ∀ a b, a ≠ b → μ.expect (fun ξ => Y ξ a*Y ξ b) ≤
      (if a.2 ∈ P a.1 then p' a.1*y a.2/p a.1 else 0)*
      (if b.2 ∈ P b.1 then p' b.1*y b.2/p b.1 else 0)) :
    μ.expect (fun ξ => ∑ t, ∑ i ∈ F, Y ξ (t,i))=
      (∑ t, (∑ i ∈ F ∩ P t, y i)*p' t/p t) ∧
    μ.variance (fun ξ => ∑ t, ∑ i ∈ F, Y ξ (t,i)) ≤
      g*(∑ t, (∑ i ∈ F ∩ P t, y i)*p' t/p t) := by
  classical
  let A : Finset (T × I) := univ.filter (fun a => a.2 ∈ F)
  let m : T × I → ℝ := fun a => if a.2 ∈ P a.1 then p' a.1*y a.2/p a.1 else 0
  have he := μ.restricted_moments Y m A (fun a => hm a.1 a.2) hv hc
  have hs : ∀ ξ, (∑ a ∈ A, Y ξ a)=∑ t, ∑ i ∈ F, Y ξ (t,i) := by
    intro ξ
    simp only [A,sum_filter,Fintype.sum_prod_type,sum_ite_mem,univ_inter]
  have hs' : (∑ a ∈ A, m a)=∑ t, (∑ i ∈ F ∩ P t, y i)*p' t/p t := by
    simp only [A,m,sum_filter,Fintype.sum_prod_type,sum_ite_mem,univ_inter,← sum_div,← mul_sum]
    apply sum_congr rfl
    intro t _
    ring
  simpa only [hs,hs'] using he

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_ShortfallByDeviation
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T Ω Ξ : Type} [Fintype I] [DecidableEq I]
  [Fintype T] [DecidableEq T] [Fintype Ω] [Fintype Ξ]

theorem shortfall_from_deviation (ν : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ)
    (P : T → Finset I) (y : I → ℝ) (p : T → ℝ)
    (p' : Ω → T → ℝ)
    (U : Ω → I → ℝ) (Y : Ω → Ξ → T × I → ℝ)
    (F : Finset I) {g γ p₀ : ℝ}
    (hg : 0 ≤ g) (hγ : 0 ≤ γ) (hp₀ : 0 < p₀)
    (hy : ∀ i, 0 ≤ y i) (hF : ∑ i ∈ F, y i=1)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (hp : ∀ t, p₀ ≤ p t)
    (hcap : ∀ ω t, p' ω t ≤ 1)
    (hdev : ∀ t, ν.expect (fun ω => |p' ω t-p t|) ≤ γ+Real.sqrt (g*(1+γ)))
    (hUm : ∀ i, ν.expect (fun ω => U ω i)=y i)
    (hUv : ∀ i, ν.variance (fun ω => U ω i) ≤ g*y i)
    (hUc : ∀ i j, i ≠ j → ν.expect (fun ω => U ω i*U ω j) ≤ y i*y j)
    (hYm : ∀ ω t i, (κ ω).expect (fun ξ => Y ω ξ (t,i))=
      if i ∈ P t then p' ω t*y i/p t else 0)
    (hYv : ∀ ω a, (κ ω).variance (fun ξ => Y ω ξ a) ≤
      g*(if a.2 ∈ P a.1 then p' ω a.1*y a.2/p a.1 else 0))
    (hYc : ∀ ω a b, a ≠ b → (κ ω).expect (fun ξ => Y ω ξ a*Y ω ξ b) ≤
      (if a.2 ∈ P a.1 then p' ω a.1*y a.2/p a.1 else 0)*
      (if b.2 ∈ P b.1 then p' ω b.1*y b.2/p b.1 else 0)) :
    (ν.joint κ).expect (fun z => max
      (1-(∑ i ∈ F ∩ SupplierStars.outside P, U z.1 i)-(∑ t, ∑ i ∈ F, Y z.1 z.2 (t,i))) 0)
      ≤ Real.sqrt g+Real.sqrt (g/p₀)+(γ+Real.sqrt (g*(1+γ)))/p₀ := by
  classical
  let a := fun t => ∑ i ∈ F ∩ P t, y i
  let u := ∑ i ∈ F ∩ SupplierStars.outside P, y i
  have ha : ∀ t, 0 ≤ a t := fun t => sum_nonneg (fun i _ => hy i)
  have hu : 0 ≤ u := sum_nonneg (fun i _ => hy i)
  have hpart : u+(∑ t, a t)=1 := (SupplierStars.mass_partition y P hP F).trans hF
  have has : ∑ t, a t ≤ 1 := by linarith only [hpart,hu]
  have hu1 : u ≤ 1 := by linarith only [hpart,sum_nonneg (fun t (_ : t ∈ univ) => ha t)]
  obtain ⟨hmean,hvar⟩ := ν.restricted_moments U y (F ∩ SupplierStars.outside P) hUm hUv hUc
  have hvar' : ν.variance (fun ω => ∑ i ∈ F ∩ SupplierStars.outside P, U ω i) ≤ g :=
    hvar.trans ((mul_le_mul_of_nonneg_left hu1 hg).trans_eq (mul_one _))
  have hbundle := fun ω => bundle_subset_moments (κ ω) (Y ω) P y p (p' ω) F g
    (hYm ω) (hYv ω) (hYc ω)
  have hB : ν.expect (fun ω => |(∑ t, a t*p' ω t/p t)-(∑ t, a t)|) ≤
      (γ+Real.sqrt (g*(1+γ)))/p₀ := by
    apply rescaling_total_noise ν a p p' hp₀ ha has hp (by positivity)
    exact hdev
  apply conditional_shortfall ν κ
    (fun ω => ∑ i ∈ F ∩ SupplierStars.outside P, U ω i)
    (fun ω => ∑ t, a t*p' ω t/p t)
    (fun ω ξ => ∑ t, ∑ i ∈ F, Y ω ξ (t,i)) hpart hmean hvar'
    (fun ω => (hbundle ω).1) _ hB
  intro ω
  calc
    _ ≤ g*(∑ t, a t*p' ω t/p t) := (hbundle ω).2
    _ ≤ g*(1/p₀) := mul_le_mul_of_nonneg_left
      (rescaled_mass_bound a p (p' ω) hp₀ ha has hp (hcap ω)) hg
    _ = g/p₀ := by ring

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_CoupledNoise
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

theorem nominal_extension (P A : T → Finset I) (y : I → ℝ) (p c : T → ℝ)
    {g γ B : ℝ} {Δ : ℕ} (hg : 0 ≤ g) (hy : ∀ i, 0 ≤ y i)
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ) :
    let U := fun ω i => if i ∈ outside P then L.N ω (.inl i) else y i
    (∀ i, L.ν.expect (fun ω => U ω i)=y i) ∧
    (∀ i, L.ν.variance (fun ω => U ω i) ≤ g*y i) ∧
    (∀ i j, i ≠ j → L.ν.expect (fun ω => U ω i*U ω j) ≤ y i*y j) := by
  classical
  dsimp only
  have hm : ∀ i, i ∈ outside P → L.ν.expect (fun ω => L.N ω (.inl i))=y i := by
    intro i hi
    simpa only [weight,ite_eq_left hi] using L.nominal_mean (.inl i)
  refine ⟨?_,?_,?_⟩
  · intro i
    by_cases hi : i ∈ outside P
    · simp only [ite_eq_left hi,hm i hi]
    · simp only [ite_eq_right hi,FiniteLaw.expect_const]
  · intro i
    by_cases hi : i ∈ outside P
    · simp only [ite_eq_left hi]
      simpa only [weight,ite_eq_left hi] using L.nominal_variance (.inl i)
    · simp only [ite_eq_right hi,FiniteLaw.variance_const]
      exact mul_nonneg hg (hy i)
  · intro i j hij
    by_cases hi : i ∈ outside P <;> by_cases hj : j ∈ outside P
    · simp only [ite_eq_left hi,ite_eq_left hj]
      simpa only [weight,ite_eq_left hi,ite_eq_left hj] using L.nominal_pair (.inl i) (.inl j)
        (fun h => hij (Sum.inl.inj h))
    · simp only [ite_eq_left hi,ite_eq_right hj,FiniteLaw.expect_mul_right,hm i hi,le_refl]
    · simp only [ite_eq_right hi,ite_eq_left hj,FiniteLaw.expect_mul,hm j hj,le_refl]
    · simp only [ite_eq_right hi,ite_eq_right hj,FiniteLaw.expect_const,le_refl]

theorem coupled_old_estimates (P A : T → Finset I) (y : I → ℝ) (p c : T → ℝ)
    {g γ B p₀ : ℝ} {Δ : ℕ} (hg : 0 ≤ g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (hy : ∀ i, 0 ≤ y i) (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1) (hp : ∀ t, p₀ ≤ p t)
    (_hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (F : Finset I) (hF : ∑ i ∈ F, y i=1) (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    let μ := L.ν.joint L.κ
    let U := fun ω i => if i ∈ outside P then L.N ω (.inl i) else y i
    let Y := fun ω ξ ti => g*(L.C ω ξ ti:ℝ)
    μ.expect (fun z => max
      (1-(∑ i ∈ F ∩ outside P, U z.1 i)-(∑ t, ∑ i ∈ F, Y z.1 z.2 (t,i))) 0) ≤
      Real.sqrt g+Real.sqrt (g/p₀)+(γ+Real.sqrt (g*(1+γ)))/p₀ ∧
    μ.expect (fun z => (∑ i ∈ F ∩ outside P, U z.1 i*d i)+
      (∑ t, ∑ i ∈ F, Y z.1 z.2 (t,i)*d i)) ≤ (∑ i ∈ F, y i*d i)/p₀ := by
  classical
  dsimp only
  obtain ⟨hUm,hUv,hUp⟩ := nominal_extension P A y p c hg hy L
  have hcap : ∀ ω t, g*(L.K ω t:ℝ) ≤ 1 := fun ω t =>
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (L.total_cap ω t)) hg).trans_eq hunit
  have hdev : ∀ t, L.ν.expect (fun ω => |g*(L.K ω t:ℝ)-p t|) ≤ γ+Real.sqrt (g*(1+γ)) := by
    intro t
    apply (L.total_deviation t).trans
    apply add_le_add
    · exact (mul_le_mul_of_nonneg_left (hc1 t) hγ).trans_eq (mul_one _)
    · exact Real.sqrt_le_sqrt ((mul_le_mul_of_nonneg_left (hc1 t)
        (mul_nonneg hg (by linarith only [hγ]))).trans_eq (mul_one _))
  constructor
  · exact shortfall_from_deviation L.ν L.κ P y p
      (fun ω t => g*(L.K ω t:ℝ))
      (fun ω i => if i ∈ outside P then L.N ω (.inl i) else y i)
      (fun ω ξ ti => g*(L.C ω ξ ti:ℝ)) F hg hγ hp₀ hy hF hP hp hcap hdev
      hUm hUv hUp L.piece_mean L.piece_variance L.piece_pair
  · exact preparation_old_cost L.ν L.κ P y d p
      (fun ω t => g*(L.K ω t:ℝ))
      (fun ω i => if i ∈ outside P then L.N ω (.inl i) else y i)
      (fun ω ξ ti => g*(L.C ω ξ ti:ℝ)) F hy hd hp₀ hp₀1 hP hp hcap hUm L.piece_mean

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalOldMass
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

 theorem old_mass_id {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (F : Finset I) (z : L.Ω × (T → Finset I)) :
    (∑ a, oldAssignment L F z a)=
      (∑ i ∈ F ∩ outside P, (if i ∈ outside P then L.N z.1 (.inl i) else y i))+
      (∑ t, ∑ i ∈ F, g*(L.C z.1 z.2 (t,i):ℝ)) := by
  simp only [oldAssignment,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Sum.elim_inl,Sum.elim_inr,sum_ite_mem,univ_inter]
  congr 1
  apply sum_congr rfl
  intro i hi
  exact (ite_eq_left (mem_inter.mp hi).2).symm

 theorem old_cost_id {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (F : Finset I) (z : L.Ω × (T → Finset I)) (d : I → ℝ) :
    (∑ a, oldAssignment L F z a*(Sum.elim d (fun ti => d ti.2) a))=
      (∑ i ∈ F ∩ outside P, (if i ∈ outside P then L.N z.1 (.inl i) else y i)*d i)+
      (∑ t, ∑ i ∈ F, (g*(L.C z.1 z.2 (t,i):ℝ))*d i) := by
  simp only [oldAssignment,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Sum.elim_inl,Sum.elim_inr,ite_mul,zero_mul,sum_ite_mem,univ_inter]
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [ite_eq_left (mem_inter.mp hi).2]

theorem physical_old_estimates_s53_oai {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ}
    {g γ B p₀ : ℝ} {Δ : ℕ} (hg : 0 ≤ g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (hy : ∀ i, 0 ≤ y i) (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1) (hp : ∀ t, p₀ ≤ p t)
    (hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (F : Finset I) (hF : ∑ i ∈ F, y i=1) (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (L.ν.joint L.κ).expect (fun z => max (1-∑ a, oldAssignment L F z a) 0) ≤
      Real.sqrt g+Real.sqrt (g/p₀)+(γ+Real.sqrt (g*(1+γ)))/p₀ ∧
    (L.ν.joint L.κ).expect (fun z => ∑ a, oldAssignment L F z a*(Sum.elim d (fun ti => d ti.2) a)) ≤
      (∑ i ∈ F, y i*d i)/p₀ := by
  have he := coupled_old_estimates P A y p c hg hγ hunit L hy hp₀ hp₀1 hp hc0 hc1 hP F hF d hd
  dsimp only at he
  simpa only [old_mass_id,old_cost_id,sub_add_eq_sub_sub] using he

end MetricKMedian.Preparation
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Preparation.physical_old_estimates_s53_oai := @OAI.MetricKMedian.Preparation.physical_old_estimates_s53_oai
