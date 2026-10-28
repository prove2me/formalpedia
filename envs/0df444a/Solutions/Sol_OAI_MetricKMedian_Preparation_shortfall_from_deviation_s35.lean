-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.shortfall_from_deviation_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:07:33.502622+00:00
-- url     : https://prove2.me/submissions/cfd7353f-d690-412d-84d9-abcc7b118412

import Mathlib
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K025
import Theorems.Thm_OAI_MetricKMedian_FiniteLaw_restricted_moments_s35
import Theorems.Thm_OAI_MetricKMedian_Preparation_bundle_subset_moments_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteJoint
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
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparationNoise
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
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparationRescaling
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
-- module Solutions.OAIQ035_KM.KMedian_Preparation_ShortfallByDeviation
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

theorem shortfall_from_deviation_s35_oai (ν : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ)
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
  obtain ⟨hmean,hvar⟩ := ν.restricted_moments_s35 U y (F ∩ SupplierStars.outside P) hUm hUv hUc
  have hvar' : ν.variance (fun ω => ∑ i ∈ F ∩ SupplierStars.outside P, U ω i) ≤ g :=
    hvar.trans ((mul_le_mul_of_nonneg_left hu1 hg).trans_eq (mul_one _))
  have hbundle := fun ω => bundle_subset_moments_s35 (κ ω) (Y ω) P y p (p' ω) F g
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

theorem solution : type_of% @OAI.MetricKMedian.Preparation.shortfall_from_deviation_s35_oai := @OAI.MetricKMedian.Preparation.shortfall_from_deviation_s35_oai
