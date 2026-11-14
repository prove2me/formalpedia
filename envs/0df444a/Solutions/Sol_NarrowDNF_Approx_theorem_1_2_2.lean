-- Prove2me | solution 2 for NarrowDNF.Approx.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T09:10:03.439551+00:00
-- url     : https://prove2.me/submissions/e4ba5713-0a77-41f9-86b9-0042ad6d8f7b

import Definitions.Def_FriedgutCoalition_wProb
import Definitions.Def_FriedgutCoalition_pInfl
import Definitions.Def_NarrowDNF_Approx_Probability
import Definitions.Def_NarrowDNF_Approx_DNF
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_FiberShift
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_MainStatements
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_split
import Theorems.Thm_NarrowDNF_main_narrow_dnf

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure

section


/-!
# Finite Bernoulli product probability

The probability model is an explicit finite sum of product weights. Algebraic
identities hold for every real parameter; positivity claims state `0 ≤ p ≤ 1`.
No theorem here assumes a probability law or an analytic input without proof.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.ProductMeasure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



@[simp] private theorem p2m_bridge_bitWeight_false (p : ℝ) : bitWeight p false = 1 - p := rfl
@[simp] private theorem p2m_bridge_bitWeight_true (p : ℝ) : bitWeight p true = p := rfl

















/-- Finite distributivity for independently chosen coordinates. -/
private theorem p2m_bridge_sum_prod_coordinates {α : Type*} [Fintype α] (F : ι → α → ℝ) :
    (∑ x : ι → α, ∏ i, F i (x i)) = ∏ i, ∑ a, F i a := by
  classical
  simpa only [Fintype.piFinset_univ] using
    (Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset α)) F).symm

@[simp] private theorem p2m_bridge_sum_weight (p : ℝ) : ∑ x : ι → Bool, weight p x = 1 := by
  unfold weight
  rw [NarrowDNF.ProductMeasure.p2m_bridge_sum_prod_coordinates]
  simp

@[simp] private theorem p2m_bridge_expectation_const (p c : ℝ) : expectation (ι := ι) p (fun _ => c) = c := by
  simp [expectation, ← Finset.sum_mul]

@[simp] private theorem p2m_bridge_expectation_zero (p : ℝ) : expectation (ι := ι) p (fun _ => 0) = 0 :=
  NarrowDNF.ProductMeasure.p2m_bridge_expectation_const p 0

@[simp] private theorem p2m_bridge_expectation_one (p : ℝ) : expectation (ι := ι) p (fun _ => 1) = 1 :=
  NarrowDNF.ProductMeasure.p2m_bridge_expectation_const p 1

















@[simp] private theorem p2m_bridge_error_self (p : ℝ) (f : (ι → Bool) → Bool) : error p f f = 0 := by
  simp [error, probability]









omit [Fintype ι] in
@[simp] private theorem p2m_bridge_insertBit_at (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool) :
    insertBit i b z i = b := by simp [insertBit, Equiv.funSplitAt, Equiv.piSplitAt]































end NarrowDNF.ProductMeasure

end

end




/-! Semantic bridge from the existing author proof to the platform interface.
This file preserves all theorem hypotheses and uses no new mathematical axioms.
The platform definitions are compiled verbatim from platform/Definitions.
Lean 4.24 is used for the local proof preflight only. -/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.PlatformBridge
attribute [local instance] Classical.propDecidable

/-- Both libraries use the same finite Bernoulli product law. -/
private theorem prob_eq {n : ℕ} (p : ℝ) (E : Approx.Cube n → Prop) :
    Approx.prob p E = ProductMeasure.probability p E := by
  classical
  simp only [Approx.prob, FriedgutCoalition.wProb, ProductMeasure.probability,
    ProductMeasure.expectation, ProductMeasure.weight, ProductMeasure.bitWeight,
    FriedgutCoalition.bern, mul_ite, mul_one, mul_zero]

private theorem error_eq {n : ℕ} (p : ℝ) (f g : Approx.Cube n → Bool) :
    Approx.error p f g = ProductMeasure.error p f g := by
  classical
  simp only [Approx.error, Approx.prob, FriedgutCoalition.wProb,
    ProductMeasure.error, ProductMeasure.probability, ProductMeasure.expectation,
    ProductMeasure.weight, ProductMeasure.bitWeight, FriedgutCoalition.bern,
    mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : f x = g x <;> simp [h]

/-- Integrating the independent replacement cube leaves its selected Bernoulli bit. -/
private theorem pInfl_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) :
    FriedgutCoalition.pInfl p f i = Influence.resamplingInfluence p f i := by
  classical
  have marginal (x : ι → Bool) :
      ProductMeasure.expectation p (fun y : ι → Bool =>
        FiberShift.mismatch (f x) (f (Function.update x i (y i)))) =
        (1-p) * FiberShift.mismatch (f x) (f (Function.update x i false)) +
          p * FiberShift.mismatch (f x) (f (Function.update x i true)) := by
    rw [ProductMeasure.expectation_split p i]
    simp only [NarrowDNF.ProductMeasure.p2m_bridge_insertBit_at, NarrowDNF.ProductMeasure.p2m_bridge_expectation_const]
  calc
    _ = ProductMeasure.expectation p (fun x : ι → Bool =>
        ProductMeasure.expectation p (fun y : ι → Bool =>
          FiberShift.mismatch (f x) (f (Function.update x i (y i))))) := by
      simp only [FriedgutCoalition.pInfl, ProductMeasure.expectation,
        ProductMeasure.weight, ProductMeasure.bitWeight, FriedgutCoalition.bern,
        FiberShift.mismatch, Finset.mul_sum, mul_assoc, ite_not]
    _ = _ := by simp_rw [marginal]; rfl

private theorem totalPInfl_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (f : (ι → Bool) → Bool) :
    FriedgutCoalition.totalPInfl p f = Influence.totalInfluence p f := by
  simp only [FriedgutCoalition.totalPInfl, Influence.totalInfluence, pInfl_eq]

private theorem evalDNF_eq {n : ℕ} (g : Approx.DNF n) :
    Approx.evalDNF g = NarrowDNF.evalDNF g := by
  funext x
  unfold Approx.evalDNF NarrowDNF.evalDNF
  apply decide_eq_decide.mpr
  rfl

/-- A termwise bound is sufficient for the maximum syntactic width, including
both the empty family and the family containing the empty term. -/
private theorem width_le {n : ℕ} (g : Approx.DNF n) (R : ℝ) (hR : 0 ≤ R)
    (h : ∀ T ∈ g, (T.card : ℝ) ≤ R) : (Approx.width g : ℝ) ≤ R := by
  classical
  by_cases hne : g.Nonempty
  · obtain ⟨T, hT, hmax⟩ := Finset.exists_mem_eq_sup g hne Finset.card
    simpa only [Approx.width, hmax] using h T hT
  · have hg : g = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simpa [Approx.width, hg] using hR

/-- For nonnegative bounds, the platform maximum-width condition is equivalent
to the author specification's bound on every actual term. -/
private theorem width_le_iff {n : ℕ} (g : Approx.DNF n) (R : ℝ) (hR : 0 ≤ R) :
    (Approx.width g : ℝ) ≤ R ↔ ∀ T ∈ g, (T.card : ℝ) ≤ R := by
  constructor
  · intro hg T hT
    have hcard : T.card ≤ Approx.width g := Finset.le_sup hT
    have hcast : (T.card : ℝ) ≤ (Approx.width g : ℝ) := by exact_mod_cast hcard
    exact hcast.trans hg
  · exact width_le g R hR

/-- The existing author proof supplies the exact platform Theorem 1.2 after
proved equivalences between its separately published probability/DNF interfaces. -/
private theorem platform_theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ K : ℝ, 0 < K →
      ∀ p : ℝ, 0 < p → p ≤ 1 / 2 → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ f : Approx.Cube n → Bool, Monotone f → FriedgutCoalition.totalPInfl p f ≤ K →
      ∃ g : Approx.DNF n, (Approx.width g : ℝ) ≤ Real.exp (C * (K + 1) ^ 2 / ε ^ 2) ∧
        Approx.error p f (Approx.evalDNF g) ≤ ε := by
  obtain ⟨C, hC, h⟩ := NarrowDNF.main_narrow_dnf
  refine ⟨C, hC, ?_⟩
  intro n hn K hK p hp0 hp12 ε hε0 hε1 f hmono hI
  have hI' : Influence.totalInfluence p f ≤ K := by
    simpa only [totalPInfl_eq] using hI
  obtain ⟨g, hg, herr⟩ := h n hn K p ε hK hp0 hp12 hε0 hε1 f hmono hI'
  refine ⟨g, width_le g _ (le_of_lt (Real.exp_pos _)) hg, ?_⟩
  simpa only [error_eq, evalDNF_eq] using herr


end NarrowDNF.PlatformBridge


open NarrowDNF.Approx

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ K : ℝ, 0 < K →
      ∀ p : ℝ, 0 < p → p ≤ 1 / 2 → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ f : Cube n → Bool, Monotone f → FriedgutCoalition.totalPInfl p f ≤ K →
      ∃ g : DNF n, (width g : ℝ) ≤ Real.exp (C * (K + 1) ^ 2 / ε ^ 2) ∧
        error p f (evalDNF g) ≤ ε := by
  exact NarrowDNF.PlatformBridge.platform_theorem_1_2
