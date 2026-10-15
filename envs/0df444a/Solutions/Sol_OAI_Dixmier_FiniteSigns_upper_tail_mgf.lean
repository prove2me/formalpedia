-- Prove2me | solution 1 for OAI.Dixmier.FiniteSigns.upper_tail_mgf
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:42:12.659541+00:00
-- url     : https://prove2.me/submissions/961002be-9ab0-441d-bbac-cad8aaddba29

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/FiniteSigns.lean:L50-L65
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.FiniteSigns.upper_tail_mgf. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Countable.Small
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Dixmier
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting
import Definitions.Def_OAI_Analysis_Unitarizability_Regular
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns

-- ---- from OAI.Analysis.Unitarizability.FiniteSigns ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

namespace OAI

/-! Finite independent signs. Expectations are explicit finite sums over all sign
assignments with equal weight. -/
noncomputable section
namespace Dixmier
namespace FiniteSigns
open Finset
variable {J : Type*} [Fintype J]
attribute [local instance] OAI.Dixmier.FiniteSigns.instDecidableEq_oAI
theorem sign_mgf (a : J → ℝ) :
    ∑ σ : J → Bool, Real.exp (value a σ) =
      (2 : ℝ) ^ Fintype.card J * ∏ j, Real.cosh (a j) := by
  simp only [value, Real.exp_sum]
  rw [← Fintype.prod_sum (fun j (b : Bool) => Real.exp (a j * sign b))]
  have h (j : J) : (∑ b : Bool, Real.exp (a j * sign b)) = 2 * Real.cosh (a j) := by
    simp [sign, Real.cosh_eq]
    ring
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  simp

theorem sign_mgf_le (a : J → ℝ) :
    ∑ σ : J → Bool, Real.exp (value a σ) ≤
      (2 : ℝ) ^ Fintype.card J * Real.exp ((∑ j, (a j)^2) / 2) := by
  rw [sign_mgf]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ∏ j, Real.cosh (a j) ≤ ∏ j, Real.exp ((a j)^2/2) :=
      Finset.prod_le_prod₀ (fun j _ => (Real.cosh_pos _).le) (fun j _ => Real.cosh_le_exp_half_sq _)
    _ = _ := by rw [← Real.exp_sum]; simp only [div_eq_mul_inv, Finset.sum_mul]

theorem value_smul (a : J → ℝ) (t : ℝ) (σ : J → Bool) :
    value (fun j => t * a j) σ = t * value a σ := by
  simp only [value, Finset.mul_sum, mul_assoc]

/-- Finite Markov inequality for the equiprobable sign space. -/
theorem upper_tail_mgf (a : J → ℝ) {t u : ℝ} (ht : 0 ≤ t) :
    (((univ.filter fun σ : J → Bool => u < value a σ).card : ℕ) : ℝ) * Real.exp (t*u) ≤
      (2 : ℝ) ^ Fintype.card J * Real.exp (t^2 * (∑ j, (a j)^2) / 2) := by
  classical
  let S := univ.filter (fun σ : J → Bool => u < value a σ)
  have h1 : (S.card : ℝ) * Real.exp (t*u) ≤ ∑ σ ∈ S, Real.exp (t * value a σ) := by
    calc
      _ = ∑ σ ∈ S, Real.exp (t*u) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun σ hσ => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hσ).2.le ht))
  have h2 : (∑ σ ∈ S, Real.exp (t * value a σ)) ≤ ∑ σ : J → Bool, Real.exp (t * value a σ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => (Real.exp_pos _).le)
  have h3 := sign_mgf_le (fun j => t*a j)
  simp only [value_smul, mul_pow, ← Finset.mul_sum] at h3
  exact h1.trans (h2.trans h3)

end FiniteSigns
end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier OAI.Dixmier.FiniteSigns
open Finset
variable {J : Type*} [Fintype J]
attribute [local instance] OAI.Dixmier.FiniteSigns.instDecidableEq_oAI

theorem solution (a : J → ℝ) {t u : ℝ} (ht : 0 ≤ t) :
    (((univ.filter fun σ : J → Bool => u < value a σ).card : ℕ) : ℝ) * Real.exp (t*u) ≤
      (2 : ℝ) ^ Fintype.card J * Real.exp (t^2 * (∑ j, (a j)^2) / 2) := by
  first
    | exact OAI.Dixmier.FiniteSigns.upper_tail_mgf a ht
    | exact OAI.Dixmier.FiniteSigns.upper_tail_mgf
    | (apply OAI.Dixmier.FiniteSigns.upper_tail_mgf <;> assumption)
    | (intros; apply OAI.Dixmier.FiniteSigns.upper_tail_mgf <;> assumption)
