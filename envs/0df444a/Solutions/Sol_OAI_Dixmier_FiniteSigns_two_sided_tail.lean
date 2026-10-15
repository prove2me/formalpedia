-- Prove2me | solution 1 for OAI.Dixmier.FiniteSigns.two_sided_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:42:45.620765+00:00
-- url     : https://prove2.me/submissions/11dad092-7dc8-44ed-921e-44ffc2184060

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/FiniteSigns.lean:L82-L105
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.FiniteSigns.two_sided_tail. The node keeps its source
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
import Theorems.Thm_OAI_Dixmier_FiniteSigns_upper_tail_mgf

-- ---- from OAI.Analysis.Unitarizability.FiniteSigns ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

/-! Finite independent signs. Expectations are explicit finite sums over all sign
assignments with equal weight. -/
noncomputable section
namespace Dixmier
namespace FiniteSigns
open Finset
variable {J : Type*} [Fintype J]
attribute [local instance] OAI.Dixmier.FiniteSigns.instDecidableEq_oAI
/-- One-sided sign tail for coefficients of total squared size 1/k. -/
theorem upper_tail (a : J → ℝ) {k u : ℝ} (hk : 0 < k) (hu : 0 < u)
    (ha : ∑ j, (a j)^2 = 1/k) :
    (((univ.filter fun σ : J → Bool => u < value a σ).card : ℕ) : ℝ) ≤
      (2 : ℝ) ^ Fintype.card J * Real.exp (-k*u^2/2) := by
  have h := upper_tail_mgf a (mul_nonneg hk.le hu.le) (u := u)
  rw [ha] at h
  have hexp : (k*u)^2*(1/k)/2 = (-k*u^2/2) + (k*u)*u := by field_simp; ring
  rw [hexp, Real.exp_add, ← mul_assoc] at h
  exact (mul_le_mul_iff_left₀ (Real.exp_pos ((k*u)*u))).mp h

theorem value_neg (a : J → ℝ) (σ : J → Bool) : value (fun j => -a j) σ = -value a σ := by
  simp [value, Finset.sum_neg_distrib]

/-- The two-sided sign-tail bound as a fraction of the finite equiprobable sign space. -/
theorem two_sided_tail (a : J → ℝ) {k u : ℝ} (hk : 0 < k) (hu : 0 < u)
    (ha : ∑ j, (a j)^2 = 1/k) :
    (((univ.filter fun σ : J → Bool => u < |value a σ|).card : ℕ) : ℝ) /
      (2 : ℝ)^Fintype.card J ≤ 2 * Real.exp (-k*u^2/2) := by
  classical
  have hn : ∑ j, (-a j)^2 = 1/k := by simpa only [neg_sq] using ha
  have hp := upper_tail a hk hu ha
  have hm := upper_tail (fun j => -a j) hk hu hn
  have hs : (univ.filter fun σ : J → Bool => u < |value a σ|) ⊆
      (univ.filter fun σ : J → Bool => u < value a σ) ∪
      (univ.filter fun σ : J → Bool => u < value (fun j => -a j) σ) := by
    intro σ hσ
    simp only [mem_filter, mem_univ, true_and, mem_union, value_neg] at *
    rcases lt_abs.mp hσ with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hcard := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hr : (((univ.filter fun σ : J → Bool => u < |value a σ|).card : ℕ) : ℝ) ≤
      (((univ.filter fun σ : J → Bool => u < value a σ).card : ℕ) : ℝ) +
      (((univ.filter fun σ : J → Bool => u < value (fun j => -a j) σ).card : ℕ) : ℝ) := by
    exact_mod_cast hcard
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ Fintype.card J)).mpr
  nlinarith

end FiniteSigns
end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier OAI.Dixmier.FiniteSigns
open Finset
variable {J : Type*} [Fintype J]
attribute [local instance] OAI.Dixmier.FiniteSigns.instDecidableEq_oAI

theorem solution (a : J → ℝ) {k u : ℝ} (hk : 0 < k) (hu : 0 < u)
    (ha : ∑ j, (a j)^2 = 1/k) :
    (((univ.filter fun σ : J → Bool => u < |value a σ|).card : ℕ) : ℝ) /
      (2 : ℝ)^Fintype.card J ≤ 2 * Real.exp (-k*u^2/2) := by
  first
    | exact OAI.Dixmier.FiniteSigns.two_sided_tail a hk hu ha
    | exact OAI.Dixmier.FiniteSigns.two_sided_tail
    | (apply OAI.Dixmier.FiniteSigns.two_sided_tail <;> assumption)
    | (intros; apply OAI.Dixmier.FiniteSigns.two_sided_tail <;> assumption)
