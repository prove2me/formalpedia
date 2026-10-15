-- Prove2me | solution 1 for OAI.Dixmier.dimension_ratio_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:45:55.623772+00:00
-- url     : https://prove2.me/submissions/bb956155-431e-4073-b321-4d3fe8c18d85

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Parameters.lean:L52-L72
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.dimension_ratio_tendsto. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis
import Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix
import Definitions.Def_OAI_Analysis_Unitarizability_Parameters

-- ---- from OAI.Analysis.Unitarizability.Parameters ----
namespace OAI

/-! Ceiling parameters and dimension-ratio asymptotics. -/
noncomputable section
namespace Dixmier
open Filter Topology

theorem dimension_ratio_bound {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ} (hρ : 0 ≤ ρ) (ℓ : ℕ) :
    (fiberDimension d ρ ℓ : ℝ) / (d : ℝ)^ℓ ≤
      2 * (ρ^ℓ + 1 / (d : ℝ)^ℓ) * Real.log (2 * (d : ℝ)^ℓ) + 1 / (d : ℝ)^ℓ := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hn : (0 : ℝ) < (d : ℝ)^ℓ := pow_pos (lt_of_lt_of_le zero_lt_one hdR) _
  have hn1 : (1 : ℝ) ≤ (d : ℝ)^ℓ := one_le_pow₀ hdR
  have hlog : 0 ≤ Real.log (2 * (d : ℝ)^ℓ) := Real.log_nonneg (by nlinarith)
  have hr : (endpointCapacity d ρ ℓ : ℝ) ≤ (d : ℝ)^ℓ * ρ^ℓ + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hn.le (pow_nonneg hρ _))).le
  have hk : (fiberDimension d ρ ℓ : ℝ) ≤
      2 * (endpointCapacity d ρ ℓ : ℝ) * Real.log (2 * (d : ℝ)^ℓ) + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg (by positivity) hlog)).le
  have hk' : (fiberDimension d ρ ℓ : ℝ) ≤
      2 * ((d : ℝ)^ℓ * ρ^ℓ + 1) * Real.log (2 * (d : ℝ)^ℓ) + 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hr hlog]
  apply (div_le_iff₀ hn).mpr
  calc
    (fiberDimension d ρ ℓ : ℝ) ≤ 2 * ((d : ℝ)^ℓ * ρ^ℓ + 1) * Real.log (2 * (d : ℝ)^ℓ) + 1 := hk'
    _ = (2 * (ρ^ℓ + 1 / (d : ℝ)^ℓ) * Real.log (2 * (d : ℝ)^ℓ) + 1 / (d : ℝ)^ℓ) * (d : ℝ)^ℓ := by
      field_simp

/-- The logarithm contributes only a linear factor in the word length. -/
theorem geometric_log_tendsto {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {d : ℝ} (hd : 0 < d) :
    Tendsto (fun ℓ : ℕ => a^ℓ * Real.log (2 * d^ℓ)) atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one ha ha1
  have hl : Tendsto (fun ℓ : ℕ => (ℓ : ℝ) * a^ℓ) atTop (𝓝 0) := by
    simpa only [pow_one] using (summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖a‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg ha] using ha1)).tendsto_atTop_zero
  have h := (hp.mul_const (Real.log 2)).add (hl.mul_const (Real.log d))
  simp only [zero_mul, zero_add] at h
  convert h using 1
  ext ℓ
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hd.ne'), Real.log_pow]
  ring

/-- The dimension ratio tends to zero. -/
theorem dimension_ratio_tendsto {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun ℓ : ℕ => (fiberDimension d ρ ℓ : ℝ) / (d : ℝ)^ℓ) atTop (𝓝 0) := by
  have hdR : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  have hi0 : (0 : ℝ) ≤ (d : ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hi1 : (d : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hdR
  have h1 := geometric_log_tendsto hρ hρ1 (lt_trans zero_lt_one hdR)
  have h2 := geometric_log_tendsto hi0 hi1 (lt_trans zero_lt_one hdR)
  have h3 := tendsto_pow_atTop_nhds_zero_of_lt_one hi0 hi1
  have hu : Tendsto (fun ℓ : ℕ =>
      2 * (ρ^ℓ + 1 / (d : ℝ)^ℓ) * Real.log (2 * (d : ℝ)^ℓ) + 1 / (d : ℝ)^ℓ)
      atTop (𝓝 0) := by
    have hh := ((h1.add h2).const_mul 2).add h3
    simp only [zero_add, mul_zero] at hh
    convert hh using 1
    ext ℓ
    simp only [one_div, inv_pow]
    ring
  exact squeeze_zero (fun ℓ => div_nonneg (Nat.cast_nonneg _) (by positivity))
    (dimension_ratio_bound hd hρ) hu

end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier
open Filter Topology

theorem solution {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun ℓ : ℕ => (fiberDimension d ρ ℓ : ℝ) / (d : ℝ)^ℓ) atTop (𝓝 0) := by
  first
    | exact OAI.Dixmier.dimension_ratio_tendsto hd hρ hρ1
    | exact OAI.Dixmier.dimension_ratio_tendsto
    | (apply OAI.Dixmier.dimension_ratio_tendsto <;> assumption)
    | (intros; apply OAI.Dixmier.dimension_ratio_tendsto <;> assumption)
