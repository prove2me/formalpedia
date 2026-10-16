-- Prove2me | solution 1 for OAI.DiagonalForms.System.comparison_logMean
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:14:16.833914+00:00
-- url     : https://prove2.me/submissions/180dcf9d-1cd2-459c-ac95-16deb80d2230

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiagonalForms.lean:L618-L635
-- (upload_full_project.md Phase 4): solution for node OAI.DiagonalForms.System.comparison_logMean. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Theorems.Thm_OAI_DiagonalForms_System_comparison_inverse_integral
import Theorems.Thm_OAI_DiagonalForms_System_integral_affine_inv

-- ---- from OAI.Analysis.DiagonalForms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace DiagonalForms.System
end DiagonalForms.System

namespace QuantumCalculus
end QuantumCalculus

namespace DiagonalForms.System
end DiagonalForms.System

namespace DiagonalForms.System
open EntropyPhotonNumber

end DiagonalForms.System

end

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace DiagonalForms

namespace System

variable {P I J : Type*} (D : System P I J)

theorem source_summable (w : P → ℝ) (z : D.tests) :
    Summable (fun i => w (D.sourceParam i) * Complex.normSq (z.val i)) := by
  classical
  obtain ⟨s, hs⟩ := D.finite_values z
  let B : ℝ := ∑ p ∈ s, |w p|
  apply Summable.of_norm_bounded ((D.mass_summable z).mul_left B)
  intro i
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]
  by_cases hz : z.val i = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun p _ => abs_nonneg (w p)) (hs i hz)) (Complex.normSq_nonneg _)

theorem comparison_add {v w : P → ℝ} (hv : D.Comparison v) (hw : D.Comparison w) :
    D.Comparison (fun p => v p + w p) := by
  intro z s
  simp only [add_mul, Finset.sum_add_distrib]
  simp only [sourceForm, add_mul]
  rw [(D.source_summable v z).tsum_add (D.source_summable w z)]
  exact add_le_add (hv z s) (hw z s)

theorem comparison_smul {w : P → ℝ} (hw : D.Comparison w) {a : ℝ} (ha : 0 ≤ a) :
    D.Comparison (fun p => a * w p) := by
  intro z s
  simp only [mul_assoc, ← Finset.mul_sum]
  simp only [sourceForm, mul_assoc, tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (hw z s) ha

end System

end DiagonalForms

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

section CompactIntegral
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (k₀ : K)

end CompactIntegral
end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
theorem unitInterval_volume : (volume : Measure UnitInterval) Set.univ = 1 := by
  simp [UnitInterval]

theorem affine_pos {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (t : UnitInterval) :
    0 < (1 - t.val) * X + t.val * Y := by
  rcases t.property.1.eq_or_lt with ht | ht
  · simp [← ht, hX]
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr t.property.2) hX.le) (mul_pos ht hY)
theorem comparison_logMean {v w : P → ℝ}
    (hv : D.Comparison v) (hw : D.Comparison w)
    (hvp : ∀ p, 0 < v p) (hwp : ∀ p, 0 < w p) :
    D.Comparison (fun p => logMean (v p) (w p)) := by
  have ha (t : UnitInterval) : D.Comparison (fun p => (1-t.val)*v p+t.val*w p) :=
    D.comparison_add (D.comparison_smul hv (sub_nonneg.mpr t.property.2))
      (D.comparison_smul hw t.property.1)
  have hc (p : P) : Continuous (fun t : UnitInterval => (1-t.val)*v p+t.val*w p) := by
    fun_prop
  have hμ : (volume : Measure UnitInterval) ≠ 0 := by
    intro h
    have h1 := unitInterval_volume
    rw [h] at h1
    simp at h1
  have hh := D.comparison_inverse_integral volume ⟨0, by norm_num⟩ hμ hc
    (fun t p => affine_pos (hvp p) (hwp p) t) ha
  simp_rw [integral_affine_inv (hvp _) (hwp _), inv_inv] at hh
  exact hh

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (k₀ : K)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]

end DiagonalForms.System

namespace DiagonalForms.System
open Function
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiagonalForms OAI.DiagonalForms.System
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open MeasureTheory Set


theorem solution : type_of% @_root_.OAI.DiagonalForms.System.comparison_logMean := @_root_.OAI.DiagonalForms.System.comparison_logMean
