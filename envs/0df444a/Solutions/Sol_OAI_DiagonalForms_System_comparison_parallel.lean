-- Prove2me | solution 1 for OAI.DiagonalForms.System.comparison_parallel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:05:29.235687+00:00
-- url     : https://prove2.me/submissions/f81f8619-2d8e-4fce-812f-a0c3f532c060

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiagonalForms.lean:L259-L289
-- (upload_full_project.md Phase 4): solution for node OAI.DiagonalForms.System.comparison_parallel. The node keeps its source
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

theorem parallel_norm_bound {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (u v : ℂ) :
    parallel x y * Complex.normSq (u + v) ≤ x * Complex.normSq u + y * Complex.normSq v := by
  unfold parallel
  rw [div_mul_eq_mul_div, div_le_iff₀ (add_pos hx hy)]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (x * u.re - y * v.re), sq_nonneg (x * u.im - y * v.im)]

theorem parallel_minimum {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (z : ℂ) :
    x * Complex.normSq (((y / (x + y) : ℝ) : ℂ) * z) +
      y * Complex.normSq (((x / (x + y) : ℝ) : ℂ) * z) = parallel x y * Complex.normSq z := by
  simp only [Complex.normSq_mul, Complex.normSq_ofReal]
  unfold parallel
  field_simp [ne_of_gt (add_pos hx hy)]
  ring

theorem comparison_parallel {v w : P → ℝ} (hv : D.Comparison v) (hw : D.Comparison w)
    (hvp : ∀ p, 0 < v p) (hwp : ∀ p, 0 < w p) :
    D.Comparison (fun p => parallel (v p) (w p)) := by
  intro z s
  let u := D.multiplier (fun p => w p / (v p + w p)) z
  let t := D.multiplier (fun p => v p / (v p + w p)) z
  have hut : u + t = z := by
    apply Subtype.ext
    funext i
    simp only [u, t, Submodule.coe_add, Pi.add_apply, multiplier_apply,
      ← add_mul, ← Complex.ofReal_add]
    rw [← add_div, add_comm (w _), div_self (ne_of_gt (add_pos (hvp _) (hwp _)))]
    simp
  have hmap (j : J) : D.map u j + D.map t j = D.map z j := by
    rw [← Pi.add_apply, ← map_add, hut]
  calc
    _ ≤ ∑ j ∈ s, (v (D.targetParam j) * Complex.normSq (D.map u j) +
        w (D.targetParam j) * Complex.normSq (D.map t j)) := by
      apply Finset.sum_le_sum
      intro j _
      rw [← hmap j]
      exact parallel_norm_bound (hvp _) (hwp _) _ _
    _ = (∑ j ∈ s, v (D.targetParam j) * Complex.normSq (D.map u j)) +
        ∑ j ∈ s, w (D.targetParam j) * Complex.normSq (D.map t j) := Finset.sum_add_distrib
    _ ≤ D.sourceForm v u + D.sourceForm w t := add_le_add (hv u s) (hw t s)
    _ = D.sourceForm (fun p => parallel (v p) (w p)) z := by
      simp only [sourceForm]
      rw [← (D.source_summable v u).tsum_add (D.source_summable w t)]
      apply tsum_congr
      intro i
      exact parallel_minimum (hvp _) (hwp _) (z.val i)

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


theorem solution : type_of% @_root_.OAI.DiagonalForms.System.comparison_parallel := @_root_.OAI.DiagonalForms.System.comparison_parallel
