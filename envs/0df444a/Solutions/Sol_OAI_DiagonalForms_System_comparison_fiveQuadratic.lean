-- Prove2me | solution 1 for OAI.DiagonalForms.System.comparison_fiveQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:20:35.95044+00:00
-- url     : https://prove2.me/submissions/708753b9-d0f4-4888-84f2-2279743f179e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiagonalForms.lean:L859-L903
-- (upload_full_project.md Phase 4): solution for node OAI.DiagonalForms.System.comparison_fiveQuadratic. The node keeps its source
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

theorem comparison_fiveQuadratic {v₀ v₁ v₂ v₃ v₄ F δ : P → ℝ}
    (h₀ : D.Comparison v₀) (h₁ : D.Comparison v₁) (h₂ : D.Comparison v₂)
    (h₃ : D.Comparison v₃) (h₄ : D.Comparison v₄)
    (hmin : ∀ p ξ, fiveQuadratic (v₀ p) (v₁ p) (v₂ p) (v₃ p) (v₄ p)
      ξ ((δ p : ℂ)*ξ) = F p*Complex.normSq ξ)
    (hlower : ∀ p ξ φ, F p*Complex.normSq ξ ≤
      fiveQuadratic (v₀ p) (v₁ p) (v₂ p) (v₃ p) (v₄ p) ξ φ) :
    D.Comparison F := by
  intro z s
  let φ := D.multiplier δ z
  have hsum : HasSum (fun i => fiveQuadratic (v₀ (D.sourceParam i)) (v₁ (D.sourceParam i))
      (v₂ (D.sourceParam i)) (v₃ (D.sourceParam i)) (v₄ (D.sourceParam i)) (z.val i) (φ.val i))
      (D.sourceForm v₀ (z-φ)+D.sourceForm v₁ (z+φ)+D.sourceForm v₂ (z+φ)+
        D.sourceForm v₃ (z-φ)+D.sourceForm v₄ φ) := by
    have h := (((((D.source_summable v₀ (z-φ)).hasSum.add
      (D.source_summable v₁ (z+φ)).hasSum).add
      (D.source_summable v₂ (z+φ)).hasSum).add
      (D.source_summable v₃ (z-φ)).hasSum).add
      (D.source_summable v₄ φ).hasSum)
    simpa only [sourceForm, fiveQuadratic, Submodule.coe_sub, Submodule.coe_add,
      Pi.sub_apply, Pi.add_apply] using h
  have heq : D.sourceForm v₀ (z-φ)+D.sourceForm v₁ (z+φ)+D.sourceForm v₂ (z+φ)+
      D.sourceForm v₃ (z-φ)+D.sourceForm v₄ φ = D.sourceForm F z := by
    apply hsum.unique
    convert (D.source_summable F z).hasSum using 1
    · funext i
      exact hmin (D.sourceParam i) (z.val i)
    · rfl
  calc
    ∑ j ∈ s, F (D.targetParam j)*Complex.normSq (D.map z j) ≤
        ∑ j ∈ s, fiveQuadratic (v₀ (D.targetParam j)) (v₁ (D.targetParam j))
          (v₂ (D.targetParam j)) (v₃ (D.targetParam j)) (v₄ (D.targetParam j))
            (D.map z j) (D.map φ j) :=
      Finset.sum_le_sum (fun j _ => hlower _ _ _)
    _ = (∑ j ∈ s, v₀ (D.targetParam j)*Complex.normSq (D.map (z-φ) j))+
        (∑ j ∈ s, v₁ (D.targetParam j)*Complex.normSq (D.map (z+φ) j))+
        (∑ j ∈ s, v₂ (D.targetParam j)*Complex.normSq (D.map (z+φ) j))+
        (∑ j ∈ s, v₃ (D.targetParam j)*Complex.normSq (D.map (z-φ) j))+
        (∑ j ∈ s, v₄ (D.targetParam j)*Complex.normSq (D.map φ j)) := by
      simp only [fiveQuadratic, Finset.sum_add_distrib, map_sub, map_add, Pi.sub_apply, Pi.add_apply]
    _ ≤ D.sourceForm v₀ (z-φ)+D.sourceForm v₁ (z+φ)+D.sourceForm v₂ (z+φ)+
        D.sourceForm v₃ (z-φ)+D.sourceForm v₄ φ :=
      add_le_add (add_le_add (add_le_add (add_le_add (h₀ (z-φ) s) (h₁ (z+φ) s))
        (h₂ (z+φ) s)) (h₃ (z-φ) s)) (h₄ φ s)
    _ = D.sourceForm F z := heq

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
open Function


theorem solution : type_of% @_root_.OAI.DiagonalForms.System.comparison_fiveQuadratic := @_root_.OAI.DiagonalForms.System.comparison_fiveQuadratic
