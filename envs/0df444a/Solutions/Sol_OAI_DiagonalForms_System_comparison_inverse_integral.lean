-- Prove2me | solution 1 for OAI.DiagonalForms.System.comparison_inverse_integral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:11:20.359642+00:00
-- url     : https://prove2.me/submissions/e71c0a23-e564-4bc2-ae45-385fc4d450aa

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiagonalForms.lean:L554-L580
-- (upload_full_project.md Phase 4): solution for node OAI.DiagonalForms.System.comparison_inverse_integral. The node keeps its source
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
import Theorems.Thm_OAI_DiagonalForms_System_comparison_harmonic_sum_nonneg
import Theorems.Thm_OAI_DiagonalForms_System_integral_comp_simpleFunc
import Theorems.Thm_OAI_DiagonalForms_System_integral_compactApprox_tendsto

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

theorem sourceForm_finite (z : D.tests) :
    ∃ (s : Finset P) (c : P → ℝ), ∀ w : P → ℝ,
      D.sourceForm w z = ∑ p ∈ s, w p * c p := by
  classical
  obtain ⟨s, hs⟩ := D.finite_values z
  let c (p : P) : ℝ := ∑' i, if p = D.sourceParam i then Complex.normSq (z.val i) else 0
  refine ⟨s, c, ?_⟩
  intro w
  have hsum (p : P) : Summable (fun i => if p = D.sourceParam i then Complex.normSq (z.val i) else 0) := by
    apply Summable.of_nonneg_of_le _ _ (D.mass_summable z)
    · intro i
      split_ifs
      · exact Complex.normSq_nonneg _
      · exact le_rfl
    · intro i
      split_ifs
      · exact le_rfl
      · exact Complex.normSq_nonneg _
  simp only [c, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun p _ => (hsum p).mul_left (w p))]
  apply tsum_congr
  intro i
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  by_cases hz : z.val i = 0
  · simp [hz]
  · simp [hs i hz]

theorem sourceForm_tendsto {α : Type*} {l : Filter α} {w : α → P → ℝ} {v : P → ℝ}
    (h : ∀ p, Tendsto (fun a => w a p) l (𝓝 (v p))) (z : D.tests) :
    Tendsto (fun a => D.sourceForm (w a) z) l (𝓝 (D.sourceForm v z)) := by
  obtain ⟨s, c, hc⟩ := D.sourceForm_finite z
  simp_rw [hc]
  exact tendsto_finsetSum s (fun p _ => (h p).mul_const (c p))

theorem comparison_tendsto {α : Type*} {l : Filter α} [NeBot l]
    {w : α → P → ℝ} {v : P → ℝ} (hw : ∀ a, D.Comparison (w a))
    (hlim : ∀ p, Tendsto (fun a => w a p) l (𝓝 (v p))) : D.Comparison v := by
  intro z s
  exact le_of_tendsto_of_tendsto
    (tendsto_finsetSum s (fun j _ => (hlim _).mul_const _))
    (D.sourceForm_tendsto hlim z) (Eventually.of_forall (fun a => hw a z s))

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

theorem comparison_inverse_integral {K : Type*} [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (k₀ : K) (hμ : μ ≠ 0) {w : K → P → ℝ}
    (hcont : ∀ p, Continuous (fun k => w k p)) (hwp : ∀ k p, 0 < w k p)
    (hw : ∀ k, D.Comparison (w k)) :
    D.Comparison (fun p => (∫ k, (w k p)⁻¹ ∂μ)⁻¹) := by
  apply D.comparison_tendsto (l := atTop)
    (w := fun n p => (∫ k, (w (compactApprox k₀ n k) p)⁻¹ ∂μ)⁻¹)
  · intro n
    have he (p : P) := integral_comp_simpleFunc μ (compactApprox k₀ n) (fun k => (w k p)⁻¹)
    simp_rw [he]
    simpa only [div_eq_mul_inv, Measure.real] using D.comparison_harmonic_sum_nonneg
      (compactApprox k₀ n).range (fun _ _ => ENNReal.toReal_nonneg)
      (fun k _ => hwp k) (fun k _ => hw k)
  · intro p
    have hg : Continuous (fun k => (w k p)⁻¹) :=
      (hcont p).inv₀ (fun k => (hwp k p).ne')
    have hs : Function.support (fun k => (w k p)⁻¹) = Set.univ := by
      ext k
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact inv_ne_zero (hwp k p).ne'
    have hi : 0 < ∫ k, (w k p)⁻¹ ∂μ := by
      rw [integral_pos_iff_support_of_nonneg
        (fun k => inv_nonneg.mpr (hwp k p).le)
        (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)), hs]
      exact Measure.measure_univ_pos.mpr hμ
    exact (integral_compactApprox_tendsto μ k₀ hg).inv₀ hi.ne'

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
open MeasureTheory


theorem solution : type_of% @_root_.OAI.DiagonalForms.System.comparison_inverse_integral := @_root_.OAI.DiagonalForms.System.comparison_inverse_integral
