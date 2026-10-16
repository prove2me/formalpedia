-- Prove2me | solution 1 for OAI.DiagonalForms.System.comparison_dualLogMean
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:16:38.668746+00:00
-- url     : https://prove2.me/submissions/6b94817a-658e-4212-adfd-81a8e3ca9e5c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiagonalForms.lean:L659-L686
-- (upload_full_project.md Phase 4): solution for node OAI.DiagonalForms.System.comparison_dualLogMean. The node keeps its source
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
import Theorems.Thm_OAI_DiagonalForms_System_integral_affine_inv
import Theorems.Thm_OAI_DiagonalForms_System_integral_comp_simpleFunc
import Theorems.Thm_OAI_DiagonalForms_System_integral_compactApprox_tendsto

-- ---- from OAI.Analysis.DiagonalForms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

theorem comparison_zero : D.Comparison (fun _ => 0) := by
  intro z s
  simp [sourceForm]

theorem comparison_finsetSum {K : Type*} (s : Finset K) {w : K → P → ℝ}
    (hw : ∀ k ∈ s, D.Comparison (w k)) : D.Comparison (fun p => ∑ k ∈ s, w k p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using D.comparison_zero
  | @insert k s hk ih =>
    simp only [Finset.forall_mem_insert] at hw
    simpa only [Finset.sum_insert hk] using D.comparison_add hw.1 (ih hw.2)

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

include k₀ in
theorem comparison_integral {w : K → P → ℝ}
    (hcont : ∀ p, Continuous (fun k => w k p)) (hw : ∀ k, D.Comparison (w k)) :
    D.Comparison (fun p => ∫ k, w k p ∂μ) := by
  apply D.comparison_tendsto (l := atTop)
    (w := fun n p => ∫ k, w (compactApprox k₀ n k) p ∂μ)
  · intro n
    have he (p : P) := integral_comp_simpleFunc μ (compactApprox k₀ n) (fun k => w k p)
    simp_rw [he]
    apply D.comparison_finsetSum
    intro k _
    exact D.comparison_smul (hw k) ENNReal.toReal_nonneg
  · intro p
    exact integral_compactApprox_tendsto μ k₀ (hcont p)

end CompactIntegral
end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
theorem affine_pos {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (t : UnitInterval) :
    0 < (1 - t.val) * X + t.val * Y := by
  rcases t.property.1.eq_or_lt with ht | ht
  · simp [← ht, hX]
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr t.property.2) hX.le) (mul_pos ht hY)
end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)

theorem inverse_logMean_inverse {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    (logMean X⁻¹ Y⁻¹)⁻¹ = X*Y/logMean X Y := by
  by_cases he : X = Y
  · subst Y
    simp [logMean, hX.ne']
  · have he' : X⁻¹ ≠ Y⁻¹ := fun h => he (inv_injective h)
    have hd : Y-X ≠ 0 := sub_ne_zero.mpr (Ne.symm he)
    have hl : Real.log Y - Real.log X ≠ 0 := by
      apply sub_ne_zero.mpr
      intro h
      apply he
      exact (Real.log_injOn_pos hY hX h).symm
    simp only [logMean, ite_eq_right he, ite_eq_right he', Real.log_inv]
    field_simp
    ring

theorem comparison_dualLogMean {v w : P → ℝ}
    (hv : D.Comparison v) (hw : D.Comparison w)
    (hvp : ∀ p, 0 < v p) (hwp : ∀ p, 0 < w p) :
    D.Comparison (fun p => v p*w p/logMean (v p) (w p)) := by
  have ha (t : UnitInterval) :
      D.Comparison (fun p => ((1-t.val)/(v p)+t.val/(w p))⁻¹) := by
    have hh := D.comparison_harmonic_sum_nonneg (Finset.univ : Finset (Fin 2))
      (w := fun i p => if i = 0 then v p else w p)
      (c := fun i => if i = 0 then 1-t.val else t.val)
      (by intro i _; split_ifs; exact sub_nonneg.mpr t.property.2; exact t.property.1)
      (by intro i _ p; split_ifs; exact hvp p; exact hwp p)
      (by intro i _; split_ifs; exact hv; exact hw)
    simpa [Fin.sum_univ_two] using hh
  have hc (p : P) :
      Continuous (fun t : UnitInterval => ((1-t.val)/(v p)+t.val/(w p))⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · intro t
      simpa [div_eq_mul_inv] using (affine_pos (inv_pos.mpr (hvp p))
        (inv_pos.mpr (hwp p)) t).ne'
  have hh := D.comparison_integral volume (⟨0, by norm_num⟩ : UnitInterval) hc ha
  have he (p : P) : (∫ t : UnitInterval, ((1-t.val)/(v p)+t.val/(w p))⁻¹) =
      v p*w p/logMean (v p) (w p) := by
    simp only [div_eq_mul_inv]
    rw [integral_affine_inv (inv_pos.mpr (hvp p)) (inv_pos.mpr (hwp p)),
      inverse_logMean_inverse (hvp p) (hwp p), div_eq_mul_inv]
  simp_rw [he] at hh
  exact hh

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


theorem solution : type_of% @_root_.OAI.DiagonalForms.System.comparison_dualLogMean := @_root_.OAI.DiagonalForms.System.comparison_dualLogMean
