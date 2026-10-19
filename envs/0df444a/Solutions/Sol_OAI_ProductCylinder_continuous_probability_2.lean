-- Prove2me | solution 2 for OAI.ProductCylinder.continuous_probability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:19:33.870478+00:00
-- url     : https://prove2.me/submissions/2e76a54f-4f4b-4938-bda7-3d5b2d7cb41c

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/ProductCylinder.lean:L300-L322
-- (upload_full_project.md Phase 4): solution for node OAI.ProductCylinder.continuous_probability. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder

-- ---- from OAI.Probability.CriticalZ3.ProductCylinder ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uF uI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

/-! Exact reduction of finite cylinder observables under the infinite Bernoulli law. -/
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace ProductCylinder
universe u
variable {E F : Type u}

theorem map_restrict (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1) :
    (law p).map J.restrict = finiteLaw J p := Measure.infinitePi_map_restrict _

theorem cylinder_probability (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (A : Set (J → Bool)) :
    law p (J.restrict ⁻¹' A) = finiteLaw J p A := by
  rw [←map_restrict,Measure.map_apply (Finset.measurable_restrict _) (Set.toFinite A).measurableSet]

theorem probability_determined (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (A : Set (E → Bool)) (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) :
    law p A = finiteLaw J p {ξ | extend J ξ ∈ A} := by
  rw [←cylinder_probability]
  congr 1
  ext ω
  exact hA (extend J (J.restrict ω)) ω (by intro e he; simp [extend,he,Finset.restrict])

end ProductCylinder

/-! Harris association for finite independent bits, including fixed coordinates. -/
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace FiniteAssociation
universe u
variable {E : Type u}

end FiniteAssociation

namespace ProductCylinder
variable {E : Type uE}

/-- The finite law is a polynomial in its bit parameters. -/
theorem finite_mass (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1) (ξ : J → Bool) :
    (finiteLaw J p).real {ξ} = ∏ e : J, if ξ e = true then (p e : ℝ) else 1-(p e : ℝ) := by
  rw [Measure.real_def,finiteLaw,Measure.pi_singleton,ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro e _
  change (bernoulliMeasure true false (p e)).real {ξ e} = _
  rw [bernoulliMeasure_real_apply (p e) (measurableSet_singleton _)]
  cases ξ e <;> simp [unitInterval.coe_symm_eq]

theorem continuous_probability (J : Finset E) (A : Set (E → Bool))
    (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) :
    Continuous (fun p : E → Set.Icc (0 : ℝ) 1 => (law p).real A) := by
  have he (p : E → Set.Icc (0 : ℝ) 1) : (law p).real A =
      ∑ ξ : J → Bool, (∏ e : J, if ξ e then (p e : ℝ) else 1-(p e : ℝ)) *
        (if extend J ξ ∈ A then 1 else 0) := by
    rw [Measure.real_def,probability_determined J p A hA]
    change (finiteLaw J p).real {ξ | extend J ξ ∈ A} = _
    rw [←integral_indicator_one (Set.toFinite _).measurableSet]
    rw [integral_fintype (Integrable.of_finite)]
    apply Finset.sum_congr rfl
    intro ξ _
    rw [finite_mass]
    simp [Set.indicator,smul_eq_mul]
  simp_rw [he]
  apply continuous_finsetSum
  intro ξ _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd
  intro e _
  cases ξ e
  · exact continuous_const.sub (continuous_subtype_val.comp (continuous_apply e.val))
  · exact continuous_subtype_val.comp (continuous_apply e.val)

end ProductCylinder

end OAI

-- ---- platform node ----
open OAI OAI.ProductCylinder
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical


theorem solution.{uE} : type_of% @_root_.OAI.ProductCylinder.continuous_probability.{uE} := @_root_.OAI.ProductCylinder.continuous_probability.{uE}
