-- Prove2me | solution 1 for OAI.GaussianPropeller.HeatConvolution.stein_trace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:59:09.215661+00:00
-- url     : https://prove2.me/submissions/f9ad8588-eabb-41c2-8725-c3422d9d1378

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/HeatConvolution.lean:L101-L157
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.HeatConvolution.stein_trace. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Theorems.Thm_OAI_GaussianPropeller_Stein_integration_by_parts

-- ---- from OAI.Probability.GaussianPropeller.Stein ----
namespace OAI

universe uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

open Filter
open scoped Topology
namespace GaussianPropeller.Stein
open GaussianPropeller.Translation

variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

lemma integrable_bounded {H : E → ℝ} (hH : AEStronglyMeasurable H γ)
    {B : ℝ} (hB : ∀ x, ‖H x‖ ≤ B) : Integrable H γ :=
  Integrable.mono' (integrable_const B) hH (ae_of_all _ hB)

end GaussianPropeller.Stein

end OAI

-- ---- from OAI.Probability.GaussianPropeller.HeatConvolution ----
namespace OAI

universe uV uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology

namespace GaussianPropeller.HeatConvolution
open GaussianPropeller.Stein
variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

section General
variable {V : Type uV} [NormedAddCommGroup V]

variable [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

end General

lemma stein_trace {g : E → E} {K : E → E →L[ℝ] E}
    (hg : ∀ x, HasFDerivAt g (K x) x) (hcK : Continuous K)
    {C D : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (hD : ∀ x, ‖K x‖ ≤ D)
    (r : ℝ) (x : E) :
    (∫ z, ⟪g (x+r•z),z⟫ ∂γ) = r*(∫ z, ∑ i, ⟪K (x+r•z)
      (EuclideanSpace.basisFun ι ℝ i), EuclideanSpace.basisFun ι ℝ i⟫ ∂γ) := by
  let e := EuclideanSpace.basisFun ι ℝ
  have hc : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have hC0 : 0 ≤ C := (norm_nonneg (g 0)).trans (hC 0)
  have hD0 : 0 ≤ D := (norm_nonneg (K 0)).trans (hD 0)
  have he (i : ι) : ‖e i‖ = 1 := e.orthonormal.norm_eq_one i
  have hi (i : ι) :
      r*(∫ z, ⟪e i,K (x+r•z) (e i)⟫ ∂γ) =
        ∫ z, ⟪e i,g (x+r•z)⟫*⟪e i,z⟫ ∂γ := by
    have hh := integration_by_parts (H := fun z => ⟪e i,g (x+r•z)⟫)
      (D := fun z => r • ((innerSL ℝ (e i)).comp (K (x+r•z))))
      (B := C) (C := |r| *D) ?_ (by fun_prop) ?_ ?_ (e i)
    · simpa only [smul_apply, ContinuousLinearMap.comp_apply,
        innerSL_apply_apply, smul_eq_mul, integral_const_mul] using hh
    · intro z
      have hh := ((innerSL ℝ (e i)).hasFDerivAt).comp z
        ((hg (x+r•z)).comp z ((hasFDerivAt_id z).const_smul r |>.const_add x))
      convert hh using 1 <;> (first | rfl | (ext v; simp))
    · intro z
      exact (norm_inner_le_norm _ _).trans (by rw [he, one_mul]; exact hC _)
    · intro z
      rw [norm_smul, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        ‖(innerSL ℝ (e i)).comp (K (x+r•z))‖ ≤ ‖innerSL ℝ (e i)‖*‖K (x+r•z)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ D := by rw [innerSL_apply_norm, he, one_mul]; exact hD _
  have hleft (i : ι) : Integrable (fun z : E => ⟪e i,g (x+r•z)⟫*⟪e i,z⟫) γ := by
    apply Integrable.mono' ((IsGaussian.integrable_id (μ := γ)).norm.const_mul C) (by fun_prop)
    filter_upwards [] with z
    rw [norm_mul]
    have ha : ‖⟪e i,g (x+r•z)⟫‖ ≤ C :=
      (norm_inner_le_norm _ _).trans (by rw [he, one_mul]; exact hC _)
    have hb : ‖⟪e i,z⟫‖ ≤ ‖z‖ := by simpa only [he, one_mul] using norm_inner_le_norm (e i) z
    exact mul_le_mul ha hb (norm_nonneg _) hC0
  have hright (i : ι) : Integrable (fun z : E => ⟪e i,K (x+r•z) (e i)⟫) γ := by
    apply integrable_bounded (by fun_prop) (B := D)
    intro z
    calc
      ‖⟪e i,K (x+r•z) (e i)⟫‖ ≤ ‖e i‖*‖K (x+r•z) (e i)‖ := norm_inner_le_norm _ _
      _ ≤ D := by rw [he, one_mul]; simpa only [he, mul_one] using
        ((K _).le_opNorm (e i)).trans (mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _))
  calc
    (∫ z, ⟪g (x+r•z),z⟫ ∂γ) = ∫ z, ∑ i, ⟪e i,g (x+r•z)⟫*⟪e i,z⟫ ∂γ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simpa only [real_inner_comm (e _) (g _)] using (e.sum_inner_mul_inner (g (x+r•z)) z).symm
    _ = ∑ i, ∫ z, ⟪e i,g (x+r•z)⟫*⟪e i,z⟫ ∂γ := integral_finsetSum _ (fun i _ => hleft i)
    _ = ∑ i, r*(∫ z, ⟪e i,K (x+r•z) (e i)⟫ ∂γ) := by simp_rw [hi]
    _ = r*(∫ z, ∑ i, ⟪e i,K (x+r•z) (e i)⟫ ∂γ) := by
      rw [integral_finsetSum _ (fun i _ => hright i), Finset.mul_sum]
    _ = _ := by congr 1; apply integral_congr_ae; filter_upwards [] with z; congr 1; ext i; exact real_inner_comm _ _

end GaussianPropeller.HeatConvolution

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.HeatConvolution
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open GaussianPropeller.Stein


theorem solution.{uι} : type_of% @_root_.OAI.GaussianPropeller.HeatConvolution.stein_trace.{uι} := @_root_.OAI.GaussianPropeller.HeatConvolution.stein_trace.{uι}
