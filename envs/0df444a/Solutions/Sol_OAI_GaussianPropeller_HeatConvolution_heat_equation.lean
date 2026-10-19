-- Prove2me | solution 1 for OAI.GaussianPropeller.HeatConvolution.heat_equation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:02:15.22098+00:00
-- url     : https://prove2.me/submissions/5f2ea186-ffc4-4b28-b39d-60bdcce5aec9

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/HeatConvolution.lean:L170-L206
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.HeatConvolution.heat_equation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Theorems.Thm_OAI_GaussianPropeller_HeatConvolution_stein_trace

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
-- [generator] dropped: open GaussianPropeller.Stein
variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

section General
variable {V : Type uV} [NormedAddCommGroup V]

lemma integrable_shift [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {F : E → V} (hF : Continuous F) {B : ℝ}
    (hB : ∀ x, ‖F x‖ ≤ B) (t : ℝ) (x : E) :
    Integrable (fun z => F (x+Real.sqrt t • z)) γ :=
  Integrable.mono' (integrable_const B) (by fun_prop) (ae_of_all _ (fun z => hB _))

variable [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

lemma time_deriv_heat {F : E → V} {D : E → E →L[ℝ] V}
    (hD : ∀ x, HasFDerivAt F (D x) x) (hcD : Continuous D)
    {B C : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (hC : ∀ x, ‖D x‖ ≤ C)
    {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => heat F s x)
      ((1/(2*Real.sqrt t)) • (∫ z, D (x+Real.sqrt t • z) z ∂γ)) t := by
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun x => (hD x).continuousAt)
  have hC0 : 0 ≤ C := (norm_nonneg (D 0)).trans (hC 0)
  have hp : 0 < Real.sqrt (t/2) := Real.sqrt_pos.mpr (by linarith)
  have hi : Integrable (fun z : E => ‖z‖) γ := (IsGaussian.integrable_id (μ := γ)).norm
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := γ) (x₀ := t) (F := fun s z => F (x+Real.sqrt s • z))
    (F' := fun s z => (1/(2*Real.sqrt s)) • D (x+Real.sqrt s • z) z)
    (s := Ioo (t/2) (2*t)) (bound := fun z => (1/(2*Real.sqrt (t/2)))*C*‖z‖)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall (fun s => by fun_prop))
    (integrable_shift hc hB t x) (by fun_prop) ?_ (hi.const_mul _) ?_
  · simpa only [integral_smul, heat] using hd.2
  · filter_upwards [] with z s hs
    have hs0 : 0 < s := by linarith only [hs.1, ht]
    have hsqrt : Real.sqrt (t/2) ≤ Real.sqrt s := Real.sqrt_le_sqrt hs.1.le
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (by positivity))]
    calc
      (1/(2*Real.sqrt s))*‖D (x+Real.sqrt s • z) z‖ ≤
          (1/(2*Real.sqrt (t/2)))*(C*‖z‖) :=
        mul_le_mul (one_div_le_one_div_of_le (by positivity) (by linarith))
          ((D _).le_opNorm z |>.trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)))
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · filter_upwards [] with z s hs
    have hs0 : s ≠ 0 := ne_of_gt (by linarith only [hs.1, ht])
    simpa only [Function.comp_def, map_smul] using
      (hD (x+Real.sqrt s • z)).comp_hasDerivAt s
        ((Real.hasDerivAt_sqrt hs0).smul_const z |>.const_add x)

end General

lemma heat_equation {F : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hF : ∀ x, HasFDerivAt F (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (K x) x) (hcK : Continuous K)
    {B C D : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (hC : ∀ x, ‖g x‖ ≤ C)
    (hD : ∀ x, ‖K x‖ ≤ D) {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => heat F s x)
      ((∑ i : ι, ⟪(heat K t x) (EuclideanSpace.basisFun ι ℝ i),
        EuclideanSpace.basisFun ι ℝ i⟫)/2) t := by
  have hcg : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have hd := time_deriv_heat hF (by fun_prop) hB (fun x => by
    rw [innerSL_apply_norm]; exact hC x) ht x
  simp only [innerSL_apply_apply, smul_eq_mul] at hd
  rw [stein_trace hg hcK hC hD] at hd
  have hi : Integrable (fun z => K (x+Real.sqrt t • z)) γ :=
    Integrable.mono' (integrable_const D) (by fun_prop) (ae_of_all _ (fun z => hD _))
  have heq : (∫ z, ∑ i : ι, ⟪K (x+Real.sqrt t • z)
      (EuclideanSpace.basisFun ι ℝ i), EuclideanSpace.basisFun ι ℝ i⟫ ∂γ) =
      ∑ i : ι, ⟪(heat K t x) (EuclideanSpace.basisFun ι ℝ i),
        EuclideanSpace.basisFun ι ℝ i⟫ := by
    let e := EuclideanSpace.basisFun ι ℝ
    have hii (i : ι) : Integrable (fun z => ⟪K (x+Real.sqrt t • z) (e i),e i⟫) γ :=
      ((ContinuousLinearMap.apply ℝ E (e i)).integrable_comp hi).inner_const (e i)
    rw [integral_finsetSum _ (fun i _ => hii i)]
    apply Finset.sum_congr rfl
    intro i _
    change (∫ z, ⟪K (x+Real.sqrt t • z) (e i),e i⟫ ∂γ) = ⟪heat K t x (e i),e i⟫
    calc
      _ = ∫ z, ⟪e i,K (x+Real.sqrt t • z) (e i)⟫ ∂γ :=
        integral_congr_ae (ae_of_all _ (fun z => real_inner_comm _ _))
      _ = ⟪e i,∫ z, K (x+Real.sqrt t • z) (e i) ∂γ⟫ :=
        integral_inner ((ContinuousLinearMap.apply ℝ E (e i)).integrable_comp hi) _
      _ = _ := by
        rw [← ContinuousLinearMap.integral_apply hi]
        exact real_inner_comm _ _
  rw [heq] at hd
  convert! hd using 1
  field_simp [ne_of_gt (Real.sqrt_pos.mpr ht)]

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


theorem solution.{uι} : type_of% @_root_.OAI.GaussianPropeller.HeatConvolution.heat_equation.{uι} := @_root_.OAI.GaussianPropeller.HeatConvolution.heat_equation.{uι}
