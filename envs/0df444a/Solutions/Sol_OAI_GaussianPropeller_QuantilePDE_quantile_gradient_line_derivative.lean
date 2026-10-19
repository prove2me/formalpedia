-- Prove2me | solution 1 for OAI.GaussianPropeller.QuantilePDE.quantile_gradient_line_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:04:32.994985+00:00
-- url     : https://prove2.me/submissions/1f8901bb-abca-4dce-8748-63df1fc84419

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/QuantileCalculus.lean:L30-L53
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.QuantilePDE.quantile_gradient_line_derivative. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus

-- ---- from OAI.Probability.GaussianPropeller.Quantile ----
namespace OAI

universe uX

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace GaussianPropeller.Quantile

lemma cdfIso_coe (x : ℝ) : (cdfIso x : ℝ) = Φ x := rfl
lemma q_of_mem {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : q p = cdfIso.symm ⟨p,hp⟩ := by
  simp [q, hp]
lemma Φ_q {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : Φ (q p) = p := by
  rw [q_of_mem hp, ← cdfIso_coe]
  exact congrArg Subtype.val (cdfIso.apply_symm_apply ⟨p,hp⟩)
lemma continuousOn_q : ContinuousOn q (Ioo (0:ℝ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun p : Ioo (0:ℝ) 1 => q p)
  have heq : (fun p : Ioo (0:ℝ) 1 => q p) = cdfIso.symm := by
    funext p
    exact q_of_mem p.2
  rw [heq]
  exact cdfIso.symm.continuous
lemma continuousAt_q {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : ContinuousAt q p :=
  continuousOn_q.continuousAt (isOpen_Ioo.mem_nhds hp)
lemma hasDerivAt_q {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    HasDerivAt q (φ (q p))⁻¹ p := by
  apply HasDerivAt.of_local_left_inverse (continuousAt_q hp) (hasDerivAt_Φ (q p))
    (ne_of_gt (φ_pos _))
  filter_upwards [isOpen_Ioo.mem_nhds hp] with y hy
  exact Φ_q hy
section Integration
variable {X : Type uX} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

end Integration
end GaussianPropeller.Quantile

end OAI

-- ---- from OAI.Probability.GaussianPropeller.QuantileCalculus ----
namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

open scoped RealInnerProductSpace
namespace GaussianPropeller.QuantilePDE
open GaussianPropeller.Quantile

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma quantile_fderiv {u : E → ℝ} {g : E} {x : E}
    (hu : u x ∈ Ioo (0:ℝ) 1) (hd : HasFDerivAt u (innerSL ℝ g) x) :
    HasFDerivAt (fun y => q (u y)) (innerSL ℝ ((φ (q (u x)))⁻¹ • g)) x := by
  have hh := (hasDerivAt_q hu).comp_hasFDerivAt x hd
  convert hh using 1 <;> (first | rfl | (ext y; simp))

lemma quantile_gradient_line_derivative {u : E → ℝ} {g : E → E}
    {K : E → E →L[ℝ] E} (hu : ∀ x, u x ∈ Ioo (0:ℝ) 1)
    (hdu : ∀ x, HasFDerivAt u (innerSL ℝ (g x)) x)
    (hdg : ∀ x, HasFDerivAt g (K x) x) (x e : E) :
    HasDerivAt (fun s : ℝ => ⟪(φ (q (u (x+s•e))))⁻¹ • g (x+s•e), e⟫)
      ((φ (q (u x)))⁻¹*⟪K x e,e⟫ +
        q (u x)*(φ (q (u x)))⁻¹^2*⟪g x,e⟫^2) 0 := by
  have hdx : HasDerivAt (fun s : ℝ => x+s•e) e 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const e).const_add x
  have hdv : HasDerivAt (fun s : ℝ => q (u (x+s•e)))
      ((φ (q (u x)))⁻¹*⟪g x,e⟫) 0 := by
    simpa [Function.comp_def] using (quantile_fderiv (hu (x+0•e)) (hdu (x+0•e))).comp_hasDerivAt 0 hdx
  have hdφ := (hasDerivAt_φ (q (u (x+0•e)))).comp 0 hdv
  have hdi := hdφ.inv (ne_of_gt (φ_pos _))
  have hdg' : HasDerivAt (fun s : ℝ => g (x+s•e)) (K x e) 0 := by
    simpa only [Function.comp_def, zero_smul, add_zero] using (hdg (x+0•e)).comp_hasDerivAt 0 hdx
  have hi : HasDerivAt (fun s : ℝ => ⟪g (x+s•e), e⟫) ⟪K x e,e⟫ 0 := by
    simpa using hdg'.inner ℝ (hasDerivAt_const (0:ℝ) e)
  have hh := hdi.mul hi
  convert hh using 1 <;> try rfl
  · funext s; simp only [real_inner_smul_left, Function.comp_def, Pi.mul_apply, Pi.inv_apply]
  · simp only [Function.comp_def, zero_smul, add_zero, Pi.inv_apply]
    field_simp [ne_of_gt (φ_pos (q (u x)))]
    ring

end GaussianPropeller.QuantilePDE

namespace GaussianPropeller.SmoothCDF
open GaussianPropeller.Quantile
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end GaussianPropeller.SmoothCDF

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.QuantilePDE
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open GaussianPropeller.Quantile


theorem solution.{uE} : type_of% @_root_.OAI.GaussianPropeller.QuantilePDE.quantile_gradient_line_derivative.{uE} := @_root_.OAI.GaussianPropeller.QuantilePDE.quantile_gradient_line_derivative.{uE}
