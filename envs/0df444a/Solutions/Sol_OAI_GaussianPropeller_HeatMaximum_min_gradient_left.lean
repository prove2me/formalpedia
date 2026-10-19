-- Prove2me | solution 1 for OAI.GaussianPropeller.HeatMaximum.min_gradient_left
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:08:35.227517+00:00
-- url     : https://prove2.me/submissions/9cefb1e1-09a9-475b-8277-de1d7de63820

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/HeatMaximum.lean:L130-L160
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.HeatMaximum.min_gradient_left. The node keeps its source
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
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum

-- ---- from OAI.Probability.GaussianPropeller.HeatMaximum ----
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

open Set Filter
open scoped Topology RealInnerProductSpace

namespace GaussianPropeller.HeatMaximum

section Spatial
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasDerivAt_line {v : E → ℝ} {p : E → E}
    (hp : ∀ x, HasFDerivAt v (innerSL ℝ (p x)) x) (x e : E) (s : ℝ) :
    HasDerivAt (fun s : ℝ => v (x+s • e)) (⟪p (x+s • e),e⟫) s := by
  convert (hp (x+s • e)).comp_hasDerivAt s
    (((hasDerivAt_id s).smul_const e).const_add x) using 1 <;> first | rfl | simp

lemma min_gradient_left {v : E → ℝ} {p : E → E} {a b σ : ℝ} {x y : E}
    (hp : ∀ x, HasFDerivAt v (innerSL ℝ (p x)) x) (ha : 0 < a)
    (hm : ∀ x' y', deficit v a b σ x y ≤ deficit v a b σ x' y') :
    p (a • x+b • y)-p x = -(2*σ) • x := by
  let e := p (a • x+b • y)-p x+(2*σ) • x
  have hm' : IsLocalMin (fun s : ℝ => deficit v a b σ (x+s • e) y) 0 := by
    apply Filter.Eventually.of_forall
    intro s
    simpa only [zero_smul, add_zero] using hm (x+s • e) y
  have hz : HasDerivAt (fun s : ℝ => v (a • (x+s • e)+b • y))
      (a*⟪p (a • x+b • y),e⟫) 0 := by
    have hpath : HasDerivAt (fun s : ℝ => a • (x+s • e)+b • y) (a • e) 0 := by
      convert ((((hasDerivAt_id (0:ℝ)).smul_const e).const_add x).const_smul a).add_const (b • y) using 1 <;> simp
    convert (hp (a • (x+(0:ℝ) • e)+b • y)).comp_hasDerivAt 0 hpath using 1 <;>
      first | rfl | simp [innerSL_apply_apply]
  have hx := hasDerivAt_line hp x e 0
  have hn := (((hasDerivAt_id (0:ℝ)).smul_const e).const_add x).norm_sq
  have hd := ((hz.sub (hx.const_mul a)).sub_const (b*v y)).add
    (((hn.const_mul a).const_add 1 |>.add_const (b*‖y‖^2)).const_mul σ)
  have hzero := hm'.hasDerivAt_eq_zero hd
  have hei : ⟪e,e⟫ = ⟪p (a • x+b • y),e⟫-⟪p x,e⟫+(2*σ)*⟪x,e⟫ := by
    change ⟪p (a • x+b • y)-p x+(2*σ) • x,e⟫ = _
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  rw [real_inner_self_eq_norm_sq] at hei
  have he : a*‖e‖^2 = 0 := by
    simp only [zero_smul, add_zero, id_eq, one_smul] at hzero
    rw [hei]
    nlinarith only [hzero]
  have he0 : e = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp he).resolve_left ha.ne'))
  dsimp only [e] at he0
  simpa only [neg_smul] using eq_neg_iff_add_eq_zero.mpr he0

end Spatial
end GaussianPropeller.HeatMaximum

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.HeatMaximum
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
open Set Filter
open scoped Topology RealInnerProductSpace


theorem solution.{uE} : type_of% @_root_.OAI.GaussianPropeller.HeatMaximum.min_gradient_left.{uE} := @_root_.OAI.GaussianPropeller.HeatMaximum.min_gradient_left.{uE}
