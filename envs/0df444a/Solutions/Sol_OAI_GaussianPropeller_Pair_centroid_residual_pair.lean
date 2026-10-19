-- Prove2me | solution 1 for OAI.GaussianPropeller.Pair.centroid_residual_pair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:59:42.369978+00:00
-- url     : https://prove2.me/submissions/b765f1fb-4f36-43ac-81e2-aa156ae2c540

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/PairBounds.lean:L193-L252
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Pair.centroid_residual_pair. The node keeps its source
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
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral
import Theorems.Thm_OAI_GaussianPropeller_PairGeometry_orthonormal_triple_of_gram_pos
import Theorems.Thm_OAI_GaussianPropeller_PairIntegral_lintegral_triangle_gaussian

-- ---- from OAI.Probability.GaussianPropeller.GaussianCoordinates ----
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
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Analytic
section FamilyLaw
variable {E : Type uE} {ι : Type uι} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

lemma covariance_inner_stdGaussian (u v : E) :
    cov[fun x => ⟪u,x⟫, fun x => ⟪v,x⟫; stdGaussian E] = ⟪u,v⟫ := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply]

lemma hasGaussianLaw_innerFamily (v : ι → E) :
    HasGaussianLaw (fun x : E => fun i => ⟪v i,x⟫) (stdGaussian E) := by
  exact (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun
    (ContinuousLinearMap.pi (fun i => InnerProductSpace.toDual ℝ E (v i)))

lemma indep_innerFamily (v : ι → E) (hv : Pairwise (fun i j => ⟪v i,v j⟫ = 0)) :
    iIndepFun (fun i x => ⟪v i,x⟫) (stdGaussian E) := by
  exact (hasGaussianLaw_innerFamily v).iIndepFun_of_covariance_eq_zero
    (fun i j hij => (covariance_inner_stdGaussian _ _).trans (hv hij))

lemma map_inner_stdGaussian (v : E) :
    (stdGaussian E).map (fun x => ⟪v,x⟫) = gaussianReal 0 (‖v‖^2).toNNReal := by
  change (stdGaussian E).map (InnerProductSpace.toDual ℝ E v) = _
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, LinearIsometryEquiv.norm_map]

end FamilyLaw

end GaussianPropeller.Analytic

namespace GaussianPropeller.Analytic

open scoped ENNReal

section TripleLaw
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma map_orthonormal_triple_stdGaussian (v : Fin 3 → E) (hv : Orthonormal ℝ v) :
    (stdGaussian E).map (fun x => (⟪v 0,x⟫, ⟪v 1,x⟫, ⟪v 2,x⟫)) =
      (gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hi := indep_innerFamily v (fun _ _ hij => hv.2 hij)
  have hm (i : Fin 3) : (stdGaussian E).map (fun x => ⟪v i,x⟫) = gaussianReal 0 1 := by
    rw [map_inner_stdGaussian, hv.1 i]
    norm_num
  have hp := hi.indepFun_prodMk (fun _ => by fun_prop) 1 2 0 (by decide) (by decide)
  rw [hp.symm.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop), hm,
    (hi.indepFun (by decide : (1:Fin 3) ≠ 2)).map_prod_eq_prod_map_map
      (by fun_prop) (by fun_prop), hm, hm]

lemma lintegral_orthonormal_triple (v : Fin 3 → E) (hv : Orthonormal ℝ v)
    (f : ℝ × ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f (⟪v 0,x⟫,⟪v 1,x⟫,⟪v 2,x⟫) ∂stdGaussian E =
      ∫⁻ s : ℝ, (∫⁻ u : ℝ, (∫⁻ w : ℝ, f (s,u,w) ∂gaussianReal 0 1)
        ∂gaussianReal 0 1) ∂gaussianReal 0 1 := by
  rw [← lintegral_map hf (by fun_prop), map_orthonormal_triple_stdGaussian v hv,
    lintegral_prod _ hf.aemeasurable]
  apply lintegral_congr
  intro s
  exact lintegral_prod _ (hf.comp (measurable_const.prodMk measurable_id)).aemeasurable

end TripleLaw
end GaussianPropeller.Analytic

end OAI

-- ---- from OAI.Probability.GaussianPropeller.PairIntegral ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

namespace GaussianPropeller.PairIntegral

lemma measurable_triangle : Measurable (fun p : ℝ × ℝ × ℝ => triangle p.1 p.2.1 p.2.2) := by
  unfold triangle
  exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop))
    (Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop)
      measurable_const) measurable_const

end GaussianPropeller.PairIntegral

namespace GaussianPropeller.PairIntegral

end GaussianPropeller.PairIntegral

namespace GaussianPropeller.PairIntegral

lemma integral_le_of_lintegral_ofReal_le {X : Type uX} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : Integrable f μ) {b : ℝ} (hb : 0 ≤ b)
    (h : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal b) : ∫ x, f x ∂μ ≤ b := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  have hh := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) h
  rw [ENNReal.toReal_ofReal hb] at hh
  linarith only [hh, ENNReal.toReal_nonneg (a := ∫⁻ x, ENNReal.ofReal (-f x) ∂μ)]

end GaussianPropeller.PairIntegral

end OAI

-- ---- from OAI.Probability.GaussianPropeller.PairBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

universe uE

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
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

namespace GaussianPropeller.PairGeometry

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end GaussianPropeller.PairGeometry

namespace GaussianPropeller.Pair

open GaussianPropeller.Analytic GaussianPropeller.PairIntegral GaussianPropeller.PairGeometry

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma triangle_inner_bound (e u v : E) (he : ‖e‖ = 1)
    (heu : ⟪e,u⟫ = 0) (hev : ⟪e,v⟫ = 0)
    (hd : 0 < ‖u‖^2*‖v‖^2-⟪u,v⟫^2) :
    ∫⁻ x, triangle ⟪e,x⟫ ⟪u,x⟫ ⟪v,x⟫ ∂stdGaussian E ≤
      ENNReal.ofReal (9/(2*Real.pi*Real.sqrt (2*Real.pi)*
        Real.sqrt (‖u‖^2*‖v‖^2-⟪u,v⟫^2))) := by
  obtain ⟨f,a,b,c,hf,he',ha,hc,hu,hv,hd'⟩ := orthonormal_triple_of_gram_pos e u v he heu hev hd
  have hm : Measurable (fun p : ℝ × ℝ × ℝ => triangle p.1 (a*p.2.1) (b*p.2.1+c*p.2.2)) :=
    measurable_triangle.comp (show Measurable (fun p : ℝ × ℝ × ℝ =>
      (p.1, a*p.2.1, b*p.2.1+c*p.2.2)) from by fun_prop)
  have hs : Real.sqrt (‖u‖^2*‖v‖^2-⟪u,v⟫^2) = a*c := by
    rw [← hd', Real.sqrt_sq (mul_nonneg ha.le hc.le)]
  have hfun (x : E) : triangle ⟪e,x⟫ ⟪u,x⟫ ⟪v,x⟫ =
      triangle ⟪f 0,x⟫ (a*⟪f 1,x⟫) (b*⟪f 1,x⟫+c*⟪f 2,x⟫) := by
    rw [← he', hu, hv]
    simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial]
  calc
    _ = ∫⁻ t : ℝ, (∫⁻ w : ℝ, (∫⁻ y : ℝ, triangle t (a*w) (b*w+c*y)
        ∂gaussianReal 0 1) ∂gaussianReal 0 1) ∂gaussianReal 0 1 := by
      simp_rw [hfun]
      exact lintegral_orthonormal_triple f hf _ hm
    _ ≤ ENNReal.ofReal (9/(2*Real.pi*Real.sqrt (2*Real.pi)*a*c)) :=
      lintegral_triangle_gaussian b ha hc
    _ = _ := by
      rw [hs]
      congr 1
      congr 1
      ring

lemma setIntegral_inner_le_triangle (K : Set E) (hK : MeasurableSet K)
    (e u v : E) (he : ‖e‖ = 1) (heu : ⟪e,u⟫ = 0) (hev : ⟪e,v⟫ = 0)
    (hd : 0 < ‖u‖^2*‖v‖^2-⟪u,v⟫^2)
    (huK : ∀ x ∈ K, ⟪u,x⟫ ≤ ⟪e,x⟫) (hvK : ∀ x ∈ K, ⟪v,x⟫ ≤ ⟪e,x⟫)
    (hu0 : ∫ x in K, ⟪u,x⟫ ∂stdGaussian E = 0)
    (hv0 : ∫ x in K, ⟪v,x⟫ ∂stdGaussian E = 0) :
    ∫ x in K, ⟪e,x⟫ ∂stdGaussian E ≤
      9/(2*Real.pi*Real.sqrt (2*Real.pi)*Real.sqrt (‖u‖^2*‖v‖^2-⟪u,v⟫^2)) := by
  let f : E → ℝ := K.indicator (fun x => ⟪e,x⟫+⟪u,x⟫+⟪v,x⟫)
  have hi (w : E) : Integrable (fun x => ⟪w,x⟫) (stdGaussian E) :=
    IsGaussian.integrable_dual _ (InnerProductSpace.toDual ℝ E w)
  have hfi : Integrable f (stdGaussian E) := ((hi e).add (hi u) |>.add (hi v)).indicator hK
  have hfint : ∫ x, f x ∂stdGaussian E = ∫ x in K, ⟪e,x⟫ ∂stdGaussian E := by
    rw [show f = K.indicator (fun x => ⟪e,x⟫+⟪u,x⟫+⟪v,x⟫) from rfl,
      integral_indicator hK, integral_add (f := fun x => ⟪e,x⟫+⟪u,x⟫)
        ((hi e).integrableOn.add (hi u).integrableOn) (hi v).integrableOn,
      integral_add (hi e).integrableOn (hi u).integrableOn, hu0, hv0]
    ring
  rw [← hfint]
  apply integral_le_of_lintegral_ofReal_le hfi (by positivity)
  apply le_trans _ (triangle_inner_bound e u v he heu hev hd)
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ K
  · simp only [f, Set.indicator_of_mem hx, triangle, ite_eq_left (huK x hx), ite_eq_left (hvK x hx)]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  · simp only [f, Set.indicator_of_notMem hx, ENNReal.ofReal_zero, zero_le]

end GaussianPropeller.Pair

namespace GaussianPropeller.Pair

open GaussianPropeller.Analytic GaussianPropeller.PairIntegral

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integral_inner_eq_inner_integral (K : Set E) (w : E) :
    ∫ x in K, ⟪w,x⟫ ∂stdGaussian E = ⟪w, ∫ x in K, x ∂stdGaussian E⟫ := by
  exact (InnerProductSpace.toDual ℝ E w).integral_comp_comm
    IsGaussian.integrable_id.integrableOn

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sqrt_gram_smul {u v : E} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (‖a • u‖^2*‖b • v‖^2-⟪a • u,b • v⟫^2) =
      a*b*Real.sqrt (‖u‖^2*‖v‖^2-⟪u,v⟫^2) := by
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
  rw [show (a*‖u‖)^2*(b*‖v‖)^2-(b*(a*⟪u,v⟫))^2 =
    (a*b)^2*(‖u‖^2*‖v‖^2-⟪u,v⟫^2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg ha hb)]

lemma centroid_residual_pair (K : Set E) (hK : MeasurableSet K)
    (z r s : E) (hz : z ≠ 0) (hzK : ∫ x in K, x ∂stdGaussian E = z)
    (hzr : ⟪z,r⟫ = 0) (hzs : ⟪z,s⟫ = 0)
    {L M : ℝ} (hL : 0 < L) (hM : 0 < M)
    (hrK : ∀ x ∈ K, ⟪r,x⟫ ≤ L*⟪z,x⟫)
    (hsK : ∀ x ∈ K, ⟪s,x⟫ ≤ M*⟪z,x⟫)
    (hd : 0 < ‖r‖^2*‖s‖^2-⟪r,s⟫^2) :
    Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2) ≤
      9*‖z‖*L*M/(2*Real.pi*Real.sqrt (2*Real.pi)) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let e := ‖z‖⁻¹ • z
  let u := (L*‖z‖)⁻¹ • r
  let v := (M*‖z‖)⁻¹ • s
  have he : ‖e‖ = 1 := by simp [e, norm_smul, hn.ne']
  have heu : ⟪e,u⟫ = 0 := by simp [e,u,inner_smul_left,inner_smul_right,hzr]
  have hev : ⟪e,v⟫ = 0 := by simp [e,v,inner_smul_left,inner_smul_right,hzs]
  have huv : 0 < ‖u‖^2*‖v‖^2-⟪u,v⟫^2 := by
    dsimp [u,v]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos hL hn)),
      abs_of_pos (inv_pos.mpr (mul_pos hM hn)), inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_trivial]
    nlinarith only [mul_pos (sq_pos_of_pos (inv_pos.mpr (mul_pos hL hn)))
      (mul_pos (sq_pos_of_pos (inv_pos.mpr (mul_pos hM hn))) hd)]
  have huK (x : E) (hx : x ∈ K) : ⟪u,x⟫ ≤ ⟪e,x⟫ := by
    simp only [u,e,inner_smul_left,starRingEnd_apply,star_trivial]
    have hh := mul_le_mul_of_nonneg_left (hrK x hx) (inv_nonneg.mpr (mul_pos hL hn).le)
    calc
      _ ≤ (L*‖z‖)⁻¹*(L*⟪z,x⟫) := hh
      _ = _ := by field_simp
  have hvK (x : E) (hx : x ∈ K) : ⟪v,x⟫ ≤ ⟪e,x⟫ := by
    simp only [v,e,inner_smul_left,starRingEnd_apply,star_trivial]
    have hh := mul_le_mul_of_nonneg_left (hsK x hx) (inv_nonneg.mpr (mul_pos hM hn).le)
    calc
      _ ≤ (M*‖z‖)⁻¹*(M*⟪z,x⟫) := hh
      _ = _ := by field_simp
  have hu0 : ∫ x in K, ⟪u,x⟫ ∂stdGaussian E = 0 := by
    rw [integral_inner_eq_inner_integral, hzK]
    simp only [u, inner_smul_left, starRingEnd_apply, star_trivial,
      real_inner_comm z r, hzr, mul_zero]
  have hv0 : ∫ x in K, ⟪v,x⟫ ∂stdGaussian E = 0 := by
    rw [integral_inner_eq_inner_integral, hzK]
    simp only [v, inner_smul_left, starRingEnd_apply, star_trivial,
      real_inner_comm z s, hzs, mul_zero]
  have heK : ∫ x in K, ⟪e,x⟫ ∂stdGaussian E = ‖z‖ := by
    rw [integral_inner_eq_inner_integral, hzK]
    simp only [e,inner_smul_left,starRingEnd_apply,star_trivial,real_inner_self_eq_norm_sq]
    field_simp
  have hh := setIntegral_inner_le_triangle K hK e u v he heu hev huv huK hvK hu0 hv0
  rw [heK] at hh
  have hsqrt : Real.sqrt (‖u‖^2*‖v‖^2-⟪u,v⟫^2) =
      (L*‖z‖)⁻¹*(M*‖z‖)⁻¹*Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2) :=
    sqrt_gram_smul (by positivity) (by positivity)
  rw [hsqrt] at hh
  have hp : 0 < Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2) := Real.sqrt_pos.mpr hd
  have hc : 0 < 2*Real.pi*Real.sqrt (2*Real.pi) := by positivity
  have hh' := (le_div_iff₀ (show 0 < 2*Real.pi*Real.sqrt (2*Real.pi)*
      ((L*‖z‖)⁻¹*(M*‖z‖)⁻¹*Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2)) by positivity)).mp hh
  apply (le_div_iff₀ hc).mpr
  have := mul_le_mul_of_nonneg_right hh' (show 0 ≤ ‖z‖*L*M by positivity)
  convert this using 1 <;> field_simp

end GaussianPropeller.Pair

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Pair
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
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open GaussianPropeller.Analytic GaussianPropeller.PairIntegral


theorem solution.{uE} : type_of% @_root_.OAI.GaussianPropeller.Pair.centroid_residual_pair.{uE} := @_root_.OAI.GaussianPropeller.Pair.centroid_residual_pair.{uE}
