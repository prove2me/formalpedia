-- Prove2me | solution 1 for OAI.GaussianPropeller.EhrhardSmooth.qheat_concave
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:13:19.838989+00:00
-- url     : https://prove2.me/submissions/be7b114b-e32c-4daf-811c-e66dc16d1349

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/SmoothedConcavity.lean:L82-L143
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.EhrhardSmooth.qheat_concave. The node keeps its source
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
import Theorems.Thm_OAI_GaussianPropeller_HeatConvolution_fderiv_heat
import Theorems.Thm_OAI_GaussianPropeller_HeatConvolution_heat_equation
import Theorems.Thm_OAI_GaussianPropeller_HeatMaximum_heat_concave
import Theorems.Thm_OAI_GaussianPropeller_QuantilePDE_quantile_gradient_line_derivative
import Theorems.Thm_OAI_GaussianPropeller_SmoothCDF_hess_bound

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

lemma continuous_heat [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {F : E → V} (hF : Continuous F) {B : ℝ}
    (hB : ∀ x, ‖F x‖ ≤ B) : Continuous (fun p : ℝ × E => heat F p.1 p.2) := by
  apply continuous_of_dominated (bound := fun _ : E => B)
  · intro p; fun_prop
  · intro p; exact ae_of_all _ (fun z => hB _)
  · exact integrable_const _
  · filter_upwards [] with z; fun_prop

variable [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

end General

lemma heat_gradient {F : E → ℝ} {g : E → E}
    (hF : ∀ x, HasFDerivAt F (innerSL ℝ (g x)) x) (hcg : Continuous g)
    {B C : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (hC : ∀ x, ‖g x‖ ≤ C)
    (t : ℝ) (x : E) :
    HasFDerivAt (heat F t) (innerSL ℝ (heat g t x)) x := by
  have hd := fderiv_heat hF (by fun_prop) hB (fun x => by
    rw [innerSL_apply_norm]; exact hC x) t x
  have heq : heat (fun y => innerSL ℝ (g y)) t x = innerSL ℝ (heat g t x) :=
    (innerSL ℝ).integral_comp_comm (integrable_shift hcg hC t x)
  rwa [heq] at hd

end GaussianPropeller.HeatConvolution

end OAI

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
lemma q_Φ (x : ℝ) : q (Φ x) = x := by
  rw [q_of_mem (Φ_mem x)]
  exact cdfIso.symm_apply_apply x
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
lemma strictMonoOn_q : StrictMonoOn q (Ioo (0:ℝ) 1) := by
  intro a ha b hb hab
  rw [q_of_mem ha, q_of_mem hb]
  exact cdfIso.symm.strictMono hab

lemma I_pos (p : ℝ) : 0 < I p := φ_pos _
lemma I_Φ (x : ℝ) : I (Φ x) = φ x := by simp [I, q_Φ]
lemma hasDerivAt_I {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : HasDerivAt I (-q p) p := by
  convert (hasDerivAt_φ (q p)).comp p (hasDerivAt_q hp) using 1 <;>
    first | rfl | field_simp [ne_of_gt (φ_pos (q p))]
lemma antitoneOn_I_deriv : AntitoneOn (fun p => -q p) (Ioo (0:ℝ) 1) := by
  intro a ha b hb hab
  exact neg_le_neg (strictMonoOn_q.monotoneOn ha hb hab)
lemma concaveOn_I : ConcaveOn ℝ (Ioo (0:ℝ) 1) I := by
  have hanti : AntitoneOn (deriv I) (Ioo (0:ℝ) 1) := by
    intro a ha b hb hab
    rw [(hasDerivAt_I ha).deriv, (hasDerivAt_I hb).deriv]
    exact antitoneOn_I_deriv ha hb hab
  apply (hanti.mono interior_subset).concaveOn_of_deriv (convex_Ioo 0 1)
  · exact fun p hp => (hasDerivAt_I hp).continuousAt.continuousWithinAt
  · exact fun p hp => (hasDerivAt_I (interior_subset hp)).differentiableAt.differentiableWithinAt

lemma concave_le_tangent {S : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ S f)
    {x y d : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f d x) :
    f y ≤ f x+d*(y-x) := by
  rcases lt_trichotomy x y with h | rfl | h
  · have hh := hf.slope_le_of_hasDerivAt hx hy h hd
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr h)).mp hh
    linarith
  · simp
  · have hh := hf.le_slope_of_hasDerivAt hy hx h hd
    rw [slope_def_field] at hh
    have hh' := (le_div_iff₀ (sub_pos.mpr h)).mp hh
    nlinarith only [hh']

lemma I_le_tangent {p r : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) (hr : r ∈ Ioo (0:ℝ) 1) :
    I r ≤ I p-q p*(r-p) := by
  simpa only [neg_mul, sub_eq_add_neg] using concave_le_tangent concaveOn_I hp hr (hasDerivAt_I hp)

lemma φ_le_zero (x : ℝ) : φ x ≤ φ 0 := by
  unfold φ
  simp only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one]
  exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))

section Integration
variable {X : Type uX} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

lemma integrable_Φ_comp {f : X → ℝ} (hf : AEStronglyMeasurable f μ) :
    Integrable (fun x => Φ (f x)) μ := by
  apply Integrable.mono' (integrable_const (1:ℝ)) (continuous_Φ.comp_aestronglyMeasurable hf)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]
  exact (Φ_lt_one _).le
lemma integrable_φ_comp {f : X → ℝ} (hf : AEStronglyMeasurable f μ) :
    Integrable (fun x => φ (f x)) μ := by
  apply Integrable.mono' (integrable_const (φ 0)) (continuous_φ.comp_aestronglyMeasurable hf)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (φ_pos _)]
  exact φ_le_zero _
lemma integral_Φ_mem {f : X → ℝ} (hf : AEStronglyMeasurable f μ) :
    (∫ x, Φ (f x) ∂μ) ∈ Ioo (0:ℝ) 1 := by
  have hpos {g : X → ℝ} (hg : Integrable g μ) (hh : ∀ x, 0 < g x) : 0 < ∫ x, g x ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun x => (hh x).le) hg).mpr
    have heq : Function.support g = univ := by ext x; simp [Function.mem_support, ne_of_gt (hh x)]
    simp [heq]
  refine ⟨hpos (integrable_Φ_comp hf) (fun x => Φ_pos _), ?_⟩
  have hh := hpos ((integrable_const (1:ℝ)).sub (integrable_Φ_comp hf))
    (fun x => sub_pos.mpr (Φ_lt_one (f x)))
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (integrable_const (1:ℝ)) (integrable_Φ_comp hf), integral_const] at hh
  simp only [probReal_univ, smul_eq_mul, one_mul] at hh
  linarith only [hh]

lemma integral_φ_le_I {f : X → ℝ} (hf : AEStronglyMeasurable f μ) :
    (∫ x, φ (f x) ∂μ) ≤ I (∫ x, Φ (f x) ∂μ) := by
  let p := ∫ x, Φ (f x) ∂μ
  have hp : p ∈ Ioo (0:ℝ) 1 := integral_Φ_mem hf
  have hi := integral_mono (integrable_φ_comp hf)
    ((integrable_const (I p)).sub (((integrable_Φ_comp hf).sub (integrable_const p)).const_mul (q p)))
    (fun x => by simpa only [I_Φ, Pi.sub_apply] using I_le_tangent hp (Φ_mem (f x)))
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (integrable_const (I p)), integral_const, integral_const_mul,
    integral_sub (integrable_Φ_comp hf) (integrable_const p), integral_const] at hi
  · simpa only [probReal_univ, smul_eq_mul, one_mul, show (∫ x, Φ (f x) ∂μ) = p from rfl,
      sub_self, mul_zero, sub_zero] using hi
  · exact ((integrable_Φ_comp hf).sub (integrable_const p)).const_mul (q p)

lemma hasDerivAt_integral_shift {f : X → ℝ} (hf : AEStronglyMeasurable f μ) (a : ℝ) :
    HasDerivAt (fun s => ∫ x, Φ (f x+s) ∂μ) (∫ x, φ (f x+a) ∂μ) a := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ) (bound := fun _ => φ 0)
    (F' := fun s x => φ (f x+s)) (by simp) ?_ (integrable_Φ_comp (hf.add_const a))
    (continuous_φ.comp_aestronglyMeasurable (hf.add_const a)) ?_ (integrable_const (φ 0)) ?_).2
  · exact Filter.Eventually.of_forall fun s => continuous_Φ.comp_aestronglyMeasurable (hf.add_const s)
  · filter_upwards [] with x
    intro s _
    rw [Real.norm_eq_abs, abs_of_pos (φ_pos _)]
    exact φ_le_zero _
  · filter_upwards [] with x
    intro s _
    simpa only [mul_one, Function.comp_def, id_eq] using (hasDerivAt_Φ (f x+s)).comp s ((hasDerivAt_id s).const_add (f x))

lemma hasDerivAt_quantile_shift {f : X → ℝ} (hf : AEStronglyMeasurable f μ) (a : ℝ) :
    HasDerivAt (fun s => q (∫ x, Φ (f x+s) ∂μ))
      ((∫ x, φ (f x+a) ∂μ)/I (∫ x, Φ (f x+a) ∂μ)) a := by
  convert (hasDerivAt_q (integral_Φ_mem (hf.add_const a))).comp a
    (hasDerivAt_integral_shift hf a) using 1 <;> first | rfl | (simp only [I]; ring)

lemma quantile_shift_le {f : X → ℝ} (hf : AEStronglyMeasurable f μ) {a : ℝ} (ha : 0 ≤ a) :
    q (∫ x, Φ (f x+a) ∂μ) ≤ q (∫ x, Φ (f x) ∂μ)+a := by
  have hd (s : ℝ) := (hasDerivAt_quantile_shift hf s).sub (hasDerivAt_id s)
  have hm : Antitone (fun s => q (∫ x, Φ (f x+s) ∂μ)-s) := antitone_of_hasDerivAt_nonpos hd
    (fun s => by
      have hh := (div_le_one (I_pos _)).mpr (integral_φ_le_I (hf.add_const s))
      exact sub_nonpos.mpr hh)
  have hh := hm ha
  simp only [add_zero, sub_zero] at hh
  linarith only [hh]

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

lemma trace_quantile_hessian {ι : Type uι} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (v a : ℝ) (g : E) (K : E →L[ℝ] E) :
    (∑ i : ι, (a*⟪K (e i),e i⟫ + v*a^2*⟪g,e i⟫^2)) - v*‖a • g‖^2 =
      a*(∑ i : ι, ⟪K (e i),e i⟫) := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    e.sum_sq_inner_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

end GaussianPropeller.QuantilePDE

namespace GaussianPropeller.SmoothCDF
open GaussianPropeller.Quantile
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma fderiv {f : E → ℝ} {g : E → E}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x) (x : E) :
    HasFDerivAt (fun y => Φ (f y)) (innerSL ℝ (grad f g x)) x := by
  have h := (hasDerivAt_Φ (f x)).comp_hasFDerivAt x (hf x)
  convert h using 1 <;> (first | rfl | (ext e; simp [grad]))

lemma grad_fderiv {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (K x) x) (x : E) :
    HasFDerivAt (grad f g) (hess f g K x) x := by
  have h := ((hasDerivAt_φ (f x)).comp_hasFDerivAt x (hf x)).smul (hg x)
  convert h using 1 <;> try rfl
  ext e
  simp only [hess, sub_apply, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul, Function.comp_def]
  module

lemma continuous_hess {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hf : Continuous f) (hg : Continuous g) (hK : Continuous K) : Continuous (hess f g K) := by
  have hφ := continuous_φ.comp hf
  unfold hess
  fun_prop

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma cdf_bound [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x : E) : ‖Φ (f x)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]; exact (Φ_lt_one _).le

lemma grad_bound {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : ∀ x, ‖g x‖ ≤ L) (x : E) : ‖grad f g x‖ ≤ φ 0*L := by
  rw [grad, norm_smul, Real.norm_eq_abs, abs_of_pos (φ_pos _)]
  exact mul_le_mul (φ_le_zero _) (hL x) (norm_nonneg _) (φ_pos _).le

end GaussianPropeller.SmoothCDF

end OAI

-- ---- from OAI.Probability.GaussianPropeller.SmoothedConcavity ----
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace

open scoped NNReal
namespace GaussianPropeller.EhrhardSmooth
open GaussianPropeller.Quantile GaussianPropeller.QuantilePDE GaussianPropeller.HeatConvolution
variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

lemma heat_mem {f : E → ℝ} (hf : Continuous f) (t : ℝ) (x : E) :
    heat (fun y => Φ (f y)) t x ∈ Ioo (0:ℝ) 1 := integral_Φ_mem (by fun_prop)

lemma continuous_qheat {f : E → ℝ} (hf : Continuous f) :
    Continuous (fun p : ℝ × E => qheat f p.1 p.2) := by
  have hh := continuous_heat (continuous_Φ.comp hf) (SmoothCDF.cdf_bound f)
  exact continuous_iff_continuousAt.mpr fun p =>
    (continuousAt_q (heat_mem hf p.1 p.2)).comp (f := fun p : ℝ × E => heat (fun y => Φ (f y)) p.1 p.2) hh.continuousAt

lemma qheat_zero (f : E → ℝ) (x : E) : qheat f 0 x = f x := by
  simp [qheat, heat, q_Φ]

lemma qheat_le {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (t : ℝ) (x y : E) :
    qheat f t x ≤ qheat f t y + L*‖x-y‖ := by
  have hc := hf.continuous
  have hfm : AEStronglyMeasurable (fun z : E => f (y+Real.sqrt t • z)) γ := by fun_prop
  have hxm : AEStronglyMeasurable (fun z : E => f (x+Real.sqrt t • z)) γ := by fun_prop
  have hxy (z : E) : f (x+Real.sqrt t • z) ≤ f (y+Real.sqrt t • z)+L*‖x-y‖ := by
    have hh := hf.dist_le_mul (x+Real.sqrt t • z) (y+Real.sqrt t • z)
    rw [Real.dist_eq, dist_eq_norm, add_sub_add_right_eq_sub] at hh
    linarith only [le_abs_self (f (x+Real.sqrt t • z)-f (y+Real.sqrt t • z)), hh]
  have hint : (∫ z : E, Φ (f (x+Real.sqrt t • z)) ∂γ) ≤
      ∫ z : E, Φ (f (y+Real.sqrt t • z)+L*‖x-y‖) ∂γ :=
    integral_mono (integrable_Φ_comp hxm) (integrable_Φ_comp (hfm.add_const _))
      (fun z => strictMono_Φ.monotone (hxy z))
  exact (strictMonoOn_q.monotoneOn (integral_Φ_mem hxm)
    (integral_Φ_mem (hfm.add_const _)) hint).trans (quantile_shift_le hfm (by positivity))

lemma qheat_lipschitz {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (t : ℝ) :
    LipschitzWith L (qheat f t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm, abs_le]
  have hxy := qheat_le hf t x y
  have hyx := qheat_le hf t y x
  rw [norm_sub_rev y x] at hyx
  constructor <;> linarith only [hxy,hyx]

lemma growth_bound {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (T : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, ∀ x, |qheat f t x| ≤ M+L*‖x‖ := by
  have hc : Continuous (fun t : ℝ => |qheat f t 0|) :=
    ((continuous_qheat hf.continuous).comp (continuous_id.prodMk continuous_const)).abs
  obtain ⟨M,hM⟩ := (isCompact_Icc.image hc).bddAbove
  refine ⟨max M 0, le_max_right _ _,?_⟩
  intro t ht x
  have hm : |qheat f t 0| ≤ max M 0 := (hM (mem_image_of_mem _ ht)).trans (le_max_left _ _)
  have hd := (qheat_lipschitz hf t).dist_le_mul x 0
  simp only [Real.dist_eq, dist_zero_right] at hd
  have hh := abs_sub_le (qheat f t x) (qheat f t 0) 0
  simp only [sub_zero] at hh
  linarith only [hh,hm,hd]

lemma qheat_concave {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (K x) x) (hK : Continuous K)
    {L : ℝ≥0} {D : ℝ} (hL : ∀ x, ‖g x‖ ≤ L) (hD : ∀ x, ‖K x‖ ≤ D)
    (hconc : ConcaveOn ℝ univ f) {T : ℝ} (hT : 0 ≤ T) :
    ConcaveOn ℝ univ (qheat f T) := by
  have hcf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hcg : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have hlip : LipschitzWith L f := lipschitzWith_of_nnnorm_fderiv_le
    (fun x => (hf x).differentiableAt) (fun x => by
      rw [(hf x).fderiv]
      exact_mod_cast (show ‖innerSL ℝ (g x)‖ ≤ L by rw [innerSL_apply_norm]; exact hL x))
  let F : E → ℝ := fun x => Φ (f x)
  let G : E → E := SmoothCDF.grad f g
  let J : E → E →L[ℝ] E := SmoothCDF.hess f g K
  have hF (x : E) : HasFDerivAt F (innerSL ℝ (G x)) x := SmoothCDF.fderiv hf x
  have hG (x : E) : HasFDerivAt G (J x) x := SmoothCDF.grad_fderiv hf hg x
  have hcG : Continuous G := continuous_iff_continuousAt.mpr (fun x => (hG x).continuousAt)
  have hcJ : Continuous J := SmoothCDF.continuous_hess hcf hcg hK
  have hFB (x : E) : ‖F x‖ ≤ 1 := SmoothCDF.cdf_bound f x
  have hGB (x : E) : ‖G x‖ ≤ φ 0*L := SmoothCDF.grad_bound hL x
  have hJB (x : E) : ‖J x‖ ≤ φ 0*(D+(L:ℝ)^2) := SmoothCDF.hess_bound L.coe_nonneg hL hD x
  let u : ℝ → E → ℝ := heat F
  let v : ℝ → E → ℝ := qheat f
  let p : ℝ → E → E := fun t x => (φ (v t x))⁻¹ • heat G t x
  let H : ℝ → E → E → ℝ := fun t x e =>
    (φ (v t x))⁻¹*⟪heat J t x e,e⟫ + v t x*(φ (v t x))⁻¹^2*⟪heat G t x,e⟫^2
  have hu (t : ℝ) (x : E) : u t x ∈ Ioo (0:ℝ) 1 := heat_mem hcf t x
  have hdu (t : ℝ) (x : E) : HasFDerivAt (u t) (innerSL ℝ (heat G t x)) x :=
    heat_gradient hF hcG hFB hGB t x
  have hdg (t : ℝ) (x : E) : HasFDerivAt (heat G t) (heat J t x) x :=
    fderiv_heat hG hcJ hGB hJB t x
  have hdv (t : ℝ) (x : E) : HasFDerivAt (v t) (innerSL ℝ (p t x)) x :=
    quantile_fderiv (hu t x) (hdu t x)
  obtain ⟨M,hM,hgrowth⟩ := growth_bound hlip T
  apply HeatMaximum.heat_concave (EuclideanSpace.basisFun ι ℝ)
    (fun i => (EuclideanSpace.basisFun ι ℝ).orthonormal.norm_eq_one i)
    (p := p) (H := H) hT L.coe_nonneg hM (continuous_qheat hcf)
  · change ConcaveOn ℝ univ (qheat f 0)
    rw [show qheat f 0 = f from funext (qheat_zero f)]
    exact hconc
  · intro t _ x; exact hdv t x
  · intro t _ x e
    exact quantile_gradient_line_derivative (hu t) (hdu t) (hdg t) x e
  · intro t ht x
    have hh := (hasDerivAt_q (hu t x)).comp t (heat_equation hF hG hcJ hFB hGB hJB ht.1 x)
    have heq := trace_quantile_hessian (EuclideanSpace.basisFun ι ℝ)
      (v t x) ((φ (v t x))⁻¹) (heat G t x) (heat J t x)
    change HasDerivAt (fun s => q (u s x))
      (((∑ i : ι, H t x (EuclideanSpace.basisFun ι ℝ i))-v t x*‖p t x‖^2)/2) t
    convert hh using 1 <;> try rfl
    change ((∑ i : ι, ((φ (v t x))⁻¹*⟪heat J t x (EuclideanSpace.basisFun ι ℝ i),
      EuclideanSpace.basisFun ι ℝ i⟫ + v t x*(φ (v t x))⁻¹^2*⟪heat G t x,
      EuclideanSpace.basisFun ι ℝ i⟫^2))-v t x*‖(φ (v t x))⁻¹ • heat G t x‖^2)/2 = _
    rw [heq]
    change (φ (q (u t x)))⁻¹*(∑ i : ι, ⟪heat J t x (EuclideanSpace.basisFun ι ℝ i),
      EuclideanSpace.basisFun ι ℝ i⟫)/2 = _
    ring
  · intro t _ x
    have hh := (hdv t x).le_of_lipschitz (qheat_lipschitz hlip t)
    simpa only [innerSL_apply_norm] using hh
  · exact hgrowth

end GaussianPropeller.EhrhardSmooth

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.EhrhardSmooth
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
open GaussianPropeller.Quantile GaussianPropeller.QuantilePDE GaussianPropeller.HeatConvolution


theorem solution.{uι} : type_of% @_root_.OAI.GaussianPropeller.EhrhardSmooth.qheat_concave.{uι} := @_root_.OAI.GaussianPropeller.EhrhardSmooth.qheat_concave.{uι}
