-- Prove2me | solution 1 for OAI.HardSphere.CellOrbital.grid_stationary_low_above
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:08:06.468694+00:00
-- url     : https://prove2.me/submissions/927bc03f-561a-4346-a873-99fc9c3dc05c

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002
import Theorems.Thm_OAI_HardSphere_CellOrbital_physical_deficiency
import Theorems.Thm_OAI_HardSphere_IsGroundVector_groundPathLaw_marginal

section
-- module Solutions.OAIQ054_HS.HardSphere_Capacity_IntegralMulSq
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HardSphere.RayCapacity

lemma integral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x*g x ∂μ)^2 ≤ (∫ x, (f x)^2 ∂μ)*(∫ x, (g x)^2 ∂μ) := by
  let F := hf.toLp f
  let G := hg.toLp g
  have hi : inner ℝ F G=∫ x, f x*g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    simp [F,G,hx,hy,mul_comm]
  have hnF : ‖F‖^2=∫ x, (f x)^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp [F,hx,pow_two]
  have hnG : ‖G‖^2=∫ x, (g x)^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    simp [G,hx,pow_two]
  rw [← hi,← hnF,← hnG,← mul_pow,← sq_abs (inner ℝ F G)]
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (abs_real_inner_le_norm F G)

lemma interval_memLp_two {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) : MemLp f 2 (volume.restrict (Ioc a b)) := by
  apply (memLp_two_iff_integrable_sq (hf.mono Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc)).mpr
  exact hf.pow 2 |>.integrableOn_Icc |>.mono_set Ioc_subset_Icc_self

lemma inv_sq_integral {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    (∫ t : ℝ in r..s, (t⁻¹)^2)=r⁻¹-s⁻¹ := by
  have hc : ContinuousOn (fun t : ℝ ↦ (t⁻¹)^2) (uIcc r s) := by
    rw [uIcc_of_le hrs]
    exact (continuousOn_id.inv₀ (fun t ht ↦ (hr.trans_le ht.1).ne')).pow 2
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ ↦ -(t⁻¹)) (f' := fun t ↦ (t⁻¹)^2) (a := r) (b := s) ?_
    hc.intervalIntegrable
  · simpa only [neg_sub_neg] using h
  · intro t ht
    rw [uIcc_of_le hrs] at ht
    convert (hasDerivAt_inv (hr.trans_le ht.1).ne').neg using 1
    all_goals try with_reducible_and_instances rfl
    simp

lemma ray_pointwise {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 1 f) {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    ‖f s-f r‖^2 ≤ (r⁻¹-s⁻¹)*(∫ t in r..s, ‖deriv f t‖^2*t^2) := by
  have hdc : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hfg : ContinuousOn (fun t : ℝ ↦ ‖deriv f t‖*t) (Icc r s) :=
    (hdc.norm.mul continuous_id).continuousOn
  have hig : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Icc r s) :=
    continuousOn_id.inv₀ (fun t ht ↦ (hr.trans_le ht.1).ne')
  have hcauchy := integral_mul_sq_le (interval_memLp_two hig) (interval_memLp_two hfg)
  have hprod : (∫ t in Ioc r s, t⁻¹*(‖deriv f t‖*t))=∫ t in r..s, ‖deriv f t‖ := by
    rw [intervalIntegral.integral_of_le hrs]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    field_simp [(hr.trans ht.1).ne']
  have hgrad : (∫ t in Ioc r s, (‖deriv f t‖*t)^2)=∫ t in r..s, ‖deriv f t‖^2*t^2 := by
    rw [intervalIntegral.integral_of_le hrs]
    simp only [mul_pow]
  have hinv : (∫ t in Ioc r s, (t⁻¹)^2)=r⁻¹-s⁻¹ := by
    rw [← intervalIntegral.integral_of_le hrs,inv_sq_integral hr hrs]
  rw [hprod,hgrad,hinv] at hcauchy
  have hdis := norm_sub_le_integral_of_norm_deriv_le_of_le hrs
    hf.continuous.continuousOn (hf.differentiable (by norm_num)).differentiableOn
    (ae_of_all _ (fun _ _ ↦ le_rfl)) (hdc.norm.intervalIntegrable r s)
  exact (pow_le_pow_left₀ (norm_nonneg _) hdis 2).trans hcauchy

lemma ray_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 1 f) {r R : ℝ} (hr : 0 < r) (hR : 0≤R)
    (hz : ∀ t ∈ Icc (0:ℝ) r, f t=0) :
    (∫ t in (0:ℝ)..R, ‖f t‖^2*t^2) ≤
      R^3/(3*r)*(∫ t in (0:ℝ)..R, ‖deriv f t‖^2*t^2) := by
  have hdc := hf.continuous_deriv (by norm_num)
  have hgrad : Continuous (fun t : ℝ ↦ ‖deriv f t‖^2*t^2) :=
    (hdc.norm.pow 2).mul (continuous_id.pow 2)
  let A := ∫ t in (0:ℝ)..R, ‖deriv f t‖^2*t^2
  have hA : 0≤A := intervalIntegral.integral_nonneg_of_forall hR
    (fun _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hb (s : ℝ) (hs : s∈Icc (0:ℝ) R) : ‖f s‖^2 ≤ r⁻¹*A := by
    by_cases hsr : s ≤ r
    · rw [hz s ⟨hs.1,hsr⟩,norm_zero,zero_pow (by decide)]
      exact mul_nonneg (inv_nonneg.mpr hr.le) hA
    · have hrs : r ≤ s := le_of_lt (lt_of_not_ge hsr)
      have hp := ray_pointwise hf hr hrs
      rw [hz r ⟨hr.le,le_rfl⟩,sub_zero] at hp
      have hI : 0≤∫ t in r..s, ‖deriv f t‖^2*t^2 :=
        intervalIntegral.integral_nonneg_of_forall hrs (fun _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
      have hIA : (∫ t in r..s, ‖deriv f t‖^2*t^2)≤A :=
        intervalIntegral.integral_mono_interval hr.le hrs hs.2
          (ae_of_all _ (fun _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))) (hgrad.intervalIntegrable 0 R)
      apply hp.trans
      exact (mul_le_mul_of_nonneg_right (sub_le_self _ (inv_nonneg.mpr (hr.le.trans hrs))) hI).trans
        (mul_le_mul_of_nonneg_left hIA (inv_nonneg.mpr hr.le))
  have h := intervalIntegral.integral_mono_on (μ := volume) hR
    (((hf.continuous.norm.pow 2).mul (continuous_id.pow 2)).intervalIntegrable 0 R)
    ((continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 R)
    (fun t ht ↦ mul_le_mul_of_nonneg_right (hb t ht) (sq_nonneg t))
  simp only [Pi.mul_apply,Pi.pow_apply,id_eq] at h
  rw [intervalIntegral.integral_const_mul,integral_pow] at h
  norm_num at h
  convert h using 1; dsimp [A]; ring

lemma ray_lintegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 1 f) {r R B : ℝ} (hr : 0 < r) (hR : 0≤R)
    (hRB : R≤B) (hz : ∀ t ∈ Icc (0:ℝ) r, f t=0)
    {g : ℝ → ℝ} (hg : Continuous g) (hgn : ∀t, 0≤g t)
    (hgrad : ∀t∈Icc (0:ℝ) R, ‖deriv f t‖^2 ≤ g t) :
    (∫⁻ t in Ioc (0:ℝ) R, ENNReal.ofReal (t^2)*ENNReal.ofReal (‖f t‖^2)) ≤
      ENNReal.ofReal (B^3/(3*r))*(∫⁻ t in Ioc (0:ℝ) R, ENNReal.ofReal (t^2)*ENNReal.ofReal (g t)) := by
  have hB := hR.trans hRB
  have hdc := hf.continuous_deriv (by norm_num)
  have hgi : IntervalIntegrable (fun t ↦ g t*t^2) volume 0 R := (hg.mul (continuous_id.pow 2)).intervalIntegrable 0 R
  have hfi : IntervalIntegrable (fun t ↦ ‖f t‖^2*t^2) volume 0 R :=
    ((hf.continuous.norm.pow 2).mul (continuous_id.pow 2)).intervalIntegrable 0 R
  have hdi : IntervalIntegrable (fun t ↦ ‖deriv f t‖^2*t^2) volume 0 R := ((hdc.norm.pow 2).mul (continuous_id.pow 2)).intervalIntegrable 0 R
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hR hdi hgi
    (fun t ht ↦ mul_le_mul_of_nonneg_right (hgrad t ht) (sq_nonneg t))
  have hbound := (ray_integral hf hr hR hz).trans
    (mul_le_mul_of_nonneg_left hmono (by positivity : 0≤R^3/(3*r)))
  have hcoef : R^3/(3*r) ≤ B^3/(3*r) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hR hRB 3) (by positivity)
  have hfinal := hbound.trans (mul_le_mul_of_nonneg_right hcoef
    (intervalIntegral.integral_nonneg_of_forall hR (fun t ↦ mul_nonneg (hgn t) (sq_nonneg t))))
  rw [intervalIntegral.integral_of_le hR,intervalIntegral.integral_of_le hR] at hfinal
  have hfI : (∫⁻ t in Ioc (0:ℝ) R, ENNReal.ofReal (t^2)*ENNReal.ofReal (‖f t‖^2))=
      ENNReal.ofReal (∫ t in Ioc (0:ℝ) R, ‖f t‖^2*t^2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Ioc 0 R)) (f := fun t ↦ ‖f t‖^2*t^2)
      hfi.1
      (ae_of_all _ (fun t ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)))]
    apply lintegral_congr
    intro t
    rw [ENNReal.ofReal_mul (sq_nonneg _),mul_comm]
  have hgI : (∫⁻ t in Ioc (0:ℝ) R, ENNReal.ofReal (t^2)*ENNReal.ofReal (g t))=
      ENNReal.ofReal (∫ t in Ioc (0:ℝ) R, g t*t^2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Ioc 0 R)) (f := fun t ↦ g t*t^2)
      hgi.1
      (ae_of_all _ (fun t ↦ mul_nonneg (hgn t) (sq_nonneg _)))]
    apply lintegral_congr
    intro t
    rw [ENNReal.ofReal_mul (hgn t),mul_comm]
  rw [hfI,hgI,← ENNReal.ofReal_mul (by positivity : 0≤B^3/(3*r))]
  exact ENNReal.ofReal_le_ofReal hfinal

end HardSphere.RayCapacity

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_Point
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates

lemma polar_integral (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p) = ∫⁻ θ in angle, ∫⁻ r in Ioi (0:ℝ),
      ENNReal.ofReal r*F (r*Real.cos θ,r*Real.sin θ) := by
  rw [← lintegral_comp_polarCoord_symm F]
  exact setLIntegral_prod_symm _ (by fun_prop)

lemma cylindrical_integral (F : Point → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p)=∫⁻ θ in angle, ∫⁻ z : ℝ, ∫⁻ r : ℝ,
      ENNReal.ofReal r*F (z,(r*Real.cos θ,r*Real.sin θ)) := by
  rw [Measure.volume_eq_prod,lintegral_prod _ hF.aemeasurable]
  have hp (z : ℝ) := polar_integral (fun p ↦ F (z,p)) (hF.comp (measurable_const.prodMk measurable_id))
  conv_lhs => arg 2; ext z; rw [hp z]
  have he (z θ : ℝ) : (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal r*F (z,(r*Real.cos θ,r*Real.sin θ)))=
      ∫⁻ r : ℝ, ENNReal.ofReal r*F (z,(r*Real.cos θ,r*Real.sin θ)) := by
    apply setLIntegral_eq_of_support_subset
    intro r hr
    by_contra h
    have hr0 : r≤0 := not_lt.mp h
    simp only [ENNReal.ofReal_of_nonpos hr0,zero_mul,Function.mem_support,ne_eq,not_true_eq_false] at hr
  simp_rw [he]
  apply lintegral_lintegral_swap
  exact (by fun_prop : Measurable (fun p : (ℝ × ℝ) × ℝ ↦
    ENNReal.ofReal p.2*F (p.1.1,(p.2*Real.cos p.1.2,p.2*Real.sin p.1.2)))).lintegral_prod_right.aemeasurable

lemma spherical_integral (F : Point → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p)=∫⁻ θ in angle, ∫⁻ φ in angle, ∫⁻ r in Ioi (0:ℝ),
      ENNReal.ofReal (r^2*Real.cos φ)*F (spherePoint r φ θ) := by
  rw [cylindrical_integral F hF]
  apply lintegral_congr
  intro θ
  let G : ℝ × ℝ → ℝ≥0∞ := fun p ↦
    ENNReal.ofReal p.1*F (p.2,(p.1*Real.cos θ,p.1*Real.sin θ))
  have hG : Measurable G := by unfold G; fun_prop
  rw [← lintegral_prod_symm G hG.aemeasurable,← Measure.volume_eq_prod,polar_integral G hG]
  apply lintegral_congr
  intro φ
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp [G,spherePoint]
  rw [← mul_assoc,← ENNReal.ofReal_mul (le_of_lt hr)]
  congr 2
  ring

open Filter
open scoped Topology BigOperators

lemma spherePoint_eq (r φ θ : ℝ) : spherePoint r φ θ=r • direction φ θ := by
  ext <;> simp [spherePoint,direction,mul_assoc]

lemma sqRadius_smul (t : ℝ) (x : Point) : sqRadius (t • x)=t^2*sqRadius x := by
  simp only [sqRadius,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

lemma direction_unit (φ θ : ℝ) : sqRadius (direction φ θ)=1 := by
  have hp := Real.sin_sq_add_cos_sq φ
  have ht := Real.cos_sq_add_sin_sq θ
  dsimp [sqRadius,direction]
  nlinarith [sq_nonneg (Real.cos φ)]

lemma ray_terminal {K : Set Point} (hk : IsClosed K) (hc : Convex ℝ K) (h0 : (0:Point)∈K)
    {B : ℝ} (hB : 0≤B) (hb : ∀ x∈K, sqRadius x≤B^2) {ω : Point} (hu : sqRadius ω=1) :
    ∃ R : ℝ, 0≤R ∧ R≤B ∧ {t : ℝ | 0≤t ∧ t • ω∈K}=Icc 0 R := by
  let S : Set ℝ := {t : ℝ | 0≤t ∧ t • ω∈K}
  have hs0 : (0:ℝ)∈S := by simpa [S] using h0
  have hsclosed : IsClosed S := isClosed_Ici.inter (hk.preimage (continuous_id.smul continuous_const))
  have hsub : S⊆Icc 0 B := by
    intro t ht
    have hn := hb (t • ω) ht.2
    rw [sqRadius_smul,hu,mul_one] at hn
    exact ⟨ht.1,(sq_le_sq₀ ht.1 hB).mp hn⟩
  have hscompact : IsCompact S := isCompact_Icc.of_isClosed_subset hsclosed hsub
  have hsconvex : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),?_⟩
    simpa only [smul_eq_mul,add_smul,mul_smul] using hc hx.2 hy.2 ha hb hab
  let R := sSup S
  have hR : R∈S := hscompact.sSup_mem ⟨0,hs0⟩
  refine ⟨R,(hsub hR).1,(hsub hR).2,?_⟩
  ext t
  constructor
  · intro ht
    exact ⟨ht.1,le_csSup hscompact.bddAbove ht⟩
  · intro ht
    exact hsconvex.ordConnected.out hs0 hR ht

end HardSphere.SphericalCoordinates

namespace HardSphere.SphericalCoordinates
open scoped Topology

lemma linear_unit_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Point →L[ℝ] E) {ω : Point} (hu : sqRadius ω=1) :
    ‖D ω‖^2 ≤ ‖D axis0‖^2+‖D axis1‖^2+‖D axis2‖^2 := by
  have he : ω=ω.1 • axis0+ω.2.1 • axis1+ω.2.2 • axis2 := by
    ext <;> simp [axis0,axis1,axis2]
  have hn : ‖D ω‖ ≤ |ω.1| * ‖D axis0‖+|ω.2.1| * ‖D axis1‖+|ω.2.2| * ‖D axis2‖ := by
    have hd := congrArg D he
    simp only [map_add,map_smul] at hd
    rw [hd]
    calc
      _ ≤ (‖ω.1 • D axis0‖+‖ω.2.1 • D axis1‖)+‖ω.2.2 • D axis2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = _ := by simp only [norm_smul,Real.norm_eq_abs]
  have hcs (a b c A B C : ℝ) : (a*A+b*B+c*C)^2≤(a^2+b^2+c^2)*(A^2+B^2+C^2) := by
    nlinarith [sq_nonneg (a*B-b*A),sq_nonneg (a*C-c*A),sq_nonneg (b*C-c*B)]
  have hs := hcs |ω.1| |ω.2.1| |ω.2.2| ‖D axis0‖ ‖D axis1‖ ‖D axis2‖
  simp only [sq_abs] at hs
  change ω.1^2+ω.2.1^2+ω.2.2^2=1 at hu
  rw [hu,one_mul] at hs
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hs

lemma gradSq_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Point → E) (x : Point) : 0≤gradSq f x := by unfold gradSq; positivity

lemma continuous_gradSq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (hf : ContDiff ℝ 1 f) : Continuous (gradSq f) := by
  have hd := hf.continuous_fderiv (by norm_num)
  unfold gradSq
  exact (((hd.clm_apply continuous_const).norm.pow 2).add
    ((hd.clm_apply continuous_const).norm.pow 2)).add
    ((hd.clm_apply continuous_const).norm.pow 2)

lemma ray_deriv_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (hf : ContDiff ℝ 1 f) {ω : Point} (hu : sqRadius ω=1) (t : ℝ) :
    ‖deriv (fun s : ℝ ↦ f (s • ω)) t‖^2≤gradSq f (t • ω) := by
  have hd := ((hf.differentiable (by norm_num) (t • ω)).hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const ω)
  have he : deriv (fun s : ℝ ↦ f (s • ω)) t=fderiv ℝ f (t • ω) ω := by
    simpa only [Function.comp_def,id_eq,one_smul] using hd.deriv
  rw [he]
  simpa only [one_smul,gradSq] using linear_unit_bound (fderiv ℝ f (t • ω)) hu

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_RadialIndicator
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates

lemma radial_indicator {K : Set Point} {ω : Point} {R : ℝ}
    (hR : {t : ℝ | 0≤t ∧ t • ω∈K}=Icc 0 R) (a : ℝ → ℝ≥0∞) (H : Point → ℝ≥0∞) :
    (∫⁻ t in Ioi (0:ℝ), a t*(K.indicator H) (t • ω))=
      ∫⁻ t in Ioc (0:ℝ) R, a t*H (t • ω) := by
  classical
  rw [← lintegral_indicator measurableSet_Ioi,← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro t
  by_cases ht0 : 0<t
  · have hk : t • ω∈K ↔ t≤R := by
      have he := Set.ext_iff.mp hR t
      simpa only [mem_ofPred_eq,mem_Icc,ht0.le,true_and] using he
    by_cases htR : t≤R
    · simp [ht0,htR,hk.mpr htR]
    · simp [ht0,htR,mt hk.mp htR]
  · simp [ht0]

lemma convex_capacity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (hf : ContDiff ℝ 1 f) {K : Set Point}
    (hk : IsClosed K) (hc : Convex ℝ K) (h0 : (0:Point)∈K)
    {r B : ℝ} (hr : 0 < r) (hB : 0≤B) (hb : ∀x∈K,sqRadius x≤B^2)
    (hz : ∀x, sqRadius x ≤ r^2 → f x=0) :
    (∫⁻ x in K, ENNReal.ofReal (‖f x‖^2)) ≤
      ENNReal.ofReal (B^3/(3*r))*(∫⁻ x in K, ENNReal.ofReal (gradSq f x)) := by
  classical
  rw [← lintegral_indicator hk.measurableSet,← lintegral_indicator hk.measurableSet]
  have hm : Measurable (fun x ↦ ENNReal.ofReal (‖f x‖^2)) := by
    simpa only [Pi.pow_apply] using (hf.continuous.norm.pow 2).measurable.ennreal_ofReal
  rw [spherical_integral (K.indicator (fun x ↦ ENNReal.ofReal (‖f x‖^2))) (hm.indicator hk.measurableSet),
    spherical_integral (K.indicator (fun x ↦ ENNReal.ofReal (gradSq f x)))
      (((continuous_gradSq hf).measurable.ennreal_ofReal).indicator hk.measurableSet)]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro θ
  dsimp only
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro φ
  dsimp only
  obtain ⟨R,hR,hRB,he⟩ := ray_terminal hk hc h0 hB hb (direction_unit φ θ)
  simp only [spherePoint_eq]
  rw [radial_indicator he,radial_indicator he]
  have hweight (t : ℝ) : ENNReal.ofReal (t^2*Real.cos φ)=
      ENNReal.ofReal (Real.cos φ)*ENNReal.ofReal (t^2) := by
    rw [ENNReal.ofReal_mul (sq_nonneg _),mul_comm]
  simp_rw [hweight,mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,← mul_assoc,
    mul_comm (ENNReal.ofReal (B^3/(3*r))),mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply RayCapacity.ray_lintegral (f := fun t ↦ f (t • direction φ θ))
    (hf.comp (contDiff_id.smul contDiff_const)) hr hR hRB
  · intro t ht
    apply hz
    rw [sqRadius_smul,direction_unit,mul_one]
    exact pow_le_pow_left₀ ht.1 ht.2 2
  · exact (continuous_gradSq hf).comp (continuous_id.smul continuous_const)
  · intro t
    exact gradSq_nonneg f _
  · intro t _
    exact ray_deriv_bound hf (direction_unit φ θ) t

open scoped Topology

lemma translate_set_lintegral {K : Set Point} (hk : MeasurableSet K) (y : Point)
    (H : Point → ℝ≥0∞) :
    (∫⁻ x in {x | y+x∈K}, H (y+x))=∫⁻x in K,H x := by
  classical
  have hK : MeasurableSet {x : Point | y+x∈K} :=
    hk.preimage (show Measurable (fun x : Point ↦ y+x) from measurable_const.add measurable_id)
  rw [← lintegral_indicator hK,
    ← lintegral_indicator hk]
  have he : ({x | y+x∈K}.indicator (fun x ↦ H (y+x)))=fun x ↦ K.indicator H (y+x) := by
    funext x
    by_cases hx : y+x∈K <;> simp [hx]
  have : (volume : Measure Point).IsAddLeftInvariant := by
    rw [Measure.volume_eq_prod,Measure.volume_eq_prod]
    apply Measure.prod.instIsAddLeftInvariant
  rw [he,lintegral_add_left_eq_self]

lemma convex_capacity_center {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (hf : ContDiff ℝ 1 f) {K : Set Point}
    (hk : IsClosed K) (hc : Convex ℝ K) {y : Point} (hy : y∈K)
    {r B : ℝ} (hr : 0 < r) (hB : 0≤B) (hb : ∀x∈K,sqRadius (x-y)≤B^2)
    (hz : ∀x, sqRadius (x-y) ≤ r^2 → f x=0) :
    (∫⁻ x in K, ENNReal.ofReal (‖f x‖^2)) ≤
      ENNReal.ofReal (B^3/(3*r))*(∫⁻ x in K, ENNReal.ofReal (gradSq f x)) := by
  let K' : Set Point := {x | y+x∈K}
  have hkc : IsClosed K' := hk.preimage (continuous_const.add continuous_id)
  have hcv : Convex ℝ K' := by
    intro x hx z hz a b ha hb hab
    change y+(a • x+b • z)∈K
    have he : y+(a • x+b • z)=a • (y+x)+b • (y+z) := by
      rw [smul_add,smul_add]
      calc
        y+(a • x+b • z)=(a+b) • y+(a • x+b • z) := by rw [hab,one_smul]
        _ = _ := by rw [add_smul]; abel
    rw [he]
    exact hc hx hz ha hb hab
  have h := convex_capacity (f := fun x ↦ f (y+x)) (K := K') (hf.comp (contDiff_const.add contDiff_id)) hkc hcv
    (by simpa [K'] using hy) hr hB (by
      intro x hx
      simpa only [add_sub_cancel_left] using hb (y+x) hx) (by
      intro x hx
      apply hz (y+x)
      simpa only [add_sub_cancel_left] using hx)
  have hg (x : Point) : gradSq (fun z ↦ f (y+z)) x=gradSq f (y+x) := by
    simp only [gradSq,fderiv_comp_add_left]
  simp_rw [hg] at h
  dsimp only [K'] at h
  rw [translate_set_lintegral hk.measurableSet y (fun x ↦ ENNReal.ofReal (‖f x‖^2)),
    translate_set_lintegral hk.measurableSet y (fun x ↦ ENNReal.ofReal (gradSq f x))] at h
  exact h

lemma cube_radius {b y x : Point} {l : ℝ} (hl : 0≤l) (hy : y∈cube b l) (hx : x∈cube b l) :
    sqRadius (x-y)≤(Real.sqrt 3*l)^2 := by
  have hc (u v a : ℝ) (hu : a≤u ∧ u≤a+l) (hv : a≤v ∧ v≤a+l) : (u-v)^2≤l^2 := by
    have h := (sq_le_sq₀ (abs_nonneg (u-v)) hl).mpr (abs_le.mpr ⟨by linarith,by linarith⟩)
    simpa only [sq_abs] using h
  have h1 := hc x.1 y.1 b.1 ⟨hx.1.1,hx.2.1⟩ ⟨hy.1.1,hy.2.1⟩
  have h2 := hc x.2.1 y.2.1 b.2.1 ⟨hx.1.2.1,hx.2.2.1⟩ ⟨hy.1.2.1,hy.2.2.1⟩
  have h3 := hc x.2.2 y.2.2 b.2.2 ⟨hx.1.2.2,hx.2.2.2⟩ ⟨hy.1.2.2,hy.2.2.2⟩
  simp only [sqRadius,Prod.fst_sub,Prod.snd_sub,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  linarith

lemma cube_capacity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (hf : ContDiff ℝ 1 f) {b y : Point} {r l : ℝ}
    (hr : 0 < r) (hl : 0≤l) (hy : y∈cube b l)
    (hz : ∀x, sqRadius (x-y) ≤ r^2 → f x=0) :
    (∫⁻ x in cube b l, ENNReal.ofReal (‖f x‖^2)) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/r)*(∫⁻ x in cube b l, ENNReal.ofReal (gradSq f x)) := by
  have h := convex_capacity_center hf isClosed_Icc (convex_Icc _ _) hy hr
    (mul_nonneg (Real.sqrt_nonneg 3) hl) (fun _ hx ↦ cube_radius hl hy hx) hz
  have he : (Real.sqrt 3*l)^3/(3*r)=Real.sqrt 3*l^3/r := by
    rw [mul_pow,pow_succ (Real.sqrt 3) 2,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
    field_simp
  rw [he] at h
  exact h

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_ParticleGradSq
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates
open Filter
open scoped Topology BigOperators

lemma insertNth_affine {n : ℕ} (i : Fin (n+1)) (Y : Fin n → Point) (x : Point) :
    i.insertNth x Y=(ContinuousLinearMap.single ℝ (fun _ : Fin (n+1) ↦ Point) i) x+i.insertNth 0 Y := by
  funext k
  induction k using i.succAboveCases with
  | x => simp
  | p k => simp [Fin.succAbove_ne]

lemma contDiff_coordinate_slice {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n+1) → Point) → E} (hF : ContDiff ℝ 1 F) (i : Fin (n+1)) (Y : Fin n → Point) :
    ContDiff ℝ 1 (fun x ↦ F (i.insertNth x Y)) := by
  have he : (fun x : Point ↦ i.insertNth x Y)=fun x ↦
      (ContinuousLinearMap.single ℝ (fun _ : Fin (n+1) ↦ Point) i) x+i.insertNth 0 Y := funext (insertNth_affine i Y)
  change ContDiff ℝ 1 (F ∘ fun x : Point ↦ i.insertNth x Y)
  rw [he]
  exact hF.comp ((ContinuousLinearMap.contDiff _).add contDiff_const)

lemma fderiv_coordinate_slice {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n+1) → Point) → E} (hF : ContDiff ℝ 1 F)
    (i : Fin (n+1)) (Y : Fin n → Point) (x : Point) :
    fderiv ℝ (fun z ↦ F (i.insertNth z Y)) x=
      (fderiv ℝ F (i.insertNth x Y)).comp (ContinuousLinearMap.single ℝ (fun _ : Fin (n+1) ↦ Point) i) := by
  have hi : HasFDerivAt (fun z : Point ↦ i.insertNth z Y)
      (ContinuousLinearMap.single ℝ (fun _ : Fin (n+1) ↦ Point) i) x := by
    have he : (fun x : Point ↦ i.insertNth x Y)=fun x ↦
        (ContinuousLinearMap.single ℝ (fun _ : Fin (n+1) ↦ Point) i) x+i.insertNth 0 Y := funext (insertNth_affine i Y)
    rw [he]
    exact (ContinuousLinearMap.hasFDerivAt _).add_const _
  have hf := ((hF.differentiable (by norm_num) (i.insertNth x Y)).hasFDerivAt).comp x hi
  simpa only [Function.comp_def] using hf.fderiv

lemma gradSq_coordinate_slice {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n+1) → Point) → E} (hF : ContDiff ℝ 1 F)
    (i : Fin (n+1)) (Y : Fin n → Point) (x : Point) :
    gradSq (fun z ↦ F (i.insertNth z Y)) x=particleGradSq F i (i.insertNth x Y) := by
  simp only [gradSq,fderiv_coordinate_slice hF,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.single_apply,particleGradSq]

lemma continuous_particleGradSq {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin n → Point) → E} (hF : ContDiff ℝ 1 F) (i : Fin n) :
    Continuous (particleGradSq F i) := by
  have hd := hF.continuous_fderiv (by norm_num)
  unfold particleGradSq
  exact (((hd.clm_apply continuous_const).norm.pow 2).add
    ((hd.clm_apply continuous_const).norm.pow 2)).add
    ((hd.clm_apply continuous_const).norm.pow 2)

lemma lintegral_insertNth {n : ℕ} (μ : Fin (n+1) → Measure Point) [∀i,SigmaFinite (μ i)]
    (i : Fin (n+1)) (H : (Fin (n+1) → Point) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ X, H X ∂Measure.pi μ)=
      ∫⁻ Y, ∫⁻ x, H (i.insertNth x Y) ∂μ i ∂Measure.pi (fun j ↦ μ (i.succAbove j)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ Point) i
  have he := (measurePreserving_piFinSuccAbove μ i).symm
  rw [← he.lintegral_comp_emb e.symm.measurableEmbedding H]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Equiv.coe_fn_mk]
  apply lintegral_prod_symm
  exact (hH.comp e.symm.measurable).aemeasurable

lemma sector_coordinate_capacity {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n+1) → Point) → E} (hF : ContDiff ℝ 1 F)
    {r l : ℝ} (hr : 0 < r) (hl : 0≤l) (b : Fin (n+1) → Point)
    (i : Fin (n+1)) (j : Fin n) (hb : b (i.succAbove j)=b i)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c) ≤ r^2 → F X=0) :
    (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun a ↦ volume.restrict (cube (b a) l))) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/r)*
        (∫⁻ X, ENNReal.ofReal (particleGradSq F i X) ∂Measure.pi (fun a ↦ volume.restrict (cube (b a) l))) := by
  have hm : Measurable (fun X ↦ ENNReal.ofReal (‖F X‖^2)) := by
    simpa only [Pi.pow_apply] using (hF.continuous.norm.pow 2).measurable.ennreal_ofReal
  rw [lintegral_insertNth _ i _ hm,lintegral_insertNth _ i _ (continuous_particleGradSq hF i).measurable.ennreal_ofReal,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  have hae : ∀ᵐ Y ∂Measure.pi (fun a : Fin n ↦ volume.restrict (cube (b (i.succAbove a)) l)),
      Y j∈cube (b (i.succAbove j)) l :=
    Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem isClosed_Icc.measurableSet)
  filter_upwards [hae] with Y hY
  rw [hb] at hY
  have h := cube_capacity (contDiff_coordinate_slice hF i Y) hr hl hY (by
    intro x hx
    apply hz (i.insertNth x Y) i (i.succAbove j) (Fin.ne_succAbove i j)
    simpa only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove] using hx)
  simp_rw [gradSq_coordinate_slice hF] at h
  exact h

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_ActiveLabels
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates
open scoped BigOperators

lemma mem_activeLabels {α ι : Type*} [Fintype α] (σ : α → ι) (i : α) :
    i∈activeLabels σ ↔ ∃ j, j≠i ∧ σ j=σ i := by
  classical
  simp only [activeLabels,Finset.mem_filter,Finset.mem_univ,true_and]

lemma inactive_card_le {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α] (σ : α → ι) :
    (activeLabels σ)ᶜ.card≤Fintype.card ι := by
  classical
  apply Finset.card_le_card_of_injOn σ (by simp)
  intro a ha b _ hab
  by_contra hne
  have ha' : a∉activeLabels σ := Finset.mem_compl.mp ha
  apply ha'
  simp only [activeLabels,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨b,(fun h ↦ hne h.symm),hab.symm⟩

lemma active_card_lower {α ι : Type*} [Fintype α] [Fintype ι] (σ : α → ι) :
    Fintype.card α-Fintype.card ι≤(activeLabels σ).card := by
  classical
  have h := inactive_card_le σ
  rw [Finset.card_compl] at h
  have hc := (activeLabels σ).card_le_univ
  omega

lemma sector_capacity {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n+1) → Point) → E} (hF : ContDiff ℝ 1 F)
    {r l : ℝ} (hr : 0 < r) (hl : 0≤l) {ι : Type*} [Fintype ι]
    (b : ι → Point) (σ : Fin (n+1) → ι)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c) ≤ r^2 → F X=0) :
    ((n+1-Fintype.card ι : ℕ) : ℝ≥0∞)*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/r)*
        ∑ i, (∫⁻ X, ENNReal.ofReal (particleGradSq F i X)
          ∂Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))) := by
  classical
  let μ := Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))
  let M := ∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂μ
  let G := fun i ↦ ∫⁻ X, ENNReal.ofReal (particleGradSq F i X) ∂μ
  let C := ENNReal.ofReal (Real.sqrt 3*l^3/r)
  have hi (i : Fin (n+1)) (hi : i∈activeLabels σ) : M≤C*G i := by
    obtain ⟨j,hji,hs⟩ := (mem_activeLabels σ i).mp hi
    obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hji
    exact sector_coordinate_capacity hF hr hl (fun a ↦ b (σ a)) i k (congrArg b hs) hz
  have hs := Finset.sum_le_sum hi
  have hcard := active_card_lower σ
  rw [Fintype.card_fin] at hcard
  calc
    _ ≤ ((activeLabels σ).card : ℝ≥0∞)*M := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = ∑ _ ∈ activeLabels σ, M := by simp
    _ ≤ ∑ i ∈ activeLabels σ, C*G i := hs
    _ = C*∑ i ∈ activeLabels σ, G i := (Finset.mul_sum _ _ _).symm
    _ ≤ C*∑ i, G i := by gcongr; exact Finset.subset_univ _
    _ = _ := rfl

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_Energy
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
namespace HardSphere.Variational
variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype J]

omit [InnerProductSpace ℂ H] in
lemma energy_nonneg (u : H × (J → H)) : 0 ≤ energy u :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma energy_smul (c : ℂ) (u : H × (J → H)) :
    energy (c • u) = ‖c‖ ^ 2 * energy u := by
  simp [energy, norm_smul, mul_pow, Finset.mul_sum]

theorem rayleigh (M : Submodule ℂ (H × (J → H))) (u : H × (J → H))
    (hmin : ∀ v ∈ M, ‖v.1‖ = 1 → energy u ≤ energy v)
    (v : H × (J → H)) (hv : v ∈ M) :
    energy u * ‖v.1‖ ^ 2 ≤ energy v := by
  by_cases hz : ‖v.1‖ = 0
  · simpa [hz] using energy_nonneg v
  · let c : ℂ := ((‖v.1‖ : ℂ))⁻¹
    have hc : ‖c‖ = ‖v.1‖⁻¹ := by simp [c, Complex.norm_real]
    have hv' : ‖(c • v).1‖ = 1 := by
      simp only [Prod.smul_fst, norm_smul, hc]
      exact inv_mul_cancel₀ hz
    have h := hmin (c • v) (M.smul_mem c hv) hv'
    rw [energy_smul, hc] at h
    calc
      energy u * ‖v.1‖ ^ 2 ≤ (‖v.1‖⁻¹ ^ 2 * energy v) * ‖v.1‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h (sq_nonneg _)
      _ = energy v := by field_simp

lemma norm_add_real_smul_sq (x y : H) (t : ℝ) :
    ‖x + (t : ℂ) • y‖ ^ 2 =
      ‖x‖ ^ 2 + 2 * t * (inner ℂ x y).re + t ^ 2 * ‖y‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul, mul_pow]
  simp [Complex.norm_real, sq_abs, mul_assoc]

lemma energy_add_real_smul (u v : H × (J → H)) (t : ℝ) :
    energy (u + (t : ℂ) • v) =
      energy u + 2 * t * (gradientPairing u v).re + t ^ 2 * energy v := by
  change (∑ i, ‖u.2 i + (t : ℂ) • v.2 i‖ ^ 2) = _
  simp_rw [norm_add_real_smul_sq]
  simp only [energy, gradientPairing, Finset.sum_add_distrib, Finset.mul_sum,
    Complex.re_sum]

lemma linear_term_zero {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + 2 * b * t) : b = 0 := by
  have hd : 0 < a + 1 := by linarith
  have hh := mul_nonneg (h (-b / (a + 1))) (sq_nonneg (a + 1))
  have heq : (a * (-b / (a + 1)) ^ 2 + 2 * b * (-b / (a + 1))) *
      (a + 1) ^ 2 = -(a + 2) * b ^ 2 := by
    field_simp
    ring
  rw [heq] at hh
  have hb := sq_nonneg b
  have hprod := mul_nonneg ha hb
  nlinarith

theorem ground_pairing (M : Submodule ℂ (H × (J → H)))
    (u : H × (J → H)) (hu : u ∈ M) (hnorm : ‖u.1‖ = 1)
    (hmin : ∀ v ∈ M, ‖v.1‖ = 1 → energy u ≤ energy v)
    (v : H × (J → H)) (hv : v ∈ M) :
    gradientPairing u v = (energy u : ℂ) * inner ℂ u.1 v.1 := by
  have hre (w : H × (J → H)) (hw : w ∈ M) :
      (gradientPairing u w).re = energy u * (inner ℂ u.1 w.1).re := by
    have ha : 0 ≤ energy w - energy u * ‖w.1‖ ^ 2 :=
      sub_nonneg.mpr (rayleigh M u hmin w hw)
    have hpoly (t : ℝ) : 0 ≤
        (energy w - energy u * ‖w.1‖ ^ 2) * t ^ 2 +
          2 * ((gradientPairing u w).re - energy u * (inner ℂ u.1 w.1).re) * t := by
      have h := rayleigh M u hmin (u + (t : ℂ) • w) (M.add_mem hu (M.smul_mem _ hw))
      rw [energy_add_real_smul] at h
      simp only [Prod.fst_add, Prod.smul_fst, norm_add_real_smul_sq, hnorm, one_pow] at h
      nlinarith
    exact sub_eq_zero.mp (linear_term_zero ha hpoly)
  have hI := hre (Complex.I • v) (M.smul_mem _ hv)
  have hr := hre v hv
  apply Complex.ext
  · simpa using hr
  · simpa [gradientPairing, inner_smul_right, ← Finset.mul_sum, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.mul_im] using hI

end HardSphere.Variational

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_EnergyParallelogram
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
namespace HardSphere.Variational
variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype J]

lemma energy_parallelogram (u v : H × (J → H)) :
    energy (u + v) + energy (u - v) = 2 * (energy u + energy v) := by
  change (∑ i, ‖u.2 i + v.2 i‖ ^ 2) + (∑ i, ‖u.2 i - v.2 i‖ ^ 2) = _
  rw [← Finset.sum_add_distrib]
  simp_rw [parallelogram_law_with_norm ℂ]
  simp only [energy, Finset.mul_sum, Finset.sum_add_distrib, mul_add]

theorem minimizer_eq_of_scalar_eq (M : Submodule ℂ (H × (J → H)))
    (u : H × (J → H)) (hu : u ∈ M) (hnorm : ‖u.1‖ = 1)
    (hmin : ∀ v ∈ M, ‖v.1‖ = 1 → energy u ≤ energy v)
    (v : H × (J → H)) (hv : v ∈ M) (hscalar : v.1 = u.1)
    (henergy : energy v ≤ energy u) : v = u := by
  have hnormsum : ‖(u + v).1‖ ^ 2 = 4 := by
    have he : (u + v).1 = (2 : ℂ) • u.1 := by simp [hscalar, two_smul]
    rw [he, norm_smul, hnorm]
    norm_num
  have hr := rayleigh M u hmin (u + v) (M.add_mem hu hv)
  rw [hnormsum] at hr
  have hd : energy (u - v) = 0 := by
    have hp := energy_parallelogram u v
    have hn := energy_nonneg (u - v)
    linarith
  apply Prod.ext hscalar
  funext i
  have hi : ‖u.2 i - v.2 i‖ ^ 2 ≤ energy (u - v) :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖u.2 j - v.2 j‖) (Finset.mem_univ i)
  rw [hd] at hi
  have hz : ‖u.2 i - v.2 i‖ = 0 := by nlinarith [norm_nonneg (u.2 i - v.2 i)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

end HardSphere.Variational

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_Basic
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere

lemma bosonic_iff_pullback {N : ℕ} {L : Length} (ψ : ScalarL2 N L) :
    bosonic ψ ↔ ∀ σ, permutationPullback σ ψ = ψ := by
  have hae (σ : Equiv.Perm (Fin N)) :
      (permutationPullback σ ψ : Configuration N L → ℂ) =ᵐ[volume]
        fun X ↦ ψ (permuteConfiguration σ X) :=
    Lp.coeFn_compMeasurePreserving ψ (measurePreserving_permute σ)
  constructor
  · intro h σ
    exact Lp.ext ((hae σ).trans (h σ))
  · intro h σ
    have hh := hae σ
    rw [h σ] at hh
    exact hh.symm

section

attribute [local instance] scalarL2_normedAddCommGroup scalarL2_module

@[simp] lemma mem_bosonicSubmodule {N : ℕ} {L : Length} {ψ : ScalarL2 N L} :
    ψ ∈ bosonicSubmodule N L ↔ bosonic ψ := by
  simp only [bosonicSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  exact (bosonic_iff_pullback ψ).symm

end

@[simp] lemma mem_groundFormSubmodule {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L} :
    u ∈ groundFormSubmodule N L a ↔ u ∈ dirichletDomain N L a ∧ bosonic u.1 := by
  simp [groundFormSubmodule]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FirstVariation
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
namespace HardSphere

theorem IsGroundVector.first_variation {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (v : Jet N L)
    (hv : v ∈ dirichletDomain N L a) (hb : bosonic v.1) :
    (∑ p : Direction N, inner ℂ (u.2 p) (v.2 p)) =
      (energy u : ℂ) * inner ℂ u.1 v.1 := by
  apply Variational.ground_pairing (groundFormSubmodule N L a) u
  · exact mem_groundFormSubmodule.mpr ⟨hu.1, hu.2.1⟩
  · exact hu.2.2.1
  · intro w hw hn
    exact hu.2.2.2 w (mem_groundFormSubmodule.mp hw).1
      (mem_groundFormSubmodule.mp hw).2 hn
  · exact mem_groundFormSubmodule.mpr ⟨hv, hb⟩

lemma SmoothTest.jet_permute {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest N L a) (σ : Equiv.Perm (Fin N)) :
    (f.permute σ).jet = permutationJet σ f.jet := by
  apply Prod.ext
  · apply Lp.ext
    exact (MemLp.coeFn_toLp (f.permute σ).memLp).trans
      ((Lp.coeFn_compMeasurePreserving f.jet.1 (measurePreserving_permute σ)).trans
        ((measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp
          (MemLp.coeFn_toLp f.memLp))).symm
  · funext p
    apply Lp.ext
    have h := (measurePreserving_permute (L := L) σ).quasiMeasurePreserving.ae_eq_comp
      (MemLp.coeFn_toLp (f.partial_memLp (σ.symm p.1, p.2)))
    refine (MemLp.coeFn_toLp ((f.permute σ).partial_memLp p)).trans ?_
    change coordDerivative N L (f.toFun ∘ permuteConfiguration σ) p =ᵐ[volume] _
    rw [coordDerivative_permute]
    exact ((Lp.coeFn_compMeasurePreserving _ (measurePreserving_permute σ)).trans h).symm

lemma permutationJet_mem_domain {N : ℕ} {L : Length} {a : ℝ}
    (σ : Equiv.Perm (Fin N)) {u : Jet N L} (hu : u ∈ dirichletDomain N L a) :
    permutationJet σ u ∈ dirichletDomain N L a := by
  apply map_mem_closure (permutationJet σ).continuous hu
  rintro _ ⟨f, rfl⟩
  exact ⟨f.permute σ, f.jet_permute σ⟩

lemma energy_permutationJet {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N))
    (u : Jet N L) : energy (permutationJet σ u) = energy u := by
  change (∑ p : Direction N, ‖Lp.compMeasurePreserving _ (measurePreserving_permute σ)
    (u.2 (σ.symm p.1, p.2))‖ ^ 2) = _
  simp only [Lp.norm_compMeasurePreserving]
  exact Equiv.sum_comp (Equiv.prodCongr σ.symm (Equiv.refl (Fin 3)))
    (fun p ↦ ‖u.2 p‖ ^ 2)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_PermutationPullbackComp
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
namespace HardSphere

lemma permutationPullback_comp {N : ℕ} {L : Length}
    (σ τ : Equiv.Perm (Fin N)) (ψ : ScalarL2 N L) :
    permutationPullback σ (permutationPullback τ ψ) = permutationPullback (σ * τ) ψ := by
  change Lp.compMeasurePreserving _ (measurePreserving_permute σ)
    (Lp.compMeasurePreserving _ (measurePreserving_permute τ) ψ) = _
  rw [← Lp.compMeasurePreserving_comp_apply]
  rfl

lemma inner_permutationPullback {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N))
    (ψ φ : ScalarL2 N L) :
    inner ℂ (permutationPullback σ ψ) (permutationPullback σ φ) = inner ℂ ψ φ :=
  (Lp.compMeasurePreservingₗᵢ ℂ _ (measurePreserving_permute σ)).inner_map_map ψ φ

lemma gradientPairing_permutationJet {N : ℕ} {L : Length}
    (σ : Equiv.Perm (Fin N)) (u v : Jet N L) :
    Variational.gradientPairing (permutationJet σ u) (permutationJet σ v) =
      Variational.gradientPairing u v := by
  change (∑ p : Direction N, inner ℂ (permutationPullback σ (u.2 (σ.symm p.1, p.2)))
    (permutationPullback σ (v.2 (σ.symm p.1, p.2)))) = _
  simp only [inner_permutationPullback]
  exact Equiv.sum_comp (Equiv.prodCongr σ.symm (Equiv.refl (Fin 3)))
    (fun p ↦ inner ℂ (u.2 p) (v.2 p))

theorem IsGroundVector.permutationInvariant {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (σ : Equiv.Perm (Fin N)) :
    permutationJet σ u = u := by
  have hs : (permutationJet σ u).1 = u.1 := (bosonic_iff_pullback u.1).mp hu.2.1 σ
  have hv : permutationJet σ u ∈ groundFormSubmodule N L a := by
    rw [mem_groundFormSubmodule]
    exact ⟨permutationJet_mem_domain σ hu.1, hs ▸ hu.2.1⟩
  exact Variational.minimizer_eq_of_scalar_eq (groundFormSubmodule N L a) u
    (mem_groundFormSubmodule.mpr ⟨hu.1, hu.2.1⟩) hu.2.2.1
    (fun w hw hn ↦ hu.2.2.2 w (mem_groundFormSubmodule.mp hw).1
      (mem_groundFormSubmodule.mp hw).2 hn)
    (permutationJet σ u) hv hs (le_of_eq (energy_permutationJet σ u))

lemma bosonic_sum_permutationPullback {N : ℕ} {L : Length} (ψ : ScalarL2 N L) :
    bosonic (∑ σ : Equiv.Perm (Fin N), permutationPullback σ ψ) := by
  rw [bosonic_iff_pullback]
  intro τ
  simp only [map_sum, permutationPullback_comp]
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ ↦ permutationPullback σ ψ)

lemma gradientPairing_sum_right {N : ℕ} {L : Length} {I : Type*} [Fintype I]
    (u : Jet N L) (v : I → Jet N L) :
    Variational.gradientPairing u (∑ i, v i) =
      ∑ i, Variational.gradientPairing u (v i) := by
  simp only [Variational.gradientPairing, Prod.snd_sum, Finset.sum_apply, inner_sum]
  exact Finset.sum_comm

theorem IsGroundVector.full_first_variation {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (v : Jet N L)
    (hv : v ∈ dirichletDomain N L a) :
    (∑ p : Direction N, inner ℂ (u.2 p) (v.2 p)) =
      (energy u : ℂ) * inner ℂ u.1 v.1 := by
  let w : Jet N L := ∑ σ : Equiv.Perm (Fin N), permutationJet σ v
  have hwd : w ∈ dirichletDomain N L a := by
    change w ∈ dirichletSubmodule N L a
    exact Submodule.sum_mem _ fun σ _ ↦ permutationJet_mem_domain σ hv
  have hwb : bosonic w.1 := by
    dsimp only [w]
    rw [Prod.fst_sum]
    exact bosonic_sum_permutationPullback v.1
  have hgp (σ : Equiv.Perm (Fin N)) :
      Variational.gradientPairing u (permutationJet σ v) = Variational.gradientPairing u v := by
    calc
      _ = Variational.gradientPairing (permutationJet σ u) (permutationJet σ v) := by
        rw [hu.permutationInvariant σ]
      _ = _ := gradientPairing_permutationJet σ u v
  have hip (σ : Equiv.Perm (Fin N)) :
      inner ℂ u.1 (permutationJet σ v).1 = inner ℂ u.1 v.1 := by
    calc
      _ = inner ℂ (permutationPullback σ u.1) (permutationPullback σ v.1) := by
        rw [(bosonic_iff_pullback u.1).mp hu.2.1 σ]; rfl
      _ = _ := inner_permutationPullback σ u.1 v.1
  have he := hu.first_variation w hwd hwb
  change Variational.gradientPairing u w = _ at he
  simp only [w, gradientPairing_sum_right, hgp, Prod.fst_sum, inner_sum, hip,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at he
  have hc : (Fintype.card (Equiv.Perm (Fin N)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hc
  change (Fintype.card (Equiv.Perm (Fin N)) : ℂ) * Variational.gradientPairing u v = _
  rw [he]
  ring

end HardSphere

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_ChordLift
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace PeriodicCutoff

variable (L : ℝ) [hL : Fact (0<L)]

lemma chord_continuous : Continuous (chord L) := by
  apply (QuotientAddGroup.isOpenMap_coe.isQuotientMap (AddCircle.continuous_mk' L) QuotientAddGroup.mk_surjective).continuous_iff.mpr
  simpa only [Function.comp_def,chord_coe] using (chordLift_smooth L).continuous

lemma chordLift_derivative (x : ℝ) : HasDerivAt (chordLift L)
    (2*(L/Real.pi*Real.sin (Real.pi/L*x))*Real.cos (Real.pi/L*x)) x := by
  have h := (((hasDerivAt_id x).const_mul (Real.pi/L)).sin.const_mul (L/Real.pi)).pow 2
  apply h.congr_deriv
  dsimp
  field_simp [ne_of_gt hL.out, Real.pi_ne_zero]

lemma chordLift_derivative_sq_le (x : ℝ) :
    (deriv (chordLift L) x)^2 ≤ 4*chordLift L x := by
  rw [(chordLift_derivative L x).deriv]
  have hc : Real.cos (Real.pi/L*x)^2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi/L*x),sq_nonneg (Real.sin (Real.pi/L*x))]
  simpa only [chordLift] using (show
    (2*(L/Real.pi*Real.sin (Real.pi/L*x))*Real.cos (Real.pi/L*x))^2≤
      4*(L/Real.pi*Real.sin (Real.pi/L*x))^2 by
        nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg (2*(L/Real.pi*Real.sin (Real.pi/L*x))))])

lemma centered_representative (x : AddCircle L) :
    ∃ t : ℝ, (t : AddCircle L)=x ∧ |t|≤L/2 ∧ ‖x‖=|t| := by
  let t := (AddCircle.equivIco L (-L/2) x).val
  have ht : (t : AddCircle L)=x := AddCircle.coe_equivIco
  have hb : |t|≤L/2 := by
    apply abs_le.mpr
    constructor
    · simpa only [neg_div] using (AddCircle.equivIco L (-L/2) x).property.1
    · have hu := (AddCircle.equivIco L (-L/2) x).property.2
      dsimp [t]
      linarith
  exact ⟨t,ht,hb,ht ▸ ((AddCircle.norm_coe_eq_abs_iff L (ne_of_gt hL.out)).mpr
    (by simpa only [abs_of_pos hL.out] using hb))⟩

lemma norm_sq_le_chord (x : AddCircle L) : ‖x‖^2≤(Real.pi/2)^2*chord L x := by
  obtain ⟨t,rfl,ht,hx⟩ := centered_representative L x
  have ha : |Real.pi/L*t|≤Real.pi/2 := by
    rw [abs_mul,abs_of_pos (div_pos Real.pi_pos hL.out)]
    calc
      Real.pi/L*|t|≤Real.pi/L*(L/2) := mul_le_mul_of_nonneg_left ht (le_of_lt (div_pos Real.pi_pos hL.out))
      _ = Real.pi/2 := by field_simp [ne_of_gt hL.out, Real.pi_ne_zero]
  have hb : |t|≤Real.pi/2*|L/Real.pi*Real.sin (Real.pi/L*t)| := by
    have h := mul_le_mul_of_nonneg_left (Real.mul_abs_le_abs_sin ha)
      (show 0≤L/2 from (div_pos hL.out (by norm_num)).le)
    simp only [abs_mul,abs_of_pos (div_pos Real.pi_pos hL.out)] at h
    rw [abs_mul,abs_of_pos (div_pos hL.out Real.pi_pos)]
    have he : L/2*(2/Real.pi*(Real.pi/L*|t|))=|t| := by
      field_simp [ne_of_gt hL.out, Real.pi_ne_zero]
    rw [he] at h
    convert h using 1 <;> first | rfl | (field_simp [ne_of_gt hL.out, Real.pi_ne_zero])
  rw [chord_coe,hx]
  dsimp [chordLift]
  calc
    _ ≤ (Real.pi/2*|L/Real.pi*Real.sin (Real.pi/L*t)|)^2 :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by positivity) (abs_nonneg _))).mpr hb
    _ = _ := by rw [mul_pow,sq_abs]

end PeriodicCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Operators_TransitionDerivative
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace PeriodicCutoff

lemma transition_derivative (x : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) x).hasDerivAt

lemma transition_deriv_eq_zero {x : ℝ} (hx : x∉Icc (0:ℝ) 1) :
    deriv Real.smoothTransition x=0 := by
  have he : (Real.smoothTransition =ᶠ[𝓝 x] fun _ ↦ (Real.smoothTransition x)) := by
    rcases not_and_or.mp hx with h | h
    · have hx : x<0 := lt_of_not_ge h
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      rw [Real.smoothTransition.zero_of_nonpos hy.le,Real.smoothTransition.zero_of_nonpos hx.le]
    · have hx : 1<x := lt_of_not_ge h
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      rw [Real.smoothTransition.one_of_one_le hy.le,Real.smoothTransition.one_of_one_le hx.le]
  exact ((hasDerivAt_const x (Real.smoothTransition x)).congr_of_eventuallyEq he).deriv

lemma exists_transition_bound : ∃ M : ℝ, 0<M ∧ ∀ x : ℝ, |deriv Real.smoothTransition x|≤M := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)).continuousOn
      (s := Icc (0:ℝ) 1)
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),fun x ↦ ?_⟩
  by_cases hx : x∈Icc (0:ℝ) 1
  · exact (hC x hx).trans (le_max_left _ _)
  · rw [transition_deriv_eq_zero hx,abs_zero]
    exact (zero_le_one : (0:ℝ)≤1).trans (le_max_right _ _)

end PeriodicCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_ThreeTorus
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace PeriodicCutoff
variable (L : ℝ) [hL : Fact (0<L)]

lemma pairQ_continuous : Continuous (fun p : ThreeTorus L × ThreeTorus L ↦ pairQ L p.1 p.2) := by
  unfold pairQ
  apply continuous_finsetSum
  intro j _
  exact (chord_continuous L).comp (by fun_prop)

omit hL in
lemma chordLift_le_qLift (z : Fin 3 → ℝ) (j : Fin 3) : chordLift L (z j)≤qLift L z :=
  Finset.single_le_sum (fun k _ ↦ sq_nonneg (L/Real.pi*Real.sin (Real.pi/L*z k))) (Finset.mem_univ j)

end PeriodicCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_Near
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.TightCutoff
open PeriodicCutoff MeasureTheory Set
noncomputable section

variable (L : ℝ) [hL : Fact (0<L)]

lemma distance_sum_le_pairQ (y x : ThreeTorus L) :
    (∑ j : Fin 3, dist (y j) (x j)^2) ≤ (Real.pi/2)^2*pairQ L y x := by
  rw [pairQ,Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ ↦ by simpa only [dist_eq_norm] using norm_sq_le_chord L (y j-x j)

lemma near_distance_sum {r : ℝ} (hr : 0 < r) {y x : ThreeTorus L}
    (hy : y∈near L r x) : (∑ j : Fin 3, dist (y j) (x j)^2) < (2*r)^2 := by
  have hp : Real.pi^2<10 := by nlinarith [Real.pi_lt_d2,Real.pi_pos]
  have hq := distance_sum_le_pairQ L y x
  have hs := mul_le_mul_of_nonneg_left hy (sq_nonneg (Real.pi/2))
  have hh := mul_lt_mul_of_pos_right hp (sq_pos_of_pos hr)
  nlinarith

lemma near_subset_box {r : ℝ} (hr : 0 < r) (x : ThreeTorus L) : near L r x⊆box L (2*r) x := by
  intro y hy
  simp only [box,Set.mem_univ_pi,Metric.mem_closedBall]
  intro j
  have hs := Finset.single_le_sum (f := fun j : Fin 3 ↦ dist (y j) (x j)^2)
    (fun j _ ↦ sq_nonneg _) (Finset.mem_univ j)
  have hh := near_distance_sum L hr hy
  exact (sq_le_sq₀ dist_nonneg (by positivity)).mp (hs.trans hh.le)

end
end HardSphere.TightCutoff

namespace HardSphere.TightCutoff
open PeriodicCutoff
noncomputable section
variable (L : ℝ) [hL : Fact (0<L)]

lemma angle_bounds (r : ℝ) (y x : ThreeTorus L) : 0≤angle L r y x ∧ angle L r y x≤Real.pi/2 := by
  constructor
  · exact mul_nonneg (by positivity) (Real.smoothTransition.nonneg _)
  · simpa only [angle,mul_one] using mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _)
      (show 0≤Real.pi/2 by positivity)

lemma angle_one {r : ℝ} (hr : 0 < r) {y x : ThreeTorus L} (hq : (3/2)*r^2≤pairQ L y x) :
    angle L r y x=Real.pi/2 := by
  unfold angle
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by positivity)).mpr (by nlinarith)),mul_one]

lemma angle_one_outside {r : ℝ} (hr : 0 < r) {y x : ThreeTorus L}
    (hx : y∉near L r x) : angle L r y x=Real.pi/2 :=
  angle_one L hr (not_le.mp hx).le
end
end HardSphere.TightCutoff

namespace HardSphere.TightCutoff
open PeriodicCutoff
variable (L : ℝ) [hL : Fact (0<L)]

omit hL in
lemma angleLift_derivative (r : ℝ) (z : Fin 3 → ℝ → ℝ)
    (d : Fin 3 → ℝ) (t : ℝ) (hd : ∀ j, HasDerivAt (z j) (d j) t) :
    HasDerivAt (fun s ↦ angleLift L r (fun j ↦ z j s))
      (∑ j : Fin 3, anglePartial L r (fun k ↦ z k t) j*d j) t := by
  have hc j := ((chordLift_smooth L).differentiable (by simp) (z j t)).hasDerivAt.comp t (hd j)
  have hq := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 3))) (fun j _ ↦ hc j)
  have h := ((transition_derivative ((qLift L (fun j ↦ z j t)-(5/4)*r^2)/((1/4)*r^2))).comp t
    ((hq.sub_const ((5/4)*r^2)).div_const ((1/4)*r^2))).const_mul (Real.pi/2)
  apply h.congr_deriv
  dsimp [anglePartial,angleFactor]
  calc
    _ = (2*Real.pi/r^2*deriv Real.smoothTransition ((qLift L (fun j ↦ z j t)-(5/4)*r^2)/((1/4)*r^2)))*
        ∑ j : Fin 3, deriv (chordLift L) (z j t)*d j := by ring
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring

omit hL in
lemma angleFactor_eq_zero {r : ℝ} (hr : 0 < r) {z : Fin 3 → ℝ}
    (hz : qLift L z∉Icc ((5/4)*r^2) ((3/2)*r^2)) : angleFactor L r z=0 := by
  have ht : (qLift L z-(5/4)*r^2)/((1/4)*r^2)∉Icc (0:ℝ) 1 := by
    intro hc
    apply hz
    have h0 := (le_div_iff₀ (show 0<(1/4)*r^2 by positivity)).mp hc.1
    have h1 := (div_le_iff₀ (show 0<(1/4)*r^2 by positivity)).mp hc.2
    constructor <;> nlinarith
  simp only [angleFactor,transition_deriv_eq_zero ht,mul_zero]

omit hL in
lemma anglePartial_eq_zero {r : ℝ} (hr : 0 < r) {z : Fin 3 → ℝ}
    (hz : qLift L z∉Icc ((5/4)*r^2) ((3/2)*r^2)) (j : Fin 3) : anglePartial L r z j=0 := by
  rw [anglePartial,angleFactor_eq_zero L hr hz,zero_mul]

lemma anglePartial_sq_le {r M : ℝ} (hr : 0 < r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M) (z : Fin 3 → ℝ) (j : Fin 3) :
    anglePartial L r z j^2 ≤ 24*Real.pi^2*M^2/r^2 := by
  by_cases hz : qLift L z∈Icc ((5/4)*r^2) ((3/2)*r^2)
  · have hc : (deriv (chordLift L) (z j))^2≤6*r^2 := by
      have hs := chordLift_le_qLift L z j
      have hd := chordLift_derivative_sq_le L (z j)
      nlinarith [hz.2]
    have ht : (deriv Real.smoothTransition ((qLift L z-(5/4)*r^2)/((1/4)*r^2)))^2≤M^2 := by
      rw [← sq_abs (deriv Real.smoothTransition _)]
      exact (sq_le_sq₀ (abs_nonneg _) hM).mpr (hb _)
    calc
      _ = (2*Real.pi/r^2)^2*((deriv Real.smoothTransition ((qLift L z-(5/4)*r^2)/((1/4)*r^2)))^2*
          (deriv (chordLift L) (z j))^2) := by dsimp [anglePartial,angleFactor]; ring
      _ ≤ (2*Real.pi/r^2)^2*(M^2*(6*r^2)) := by gcongr
      _ = _ := by field_simp [hr.ne']; ring
  · rw [anglePartial_eq_zero L hr hz j,zero_pow (by norm_num)]
    positivity

end HardSphere.TightCutoff

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_ConfigurationPath
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace L2Multiplier
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma coe_clm (f : α → ℂ) (hf : MemLp f ∞ μ) (u : Lp ℂ 2 μ) :
    clm f hf u =ᵐ[μ] fun x ↦ f x * u x := coe_apply f hf u

lemma clm_mul (f g : α → ℂ) (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ)
    (u : Lp ℂ 2 μ) : clm (f * g) (hg.mul hf) u = clm f hf (clm g hg u) := by
  apply Lp.ext
  filter_upwards [coe_clm (f * g) (hg.mul hf) u, coe_clm f hf (clm g hg u),
    coe_clm g hg u] with x h1 h2 h3
  simp only [h1, h2, h3, Pi.mul_apply, mul_assoc]

lemma inner_clm_right (f : α → ℂ) (hf : MemLp f ∞ μ) (u v : Lp ℂ 2 μ) :
    inner ℂ u (clm f hf v) = inner ℂ (clm (fun x ↦ conj (f x)) hf.star u) v := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_clm f hf v, coe_clm (fun x ↦ conj (f x)) hf.star u] with x h1 h2
  simp only [h1, h2, RCLike.inner_apply, map_mul, starRingEnd_self_apply]
  ring

end L2Multiplier

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CoordinateLine
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere

open scoped ComplexConjugate

lemma coordDerivative_conj {N : ℕ} {L : Length} {f : Configuration N L → ℂ}
    (hf : Differentiable ℝ (fun X : LiftedConfiguration N ↦ f (project N L X)))
    (p : Direction N) :
    coordDerivative N L (fun X ↦ conj (f X)) p = fun X ↦ conj (coordDerivative N L f p X) := by
  funext X
  unfold coordDerivative
  have h := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp (representative N L X)
    (hf _).hasFDerivAt
  exact congrArg (fun A : LiftedConfiguration N →L[ℝ] ℂ ↦
    A (Pi.single p.1 (Pi.single p.2 1))) h.fderiv

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SmoothMultiplier
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere

lemma SmoothTest.jet_multiply {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothMultiplier N L) (g : SmoothTest N L a) :
    (g.multiply f).jet = f.onJet g.jet := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (g.multiply f).memLp, MemLp.coeFn_toLp g.memLp,
      L2Multiplier.coe_clm f.toFun f.memLp_top g.jet.1] with X h1 h2 h3
    change _ = (f.onScalar g.jet.1) X
    exact h1.trans (by simpa only [SmoothTest.multiply, Pi.mul_apply, SmoothTest.jet,
      SmoothMultiplier.onScalar, h2] using h3.symm)
  · funext p
    apply Lp.ext
    have hder := coordDerivative_mul (f.smooth.differentiable (by simp))
      (g.smooth.differentiable (by simp)) p
    filter_upwards [MemLp.coeFn_toLp ((g.multiply f).partial_memLp p),
      MemLp.coeFn_toLp g.memLp, MemLp.coeFn_toLp (g.partial_memLp p),
      L2Multiplier.coe_clm f.toFun f.memLp_top (g.jet.2 p),
      L2Multiplier.coe_clm _ (f.partial_memLp_top p) g.jet.1,
      Lp.coeFn_add (f.onScalar (g.jet.2 p))
        (L2Multiplier.clm _ (f.partial_memLp_top p) g.jet.1)] with X h1 h2 h3 h4 h5 h6
    change _ = (f.onScalar (g.jet.2 p) + L2Multiplier.clm _ (f.partial_memLp_top p) g.jet.1) X
    rw [h6, Pi.add_apply, SmoothMultiplier.onScalar, h4, h5]
    simp only [SmoothTest.jet]
    rw [h1]
    change coordDerivative N L (f.toFun * g.toFun) p X = _
    rw [hder]
    simp only [Pi.add_apply, Pi.mul_apply, h2, h3]
    ring

lemma SmoothMultiplier.onJet_mem_domain {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothMultiplier N L) {u : Jet N L} (hu : u ∈ dirichletDomain N L a) :
    f.onJet u ∈ dirichletDomain N L a := by
  apply map_mem_closure f.onJet.continuous hu
  rintro _ ⟨g, rfl⟩
  exact ⟨g.multiply f, g.jet_multiply f⟩

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_InnerClmRealRight
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace L2Multiplier
open MeasureTheory
open scoped ComplexConjugate ENNReal
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
lemma inner_clm_real_right (f : α → ℂ) (hf : MemLp f ∞ μ)
    (hreal : ∀ x, conj (f x) = f x) (u v : Lp ℂ 2 μ) :
    inner ℂ u (clm f hf v) = inner ℂ (clm f hf u) v := by
  simpa only [show (fun x ↦ conj (f x)) = f from funext hreal] using
    inner_clm_right f hf u v

lemma clm_comm (f g : α → ℂ) (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ)
    (u : Lp ℂ 2 μ) : clm f hf (clm g hg u) = clm g hg (clm f hf u) := by
  rw [← clm_mul, ← clm_mul]
  congr 2
  exact mul_comm f g

end L2Multiplier
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate ENNReal
lemma SmoothMultiplier.partial_real {N : ℕ} {L : Length} (f : SmoothMultiplier N L)
    (hf : ∀ X, conj (f.toFun X) = f.toFun X) (p : Direction N) (X : Configuration N L) :
    conj (coordDerivative N L f.toFun p X) = coordDerivative N L f.toFun p X := by
  have he : (fun X ↦ conj (f.toFun X)) = f.toFun := funext hf
  rw [← congrFun (coordDerivative_conj (f.smooth.differentiable (by simp)) p) X, he]

lemma SmoothMultiplier.inner_onScalar_right {N : ℕ} {L : Length}
    (f : SmoothMultiplier N L) (hf : ∀ X, conj (f.toFun X) = f.toFun X)
    (u v : ScalarL2 N L) : inner ℂ u (f.onScalar v) = inner ℂ (f.onScalar u) v :=
  L2Multiplier.inner_clm_real_right _ _ hf u v

lemma SmoothMultiplier.onScalar_derivativeScalar_comm {N : ℕ} {L : Length}
    (f : SmoothMultiplier N L) (p : Direction N) (u : ScalarL2 N L) :
    f.onScalar (f.derivativeScalar p u) = f.derivativeScalar p (f.onScalar u) :=
  L2Multiplier.clm_comm _ _ _ _ u

theorem IsGroundVector.smooth_multiplier_identity {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (f : SmoothMultiplier N L)
    (hf : ∀ X, conj (f.toFun X) = f.toFun X) :
    energy (f.onJet u) - energy u * ‖f.onScalar u.1‖ ^ 2 =
      ∑ p : Direction N, ‖f.derivativeScalar p u.1‖ ^ 2 := by
  have hv := f.onJet_mem_domain (f.onJet_mem_domain hu.1)
  have he := hu.full_first_variation (f.onJet (f.onJet u)) hv
  have hnorm (x : ScalarL2 N L) : (inner ℂ x x).re = ‖x‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  have hpair (p : Direction N) :
      (inner ℂ (u.2 p) ((f.onJet (f.onJet u)).2 p)).re =
        ‖f.onScalar (u.2 p)‖ ^ 2 +
          2 * (inner ℂ (f.onScalar (u.2 p)) (f.derivativeScalar p u.1)).re := by
    rw [f.onJet_snd, f.onJet_snd, f.onJet_fst, map_add,
      inner_add_right, inner_add_right, ← f.onScalar_derivativeScalar_comm,
      f.inner_onScalar_right hf (u.2 p) (f.onScalar (u.2 p)),
      f.inner_onScalar_right hf (u.2 p) (f.derivativeScalar p u.1)]
    simp only [Complex.add_re, hnorm]
    ring
  have hs : (inner ℂ u.1 (f.onJet (f.onJet u)).1).re = ‖f.onScalar u.1‖ ^ 2 := by
    rw [f.onJet_fst, f.onJet_fst, f.inner_onScalar_right hf, hnorm]
  have her := congrArg Complex.re he
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hs, hpair] at her
  change (∑ p, ‖(f.onJet u).2 p‖ ^ 2) - energy u * ‖f.onScalar u.1‖ ^ 2 = _
  simp only [f.onJet_snd, norm_add_sq (𝕜 := ℂ)]
  rw [← her]
  change (∑ p, (‖f.onScalar (u.2 p)‖ ^ 2 +
      2 * (inner ℂ (f.onScalar (u.2 p)) (f.derivativeScalar p u.1)).re +
      ‖f.derivativeScalar p u.1‖ ^ 2)) -
    (∑ p, (‖f.onScalar (u.2 p)‖ ^ 2 +
      2 * (inner ℂ (f.onScalar (u.2 p)) (f.derivativeScalar p u.1)).re)) = _
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_NormSqIntegral
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace IndicatorStrong
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma norm_sq_integral (f : Lp ℂ 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re]
  · congr 1
    ext x
    simp only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]
  · exact L2.integrable_inner f f

end IndicatorStrong

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CoeScalar
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.coe_onScalar {n : ℕ} {L : Length} (f : SmoothMultiplier n L) (u : ScalarL2 n L) :
    f.onScalar u =ᵐ[volume] fun X ↦ f.toFun X*u X := L2Multiplier.coe_clm _ _ _

lemma SmoothMultiplier.coe_derivativeScalar {n : ℕ} {L : Length} (f : SmoothMultiplier n L)
    (p : Direction n) (u : ScalarL2 n L) :
    f.derivativeScalar p u =ᵐ[volume] fun X ↦ coordDerivative n L f.toFun p X*u X :=
  L2Multiplier.coe_clm _ _ _

lemma SmoothMultiplier.gradient_norm_le {S : Type*} {n : ℕ} {L : Length}
    (A : Finset S) (f : SmoothMultiplier n L) (g : S → SmoothMultiplier n L) (C : ℝ)
    (hfg : ∀ X, (∑ p : Direction n, ‖coordDerivative n L f.toFun p X‖^2) ≤
      C*∑ s∈A, ‖(g s).toFun X‖^2) (u : ScalarL2 n L) :
    (∑ p : Direction n, ‖f.derivativeScalar p u‖^2) ≤ C*∑ s∈A, ‖(g s).onScalar u‖^2 := by
  have hi (p : Direction n) : Integrable (fun X ↦ ‖(f.derivativeScalar p u) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  have hj (s : S) : Integrable (fun X ↦ ‖((g s).onScalar u) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  simp_rw [IndicatorStrong.norm_sq_integral]
  rw [← integral_finsetSum Finset.univ (fun p _ ↦ hi p),
    ← integral_finsetSum A (fun s _ ↦ hj s),← integral_const_mul]
  apply integral_mono_ae (integrable_finsetSum _ (fun p _ ↦ hi p))
    ((integrable_finsetSum _ (fun s _ ↦ hj s)).const_mul C)
  have hd : ∀ᵐ X ∂volume, ∀ p, (f.derivativeScalar p u) X=coordDerivative n L f.toFun p X*u X :=
    ae_all_iff.mpr (fun p ↦ f.coe_derivativeScalar p u)
  have hg : ∀ᵐ X ∂volume, ∀ s∈A, ((g s).onScalar u) X=(g s).toFun X*u X :=
    (ae_ball_iff A.countable_toSet).mpr (fun s _ ↦ (g s).coe_onScalar u)
  filter_upwards [hd,hg] with X hX hY
  simp_rw [hX,norm_mul,mul_pow]
  have he : (∑ s∈A, ‖((g s).onScalar u) X‖^2)=
      (∑ s∈A, ‖(g s).toFun X‖^2)*‖u X‖^2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun s hs ↦ by rw [hY s hs,norm_mul,mul_pow]
  rw [he,← Finset.sum_mul,← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hfg X) (sq_nonneg _)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FinsetEraseRecursion
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter

lemma finset_erase_recursion {S : Type*} [DecidableEq S] (a : Finset S → ℝ) (q : ℝ)
    (hq : 0 ≤ q) (h0 : a ∅ ≤ 1)
    (hr : ∀ A : Finset S, A.Nonempty → (A.card : ℝ)*a A ≤ q*∑ s∈A, a (A.erase s)) :
    ∀ A : Finset S, a A ≤ q^A.card := by
  intro A
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases hA : A.Nonempty
    · have hc : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
      have hs : (∑ s∈A, a (A.erase s)) ≤ (A.card : ℝ)*q^(A.card-1) := by
        calc
          _ ≤ ∑ _s∈A, q^(A.card-1) := Finset.sum_le_sum fun s hs ↦ by
            have hh := ih (A.erase s) (Finset.erase_ssubset hs)
            rwa [Finset.card_erase_of_mem hs] at hh
          _ = _ := by simp
      have he : q*((A.card : ℝ)*q^(A.card-1))=(A.card : ℝ)*q^A.card := by
        rw [show q^A.card=q^(A.card-1)*q by
          conv_lhs => rw [← Nat.sub_add_cancel hA.card_pos]
          rw [pow_succ]]
        ring
      have ht := (hr A hA).trans ((mul_le_mul_of_nonneg_left hs hq).trans_eq he)
      exact (mul_le_mul_iff_right₀ hc).mp (by simpa only [mul_comm (A.card : ℝ)] using ht)
    · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
      simpa [he] using h0

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FinsetProd
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.partial_finsetProd {S : Type*} [DecidableEq S] {n : ℕ} {L : Length}
    (A : Finset S) (w : S → SmoothMultiplier n L) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (SmoothMultiplier.finsetProd A w).toFun p X=
      ∑ s∈A, (∏ z∈A.erase s, (w z).toFun X)*coordDerivative n L (w s).toFun p X := by
  unfold coordDerivative
  change (fderiv ℝ (fun Y ↦ ∏ s∈A, (w s).toFun (project n L Y)) _) _ = _
  rw [fderiv_finsetProd (fun s _ ↦ (w s).smooth.differentiable (by simp) _),sum_apply]
  simp only [smul_apply,smul_eq_mul,project_representative]

lemma norm_sq_sum_of_disjoint {S : Type*} [DecidableEq S] (A : Finset S) (f : S → ℂ)
    (hf : ∀ s∈A, ∀ z∈A, s≠z → f s=0 ∨ f z=0) : ‖∑ s∈A, f s‖^2=∑ s∈A, ‖f s‖^2 := by
  by_cases h : ∃ s∈A, f s≠0
  · obtain ⟨s,hs,hfs⟩ := h
    have hz : ∀ z∈A, z≠s → f z=0 := by
      intro z hz hzs
      exact (hf z hz s hs hzs).resolve_right hfs
    rw [Finset.sum_eq_single s (fun z hza hzs ↦ hz z hza hzs) (by simp_all)]
    rw [Finset.sum_eq_single s (fun z hza hzs ↦ by rw [hz z hza hzs,norm_zero]; norm_num) (by simp_all)]
  · push Not at h
    rw [Finset.sum_eq_zero (fun s hs ↦ h s hs)]
    simp only [norm_zero,zero_pow (by norm_num : 2≠0)]
    symm
    exact Finset.sum_eq_zero fun s hs ↦ by rw [h s hs,norm_zero]; norm_num

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SubcubeBase
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates
open scoped BigOperators

lemma subdivision_index {n : ℕ} (hn : 2≤n) :
    ∃j : ℕ, 1≤j ∧ 2*j^3≤n ∧ n≤16*j^3 := by
  have hex : ∃k : ℕ, n<2*k^3 := by
    refine ⟨n+1,?_⟩
    nlinarith [sq_nonneg (n:ℤ)]
  let k := Nat.find hex
  have hk : n<2*k^3 := Nat.find_spec hex
  have hk0 : k≠0 := by intro he; simp [he] at hk
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hmin : 2*j^3≤n := by
    have ht : j<Nat.find hex := by change j<k; omega
    exact Nat.le_of_not_gt (Nat.find_min hex ht)
  have hjpos : 1≤j := by
    by_contra h
    have : j=0 := by omega
    simp [hj,this] at hk
    omega
  refine ⟨j,hjpos,hmin,?_⟩
  have hp : (j+1)^3≤(2*j)^3 := Nat.pow_le_pow_left (by omega : j+1≤2*j) 3
  rw [hj] at hk
  nlinarith

lemma subdivided_cube_capacity {n j : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n+1) → Point) → E} (hF : ContDiff ℝ 1 F)
    {r h : ℝ} (hr : 0 < r) (hh : 0≤h) (b : Point)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c) ≤ r^2 → F X=0) :
    ((n+1-j^3 : ℕ) : ℝ≥0∞)*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun _ ↦ volume.restrict (cube b (j*h)))) ≤
      ENNReal.ofReal (Real.sqrt 3*h^3/r)*
        ∑ i, (∫⁻ X, ENNReal.ofReal (particleGradSq F i X)
          ∂Measure.pi (fun _ ↦ volume.restrict (cube b (j*h)))) := by
  rw [cube_configuration_subdivision b hh]
  simp_rw [lintegral_sum_measure,tsum_fintype]
  rw [Finset.mul_sum,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  have hc : Fintype.card (Fin j × Fin j × Fin j)=j^3 := by simp only [Fintype.card_prod,Fintype.card_fin]; ring
  simpa only [hc] using sector_capacity hF hr hh (subcubeBase b h) σ hz

lemma cube_coefficient {n j : ℕ} (hn : 2≤n) (hj : 1≤j) (hup : 2*j^3≤n) (hlo : n≤16*j^3)
    {r l : ℝ} (hr : 0 < r) (hl : 0<l) :
    (1/(64*Real.sqrt 3)*r/l^3*(n:ℝ)*((n:ℝ)-1))*(Real.sqrt 3*(l/(j:ℝ))^3/r) ≤
      ((n-j^3:ℕ):ℝ) := by
  have hjs : (0:ℝ)<j := by exact_mod_cast hj
  have hrr := hr.ne'
  have hlr := hl.ne'
  have hsr : Real.sqrt 3≠0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hjn : j^3≤n := by omega
  rw [Nat.cast_sub hjn,Nat.cast_pow]
  have he : (1/(64*Real.sqrt 3)*r/l^3*(n:ℝ)*((n:ℝ)-1))*(Real.sqrt 3*(l/(j:ℝ))^3/r)=
      (n:ℝ)*((n:ℝ)-1)/(64*(j:ℝ)^3) := by field_simp
  rw [he]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<64*(j:ℝ)^3)).mpr
  have hup' : 2*(j:ℝ)^3≤(n:ℝ) := by exact_mod_cast hup
  have hlo' : (n:ℝ)≤16*(j:ℝ)^3 := by exact_mod_cast hlo
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have ht : (0:ℝ)≤(j:ℝ)^3 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hlo' (show (0:ℝ)≤n by positivity)
  have h2 := mul_le_mul_of_nonneg_left hup' ht
  nlinarith

lemma smooth_cube_energy {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin n → Point) → E} (hF : ContDiff ℝ 1 F)
    {r l : ℝ} (hr : 0 < r) (hl : 0<l) (b : Point)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c) ≤ r^2 → F X=0) :
    ENNReal.ofReal (1/(64*Real.sqrt 3)*r/l^3*(n:ℝ)*((n:ℝ)-1))*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun _ ↦ volume.restrict (cube b l))) ≤
        ∑ i, (∫⁻ X, ENNReal.ofReal (particleGradSq F i X)
          ∂Measure.pi (fun _ ↦ volume.restrict (cube b l))) := by
  by_cases hn : 2≤n
  · obtain ⟨j,hj,hu,hd⟩ := subdivision_index hn
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    have hjr : (0:ℝ)<j := by exact_mod_cast hj
    have hlj : (j:ℝ)*(l/(j:ℝ))=l := by field_simp
    have h := subdivided_cube_capacity (j := j) hF hr (le_of_lt (div_pos hl hjr)) b hz
    rw [hlj] at h
    let A := 1/(64*Real.sqrt 3)*r/l^3*((m+1:ℕ):ℝ)*(((m+1:ℕ):ℝ)-1)
    let C := Real.sqrt 3*(l/(j:ℝ))^3/r
    have hC : 0<C := by dsimp [C]; positivity
    have hA : 0≤A := by
      have hm : (1:ℝ)≤((m+1:ℕ):ℝ) := by norm_num
      have hm' : (0:ℝ)≤((m+1:ℕ):ℝ)-1 := by linarith
      dsimp [A]; positivity
    have hco : ENNReal.ofReal A*ENNReal.ofReal C≤((m+1-j^3:ℕ):ℝ≥0∞) := by
      rw [← ENNReal.ofReal_mul hA]
      have hc := ENNReal.ofReal_le_ofReal (cube_coefficient hn hj hu hd hr hl)
      simpa only [ENNReal.ofReal_natCast] using hc
    apply (ENNReal.mul_le_mul_iff_left (ne_of_gt (ENNReal.ofReal_pos.mpr hC)) ENNReal.ofReal_ne_top).mp
    calc
      _ = (ENNReal.ofReal A*ENNReal.ofReal C)*
          (∫⁻ X,ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun _ ↦ volume.restrict (cube b l))) := by
            dsimp only [A]; ac_rfl
      _ ≤ ((m+1-j^3:ℕ):ℝ≥0∞)*_ := mul_le_mul_of_nonneg_right hco (by positivity)
      _ ≤ ENNReal.ofReal C*∑ i, (∫⁻ X, ENNReal.ofReal (particleGradSq F i X)
          ∂Measure.pi (fun _ ↦ volume.restrict (cube b l))) := h
      _ = _ := mul_comm _ _
  · have hcases : n=0 ∨ n=1 := by omega
    rcases hcases with rfl | rfl <;> simp

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_PointFin
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates
open scoped BigOperators

lemma pointFin_apply (x : Point) : pointFin x=![x.1,x.2.1,x.2.2] := by
  ext i
  fin_cases i <;> rfl

lemma configurationFin_apply {n : ℕ} (X : Fin n → Point) (i : Fin n) :
    configurationFin n X i=pointFin (X i) := rfl

lemma configurationFin_single {n : ℕ} (i : Fin n) (q : Fin 3) :
    configurationFin n (Pi.single i (![axis0,axis1,axis2] q))=Pi.single i (Pi.single q 1) := by
  funext k t
  by_cases hk : k=i
  · subst k
    fin_cases q <;> fin_cases t <;> simp [configurationFin_apply,pointFin_apply,axis0,axis1,axis2]
  · simp [configurationFin_apply,hk]

lemma sqRadius_eq_sum (x : Point) : sqRadius x=∑ j : Fin 3,(pointFin x j)^2 := by
  simp [sqRadius,pointFin_apply,Fin.sum_univ_succ,add_assoc]

end HardSphere.SphericalCoordinates

namespace HardSphere
open SphericalCoordinates
open scoped BigOperators

lemma addCircle_dist_coe_sq_le (L : Length) (x y : ℝ) :
    dist (x : AddCircle L.val) (y : AddCircle L.val)^2≤(x-y)^2 := by
  have hn : dist (x : AddCircle L.val) (y : AddCircle L.val)≤|x-y| := by
    rw [dist_eq_norm,← QuotientAddGroup.mk_sub]
    exact QuotientAddGroup.norm_mk_le_norm
  have hh := (sq_le_sq₀ dist_nonneg (abs_nonneg (x-y))).mpr hn
  simpa only [sq_abs] using hh

lemma cubeParameter_distance {n : ℕ} (L : Length) (X : Fin n → Point) (i j : Fin n)
    {a : ℝ} (ha : 0≤a) (hd : sqRadius (X i-X j)≤a^2) :
    torusDistance L (cubeParameter n L X i) (cubeParameter n L X j)≤a := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨ha,le_trans ?_ hd⟩
  rw [sqRadius_eq_sum]
  apply Finset.sum_le_sum
  intro q _
  simpa only [cubeParameter,project,configurationFin_apply,map_sub,Pi.sub_apply] using
    addCircle_dist_coe_sq_le L (pointFin (X i) q) (pointFin (X j) q)

lemma SmoothTest.cube_zero {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a) (ha : 0≤a)
    (X : Fin n → Point) (i j : Fin n) (hij : i≠j) (hd : sqRadius (X i-X j)≤a^2) :
    f.toFun (cubeParameter n L X)=0 := by
  by_contra hz
  have h := f.support_allowed (subset_tsupport _ hz)
  have hdist := cubeParameter_distance L X i j ha hd
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (not_lt_of_ge hdist) (h i j hlt)
  · have hs : torusDistance L (cubeParameter n L X j) (cubeParameter n L X i)=
        torusDistance L (cubeParameter n L X i) (cubeParameter n L X j) := by
      simp only [torusDistance,dist_comm]
    rw [← hs] at hdist
    exact (not_lt_of_ge hdist) (h j i hgt)

lemma SmoothTest.cube_smooth {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a) :
    ContDiff ℝ 1 (fun X : Fin n → Point ↦ f.toFun (cubeParameter n L X)) :=
  (f.smooth.of_le (by simp)).comp (configurationFin n).contDiff

lemma SmoothTest.cube_derivative {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a)
    (X : Fin n → Point) (i : Fin n) (q : Fin 3) :
    fderiv ℝ (fun X : Fin n → Point ↦ f.toFun (cubeParameter n L X)) X
      (Pi.single i (![axis0,axis1,axis2] q))=
        coordDerivative n L f.toFun (i,q) (cubeParameter n L X) := by
  rw [cubeParameter,coordDerivative_project]
  have h := ((f.smooth.differentiable (by simp) (configurationFin n X)).hasFDerivAt).comp X
    (configurationFin n).hasFDerivAt
  rw [show (fun X ↦ f.toFun (cubeParameter n L X))=
    (fun Y ↦ f.toFun (project n L Y)) ∘ configurationFin n from rfl,h.fderiv]
  simp only [ContinuousLinearMap.comp_apply,configurationFin_single]

lemma SmoothTest.cube_gradient {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a)
    (X : Fin n → Point) (i : Fin n) :
    particleGradSq (fun X ↦ f.toFun (cubeParameter n L X)) i X=
      ∑ q : Fin 3, ‖coordDerivative n L f.toFun (i,q) (cubeParameter n L X)‖^2 := by
  have h0 := f.cube_derivative X i 0
  have h1 := f.cube_derivative X i 1
  have h2 := f.cube_derivative X i 2
  change fderiv ℝ (fun X ↦ f.toFun (cubeParameter n L X)) X (Pi.single i axis0)=_ at h0
  change fderiv ℝ (fun X ↦ f.toFun (cubeParameter n L X)) X (Pi.single i axis1)=_ at h1
  change fderiv ℝ (fun X ↦ f.toFun (cubeParameter n L X)) X (Pi.single i axis2)=_ at h2
  simp only [particleGradSq,h0,h1,h2,Fin.sum_univ_succ,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,
    Fin.sum_univ_zero,add_zero]
  ring

lemma smooth_norm_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) :
    ENNReal.ofReal (‖hf.toLp f‖^2)=∫⁻ x,ENNReal.ofReal (‖f x‖^2) ∂μ := by
  have he : ‖hf.toLp f‖^2=∫ x,‖f x‖^2 ∂μ := by
    rw [@norm_sq_eq_re_inner ℂ,L2.inner_def,← integral_re (L2.integrable_inner (hf.toLp f) (hf.toLp f))]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp only [hx,inner_self_eq_norm_sq_to_K,RCLike.re_ofReal_pow]
  rw [he,ofReal_integral_eq_lintegral_ofReal (hf.integrable_norm_pow (by decide : (2:ℕ)≠0))
    (Filter.Eventually.of_forall (fun x ↦ sq_nonneg ‖f x‖))]

lemma cube_energy_coefficient_nonneg (n : ℕ) {a l : ℝ} (ha : 0≤a) (hl : 0≤l) :
    0≤1/(64*Real.sqrt 3)*a/l^3*(n:ℝ)*((n:ℝ)-1) := by
  cases n with
  | zero => simp
  | succ n =>
    have hn : (0:ℝ)≤((n+1:ℕ):ℝ)-1 := by norm_num
    positivity

lemma SmoothTest.cube_gradient_lintegral {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a)
    (i : Fin n) :
    (∫⁻ X, ENNReal.ofReal (particleGradSq (fun X ↦ f.toFun (cubeParameter n L X)) i X)
      ∂Measure.pi (fun _ ↦ volume.restrict (cube 0 L.val)))=
        ∑ q : Fin 3, ENNReal.ofReal (‖f.jet.2 (i,q)‖^2) := by
  simp_rw [f.cube_gradient,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _)]
  rw [lintegral_finsetSum _ (fun q _ ↦ by
    exact (((f.continuous_partial (i,q)).measurable.comp (cubeParameter_preserving n L).measurable).norm.pow_const 2).ennreal_ofReal)]
  apply Finset.sum_congr rfl
  intro q _
  rw [(cubeParameter_preserving n L).lintegral_comp
    (f := fun x ↦ ENNReal.ofReal (‖coordDerivative n L f.toFun (i,q) x‖^2))
    (((f.continuous_partial (i,q)).measurable.norm.pow_const 2).ennreal_ofReal),← smooth_norm_lintegral (f.partial_memLp (i,q))]
  rfl

lemma SmoothTest.energy_lower {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a) (ha : 0<a) :
    (1/(64*Real.sqrt 3)*a/L.val^3*(n:ℝ)*((n:ℝ)-1))*‖f.jet.1‖^2≤energy f.jet := by
  have h := smooth_cube_energy f.cube_smooth ha L.property 0 (f.cube_zero ha.le)
  rw [(cubeParameter_preserving n L).lintegral_comp
    (f := fun x ↦ ENNReal.ofReal (‖f.toFun x‖^2))
    ((f.continuous.measurable.norm.pow_const 2).ennreal_ofReal),← smooth_norm_lintegral f.memLp] at h
  simp_rw [f.cube_gradient_lintegral] at h
  rw [← ENNReal.ofReal_mul (cube_energy_coefficient_nonneg n ha.le L.property.le)] at h
  have he : (∑ i : Fin n, ∑ q : Fin 3, ENNReal.ofReal (‖f.jet.2 (i,q)‖^2))=
      ENNReal.ofReal (energy f.jet) := by
    rw [energy,Fintype.sum_prod_type,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
    apply Finset.sum_congr rfl
    intro i _
    exact (ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _)).symm
  rw [he] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by unfold energy; positivity)).mp h

lemma dirichlet_energy_lower {n : ℕ} {L : Length} {a : ℝ} (ha : 0<a)
    (u : Jet n L) (hu : u∈dirichletDomain n L a) :
    (1/(64*Real.sqrt 3)*a/L.val^3*(n:ℝ)*((n:ℝ)-1))*‖u.1‖^2≤energy u := by
  have hc : IsClosed {u : Jet n L | (1/(64*Real.sqrt 3)*a/L.val^3*(n:ℝ)*((n:ℝ)-1))*‖u.1‖^2≤energy u} := by
    apply isClosed_le
    · exact continuous_const.mul (continuous_fst.norm.pow 2)
    · exact continuous_finsetSum _ (fun p _ ↦ ((continuous_apply p).comp continuous_snd).norm.pow 2)
  exact hc.closure_subset_iff.mpr (by rintro _ ⟨f,rfl⟩; exact f.energy_lower ha) hu

lemma IsGroundVector.energy_lower {n : ℕ} {L : Length} {a : ℝ} {u : Jet n L}
    (hu : IsGroundVector n L a u) (ha : 0<a) :
    1/(64*Real.sqrt 3)*a/L.val^3*(n:ℝ)*((n:ℝ)-1)≤energy u := by
  have h := dirichlet_energy_lower ha u hu.1
  simpa only [hu.2.2.1,one_pow,mul_one] using h

lemma IsGroundVector.energy_per_particle_lower {n : ℕ} {L : Length} {a : ℝ} {u : Jet n L}
    (hu : IsGroundVector n L a u) (ha : 0<a) (hn : 2≤n) :
    (1/(128*Real.sqrt 3))*(a*((n:ℝ)/L.val^3))≤energy u/(n:ℝ) := by
  have h := hu.energy_lower ha
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have hnp : (0:ℝ)<n := by linarith
  apply (le_div_iff₀ hnp).mpr
  apply le_trans _ h
  have he : (1/(128*Real.sqrt 3))*(a*((n:ℝ)/L.val^3))*(n:ℝ)=
      (1/(64*Real.sqrt 3)*a/L.val^3*(n:ℝ))*((n:ℝ)/2) := by ring
  rw [he]
  apply mul_le_mul_of_nonneg_left (by linarith)
  have hl := L.property
  positivity

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_RealComp
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.partial_realComp {n : ℕ} {L : Length} (f : SmoothMultiplier n L)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) φ)
    (hf : ∀ X, conj (f.toFun X)=f.toFun X) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (f.realComp φ hφ).toFun p X=
      ((deriv φ (f.toFun X).re : ℝ) : ℂ)*coordDerivative n L f.toFun p X := by
  let R := representative n L X
  let v : LiftedConfiguration n := Pi.single p.1 (Pi.single p.2 (1:ℝ))
  have hline : HasDerivAt (fun t : ℝ ↦ R+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add R
  have hdf := (f.smooth.differentiable (by simp) R).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hdφ := (hφ.differentiable (by simp) (f.toFun (project n L R)).re).hasDerivAt
  have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hdf
  have hchain := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hdφ.comp_of_eq 0 hreal (by simp))
  have hnew := ((f.realComp φ hφ).smooth.differentiable (by simp) R).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hline (by simp)
  have he := hnew.unique hchain
  change coordDerivative n L (f.realComp φ hφ).toFun p X = _ at he
  simp only [Complex.ofRealCLM_apply,Complex.reCLM_apply] at he
  rw [show project n L R=X from project_representative n L X] at he
  have hder : ((coordDerivative n L f.toFun p X).re : ℂ)=coordDerivative n L f.toFun p X := by
    apply Complex.ext
    · rfl
    · have h := congrArg Complex.im (f.partial_real hf p X)
      simp only [Complex.conj_im] at h
      simp only [Complex.ofReal_im]
      linarith
  change _ = ((deriv φ (f.toFun X).re * (coordDerivative n L f.toFun p X).re : ℝ) : ℂ) at he
  rw [Complex.ofReal_mul,hder] at he
  exact he

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LabelLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.partial_liftLabel {L : Length} (w : SmoothMultiplier 1 L)
    (n : ℕ) (i : Fin n) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (w.liftLabel n i).toFun p X=
      if p.1=i then coordDerivative 1 L w.toFun (0,p.2) (fun _ ↦ X i) else 0 := by
  classical
  have h := (w.smooth.differentiable (by simp)
    (labelLift n i (representative n L X))).hasFDerivAt.comp
    (representative n L X) (labelLift n i).hasFDerivAt
  change (fderiv ℝ ((fun Y : LiftedConfiguration 1 ↦ w.toFun (project 1 L Y)) ∘ labelLift n i)
    (representative n L X)) (Pi.single p.1 (Pi.single p.2 1))=_
  rw [h.fderiv,ContinuousLinearMap.comp_apply]
  by_cases hp : p.1=i
  · rw [ite_eq_left hp]
    have hd : labelLift n i (Pi.single p.1 (Pi.single p.2 1))=Pi.single 0 (Pi.single p.2 1) := by
      ext k j
      have hk : k=0 := Subsingleton.elim _ _
      subst k
      simp [labelLift,hp]
    rw [hd]
    rfl
  · rw [ite_eq_right hp]
    have hd : labelLift n i (Pi.single p.1 (Pi.single p.2 1))=0 := by
      ext k j
      simp [labelLift,Ne.symm hp]
    rw [hd,map_zero]

lemma SmoothMultiplier.partial_sum {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (SmoothMultiplier.sum w).toFun p X=∑ s, coordDerivative n L (w s).toFun p X := by
  unfold coordDerivative
  change (fderiv ℝ (fun Y ↦ ∑ s, (w s).toFun (project n L Y)) _) _ = _
  rw [fderiv_fun_sum (fun s _ ↦ (w s).smooth.differentiable (by simp) _),sum_apply]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_Bump
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

lemma bump_bounds (L : Length) (δ : ℝ) (x y : Torus L) : 0 ≤ bump L δ x y ∧ bump L δ x y ≤ 1 := by
  refine ⟨?_,Real.cos_le_one _⟩
  apply Real.cos_nonneg_of_mem_Icc
  exact ⟨by linarith [(TightCutoff.angle_bounds L.val δ y x).1,Real.pi_pos],
    (TightCutoff.angle_bounds L.val δ y x).2⟩

lemma bump_eq_zero {L : Length} {δ : ℝ} (hδ : 0<δ) (x : Torus L) {y : Torus L}
    (hy : y∉TightCutoff.near L.val δ x) : bump L δ x y=0 := by
  rw [bump,TightCutoff.angle_one_outside L.val hδ hy,Real.cos_pi_div_two]

lemma bump_support {L : Length} {δ : ℝ} (hδ : 0<δ) (x : Torus L) :
    tsupport (bump L δ x) ⊆ TightCutoff.near L.val δ x := by
  apply closure_minimal
  · intro y hy
    by_contra hn
    exact hy (bump_eq_zero hδ x hn)
  · exact isClosed_le ((pairQ_continuous L.val).comp
      (continuous_id.prodMk continuous_const)) continuous_const

lemma raw_fderiv (L : Length) (δ : ℝ) (x : Torus L) (R v : LiftedConfiguration 1) :
    fderiv ℝ (fun R ↦ (raw L δ x).toFun (project 1 L R)) R v =
      ((-Real.sin (TightCutoff.angleLift L.val δ (R 0-centerLift L x)) *
        ∑ j : Fin 3, TightCutoff.anglePartial L.val δ (R 0-centerLift L x) j*v 0 j : ℝ) : ℂ) := by
  have hd : HasDerivAt (fun t : ℝ ↦ R+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add R
  have hf := ((((raw L δ x).smooth).differentiable (by simp)) R).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd (by simp)
  have ha := TightCutoff.angleLift_derivative L.val δ
    (fun j t ↦ R 0 j+t*v 0 j-centerLift L x j) (fun j ↦ v 0 j) 0 (fun j ↦ by
      convert ((((hasDerivAt_id (0:ℝ)).mul_const (v 0 j)).const_add (R 0 j)).sub_const (centerLift L x j)) using 1 <;> first | rfl | simp only [one_mul])
  have hb := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 ha.cos
  have he : ((fun R ↦ (raw L δ x).toFun (project 1 L R)) ∘ fun t : ℝ ↦ R+t • v) =
      (fun t : ℝ ↦ (Real.cos (TightCutoff.angleLift L.val δ
        (fun j ↦ R 0 j+t*v 0 j-centerLift L x j)) : ℂ)) := by
    funext t
    exact congrArg Complex.ofReal (bump_project L δ x (R+t • v))
  rw [he] at hf
  convert hf.unique hb using 1
  all_goals try with_reducible_and_instances rfl
  simp only [zero_mul,add_zero,Complex.ofRealCLM_apply]
  rfl

lemma raw_partial (L : Length) (δ : ℝ) (x y : Torus L) (j : Fin 3) :
    coordDerivative 1 L (raw L δ x).toFun (0,j) (fun _ ↦ y)=
      ((-Real.sin (TightCutoff.angleLift L.val δ (centerLift L y-centerLift L x)) *
        TightCutoff.anglePartial L.val δ (centerLift L y-centerLift L x) j : ℝ) : ℂ) := by
  rw [coordDerivative,raw_fderiv]
  change (Complex.ofReal (-Real.sin _ * ∑ k : Fin 3, _ * (Pi.single j (1:ℝ)) k)) = _
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rfl

lemma raw_partial_sq_le {L : Length} {δ M : ℝ} (hδ : 0<δ) (hM : 0 ≤ M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M) (x y : Torus L) (j : Fin 3) :
    ‖coordDerivative 1 L (raw L δ x).toFun (0,j) (fun _ ↦ y)‖^2 ≤ 24*Real.pi^2*M^2/δ^2 := by
  rw [raw_partial,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,neg_sq]
  calc
    _ ≤ 1*(TightCutoff.anglePartial L.val δ (centerLift L y-centerLift L x) j)^2 := by
      gcongr
      exact Real.sin_sq_le_one _
    _ ≤ _ := by simpa using TightCutoff.anglePartial_sq_le L.val hδ hM hb (centerLift L y-centerLift L x) j

end HardSphere.CellOrbital

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_Chi
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

lemma chi_bounds (L : Length) (δ : ℝ) (x y : Torus L) : 0 ≤ chi L δ x y ∧ chi L δ x y ≤ 1 := by
  constructor
  · exact sq_nonneg _
  · change bump L (8*δ) x y ^ 2 ≤ 1
    nlinarith [(bump_bounds L (8*δ) x y).1,(bump_bounds L (8*δ) x y).2]

end HardSphere.CellOrbital

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_Chi2
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

lemma chiOne_apply (L : Length) (δ : ℝ) (x : Torus L) (X : Configuration 1 L) :
    (chiOne L δ x).toFun X=(chi L δ x (X 0) : ℂ) := by
  simp only [chiOne,SmoothMultiplier.mul,Pi.mul_apply,raw,SmoothMultiplier.ofSmooth,chi]
  rw [Complex.ofReal_pow,pow_two]

lemma countMultiplier_apply (n : ℕ) (L : Length) (δ : ℝ) (x : Torus L) (X : Configuration n L) :
    (countMultiplier n L δ x).toFun X=(count L δ x X : ℂ) := by
  change (∑ i : Fin n, (chiOne L δ x).toFun (fun _ ↦ X i)) = _
  simp_rw [chiOne_apply]
  exact (Complex.ofReal_sum _ _).symm

lemma countMultiplier_real (n : ℕ) (L : Length) (δ : ℝ) (x : Torus L) (X : Configuration n L) :
    conj ((countMultiplier n L δ x).toFun X)=(countMultiplier n L δ x).toFun X := by
  rw [countMultiplier_apply,Complex.conj_ofReal]

lemma chiOne_partial (L : Length) (δ : ℝ) (x y : Torus L) (j : Fin 3) :
    coordDerivative 1 L (chiOne L δ x).toFun (0,j) (fun _ ↦ y)=
      2*(bump L (8*δ) x y : ℂ)*coordDerivative 1 L (raw L (8*δ) x).toFun (0,j) (fun _ ↦ y) := by
  have he := congrFun (coordDerivative_mul ((raw L (8*δ) x).smooth.differentiable (by simp))
    ((raw L (8*δ) x).smooth.differentiable (by simp)) (0,j)) (fun _ ↦ y)
  change coordDerivative 1 L ((raw L (8*δ) x).toFun * (raw L (8*δ) x).toFun) (0,j) _ = _
  rw [he]
  change (bump L (8*δ) x y : ℂ)*_+(bump L (8*δ) x y : ℂ)*_=_
  ring

lemma countMultiplier_partial (n : ℕ) (L : Length) (δ : ℝ) (x : Torus L)
    (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (countMultiplier n L δ x).toFun p X=
      coordDerivative 1 L (chiOne L δ x).toFun (0,p.2) (fun _ ↦ X p.1) := by
  classical
  rw [countMultiplier,SmoothMultiplier.partial_sum]
  simp_rw [SmoothMultiplier.partial_liftLabel]
  simp

lemma chiOne_partial_sq_le {L : Length} {δ M : ℝ} (hδ : 0<δ) (hM : 0 ≤ M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M) (x y : Torus L) (j : Fin 3) :
    ‖coordDerivative 1 L (chiOne L δ x).toFun (0,j) (fun _ ↦ y)‖^2 ≤
      (4*(24*Real.pi^2*M^2/(8*δ)^2))*chi L δ x y := by
  rw [chiOne_partial,norm_mul,norm_mul,mul_pow,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [show ‖(2:ℂ)‖=2 by norm_num]
  have h := mul_le_mul_of_nonneg_left (raw_partial_sq_le (by positivity : 0<8*δ) hM hb x y j)
    (show 0 ≤ 4*(bump L (8*δ) x y)^2 by positivity)
  dsimp [chi]
  nlinarith

lemma countMultiplier_gradient_le {n : ℕ} {L : Length} {δ M : ℝ} (hδ : 0<δ) (hM : 0 ≤ M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M) (x : Torus L) (X : Configuration n L) :
    (∑ p : Direction n, ‖coordDerivative n L (countMultiplier n L δ x).toFun p X‖^2) ≤
      (3*(4*(24*Real.pi^2*M^2/(8*δ)^2)))*count L δ x X := by
  simp_rw [countMultiplier_partial]
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ i : Fin n, ∑ _j : Fin 3, (4*(24*Real.pi^2*M^2/(8*δ)^2))*chi L δ x (X i) := by
      exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ chiOne_partial_sq_le hδ hM hb x (X i) j
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,count,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end HardSphere.CellOrbital

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_Profile
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

lemma profile_one {h : ℝ} (hh : 0<h) {t : ℝ} (ht : t ≤ h) : profile h t=1 := by
  rw [profile,Real.smoothTransition.zero_of_nonpos (by rw [sub_nonpos]; exact (div_le_one hh).mpr ht)]
  ring

lemma profile_zero {h : ℝ} (hh : 0<h) {t : ℝ} (ht : 2*h ≤ t) : profile h t=0 := by
  rw [profile,Real.smoothTransition.one_of_one_le (by have hd := (le_div_iff₀ hh).mpr ht; linarith)]
  ring

lemma profile_deriv (h t : ℝ) : deriv (profile h) t= -deriv Real.smoothTransition (t/h-1)/h := by
  have hd := (transition_derivative (t/h-1)).comp t (((hasDerivAt_id t).div_const h).sub_const 1)
  have he := hd.const_sub 1
  have heq : (fun x : ℝ ↦ 1 - (Real.smoothTransition ∘ fun x : ℝ ↦ id x / h - 1) x) = profile h := rfl
  rw [heq] at he
  rw [he.deriv]
  ring

lemma profile_deriv_zero {h : ℝ} (hh : 0<h) {t : ℝ} (ht : t∉Icc h (2*h)) :
    deriv (profile h) t=0 := by
  rw [profile_deriv,transition_deriv_eq_zero]
  · simp
  · intro hc
    apply ht
    constructor
    · have hd := hc.1
      have hv : 1 ≤ t/h := by linarith
      exact (one_le_div hh).mp hv
    · have hv : t/h ≤ 2 := by linarith [hc.2]
      exact (div_le_iff₀ hh).mp hv

lemma profile_deriv_bound {h M : ℝ} (hh : 0<h) (_hM : 0 ≤ M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M) (t : ℝ) :
    |deriv (profile h) t| ≤ M/h := by
  rw [profile_deriv,abs_div,abs_neg,abs_of_pos hh]
  exact div_le_div_of_nonneg_right (hb _) hh.le

lemma cutoff_apply (n : ℕ) (L : Length) (δ : ℝ) (x : Torus L) (h : ℝ) (X : Configuration n L) :
    (cutoff n L δ x h).toFun X=(profile h (count L δ x X) : ℂ) := by
  change (profile h ((countMultiplier n L δ x).toFun X).re : ℂ)=_
  rw [countMultiplier_apply,Complex.ofReal_re]

lemma cutoff_partial (n : ℕ) (L : Length) (δ : ℝ) (x : Torus L) (h : ℝ)
    (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (cutoff n L δ x h).toFun p X=
      ((deriv (profile h) (count L δ x X) : ℝ) : ℂ)*coordDerivative n L (countMultiplier n L δ x).toFun p X := by
  rw [cutoff,SmoothMultiplier.partial_realComp _ _ _ (countMultiplier_real n L δ x),
    countMultiplier_apply,Complex.ofReal_re]

lemma cutoff_gradient_le {n : ℕ} {L : Length} {δ h M : ℝ} (hδ : 0<δ) (hh : 0<h) (hM : 0 ≤ M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M) (x : Torus L) (X : Configuration n L) :
    (∑ p : Direction n, ‖coordDerivative n L (cutoff n L δ x h).toFun p X‖^2) ≤
      (2*M^2*(3*(4*(24*Real.pi^2*M^2/(8*δ)^2))))/h := by
  by_cases ht : count L δ x X∈Icc h (2*h)
  · simp_rw [cutoff_partial,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    rw [← Finset.mul_sum]
    have hb2 : (deriv (profile h) (count L δ x X))^2 ≤ (M/h)^2 := by
      rw [← sq_abs (deriv _ _)]
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (profile_deriv_bound hh hM hb _)
    calc
      _ ≤ (M/h)^2*((3*(4*(24*Real.pi^2*M^2/(8*δ)^2)))*count L δ x X) :=
        mul_le_mul hb2 (countMultiplier_gradient_le hδ hM hb x X)
          (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (by positivity)
      _ ≤ (M/h)^2*((3*(4*(24*Real.pi^2*M^2/(8*δ)^2)))*(2*h)) := by gcongr; try exact ht.2
      _ = _ := by field_simp
  · simp_rw [cutoff_partial,profile_deriv_zero hh ht,Complex.ofReal_zero,zero_mul,norm_zero,
      zero_pow (by norm_num : 2≠0),Finset.sum_const_zero]
    positivity

end HardSphere.CellOrbital

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_Joint
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

lemma bump_separated {S : Type*} {L : Length} (c : S → Torus L)
    (hc : ∀ z v, z≠v → 1 ≤ dist (c z) (c v)) (z v : S) (hzv : z≠v) (y : Torus L) :
    bump L (8*(1/100)) (c z) y=0 ∨ bump L (8*(1/100)) (c v) y=0 := by
  by_contra hn
  push Not at hn
  have hbz := TightCutoff.near_subset_box L.val (by norm_num : (0:ℝ)<8*(1/100)) (c z)
    (bump_support (by norm_num) (c z) (subset_closure hn.1))
  have hbv := TightCutoff.near_subset_box L.val (by norm_num : (0:ℝ)<8*(1/100)) (c v)
    (bump_support (by norm_num) (c v) (subset_closure hn.2))
  have hd : dist (c z) (c v) ≤ (32:ℝ)/100 := by
    apply (dist_pi_le_iff (by norm_num)).mpr
    intro j
    have hzj : dist (y j) (c z j) ≤ 2*(8*(1/100)) := Set.mem_univ_pi.mp hbz j
    have hvj : dist (y j) (c v j) ≤ 2*(8*(1/100)) := Set.mem_univ_pi.mp hbv j
    have ht := dist_triangle (c z j) (y j) (c v j)
    rw [dist_comm (c z j) (y j)] at ht
    linarith
  linarith [hc z v hzv]

lemma cutoff_partials_disjoint {S : Type*} {n : ℕ} {L : Length} (c : S → Torus L)
    (hc : ∀ z v, z≠v → 1 ≤ dist (c z) (c v)) (h : ℝ) (z v : S) (hzv : z≠v)
    (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (cutoff n L (1/100) (c z) h).toFun p X=0 ∨
    coordDerivative n L (cutoff n L (1/100) (c v) h).toFun p X=0 := by
  rcases bump_separated c hc z v hzv (X p.1) with hz | hv
  · left
    simp only [cutoff_partial,countMultiplier_partial,chiOne_partial,hz,Complex.ofReal_zero,mul_zero,zero_mul]
  · right
    simp only [cutoff_partial,countMultiplier_partial,chiOne_partial,hv,Complex.ofReal_zero,mul_zero,zero_mul]

lemma joint_apply {S : Type*} [DecidableEq S] (n : ℕ) (L : Length) (c : S → Torus L)
    (h : ℝ) (A : Finset S) (X : Configuration n L) :
    (joint n L c h A).toFun X=(∏ s∈A, (profile h (count L (1/100) (c s) X) : ℂ)) := by
  change (∏ s∈A, (cutoff n L (1/100) (c s) h).toFun X)=_
  simp_rw [cutoff_apply]

lemma joint_real {S : Type*} [DecidableEq S] (n : ℕ) (L : Length) (c : S → Torus L)
    (h : ℝ) (A : Finset S) (X : Configuration n L) :
    conj ((joint n L c h A).toFun X)=(joint n L c h A).toFun X := by
  simp only [joint_apply,map_prod,Complex.conj_ofReal]

lemma joint_partial {S : Type*} [DecidableEq S] (n : ℕ) (L : Length) (c : S → Torus L)
    (h : ℝ) (A : Finset S) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (joint n L c h A).toFun p X=
      ∑ s∈A, (joint n L c h (A.erase s)).toFun X*
        coordDerivative n L (cutoff n L (1/100) (c s) h).toFun p X := by
  exact SmoothMultiplier.partial_finsetProd A _ p X

lemma joint_gradient_le {S : Type*} [DecidableEq S] {n : ℕ} {L : Length} {h M : ℝ}
    (hh : 0<h) (hM : 0 ≤ M) (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M)
    (c : S → Torus L) (hc : ∀ z v, z≠v → 1 ≤ dist (c z) (c v))
    (A : Finset S) (X : Configuration n L) :
    (∑ p : Direction n, ‖coordDerivative n L (joint n L c h A).toFun p X‖^2) ≤
      ((2*M^2*(3*(4*(24*Real.pi^2*M^2/(8*(1/100))^2))))/h)*
        ∑ s∈A, ‖(joint n L c h (A.erase s)).toFun X‖^2 := by
  have he (p : Direction n) :
      ‖coordDerivative n L (joint n L c h A).toFun p X‖^2=
      ∑ s∈A, ‖(joint n L c h (A.erase s)).toFun X‖^2*
        ‖coordDerivative n L (cutoff n L (1/100) (c s) h).toFun p X‖^2 := by
    rw [joint_partial,norm_sq_sum_of_disjoint]
    · simp_rw [norm_mul,mul_pow]
    · intro z hz v hv hzv
      rcases cutoff_partials_disjoint c hc h z v hzv p X with h1 | h2
      · exact Or.inl (by rw [h1,mul_zero])
      · exact Or.inr (by rw [h2,mul_zero])
  simp_rw [he]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  calc
    _ ≤ ‖(joint n L c h (A.erase s)).toFun X‖^2 * ((2*M^2*(3*(4*(24*Real.pi^2*M^2/(8*(1/100))^2))))/h) :=
      mul_le_mul_of_nonneg_left (cutoff_gradient_le (δ:=1/100) (by norm_num) hh hM hb (c s) X) (sq_nonneg _)
    _ = _ := mul_comm _ _

end HardSphere.CellOrbital

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_Joint2
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma joint_support {S : Type*} [DecidableEq S] {n : ℕ} {L : Length} {h : ℝ} (hh : 0<h)
    (c : S → Torus L) (A : Finset S) (u : ScalarL2 n L) :
    ∀ᵐ X ∂volume, ((joint n L c h A).onScalar u) X≠0 → ∀ s∈A, count L (1/100) (c s) X ≤ 2*h := by
  filter_upwards [(joint n L c h A).coe_onScalar u] with X hX hu s hs
  have hj : (joint n L c h A).toFun X≠0 := fun hz ↦ hu (by rw [hX,hz,zero_mul])
  rw [joint_apply] at hj
  have he : (profile h (count L (1/100) (c s) X) : ℂ)≠0 :=
    (Finset.prod_ne_zero_iff.mp hj) s hs
  by_contra hn
  have hz := profile_zero hh (le_of_lt (not_le.mp hn))
  exact he (by rw [hz,Complex.ofReal_zero])

lemma joint_gradient_norm_le {S : Type*} [DecidableEq S] {n : ℕ} {L : Length} {h M : ℝ}
    (hh : 0<h) (hM : 0 ≤ M) (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M)
    (c : S → Torus L) (hc : ∀ z v, z≠v → 1 ≤ dist (c z) (c v))
    (A : Finset S) (u : ScalarL2 n L) :
    (∑ p : Direction n, ‖(joint n L c h A).derivativeScalar p u‖^2) ≤
      ((2*M^2*(3*(4*(24*Real.pi^2*M^2/(8*(1/100))^2))))/h)*
        ∑ s∈A, ‖(joint n L c h (A.erase s)).onScalar u‖^2 :=
  SmoothMultiplier.gradient_norm_le A _ _ _ (joint_gradient_le hh hM hb c hc A) u

end HardSphere.CellOrbital

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_JointEmptyScalar
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff
open scoped ComplexConjugate
noncomputable section

lemma joint_empty_onScalar {S : Type*} [DecidableEq S] {n : ℕ} {L : Length}
    (c : S → Torus L) (h : ℝ) (u : ScalarL2 n L) : (joint n L c h ∅).onScalar u=u := by
  apply Lp.ext
  filter_upwards [(joint n L c h ∅).coe_onScalar u] with X hX
  simpa only [joint_apply,Finset.prod_empty,one_mul] using hX

theorem joint_low_counts : ∃ C B E G : ℝ, 0<C ∧ 0<B ∧ 0<E ∧ 0<G ∧
    ∀ (S : Type) [DecidableEq S] (n : ℕ) (L : Length) (r : ℝ),
      0 < r → r ≤ 1/100 → 0<n → 1/100 ≤ L.val →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (c : S → Torus L), (∀ z v, z≠v → 1 ≤ dist (c z) (c v)) →
    ∀ (k m : ℕ) (h : ℝ), 0<h → 2*h ≤ k → C*B*(k+m)*r^3 ≤ 1/4 →
      0 < m*(energy g/(n:ℝ)-C*(E+B*(k+m)*r)) →
    ∀ A : Finset S, ‖(joint n L c h A).onScalar g.1‖^2 ≤
      (G/(h*(m*(energy g/(n:ℝ)-C*(E+B*(k+m)*r)))))^A.card := by
  obtain ⟨C,B,E,hC,hB,hE,hdef⟩ := physical_deficiency
  obtain ⟨M,hM,hb⟩ := exists_transition_bound
  let G : ℝ := 2*M^2*(3*(4*(24*Real.pi^2*M^2/(8*(1/100))^2)))
  have hG : 0<G := by dsimp [G]; positivity
  refine ⟨C,B,E,G,hC,hB,hE,hG,?_⟩
  intro S _ n L r hr hrd hn hL g hg c hc k m h hh hk hsmall hgap A
  let γ : ℝ := m*(energy g/(n:ℝ)-C*(E+B*(k+m)*r))
  have hγ : 0<γ := hgap
  let q : ℝ := G/(h*γ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  change ‖(joint n L c h A).onScalar g.1‖^2 ≤ q^A.card
  apply finset_erase_recursion (fun A ↦ ‖(joint n L c h A).onScalar g.1‖^2) q hq
  · rw [joint_empty_onScalar,hg.2.2.1]
    norm_num
  · intro A hA
    let : Nonempty A := hA.to_subtype
    let u := (joint n L c h A).onJet g
    have hu : u∈dirichletDomain n L r := (joint n L c h A).onJet_mem_domain hg.1
    have hs : ∀ᵐ X ∂volume, u.1 X≠0 → ∀ z : A, count L (1/100) (c z) X ≤ k := by
      filter_upwards [joint_support hh c A g.1] with X hX huX z
      exact (hX huX z z.property).trans hk
    have hp := hdef A n L r hr hrd hn hL g hg (fun z : A ↦ c z)
      (fun z v hzv ↦ hc z v (fun he ↦ hzv (Subtype.ext he))) k m hsmall u hu hs
    have hm := hg.smooth_multiplier_identity (joint n L c h A) (joint_real n L c h A)
    have hbnd := joint_gradient_norm_le hh hM.le hb c hc A g.1
    have hpen : γ*((A.card : ℝ)*‖(joint n L c h A).onScalar g.1‖^2) ≤
        (G/h)*∑ s∈A, ‖(joint n L c h (A.erase s)).onScalar g.1‖^2 := by
      calc
        _ = m*Fintype.card A*(energy g/(n:ℝ)-C*(E+B*(k+m)*r))*‖u.1‖^2 := by
          simp only [Fintype.card_coe,u,SmoothMultiplier.onJet_fst,γ]
          ring
        _ ≤ energy u-energy g*‖u.1‖^2 := hp
        _ = ∑ p : Direction n, ‖(joint n L c h A).derivativeScalar p g.1‖^2 := hm
        _ ≤ _ := hbnd
    have hdiv := (le_div_iff₀ hγ).mpr (by simpa only [mul_comm γ] using hpen)
    have he : ((G/h)*∑ s∈A, ‖(joint n L c h (A.erase s)).onScalar g.1‖^2)/γ =
        q*∑ s∈A, ‖(joint n L c h (A.erase s)).onScalar g.1‖^2 := by
      dsimp [q]
      field_simp
    simpa only [he] using hdiv

end
end HardSphere.CellOrbital

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GroundPositionLaw
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

namespace CellOrbital

lemma joint_one {S : Type*} [DecidableEq S] {n : ℕ} {L : Length} {h : ℝ} (hh : 0<h)
    (c : S → Torus L) (A : Finset S) (X : Configuration n L)
    (hX : ∀ s∈A, count L (1/100) (c s) X ≤ h) : (joint n L c h A).toFun X=1 := by
  rw [joint_apply]
  apply Finset.prod_eq_one
  intro s hs
  rw [profile_one hh (hX s hs),Complex.ofReal_one]

lemma groundPositionLaw_le_joint {S : Type*} [DecidableEq S] {n : ℕ} {L : Length} {h : ℝ}
    (hh : 0<h) (c : S → Torus L) (A : Finset S) (u : Jet n L)
    (T : Set (Configuration n L)) (hT : MeasurableSet T)
    (hcount : ∀ X∈T, ∀ s∈A, count L (1/100) (c s) X ≤ h) :
    groundPositionLaw n L u T ≤ ENNReal.ofReal (‖(joint n L c h A).onScalar u.1‖^2) := by
  rw [groundPositionLaw,withDensity_apply _ hT,
    ← ofReal_integral_eq_lintegral_ofReal
      ((Lp.memLp u.1).integrable_norm_pow (by norm_num : (2:ℕ)≠0)).integrableOn
      (Eventually.of_forall fun X ↦ sq_nonneg ‖u.1 X‖),IndicatorStrong.norm_sq_integral]
  apply ENNReal.ofReal_le_ofReal
  have hi : Integrable (fun X ↦ ‖((joint n L c h A).onScalar u.1) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  calc
    _ = ∫ X in T, ‖((joint n L c h A).onScalar u.1) X‖^2 ∂volume := by
      apply setIntegral_congr_ae hT
      filter_upwards [(joint n L c h A).coe_onScalar u.1] with X hX hXT
      rw [hX,joint_one hh c A X (hcount X hXT),one_mul]
    _ ≤ _ := setIntegral_le_integral hi (ae_of_all _ fun X ↦ sq_nonneg _)

end CellOrbital
end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_CenteredCell
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter
noncomputable section

lemma centered_rep_abs (L : Length) (x : AddCircle L.val) :
    |((AddCircle.equivIco L.val (-L.val/2)) x).val|=‖x‖ := by
  let t := (AddCircle.equivIco L.val (-L.val/2)) x
  have ht : |t.val| ≤ |L.val|/2 := by
    rw [abs_of_pos L.property,abs_le]
    constructor <;> linarith [t.property.1,t.property.2]
  have he := (AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr ht
  rw [AddCircle.coe_equivIco] at he
  exact he.symm

lemma chi_support_centeredCell (L : Length) (c x : Torus L) (hx : chi L (1/100) c x≠0) :
    x∈centeredCell L c := by
  have hnb : bump L (8*(1/100)) c x≠0 := by
    intro he
    apply hx
    simp only [chi,he,zero_pow (by norm_num : (2:ℕ)≠0)]
  have hb := bump_support (by norm_num : (0:ℝ)<8*(1/100)) c (subset_closure hnb)
  have hb' := TightCutoff.near_subset_box L.val (by norm_num : (0:ℝ)<8*(1/100)) c hb
  intro j
  have hj : dist (x j) (c j) ≤ 2*(8*(1/100)) := Set.mem_univ_pi.mp hb' j
  have ht : |((AddCircle.equivIco L.val (-L.val/2)) (x j-c j)).val| ≤ 2*(8*(1/100)) := by
    rw [centered_rep_abs,← dist_eq_norm]
    exact hj
  obtain ⟨hl,hu⟩ := abs_le.mp ht
  constructor <;> linarith

lemma centeredCount_measurable {n : ℕ} (L : Length) (c : Torus L) :
    Measurable (centeredCount (n:=n) L c) := by
  classical
  unfold centeredCount
  simp_rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite ((centeredCell_measurable L c).preimage (measurable_pi_apply i))
    measurable_const measurable_const

lemma count_le_centeredCount {n : ℕ} (L : Length) (c : Torus L) (X : Configuration n L) :
    count L (1/100) c X ≤ (centeredCount L c X:ℝ) := by
  classical
  change (∑ i, chi L (1/100) c (X i)) ≤ ((Finset.univ.filter (fun i ↦ X i∈centeredCell L c)).card:ℝ)
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : X i∈centeredCell L c
  · simpa only [ite_eq_left hi] using (chi_bounds L (1/100) c (X i)).2
  · rw [ite_eq_right hi]
    have hz : chi L (1/100) c (X i)=0 := by
      by_contra hh
      exact hi (chi_support_centeredCell L c (X i) hh)
    exact hz.le

end
end HardSphere.CellOrbital

namespace HardSphere.CellOrbital
open MeasureTheory Set Filter
noncomputable section

lemma fin_circle_dist {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) {v w : Fin K} (hvw : v≠w) :
    1 ≤ dist ((v:ℝ) : AddCircle L.val) ((w:ℝ) : AddCircle L.val) := by
  have hi (v : Fin K) : (v:ℝ)∈Ico (0:ℝ) (0+L.val) := by
    constructor
    · positivity
    · simpa only [zero_add,hL] using (show (v:ℝ)<(K:ℝ) by exact_mod_cast v.isLt)
  have hne : ((v:ℝ):AddCircle L.val)≠((w:ℝ):AddCircle L.val) := by
    intro he
    have he' := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hi v) (hi w)).mp he
    exact hvw (Fin.ext (by exact_mod_cast he'))
  let z : ℤ := (v.val:ℤ)-(w.val:ℤ)-round (L.val⁻¹*((v:ℝ)-(w:ℝ)))*(K:ℤ)
  have hd : dist ((v:ℝ):AddCircle L.val) ((w:ℝ):AddCircle L.val)=|(z:ℝ)| := by
    rw [dist_eq_norm,← QuotientAddGroup.mk_sub,AddCircle.norm_eq]
    dsimp [z]
    push_cast
    rw [hL]
  have hz : z≠0 := by
    intro hz
    apply hne
    apply dist_eq_zero.mp
    rw [hd,hz,Int.cast_zero,abs_zero]
  have ha : (1:ℤ)≤|z| := by
    have hh : 0 < |z| := abs_pos.mpr hz
    omega
  rw [hd,← Int.cast_abs]
  exact_mod_cast ha

lemma gridCenter_separated {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) :
    ∀ z v : Fin 3 → Fin K, z≠v → 1 ≤ dist (gridCenter L z) (gridCenter L v) := by
  intro z v hzv
  obtain ⟨j,hj⟩ : ∃ j, z j≠v j := by
    by_contra hh
    push Not at hh
    exact hzv (funext hh)
  exact (fin_circle_dist hL hj).trans (dist_le_pi_dist (gridCenter L z) (gridCenter L v) j)

end
end HardSphere.CellOrbital

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_LowCountAbove
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.CellOrbital
theorem scaled_joint_low_counts_above (Amin : ℝ) : ∃ α₀ ell D₀ Q : ℝ,
    Amin≤α₀ ∧ 0<α₀ ∧ 0<ell ∧ 0<D₀ ∧ 0<Q ∧
    ∀ (S : Type) [DecidableEq S] (n : ℕ) (L : Length) (D α : ℝ),
      2≤n → 1 ≤ L.val → D=(n:ℝ)/L.val^3 → D₀ ≤ D →
      α₀/2 ≤ α → α ≤ 2*α₀ →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g →
    ∀ (c : S → Torus L), (∀ z v, z≠v → 1 ≤ dist (c z) (c v)) →
    ∀ A : Finset S, ‖(joint n L c (ell*D) A).onScalar g.1‖^2 ≤ (Q/D^2)^A.card := by
  obtain ⟨C,B,E,G,hC,hB,hE,hG,hjoint⟩ := joint_low_counts
  let b : ℝ := 1/(128*Real.sqrt 3)
  have hb : 0<b := by dsimp [b]; positivity
  let α₀ := max (max 1 Amin) (8*C*E/b)
  have hα₀ : 0<α₀ := zero_lt_one.trans_le ((le_max_left 1 Amin).trans (le_max_left _ _))
  have hCE : C*E ≤ b*α₀/8 := by
    have hh := (div_le_iff₀ hb).mp (le_max_right (max 1 Amin) (8*C*E/b))
    dsimp [α₀]
    nlinarith
  let ell := min 1 (b/(16*C*B))
  have hell : 0<ell := lt_min zero_lt_one (by positivity)
  have hCB : 16*C*B*ell ≤ b := by
    have hh := (le_div_iff₀ (by positivity : 0<16*C*B)).mp (min_le_right 1 (b/(16*C*B)))
    dsimp [ell]
    nlinarith
  let D₀ : ℝ := max (2/ell) (max (200*α₀) (max 1 (128*C*B*ell*α₀^3)))+1
  have hD₀ : 0<D₀ := by
    have hh : (2/ell) ≤ D₀-1 := by dsimp [D₀]; linarith [le_max_left (2/ell) (max (200*α₀) (max 1 (128*C*B*ell*α₀^3)))]
    have hh' : 0<2/ell := by positivity
    linarith
  let Q := 8*G/(ell^2*b*α₀)
  have hQ : 0<Q := by dsimp [Q]; positivity
  refine ⟨α₀,ell,D₀,Q,(le_max_right 1 Amin).trans (le_max_left _ _),hα₀,hell,hD₀,hQ,?_⟩
  intro S _ n L D α hn hL hDN hDD hαl hαu g hg c hc A
  have hD : 0<D := hD₀.trans_le hDD
  have hα : 0<α := (by positivity : 0<α₀/2).trans_le hαl
  have hD2 : 2/ell ≤ D := by
    have hh := le_max_left (2/ell) (max (200*α₀) (max 1 (128*C*B*ell*α₀^3)))
    dsimp [D₀] at hDD
    linarith
  have hDr : 200*α₀ ≤ D := by
    have hh := (le_max_left (200*α₀) (max 1 (128*C*B*ell*α₀^3))).trans
      (le_max_right (2/ell) (max (200*α₀) (max 1 (128*C*B*ell*α₀^3))))
    dsimp [D₀] at hDD
    linarith
  have hD1 : 1 ≤ D := by
    have hh := (le_max_left 1 (128*C*B*ell*α₀^3)).trans
      ((le_max_right (200*α₀) (max 1 (128*C*B*ell*α₀^3))).trans
        (le_max_right (2/ell) (max (200*α₀) (max 1 (128*C*B*ell*α₀^3)))))
    dsimp [D₀] at hDD
    linarith
  have hDS : 128*C*B*ell*α₀^3 ≤ D^2 := by
    have hh := (le_max_right 1 (128*C*B*ell*α₀^3)).trans
      ((le_max_right (200*α₀) (max 1 (128*C*B*ell*α₀^3))).trans
        (le_max_right (2/ell) (max (200*α₀) (max 1 (128*C*B*ell*α₀^3)))))
    dsimp [D₀] at hDD
    nlinarith
  have hh : 2 ≤ ell*D := by have ht := (div_le_iff₀ hell).mp hD2; nlinarith
  let k := ⌈2*(ell*D)⌉₊
  let m := ⌊ell*D⌋₊
  have hk : 2*(ell*D) ≤ (k:ℝ) := Nat.le_ceil _
  have hku : (k:ℝ) ≤ 2*(ell*D)+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hmu : (m:ℝ) ≤ ell*D := Nat.floor_le (by positivity)
  have hml : ell*D/2 ≤ (m:ℝ) := by
    have ht := Nat.lt_floor_add_one (ell*D)
    dsimp [m]
    linarith
  have hkm : (k:ℝ)+(m:ℝ) ≤ 4*ell*D := by linarith
  have hr : 0<α/D := by positivity
  have hrd : α/D ≤ 1/100 := (div_le_iff₀ hD).mpr (by linarith)
  have hcst : C*(E+B*((k:ℝ)+(m:ℝ))*(α/D)) ≤ b*α/2 := by
    have hcost : C*B*((k:ℝ)+(m:ℝ))*(α/D) ≤ 4*C*B*ell*α := by
      calc
        _ ≤ C*B*(4*ell*D)*(α/D) := by gcongr
        _ = _ := by field_simp
    have hCEa : C*E ≤ b*α/4 := by nlinarith only [hCE,mul_le_mul_of_nonneg_left hαl hb.le]
    have hCBa : 4*C*B*ell*α ≤ b*α/4 := by nlinarith only [mul_le_mul_of_nonneg_right hCB hα.le]
    nlinarith only [hcost,hCEa,hCBa]
  have hsmall : C*B*((k:ℝ)+(m:ℝ))*(α/D)^3 ≤ 1/4 := by
    calc
      _ ≤ C*B*(4*ell*D)*((2*α₀)/D)^3 := by gcongr
      _ = (32*C*B*ell*α₀^3)/D^2 := by field_simp; ring
      _ ≤ 1/4 := (div_le_iff₀ (sq_pos_of_pos hD)).mpr (by nlinarith only [hDS])
  have hel := hg.energy_per_particle_lower hr hn
  have haD : (α/D)*((n:ℝ)/L.val^3)=α := by rw [← hDN]; exact div_mul_cancel₀ _ hD.ne'
  rw [haD] at hel
  change b*α ≤ energy g/(n:ℝ) at hel
  let γ := (m:ℝ)*(energy g/(n:ℝ)-C*(E+B*((k:ℝ)+(m:ℝ))*(α/D)))
  have hgap : b*α/2 ≤ energy g/(n:ℝ)-C*(E+B*((k:ℝ)+(m:ℝ))*(α/D)) := by linarith
  have hγlow : ell*D*b*α₀/8 ≤ γ := by
    calc
      _ ≤ (ell*D/2)*(b*α/2) := by
        nlinarith only [mul_le_mul_of_nonneg_left hαl (by positivity : 0 ≤ ell*D*b/4)]
      _ ≤ _ := mul_le_mul hml hgap (by positivity) (by positivity)
  have hγ : 0<γ := (by positivity : 0<ell*D*b*α₀/8).trans_le hγlow
  have hj := hjoint S n L (α/D) hr hrd (by omega) (by linarith) g hg c hc k m (ell*D)
    (by positivity) hk hsmall hγ A
  apply hj.trans
  apply pow_le_pow_left₀ (by positivity)
  change G/((ell*D)*γ) ≤ Q/D^2
  have hd : ell^2*D^2*b*α₀/8 ≤ (ell*D)*γ := by
    nlinarith only [mul_le_mul_of_nonneg_left hγlow (by positivity : 0 ≤ ell*D)]
  calc
    _ ≤ G/(ell^2*D^2*b*α₀/8) := div_le_div_of_nonneg_left hG.le (by positivity) hd
    _ = _ := by dsimp [Q]; field_simp

end HardSphere.CellOrbital

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_GridLowStationary
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.CellOrbital
open Wiener

theorem grid_stationary_low_above_oai (Amin : ℝ) : ∃ α₀ ell D₀ Q : ℝ,
    Amin≤α₀ ∧ 0<α₀ ∧ 0<ell ∧ 0<D₀ ∧ 0<Q ∧
    ∀ (K n : ℕ) [Nontrivial (Fin n)] (L : Length) (D α : ℝ),
      1≤K → L.val=(K:ℝ) → D=(n:ℝ)/L.val^3 → D₀≤D → α₀/2≤α → α≤2*α₀ →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g →
    ∀ (T : ℝ), 0≤T → ∀ (q : Time) (A : Finset (Fin 3→Fin K)),
      groundPathLaw n L (α/D) T g {ω | ∀v∈A,(centeredCount L (gridCenter L v) (ω q):ℝ)<ell*D}≤
        ENNReal.ofReal ((Q/D^2)^A.card) := by
  obtain ⟨α₀,ell,D₀,Q,hA,hα,hell,hD₀,hQ,hs⟩ := scaled_joint_low_counts_above Amin
  refine ⟨α₀,ell,D₀,Q,hA,hα,hell,hD₀,hQ,?_⟩
  intro K n inst L D α hK hLK hDN hDD hαl hαu g hg T hT q A
  have hL : 1≤L.val := by rw [hLK]; exact_mod_cast hK
  have hn : 2≤n := Nat.succ_le_of_lt (by simpa only [Fintype.card_fin] using (Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial (Fin n))))
  have hset : MeasurableSet {X : Configuration n L | ∀v∈A,(centeredCount L (gridCenter L v) X:ℝ)<ell*D} := by
    simpa only [Set.ofPred_forall, Function.comp_def] using MeasurableSet.iInter (fun site ↦
      MeasurableSet.iInter (fun _ : site∈A ↦ measurableSet_lt
        ((measurable_of_countable (fun count : ℕ ↦ (count:ℝ))).comp
          (centeredCount_measurable L (gridCenter L site))) measurable_const))
  have hm := (hg.groundPathLaw_marginal T hT q).measure_preimage hset.nullMeasurableSet
  change groundPathLaw n L (α/D) T g ((fun ω ↦ ω q) ⁻¹' {X | ∀v∈A,(centeredCount L (gridCenter L v) X:ℝ)<ell*D})≤_
  rw [hm]
  apply (groundPositionLaw_le_joint (mul_pos hell (hD₀.trans_le hDD)) (gridCenter L) A g _ hset ?_).trans
  · exact ENNReal.ofReal_le_ofReal (hs (Fin 3→Fin K) n L D α hn hL hDN hDD hαl hαu g hg
      (gridCenter L) (gridCenter_separated hLK) A)
  · intro X hX v hv
    exact (count_le_centeredCount L (gridCenter L v) X).trans (hX v hv).le

end HardSphere.CellOrbital

end
end

end

end OAI
end

theorem solution : type_of% @OAI.HardSphere.CellOrbital.grid_stationary_low_above_oai := @OAI.HardSphere.CellOrbital.grid_stationary_low_above_oai
