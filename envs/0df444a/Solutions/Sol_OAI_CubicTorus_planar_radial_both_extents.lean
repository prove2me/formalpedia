-- Prove2me | solution 1 for OAI.CubicTorus.planar_radial_both_extents
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:39:10.553143+00:00
-- url     : https://prove2.me/submissions/d101885b-3fec-4f1a-a2d3-b560c2ab1406

import Mathlib
import Definitions.Def_OAIQ079A000
import Definitions.Def_OAIQ079A001

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVOneDimensionalHat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma primitive_contDiff {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ ∫ u in (0 : ℝ)..t, b u) := by
  have hd (t : ℝ) := intervalIntegral.integral_hasDerivAt_right
    (hb.continuous.intervalIntegrable 0 t) (hb.continuous.stronglyMeasurableAtFilter volume _)
    hb.continuous.continuousAt
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t ↦ (hd t).differentiableAt,?_⟩
  simpa only [funext (fun t ↦ (hd t).deriv)] using hb

lemma intervalSmoothHat_contDiff {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (a c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (intervalSmoothHat b a c) :=
  ((primitive_contDiff hb).comp (contDiff_id.sub contDiff_const)).sub
    ((primitive_contDiff hb).comp (contDiff_id.sub contDiff_const))

lemma intervalSmoothHat_hasDerivAt {b : ℝ → ℝ} (hb : Continuous b)
    (a c t : ℝ) : HasDerivAt (intervalSmoothHat b a c) (b (t-a)-b (t-c)) t := by
  have hd (x : ℝ) := intervalIntegral.integral_hasDerivAt_right
    (hb.intervalIntegrable 0 x) (hb.stronglyMeasurableAtFilter volume _) hb.continuousAt
  change HasDerivAt (fun x : ℝ ↦ (∫ u in (0 : ℝ)..x-a, b u) -
    ∫ u in (0 : ℝ)..x-c, b u) _ _
  simpa only [Function.comp_def,mul_one,id_eq,Pi.sub_def] using
    ((hd (t-a)).comp t ((hasDerivAt_id t).sub_const a)).sub
      ((hd (t-c)).comp t ((hasDerivAt_id t).sub_const c))

lemma intervalSmoothHat_eq_integral {b : ℝ → ℝ} (hb : Continuous b)
    (a c t : ℝ) : intervalSmoothHat b a c t = ∫ u in t-c..t-a, b u := by
  rw [intervalSmoothHat]
  have hh := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (hb.intervalIntegrable 0 (t-c)) (hb.intervalIntegrable (t-c) (t-a))
  linarith

lemma intervalSmoothHat_nonneg {b : ℝ → ℝ} (hb : Continuous b)
    (hb0 : ∀ t, 0 ≤ b t) {a c : ℝ} (hac : a ≤ c) (t : ℝ) :
    0 ≤ intervalSmoothHat b a c t := by
  rw [intervalSmoothHat_eq_integral hb]
  exact intervalIntegral.integral_nonneg (by linarith) (fun _ _ ↦ hb0 _)

lemma intervalSmoothHat_le_one {b : ℝ → ℝ} (hb : Continuous b)
    (hbi : Integrable b volume) (hb0 : ∀ t, 0 ≤ b t) (hb1 : ∫ t, b t = 1)
    {a c : ℝ} (hac : a ≤ c) (t : ℝ) : intervalSmoothHat b a c t ≤ 1 := by
  rw [intervalSmoothHat_eq_integral hb,intervalIntegral.integral_of_le (by linarith)]
  rw [← hb1]
  exact setIntegral_le_integral hbi (ae_of_all _ hb0)

lemma intervalSmoothHat_support {b : ℝ → ℝ} (hb : Continuous b)
    {r a c : ℝ} (hs : tsupport b ⊆ Icc (-r) r) (hac : a ≤ c) :
    tsupport (intervalSmoothHat b a c) ⊆ Icc (a-r) (c+r) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hh
  apply ht
  rw [intervalSmoothHat_eq_integral hb]
  apply intervalIntegral.integral_zero_ae
  apply ae_of_all
  intro u hu
  have htc : t-c ≤ t-a := by linarith
  rw [uIoc_of_le htc] at hu
  apply image_eq_zero_of_notMem_tsupport
  intro hub
  have hur := hs hub
  simp only [mem_Icc,not_and_or,not_le] at hh
  rcases hh with hl|hr
  · linarith [hu.2,hur.1]
  · linarith [hu.1,hur.2]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CirclePeriodize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_periodic_lift {f : ℝ → ℝ} (hp : Function.Periodic f 1)
    (hf : Continuous f) : Continuous hp.lift := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
  exact hf

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma finite_integer_support_near {f : ℝ → ℝ} (hf : HasCompactSupport f) (a : ℝ) :
    ∃ s : Finset ℤ,∀ x∈Metric.ball a 1,∀ n∉s,f (x+n)=0 := by
  classical
  obtain ⟨R,_,hR⟩ := hf.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R+|a|+1)
  refine ⟨Finset.Icc (-(N : ℤ)) N,?_⟩
  intro x hx n hn
  by_contra h
  have hb := hR _ (subset_tsupport f h)
  have hx' : |x-a|<1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hx
  have ha : |x|≤|a|+1 := by
    have hh := abs_add_le (x-a) a
    rw [sub_add_cancel] at hh
    linarith
  have hn' : |(n : ℝ)|<N := by
    have hh := norm_sub_le (x+n) x
    simp only [Real.norm_eq_abs] at hh
    rw [add_sub_cancel_left] at hh
    rw [Real.norm_eq_abs] at hb
    linarith
  apply hn
  rw [Finset.mem_Icc]
  constructor
  · exact_mod_cast (abs_le.mp hn'.le).1
  · exact_mod_cast (abs_le.mp hn'.le).2

lemma circlePeriodize_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : HasCompactSupport f) : ContDiff ℝ (⊤ : ℕ∞) (circlePeriodize f) := by
  rw [contDiff_iff_contDiffAt]
  intro a
  obtain ⟨s,hs⟩ := finite_integer_support_near hs a
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ ∑ n∈s,f (x+n)) :=
    ContDiff.sum fun n _ ↦ hf.comp (contDiff_id.add contDiff_const)
  apply hc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds a (by norm_num : (0 : ℝ)<1)] with x hx
  exact tsum_eq_sum (hs x hx)

lemma circlePeriodize_eventuallyEq {f : ℝ → ℝ} (hc : HasCompactSupport f)
    {a : ℝ} (hs : tsupport f ⊆ Ioo (a-1/2) (a+1/2))
    {x : ℝ} (hx : x∈Icc (a-1/2) (a+1/2)) : circlePeriodize f =ᶠ[𝓝 x] f := by
  classical
  obtain ⟨s,hlocal⟩ := finite_integer_support_near hc x
  have hz (n : ℤ) (hn : n≠0) : ∀ᶠ y in 𝓝 x,f (y+n)=0 := by
    have hnot : x+n∉tsupport f := by
      intro h
      have hh := hs h
      have hlo : (-1 : ℝ)<n := by linarith [hx.2,hh.1]
      have hhi : (n : ℝ)<1 := by linarith [hx.1,hh.2]
      have hlo' : (-1 : ℤ)<n := by exact_mod_cast hlo
      have hhi' : n<1 := by exact_mod_cast hhi
      omega
    exact (notMem_tsupport_iff_eventuallyEq.mp hnot).comp_tendsto
      (continuous_id.add continuous_const).continuousAt
  have hfin : ∀ᶠ y in 𝓝 x,∀ n∈s,n≠0 → f (y+n)=0 := by
    apply (eventually_all_finset s).mpr
    intro n _
    by_cases hn : n=0
    · exact Eventually.of_forall fun _ h ↦ False.elim (h hn)
    · exact (hz n hn).mono fun _ h _ ↦ h
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ)<1),hfin] with y hy hz
  unfold circlePeriodize
  rw [tsum_eq_single (0 : ℤ)]
  · simp
  · intro n hn
    by_cases hs : n∈s
    · exact hz n hs hn
    · exact hlocal y hy n hs

lemma circlePeriodize_unit_bounds {f : ℝ → ℝ} {a : ℝ}
    (hs : tsupport f ⊆ Ioo (a-1/2) (a+1/2))
    (hb : ∀ x,0≤f x ∧ f x≤1) (x : ℝ) :
    0 ≤ circlePeriodize f x ∧ circlePeriodize f x≤1 := by
  classical
  by_cases hn : ∃ n : ℤ,f (x+n)≠0
  · obtain ⟨n,hn⟩ := hn
    have huniq (m : ℤ) (hm : m≠n) : f (x+m)=0 := by
      by_contra hm'
      have h1 := hs (subset_tsupport f hn)
      have h2 := hs (subset_tsupport f hm')
      have hlo : (-1 : ℝ)<(m-n : ℤ) := by push_cast; linarith [h1.2,h2.1]
      have hhi : ((m-n : ℤ) : ℝ)<1 := by push_cast; linarith [h1.1,h2.2]
      have hlo' : (-1 : ℤ) < m-n := by exact_mod_cast hlo
      have hhi' : m-n<1 := by exact_mod_cast hhi
      omega
    rw [circlePeriodize,tsum_eq_single n huniq]
    exact hb _
  · push Not at hn
    unfold circlePeriodize
    simp only [hn,tsum_zero,le_refl,zero_le_one,and_self]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialSectionCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circlePeriodize_integral_short {f : ℝ → ℝ}
    (hc : HasCompactSupport f) {d : ℝ}
    (hs : tsupport f ⊆ Ioo (d-1/2) (d+1/2)) :
    (∫ t : AxisCircle,(circlePeriodize_periodic f).lift t)=∫ t : ℝ,f t := by
  rw [←AddCircle.intervalIntegral_preimage (1 : ℝ) (d-1/2),show d-1/2+1=d+1/2 by ring]
  calc
    _=∫ t in (d-1/2)..d+1/2,f t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact (circlePeriodize_eventuallyEq hc hs (by
        simpa only [uIcc_of_le (show d-1/2≤d+1/2 by linarith)] using ht)).eq_of_nhds
    _=∫ t : ℝ,f t := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      exact image_eq_zero_of_notMem_tsupport (fun hh ↦ ht ⟨(hs hh).1,(hs hh).2.le⟩)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_open_fiber_collar {A : Set TransverseProduct} (hA : IsOpen A)
    (j : Fin 2) (a : ℝ)
    (ha : ∀ y : TransverseProduct,y j=(a : AxisCircle) → y∈A) :
    ∃ ε : ℝ,0<ε ∧ ∀ t : ℝ,|t-a|<ε → ∀ y : TransverseProduct,y j=(t : AxisCircle) → y∈A := by
  have hc : IsCompact Aᶜ := hA.isClosed_compl.isCompact
  have hj : Continuous (Function.eval j : TransverseProduct → AxisCircle) := continuous_apply j
  have ho : IsOpen ((Function.eval j '' Aᶜ)ᶜ : Set AxisCircle) := (hc.image hj).isClosed.isOpen_compl
  have hm : (a : AxisCircle)∈((Function.eval j '' Aᶜ)ᶜ : Set AxisCircle) := by
    rintro ⟨y,hy,he⟩
    exact hy (ha y he)
  have hpre := ho.preimage (AddCircle.continuous_mk' (1 : ℝ))
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hpre a hm
  refine ⟨ε,hε,fun t ht y hy ↦ ?_⟩
  have hh := hball (show t∈Metric.ball a ε from by simpa only [Metric.mem_ball,Real.dist_eq] using ht)
  by_contra hny
  exact hh ⟨y,hny,hy⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planarProductField_admissible {σ a b : ℝ → ℝ}
    (hσ : ContDiff ℝ (⊤ : ℕ∞) σ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (pσ : Function.Periodic σ 1) (pa : Function.Periodic a 1) (pb : Function.Periodic b 1)
    (hσb : ∀ x,|σ x|≤1) (hab : ∀ y,(a y)^2+(b y)^2≤1) :
    PlanarAdmissibleField (planarProductField σ a b) := by
  have hx := (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).contDiff (n := (⊤ : ℕ∞))
  have hy := (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).contDiff (n := (⊤ : ℕ∞))
  refine ⟨((hσ.comp hx).mul (ha.comp hy)).smul contDiff_const |>.add
    ((hb.comp hy).smul contDiff_const),?_,?_⟩
  · intro n y
    unfold planarProductField
    simp only [PiLp.add_apply]
    have hs := pσ.int_mul (n 0) (y 0)
    have ha := pa.int_mul (n 1) (y 1)
    have hb := pb.int_mul (n 1) (y 1)
    simp only [mul_one] at hs ha hb
    rw [hs,ha,hb]
  · intro y
    have hs : (σ (y 0))^2≤1 := by nlinarith [sq_abs (σ (y 0)),hσb (y 0),abs_nonneg (σ (y 0))]
    have hn : ‖planarProductField σ a b y‖^2≤1 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [Fin.sum_univ_two,planarProductField,PiLp.add_apply,PiLp.smul_apply,
        PiLp.single_apply,Fin.isValue,ite_true,smul_eq_mul,
        mul_one,Fin.reduceEq,ite_false,mul_zero,add_zero,zero_add,Real.norm_eq_abs,sq_abs]
      nlinarith [hab (y 1),mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg (a (y 1)))]
    nlinarith [norm_nonneg (planarProductField σ a b y)]

lemma planeDivergence_planarProductField {σ a b : ℝ → ℝ}
    (hσ : Differentiable ℝ σ) (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (y : Plane) : planeDivergence (planarProductField σ a b) y=
      deriv σ (y 0)*a (y 1)+deriv b (y 1) := by
  have hx := (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).hasFDerivAt (x := y)
  have hy := (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).hasFDerivAt (x := y)
  have hd := (((hσ (y 0)).hasDerivAt.comp_hasFDerivAt y hx).mul
    ((ha (y 1)).hasDerivAt.comp_hasFDerivAt y hy)).smul_const (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
  have he := ((hb (y 1)).hasDerivAt.comp_hasFDerivAt y hy).smul_const (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
  have hf := hd.add he
  change HasFDerivAt (planarProductField σ a b) _ y at hf
  rw [planeDivergence,hf.fderiv]
  simp [ContinuousLinearMap.smulRight_apply,mul_comm]

theorem planarTorusPerimeter_ge_product_flux (A : Set TransverseProduct)
    {σ a b : ℝ → ℝ}
    (hσ : ContDiff ℝ (⊤ : ℕ∞) σ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (pσ : Function.Periodic σ 1) (pa : Function.Periodic a 1) (pb : Function.Periodic b 1)
    (hσb : ∀ x,|σ x|≤1) (hab : ∀ y,(a y)^2+(b y)^2≤1) :
    ENNReal.ofReal (∫ y in A,(real_periodic_deriv pσ).lift (y 0)*pa.lift (y 1)+
      (real_periodic_deriv pb).lift (y 1))≤planarTorusPerimeter A := by
  have he (y : TransverseProduct) :
      planeDivergence (planarProductField σ a b) (planarRepresentative y)=
        (real_periodic_deriv pσ).lift (y 0)*pa.lift (y 1)+
          (real_periodic_deriv pb).lift (y 1) := by
    rw [planeDivergence_planarProductField (hσ.differentiable (by simp))
      (ha.differentiable (by simp)) (hb.differentiable (by simp))]
    have e0 := (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (y 0)
    have e1 := (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (y 1)
    change (((AddCircle.equivIco (1 : ℝ) 0) (y 0) : ℝ) : AxisCircle)=y 0 at e0
    change (((AddCircle.equivIco (1 : ℝ) 0) (y 1) : ℝ) : AxisCircle)=y 1 at e1
    conv_rhs => rw [←e0,←e1]
    rfl
  rw [←show (∫ y in A,planeDivergence (planarProductField σ a b) (planarRepresentative y))=
      ∫ y in A,(real_periodic_deriv pσ).lift (y 0)*pa.lift (y 1)+
        (real_periodic_deriv pb).lift (y 1) by apply integral_congr_ae; exact Filter.Eventually.of_forall he]
  exact le_iSup_of_le (planarProductField σ a b)
    (le_iSup_of_le (planarProductField_admissible hσ ha hb pσ pa pb hσb hab) le_rfl)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma transverse_integral_mul (f g : AxisCircle → ℝ) :
    (∫ y : TransverseProduct,f (y 0)*g (y 1))=(∫ t,f t)*(∫ t,g t) := by
  simpa only [Fin.prod_univ_two,Fin.isValue,Fin.reduceFinMk,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.head_cons] using
    integral_fintype_prod_volume_eq_prod (E := fun _ : Fin 2 ↦ AxisCircle) ![f,g]

theorem planarTorusPerimeter_ge_weighted_bump_strips
    {A : Set TransverseProduct} (hA : MeasurableSet A)
    {T : Set AxisCircle} (hT : MeasurableSet T)
    {u v : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (pu : Function.Periodic u 1) (pv : Function.Periodic v 1)
    (hu0 : ∀ y,0≤u y) (huv : ∀ y,(u y)^2+(v y)^2≤1)
    {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbi : Integrable b volume)
    (hb0 : ∀ t,0≤b t) (hb1 : ∫ t,b t=1)
    {r a c : ℝ} (hs : tsupport b ⊆ Icc (-r) r) (hac : a ≤ c)
    (hshort : c-a+2*r<1)
    (hin : ∀ t : ℝ,b (t-a)≠0 → ∀ y : TransverseProduct,y 0=(t : AxisCircle) → y 1∈T → y∈A)
    (hout : ∀ t : ℝ,b (t-c)≠0 → ∀ y : TransverseProduct,y 0=(t : AxisCircle) → y∉A)
    {k : ℝ} (hk : ∀ y∈A,(real_periodic_deriv pv).lift (y 1)=k) :
    ENNReal.ofReal (k*volume.real A+2*(∫ t in T,pu.lift t))≤planarTorusPerimeter A := by
  let H := intervalSmoothHat b a c
  let d := (a+c)/2
  have hHs : tsupport H ⊆ Ioo (d-1/2) (d+1/2) := by
    apply (intervalSmoothHat_support hb.continuous hs hac).trans
    intro x hx
    dsimp only [d]
    constructor <;> linarith [hx.1,hx.2]
  have hHc : HasCompactSupport H :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport H)
      (intervalSmoothHat_support hb.continuous hs hac)
  let B : ℝ → ℝ := fun t ↦ b (t-a)
  have hBs : tsupport B ⊆ Ioo (d-1/2) (d+1/2) := by
    intro t ht
    have hh := hs (tsupport_comp_subset_preimage b (continuous_id.sub continuous_const) ht)
    change -r≤t-a ∧ t-a ≤ r at hh
    dsimp only [d]
    constructor <;> linarith [hh.1,hh.2]
  have hBc : HasCompactSupport B :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport B)
      (fun _ ht ↦ ⟨(hBs ht).1.le,(hBs ht).2.le⟩)
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := hb.comp (contDiff_id.sub contDiff_const)
  let ψ : ℝ → ℝ := fun t ↦ 2*circlePeriodize H t-1
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (contDiff_const.mul (circlePeriodize_contDiff (intervalSmoothHat_contDiff hb a c) hHc)).sub contDiff_const
  have hp : Function.Periodic ψ 1 := fun t ↦ by
    dsimp only [ψ]
    rw [circlePeriodize_periodic H t]
  have hbψ (t : ℝ) : |ψ t|≤1 := by
    have hh := circlePeriodize_unit_bounds hHs (fun t ↦
      ⟨intervalSmoothHat_nonneg hb.continuous hb0 hac t,
        intervalSmoothHat_le_one hb.continuous hbi hb0 hb1 hac t⟩) t
    apply abs_le.mpr
    dsimp only [ψ]
    constructor <;> linarith [hh.1,hh.2]
  have hd (t : ℝ) (ht : t∈Icc (d-1/2) (d+1/2)) : deriv ψ t=2*(b (t-a)-b (t-c)) := by
    have he := circlePeriodize_eventuallyEq hHc hHs ht
    dsimp only [ψ]
    rw [deriv_sub_const,deriv_const_mul 2
      ((circlePeriodize_contDiff (intervalSmoothHat_contDiff hb a c) hHc).differentiable (by simp) t),
      he.deriv_eq,(intervalSmoothHat_hasDerivAt hb.continuous a c t).deriv]
  let β : AxisCircle → ℝ := (circlePeriodize_periodic B).lift
  have hβ : Continuous β := continuous_periodic_lift _ (circlePeriodize_contDiff hB hBc).continuous
  have hβi : (∫ t,β t)=1 := by
    rw [circlePeriodize_integral_short hBc hBs]
    exact (integral_sub_right_eq_self b a).trans hb1
  have huC : Continuous (pu.lift : AxisCircle → ℝ) := continuous_periodic_lift _ hu.continuous
  have hvC : Continuous ((real_periodic_deriv pv).lift : AxisCircle → ℝ) :=
    continuous_periodic_lift _ (hv.continuous_deriv (by simp))
  have hσC : Continuous ((real_periodic_deriv hp).lift : AxisCircle → ℝ) :=
    continuous_periodic_lift _ (hψ.continuous_deriv (by simp))
  have huL (t : AxisCircle) : 0≤pu.lift t := by
    induction t using Quotient.inductionOn with | h t => exact hu0 t
  have he (y : TransverseProduct) :
      2*β (y 0)*(T.indicator pu.lift (y 1))≤
        A.indicator (fun y : TransverseProduct ↦ (real_periodic_deriv hp).lift (y 0)*pu.lift (y 1)) y := by
    let t : ℝ := ((AddCircle.equivIco (1 : ℝ) (d-1/2)) (y 0) : ℝ)
    have ht0 := ((AddCircle.equivIco (1 : ℝ) (d-1/2)) (y 0)).property
    have ht : t∈Icc (d-1/2) (d+1/2) := by
      change d-1/2≤t ∧ t<d-1/2+1 at ht0
      constructor <;> linarith [ht0.1,ht0.2]
    have hty : (t : AxisCircle)=y 0 := (AddCircle.equivIco (1 : ℝ) (d-1/2)).symm_apply_apply _
    have hBt : β (y 0)=b (t-a) := by
      rw [←hty]
      exact (circlePeriodize_eventuallyEq hBc hBs ht).eq_of_nhds
    rw [hBt]
    by_cases hy : y∈A
    · have hc0 : b (t-c)=0 := by
        by_contra hnc
        exact hout t hnc y hty.symm hy
      rw [indicator_of_mem hy]
      have hd' : (real_periodic_deriv hp).lift (y 0)=2*b (t-a) := by
        rw [←hty]
        change deriv ψ t=2*b (t-a)
        rw [hd t ht,hc0,sub_zero]
      rw [hd']
      by_cases hyT : y 1∈T
      · rw [indicator_of_mem hyT]
      · rw [indicator_of_notMem hyT,mul_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) (hb0 _)) (huL _)
    · rw [indicator_of_notMem hy]
      by_cases hyT : y 1∈T
      · have ha0 : b (t-a)=0 := by
          by_contra hna
          exact hy (hin t hna y hty.symm hyT)
        rw [ha0,mul_zero,zero_mul]
      · rw [indicator_of_notMem hyT,mul_zero]
  have hiR : Integrable (fun y : TransverseProduct ↦
      (real_periodic_deriv hp).lift (y 0)*pu.lift (y 1)) :=
    ((hσC.comp (continuous_apply 0)).mul (huC.comp (continuous_apply 1))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiL : Integrable (fun y : TransverseProduct ↦ 2*β (y 0)*T.indicator pu.lift (y 1)) := by
    have hbase : Integrable (fun y : TransverseProduct ↦ 2*β (y 0)*pu.lift (y 1)) :=
      ((continuous_const.mul (hβ.comp (continuous_apply 0))).mul (huC.comp (continuous_apply 1))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    apply (hbase.indicator (hT.preimage (measurable_pi_apply 1))).congr
    filter_upwards [] with y
    by_cases hy : y 1∈T <;> simp [hy]
  have hle := integral_mono hiL (hiR.indicator hA) he
  have hlow : (∫ y : TransverseProduct,2*β (y 0)*T.indicator pu.lift (y 1))=
      2*(∫ t in T,pu.lift t) := by
    simp_rw [mul_assoc]
    rw [integral_const_mul,transverse_integral_mul,hβi,one_mul,integral_indicator hT]
  rw [hlow,integral_indicator hA] at hle
  have hvI : Integrable (fun y : TransverseProduct ↦ (real_periodic_deriv pv).lift (y 1)) :=
    (hvC.comp (continuous_apply 1)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hflux := planarTorusPerimeter_ge_product_flux A hψ hu hv hp pu pv hbψ huv
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hflux
  rw [integral_add hiR.integrableOn hvI.integrableOn]
  have hev : (∫ y in A,(real_periodic_deriv pv).lift (y 1))=k*volume.real A := by
    calc
      _=∫ _ in A,k := setIntegral_congr_fun hA hk
      _=k*volume.real A := by simp [mul_comm,measureReal_def]
  rw [hev]
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_open_partial_fiber_collar {A : Set TransverseProduct} (hA : IsOpen A)
    {T : Set AxisCircle} (hT : IsCompact T) (a : ℝ)
    (ha : ∀ y : TransverseProduct,y 0=(a : AxisCircle) →y 1∈T →y∈A) :
    ∃ ε : ℝ,0<ε ∧ ∀ t : ℝ,|t-a|<ε →∀ y : TransverseProduct,y 0=(t : AxisCircle) →y 1∈T →y∈A := by
  have h1 : Continuous (Function.eval (1 : Fin 2) : TransverseProduct → AxisCircle) := continuous_apply 1
  have h0 : Continuous (Function.eval (0 : Fin 2) : TransverseProduct → AxisCircle) := continuous_apply 0
  have hc : IsCompact (Aᶜ∩(Function.eval (1 : Fin 2)) ⁻¹' T) :=
    (hA.isClosed_compl.inter (hT.isClosed.preimage h1)).isCompact
  have ho : IsOpen ((Function.eval (0 : Fin 2) '' (Aᶜ∩(Function.eval (1 : Fin 2)) ⁻¹' T))ᶜ : Set AxisCircle) :=
    (hc.image h0).isClosed.isOpen_compl
  have hm : (a : AxisCircle)∈((Function.eval (0 : Fin 2) '' (Aᶜ∩(Function.eval (1 : Fin 2)) ⁻¹' T))ᶜ : Set AxisCircle) := by
    rintro ⟨y,⟨hy,hyT⟩,he⟩
    exact hy (ha y he hyT)
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (ho.preimage (AddCircle.continuous_mk' (1 : ℝ))) a hm
  refine ⟨ε,hε,fun t ht y hy hyT ↦ ?_⟩
  have hh := hball (show t∈Metric.ball a ε from by simpa only [Metric.mem_ball,Real.dist_eq] using ht)
  by_contra hny
  exact hh ⟨y,⟨hny,hyT⟩,hy⟩

theorem planarTorusPerimeter_ge_corner_calibration
    {A : Set TransverseProduct} (hA : IsOpen A)
    {T : Set AxisCircle} (hT : IsCompact T)
    {u v : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (pu : Function.Periodic u 1) (pv : Function.Periodic v 1)
    (hu0 : ∀ y,0≤u y) (huv : ∀ y,(u y)^2+(v y)^2≤1)
    {a c : ℝ} (hac : a ≤ c) (hshort : c-a<1)
    (hin : ∀ y : TransverseProduct,y 0=(a : AxisCircle) →y 1∈T →y∈A)
    (hout : ∀ y : TransverseProduct,y 0=(c : AxisCircle) →y∉closure A)
    {k : ℝ} (hk : ∀ y∈A,(real_periodic_deriv pv).lift (y 1)=k) :
    ENNReal.ofReal (k*volume.real A+2*(∫ t in T,pu.lift t))≤planarTorusPerimeter A := by
  obtain ⟨ε,hε,hεA⟩ := planar_open_partial_fiber_collar hA hT a hin
  obtain ⟨δ,hδ,hδA⟩ := planar_open_fiber_collar isClosed_closure.isOpen_compl 0 c hout
  let r : ℝ := min (min ε δ) (1-(c-a))/4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : r<ε := by
    have hh := (min_le_left (min ε δ) (1-(c-a))).trans (min_le_left ε δ)
    dsimp only [r]; linarith
  have hrδ : r<δ := by
    have hh := (min_le_left (min ε δ) (1-(c-a))).trans (min_le_right ε δ)
    dsimp only [r]; linarith
  have hrc : c-a+2*r<1 := by
    have hh := min_le_right (min ε δ) (1-(c-a))
    dsimp only [r]; linarith
  let b : ContDiffBump (0 : ℝ) := ⟨r/2,r,half_pos hr,by linarith⟩
  apply planarTorusPerimeter_ge_weighted_bump_strips hA.measurableSet hT.measurableSet
    hu hv pu pv hu0 huv b.contDiff_normed b.integrable_normed (fun t ↦ b.nonneg_normed t)
    b.integral_normed (r := r) (a := a) (c := c) _ hac hrc _ _ hk
  · rw [b.tsupport_normed_eq,Real.closedBall_eq_Icc]
    simp only [sub_eq_add_neg,zero_add]
    exact Subset.rfl
  · intro t ht y hy hyT
    have hs : t-a∈Metric.ball (0 : ℝ) r := by
      rw [←b.support_normed_eq (μ := volume)]; exact ht
    have hab : |t-a| < r := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hs
    exact hεA t (hab.trans hrε) y hy hyT
  · intro t ht y hy hya
    have hs : t-c∈Metric.ball (0 : ℝ) r := by
      rw [←b.support_normed_eq (μ := volume)]; exact ht
    have hab : |t-c| < r := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hs
    exact hδA t (hab.trans hrδ) y hy (subset_closure hya)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circlePeriodize_abs_lt_one {f : ℝ → ℝ} {a : ℝ}
    (hs : tsupport f ⊆ Ioo (a-1/2) (a+1/2))
    (hb : ∀ x,|f x|<1) (x : ℝ) : |circlePeriodize f x|<1 := by
  classical
  by_cases hn : ∃ n : ℤ,f (x+n)≠0
  · obtain ⟨n,hn⟩ := hn
    have huniq (m : ℤ) (hm : m≠n) : f (x+m)=0 := by
      by_contra hm'
      have h1 := hs (subset_tsupport f hn)
      have h2 := hs (subset_tsupport f hm')
      have hlo : (-1 : ℝ)<(m-n : ℤ) := by push_cast; linarith [h1.2,h2.1]
      have hhi : ((m-n : ℤ) : ℝ)<1 := by push_cast; linarith [h1.1,h2.2]
      have hlo' : (-1 : ℤ) < m-n := by exact_mod_cast hlo
      have hhi' : m-n<1 := by exact_mod_cast hhi
      omega
    rw [circlePeriodize,tsum_eq_single n huniq]
    exact hb _
  · push Not at hn
    simp only [circlePeriodize,hn,tsum_zero,abs_zero,zero_lt_one]

theorem exists_planar_affine_band_field {L q : ℝ} (hL : L∈Ioo 0 (1/2))
    (hq : q∈Ioo 0 1) :
    ∃ u v : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) u ∧ContDiff ℝ (⊤ : ℕ∞) v ∧
      Function.Periodic u 1 ∧Function.Periodic v 1 ∧
      (∀ y,0≤u y) ∧(∀ y,(u y)^2+(v y)^2=1) ∧
      (∀ y,|y|≤L →u y=Real.sqrt (1-(q/L*y)^2)) ∧
      (∀ y,|y|<L →deriv v y=q/L) := by
  have hLq : L<L/q := (lt_div_iff₀ hq.1).mpr (by nlinarith [hL.1,hq.2])
  obtain ⟨R,hLR,hR⟩ := exists_between (lt_min hL.2 hLq)
  have hRhalf : R<1/2 := hR.trans_le (min_le_left _ _)
  have hqR : (q/L)*R<1 := by
    have hh := (lt_div_iff₀ hq.1).mp (hR.trans_le (min_le_right _ _))
    rw [div_mul_eq_mul_div]
    apply (div_lt_one hL.1).mpr
    nlinarith
  let χ : ContDiffBump (0 : ℝ) := ⟨L,R,hL.1,hLR⟩
  let f : ℝ → ℝ := fun t ↦ (q/L*t)*χ t
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (contDiff_const.mul contDiff_id).mul χ.contDiff
  have hfs : tsupport f ⊆ Ioo ((0 : ℝ)-1/2) (0+1/2) := by
    apply (tsupport_mul_subset_right (f := fun t ↦ q/L*t) (g := χ)).trans
    rw [χ.tsupport_eq,Real.closedBall_eq_Icc]
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f)
      (fun _ ht ↦ ⟨(hfs ht).1.le,(hfs ht).2.le⟩)
  have hfb (t : ℝ) : |f t|<1 := by
    by_cases hz : χ t=0
    · simp [f,hz]
    have ht : |t|<R := by
      have hh : t∈Metric.ball (0 : ℝ) R := by rwa [←χ.support_eq]
      simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hh
    have hqL : 0<q/L := div_pos hq.1 hL.1
    calc
      |f t|=(q/L)* |t| *χ t := by simp only [f,abs_mul,abs_of_pos hqL,abs_of_nonneg χ.nonneg]
      _≤(q/L)* |t| := mul_le_of_le_one_right (mul_nonneg hqL.le (abs_nonneg _)) χ.le_one
      _<(q/L)*R := mul_lt_mul_of_pos_left ht hqL
      _<1 := hqR
  let v := circlePeriodize f
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := circlePeriodize_contDiff hf hfc
  have hpv : Function.Periodic v 1 := circlePeriodize_periodic f
  have hvb (t : ℝ) : |v t|<1 := circlePeriodize_abs_lt_one hfs hfb t
  have hpos (t : ℝ) : 0<1-(v t)^2 := by
    nlinarith [hvb t,abs_nonneg (v t),sq_abs (v t)]
  let u : ℝ → ℝ := fun t ↦ Real.sqrt (1-(v t)^2)
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := (contDiff_const.sub (hv.pow 2)).sqrt (fun t ↦ (hpos t).ne')
  have hpu : Function.Periodic u 1 := fun t ↦ by dsimp only [u]; rw [hpv t]
  refine ⟨u,v,hu,hv,hpu,hpv,fun t ↦ Real.sqrt_nonneg _,?_,?_,?_⟩
  · intro t
    dsimp only [u]
    rw [Real.sq_sqrt (hpos t).le]
    ring
  · intro t ht
    have htc : t∈Icc ((0 : ℝ)-1/2) (0+1/2) := by
      obtain ⟨ht0,ht1⟩ := abs_le.mp ht
      constructor <;> linarith
    have hχ : χ t=1 := χ.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using ht)
    dsimp only [u,v]
    rw [(circlePeriodize_eventuallyEq hfc hfs htc).eq_of_nhds]
    simp only [f,hχ,mul_one]
  · intro t ht
    have htc : t∈Icc ((0 : ℝ)-1/2) (0+1/2) := by
      obtain ⟨ht0,ht1⟩ := abs_lt.mp ht
      constructor <;> linarith
    have hχ := χ.eventuallyEq_one_of_mem_ball (show t∈Metric.ball (0 : ℝ) L from by
      simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)
    have he : f=ᶠ[𝓝 t](fun t : ℝ ↦ q/L*t) := by
      filter_upwards [hχ] with x hx
      simp only [f,hx,Pi.one_apply,mul_one]
    change deriv (circlePeriodize f) t=q/L
    rw [(circlePeriodize_eventuallyEq hfc hfs htc).deriv_eq,he.deriv_eq]
    simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma closedCentralArc_isCompact (K : ℝ) : IsCompact (closedCentralArc K) :=
  isCompact_Icc.image (AddCircle.continuous_mk' (1 : ℝ))

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_PlanarRadialDownset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_closedCentralArc {K : ℝ} (hK : K∈Ico 0 (1/2)) (f : AxisCircle →ℝ) :
    (∫ z in closedCentralArc K,f z)=∫ t in (-K)..K,f (t : AxisCircle) := by
  have hsub : Icc (-K) K ⊆ Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ)+1) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2,hK.2]
  have he (t : ℝ) (ht : t∈Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ)+1)) :
      (t : AxisCircle)∈closedCentralArc K ↔t∈Icc (-K) K := by
    constructor
    · rintro ⟨s,hs,hst⟩
      have hh := (AddCircle.coe_eq_coe_iff_of_mem_Ioc (hsub hs) ht).mp hst
      rwa [←hh]
    · intro ht
      exact ⟨t,ht,rfl⟩
  calc
    _=∫ z : AxisCircle,(closedCentralArc K).indicator f z :=
      (integral_indicator (closedCentralArc_isCompact K).measurableSet).symm
    _=∫ t in Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ)+1),(closedCentralArc K).indicator f (t : AxisCircle) :=
      (AddCircle.integral_preimage (1 : ℝ) (-(1/2 : ℝ)) _).symm
    _=∫ t in Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ)+1),(Icc (-K) K).indicator
        (fun t : ℝ ↦ f (t : AxisCircle)) t := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      by_cases htk : t∈Icc (-K) K
      · simp only [indicator_of_mem htk,indicator_of_mem ((he t ht).mpr htk)]
      · simp only [indicator_of_notMem htk,indicator_of_notMem (mt (he t ht).mp htk)]
    _=∫ t in Icc (-K) K,f (t : AxisCircle) := by
      rw [setIntegral_indicator measurableSet_Icc,inter_eq_right.mpr hsub]
    _=∫ t in (-K)..K,f (t : AxisCircle) := by
      rw [intervalIntegral.integral_of_le (by linarith [hK.1]),integral_Icc_eq_integral_Ioc]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_scaled_semicircle {L : ℝ} (hL : 0<L) :
    (∫ t in (-L)..L,Real.sqrt (1-(t/L)^2))=Real.pi*L/2 := by
  have hi := intervalIntegral.integral_comp_div (fun t : ℝ ↦ Real.sqrt (1-t^2))
    (a := -L) (b := L) hL.ne'
  rw [neg_div,div_self hL.ne',integral_sqrt_one_sub_sq] at hi
  calc
    _=L*(Real.pi/2) := hi
    _=Real.pi*L/2 := by ring

theorem planarTorusPerimeter_ge_semicircle_calibration
    {A : Set TransverseProduct} (hA : IsOpen A) {L : ℝ} (hL : L∈Ioo 0 (1/2))
    (hband : ∀ y∈A,∃ t : ℝ,|t|<L ∧(t : AxisCircle)=y 1)
    (hin : ∀ t : ℝ,|t|<L →∀ y : TransverseProduct,y 0=0 →y 1=(t : AxisCircle) →y∈A)
    (hout : ∀ y : TransverseProduct,y 0=((1/2 : ℝ) : AxisCircle) →y∉closure A) :
    ENNReal.ofReal (volume.real A/L+Real.pi*L)≤planarTorusPerimeter A := by
  let f : ℝ →ℝ := fun t ↦ Real.sqrt (1-(t/L)^2)
  have hf : Continuous f := (continuous_const.sub ((continuous_id.div_const L).pow 2)).sqrt
  have hb (q : ℝ) (hq : q∈Ioo 0 1) :
      ENNReal.ofReal (q/L*volume.real A+2*(∫ t in (-(q*L))..(q*L),f t))≤planarTorusPerimeter A := by
    obtain ⟨u,v,hu,hv,pu,pv,hu0,huv,huBand,hvBand⟩ := exists_planar_affine_band_field hL hq
    have hqL : 0<q*L := mul_pos hq.1 hL.1
    have hqLL : q*L<L := by nlinarith [hq.2,hL.1]
    have hKhalf : q*L<1/2 := hqLL.trans hL.2
    have hbound := planarTorusPerimeter_ge_corner_calibration hA (closedCentralArc_isCompact (q*L))
      hu hv pu pv hu0 (fun t ↦ (huv t).le) (a := 0) (c := 1/2) (by norm_num) (by norm_num)
      (fun y hy0 hyT ↦ ?_) hout (k := q/L) (fun y hy ↦ ?_)
    · have hInt : (∫ t in (-(q*L))..(q*L),f t)≤∫ z in closedCentralArc (q*L),pu.lift z := by
        rw [integral_closedCentralArc ⟨hqL.le,hKhalf⟩]
        change (∫ t in (-(q*L))..(q*L),f t)≤∫ t in (-(q*L))..(q*L),u t
        apply intervalIntegral.integral_mono_on (by linarith) (hf.intervalIntegrable _ _) (hu.continuous.intervalIntegrable _ _)
        intro t ht
        have htL : |t|≤L := (abs_le.mpr ht).trans hqLL.le
        rw [huBand t htL]
        apply Real.sqrt_le_sqrt
        have hq2 : q^2≤1 := by nlinarith [hq.1,hq.2]
        have hmul := mul_nonneg (sq_nonneg (t/L)) (sub_nonneg.mpr hq2)
        have he : (q/L*t)^2=q^2*(t/L)^2 := by ring
        rw [he]
        nlinarith
      exact (ENNReal.ofReal_le_ofReal (by linarith)).trans hbound
    · obtain ⟨t,ht,he⟩ := hyT
      have htt : |t|<L := (abs_le.mpr ht).trans_lt hqLL
      exact hin t htt y (by simpa using hy0) he.symm
    · obtain ⟨t,ht,he⟩ := hband y hy
      rw [←he]
      exact hvBand t ht
  have hp : Continuous (fun z : ℝ ↦ ∫ t in (0 : ℝ)..z,f t) :=
    intervalIntegral.continuous_primitive (fun _ _ ↦ hf.intervalIntegrable _ _) 0
  have hI : Continuous (fun q : ℝ ↦ ∫ t in (-(q*L))..(q*L),f t) := by
    have he (q : ℝ) : (∫ t in (-(q*L))..(q*L),f t)=
        (∫ t in (0 : ℝ)..(q*L),f t)-(∫ t in (0 : ℝ)..(-(q*L)),f t) :=
      (intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)).symm
    simp_rw [he]
    exact (hp.comp (continuous_id.mul_const L)).sub (hp.comp (continuous_id.mul_const L).neg)
  have hc : Continuous (fun q : ℝ ↦ ENNReal.ofReal (q/L*volume.real A+2*(∫ t in (-(q*L))..(q*L),f t))) :=
    ENNReal.continuous_ofReal.comp (((continuous_id.div_const L).mul_const _).add (continuous_const.mul hI))
  have hs : IsClosed {q : ℝ | ENNReal.ofReal (q/L*volume.real A+2*(∫ t in (-(q*L))..(q*L),f t))≤planarTorusPerimeter A} :=
    isClosed_le hc continuous_const
  have h1 : (1 : ℝ)∈closure (Ioo (0 : ℝ) 1) := by rw [closure_Ioo (by norm_num : (0 : ℝ)≠1)]; exact ⟨by norm_num,le_rfl⟩
  have hh := closure_minimal (fun q hq ↦ hb q hq) hs h1
  change ENNReal.ofReal (1/L*volume.real A+2*(∫ t in (-(1*L))..(1*L),f t))≤planarTorusPerimeter A at hh
  simp only [one_mul] at hh
  change ENNReal.ofReal (1/L*volume.real A+2*(∫ t in (-L)..L,Real.sqrt (1-(t/L)^2)))≤_ at hh
  rw [integral_scaled_semicircle hL.1] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planarAxisPoint_continuous : Continuous planarAxisPoint := by
  apply continuous_pi
  intro j
  fin_cases j
  · exact continuous_const
  · exact AddCircle.continuous_mk' (1 : ℝ)

lemma planar_axis_can_grow {A : Set TransverseProduct} (hA : IsOpen A)
    {t : ℝ} (ht : t<1/2) (hm : planarAxisPoint t∈A) :
    ∃ s : ℝ,t < s ∧ s<1/2 ∧ planarAxisPoint s∈A := by
  have ho : IsOpen (planarAxisPoint ⁻¹' A ∩ Iio (1/2 : ℝ)) :=
    (hA.preimage planarAxisPoint_continuous).inter isOpen_Iio
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp ho t ⟨hm,ht⟩
  have he : t+ε/2∈Metric.ball t ε := by
    rw [Metric.mem_ball,Real.dist_eq]
    have hp : 0<ε/2 := half_pos hε
    rw [show t+ε/2-t=ε/2 by ring,abs_of_pos hp]
    linarith
  exact ⟨t+ε/2,by linarith,(hball he).2,(hball he).1⟩

lemma axisCircle_norm_le_half (z : AxisCircle) : ‖z‖≤1/2 := by
  simpa using AddCircle.norm_le_half_period 1 (x := z) (by norm_num)

lemma axisCircle_norm_coe_small {t : ℝ} (ht : |t|≤1/2) : ‖(t : AxisCircle)‖=|t| := by
  apply (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr
  simpa using ht

theorem planar_radial_extent {A : Set TransverseProduct} (hA : IsOpen A)
    (hd : PlanarRadialDownset A) (h0 : (0 : TransverseProduct)∈A)
    (hout : planarAxisPoint (1/2)∉closure A) :
    ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
      (∀ y∈A,‖y 1‖<L) ∧
      (∀ t : ℝ,|t|<L →∀ y : TransverseProduct,y 0=0 →y 1=(t : AxisCircle) →y∈A) := by
  let T : Set ℝ := {t | t∈Icc 0 (1/2) ∧ planarAxisPoint t∈A}
  have he0 : planarAxisPoint 0=(0 : TransverseProduct) := by ext j; fin_cases j <;> simp [planarAxisPoint]
  have hzero : planarAxisPoint 0∈A := he0 ▸ h0
  have hne : T.Nonempty := ⟨0,⟨by constructor <;> norm_num,hzero⟩⟩
  have hb : BddAbove T := ⟨1/2,fun t ht ↦ ht.1.2⟩
  let L : ℝ := sSup T
  have hLhalf : L≤1/2 := csSup_le hne (fun t ht ↦ ht.1.2)
  have hcl : planarAxisPoint L∈closure A := by
    exact closure_minimal (s := T) (t := planarAxisPoint ⁻¹' closure A)
      (fun t ht ↦ subset_closure ht.2)
      (isClosed_closure.preimage planarAxisPoint_continuous) (csSup_mem_closure hne hb)
  have hLlt : L<1/2 := lt_of_le_of_ne hLhalf (fun he ↦ hout (he ▸ hcl))
  obtain ⟨s,hs,hsH,hsA⟩ := planar_axis_can_grow hA (by norm_num : (0 : ℝ)<1/2) hzero
  have hsL : s≤L := le_csSup hb ⟨⟨hs.le,hsH.le⟩,hsA⟩
  refine ⟨L,⟨hs.trans_le hsL,hLlt⟩,?_,?_⟩
  · intro y hy
    have hp : planarAxisPoint ‖y 1‖∈A := by
      apply hd _ y _ hy
      intro j
      fin_cases j
      · simp [planarAxisPoint]
      · change ‖((‖y 1‖ : ℝ) : AxisCircle)‖≤‖y 1‖
        rw [axisCircle_norm_coe_small (by simpa only [abs_norm] using axisCircle_norm_le_half (y 1)),abs_norm]
    have hrL : ‖y 1‖≤L := le_csSup hb ⟨⟨norm_nonneg _,axisCircle_norm_le_half _⟩,hp⟩
    obtain ⟨s,hs,hsH,hsA⟩ := planar_axis_can_grow hA (hrL.trans_lt hLlt) hp
    exact hs.trans_le (le_csSup hb ⟨⟨(norm_nonneg _).trans hs.le,hsH.le⟩,hsA⟩)
  · intro t ht y hy0 hy1
    obtain ⟨s,hs,hst⟩ := exists_lt_of_lt_csSup hne ht
    apply hd y (planarAxisPoint s) _ hs.2
    intro j
    fin_cases j
    · simp [planarAxisPoint,hy0]
    · change ‖y 1‖≤‖(s : AxisCircle)‖
      rw [hy1,axisCircle_norm_coe_small (ht.le.trans hLhalf),
        axisCircle_norm_coe_small (by simpa [abs_of_nonneg hs.1.1] using hs.1.2),abs_of_nonneg hs.1.1]
      exact hst.le

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisCircle_exists_centered_rep (z : AxisCircle) :
    ∃ t : ℝ,(t : AxisCircle)=z ∧ |t|=‖z‖ := by
  let t := (AddCircle.equivIco (1 : ℝ) (-(1/2 : ℝ)) z : ℝ)
  have ht := (AddCircle.equivIco (1 : ℝ) (-(1/2 : ℝ)) z).property
  have hbound : |t|≤1/2 := abs_le.mpr ⟨ht.1,by dsimp [t]; linarith [ht.2]⟩
  have he : (t : AxisCircle)=z := AddCircle.coe_equivIco
  exact ⟨t,he,by rw [←he,axisCircle_norm_coe_small hbound]⟩

lemma planar_radial_empty_fiber {A : Set TransverseProduct} (hd : PlanarRadialDownset A)
    (hout : planarFirstAxisPoint (1/2)∉closure A) :
    ∀ y : TransverseProduct,y 0=((1/2 : ℝ) : AxisCircle) →y∉closure A := by
  let f : TransverseProduct →TransverseProduct := fun y ↦ ![y 0,0]
  have hc : Continuous f := by
    apply continuous_pi
    intro j
    fin_cases j
    · exact continuous_apply 0
    · exact continuous_const
  have hm : A⊆f ⁻¹' closure A := by
    intro y hy
    apply subset_closure
    apply hd (f y) y _ hy
    intro j
    fin_cases j <;> simp [f]
  have hcl := closure_minimal hm (isClosed_closure.preimage hc)
  intro y hy hya
  apply hout
  have he : f y=planarFirstAxisPoint (1/2) := by
    ext j
    fin_cases j <;> simp [f,planarFirstAxisPoint,hy]
  exact he ▸ hcl hya

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialAreaDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planarSwap_measurePreserving : MeasurePreserving planarSwap :=
  volume_measurePreserving_piCongrLeft _ _

lemma planeSwap_single (j : Fin 2) : planeSwap (EuclideanSpace.single j 1)=
    EuclideanSpace.single (Equiv.swap 0 1 j) 1 := by
  ext k
  fin_cases j <;> fin_cases k <;> simp

lemma planeDivergence_swap {F : Plane →Plane} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Plane) :
    planeDivergence (fun y ↦ planeSwap (F (planeSwap y))) x=planeDivergence F (planeSwap x) := by
  have hd := planeSwap.toContinuousLinearEquiv.hasFDerivAt.comp x
    (((hF.differentiable (by simp) _).hasFDerivAt).comp x planeSwap.toContinuousLinearEquiv.hasFDerivAt)
  change HasFDerivAt (fun y ↦ planeSwap (F (planeSwap y))) _ x at hd
  rw [planeDivergence,hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    planeDivergence]
  simp
  rw [planeSwap_single,planeSwap_single]
  norm_num
  ring

lemma planarAdmissibleField_swap {F : Plane →Plane} (hF : PlanarAdmissibleField F) :
    PlanarAdmissibleField (fun y ↦ planeSwap (F (planeSwap y))) := by
  refine ⟨planeSwap.contDiff.comp (hF.1.comp planeSwap.contDiff),?_,?_⟩
  · intro n y
    change planeSwap (F (planeSwap (y+WithLp.toLp 2 (fun j ↦ (n j : ℝ)))))=planeSwap (F (planeSwap y))
    rw [map_add]
    have he : planeSwap (WithLp.toLp 2 (fun j ↦ (n j : ℝ)))=
        WithLp.toLp 2 (fun j ↦ ((n (Equiv.swap 0 1 j)) : ℝ)) := by ext j; rfl
    rw [he,hF.2.1]
  · intro y
    rw [planeSwap.norm_map]
    exact hF.2.2 _

lemma planeSwap_representative (y : TransverseProduct) :
    planeSwap (planarRepresentative y)=planarRepresentative (planarSwap y) := by
  ext j
  simp only [planeSwap_apply,planarRepresentative,planarSwap_apply]

lemma planarTorusPerimeter_swap_le (A : Set TransverseProduct) :
    planarTorusPerimeter (planarSwap ⁻¹' A)≤planarTorusPerimeter A := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  let G : Plane →Plane := fun y ↦ planeSwap (F (planeSwap y))
  have hG : PlanarAdmissibleField G := planarAdmissibleField_swap hF
  have hh := planarSwap_measurePreserving.setIntegral_preimage_emb planarSwap.measurableEmbedding
    (fun y ↦ planeDivergence G (planarRepresentative y)) A
  have he : (fun y ↦ planeDivergence G (planarRepresentative (planarSwap y)))=
      (fun y ↦ planeDivergence F (planarRepresentative y)) := by
    funext y
    rw [show planeDivergence G (planarRepresentative (planarSwap y))=planeDivergence F (planeSwap (planarRepresentative (planarSwap y))) from planeDivergence_swap hF.1 _,
      planeSwap_representative,planarSwap_involutive]
  rw [he] at hh
  rw [hh]
  exact le_iSup_of_le G (le_iSup_of_le hG le_rfl)

theorem planarTorusPerimeter_swap (A : Set TransverseProduct) :
    planarTorusPerimeter (planarSwap ⁻¹' A)=planarTorusPerimeter A := by
  refine le_antisymm (planarTorusPerimeter_swap_le A) ?_
  have hh := planarTorusPerimeter_swap_le (planarSwap ⁻¹' A)
  have he : planarSwap ⁻¹' (planarSwap ⁻¹' A)=A := by ext y; simp
  rwa [he] at hh

lemma planar_volume_swap (A : Set TransverseProduct) :
    volume.real (planarSwap ⁻¹' A)=volume.real A := by
  apply congrArg ENNReal.toReal
  exact planarSwap_measurePreserving.measure_preimage_emb planarSwap.measurableEmbedding A

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planarSwap_continuous : Continuous planarSwap := by
  apply continuous_pi
  intro j
  simpa only [planarSwap_apply] using (continuous_apply (Equiv.swap 0 1 j) : Continuous (fun y : TransverseProduct ↦ y (Equiv.swap 0 1 j)))

lemma planarSwap_closure_subset (A : Set TransverseProduct) :
    closure (planarSwap ⁻¹' A)⊆planarSwap ⁻¹' closure A :=
  closure_minimal (preimage_mono subset_closure) (isClosed_closure.preimage planarSwap_continuous)

lemma planarRadialDownset_swap {A : Set TransverseProduct} (hd : PlanarRadialDownset A) :
    PlanarRadialDownset (planarSwap ⁻¹' A) := by
  intro y z hyz hz
  apply hd (planarSwap y) (planarSwap z) _ hz
  intro j
  simpa only [planarSwap_apply] using hyz (Equiv.swap 0 1 j)

lemma planar_radial_full_calibration {A : Set TransverseProduct} (hA : IsOpen A)
    (hd : PlanarRadialDownset A) (h0 : (0 : TransverseProduct)∈A)
    (hout0 : planarFirstAxisPoint (1/2)∉closure A)
    (hout1 : planarAxisPoint (1/2)∉closure A) :
    ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
      (∀ y∈A,‖y 1‖<L) ∧
      (∀ y : TransverseProduct,y 0=0 →‖y 1‖<L →y∈A) ∧
      ENNReal.ofReal (volume.real A/L+Real.pi*L)≤planarTorusPerimeter A := by
  obtain ⟨L,hL,hband,hin⟩ := planar_radial_extent hA hd h0 hout1
  refine ⟨L,hL,hband,?_,planarTorusPerimeter_ge_semicircle_calibration hA hL ?_ hin
    (planar_radial_empty_fiber hd hout0)⟩
  · intro y hy0 hy1
    obtain ⟨t,he,ht⟩ := axisCircle_exists_centered_rep (y 1)
    exact hin t (ht.trans_lt hy1) y hy0 he.symm
  · intro y hy
    obtain ⟨t,he,ht⟩ := axisCircle_exists_centered_rep (y 1)
    exact ⟨t,ht ▸ hband y hy,he⟩

theorem planar_radial_both_extents_oai {A : Set TransverseProduct} (hA : IsOpen A)
    (hd : PlanarRadialDownset A) (h0 : (0 : TransverseProduct)∈A)
    (hout0 : planarFirstAxisPoint (1/2)∉closure A)
    (hout1 : planarAxisPoint (1/2)∉closure A) (j : Fin 2) :
    ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
      (∀ y∈A,‖y j‖<L) ∧
      (∀ y : TransverseProduct,(∀ k : Fin 2,k≠j →y k=0) →‖y j‖<L →y∈A) ∧
      ENNReal.ofReal (volume.real A/L+Real.pi*L)≤planarTorusPerimeter A := by
  fin_cases j
  · have h0' : (0 : TransverseProduct)∈planarSwap ⁻¹' A := by simpa using h0
    have hout0' : planarFirstAxisPoint (1/2)∉closure (planarSwap ⁻¹' A) := by
      intro hh
      apply hout1
      simpa only [mem_preimage,planarSwap_firstAxisPoint] using planarSwap_closure_subset A hh
    have hout1' : planarAxisPoint (1/2)∉closure (planarSwap ⁻¹' A) := by
      intro hh
      apply hout0
      simpa only [mem_preimage,planarSwap_secondAxisPoint] using planarSwap_closure_subset A hh
    obtain ⟨L,hL,hband,hin,hp⟩ := planar_radial_full_calibration (hA.preimage planarSwap_continuous)
      (planarRadialDownset_swap hd) h0' hout0' hout1'
    refine ⟨L,hL,?_,?_,?_⟩
    · intro y hy
      have hb := hband (planarSwap y) (by simpa using hy)
      simpa using hb
    · intro y hzero hy
      have hb := hin (planarSwap y) (by simpa using hzero 1 (by decide)) (by simpa using hy)
      simpa using hb
    · simpa only [planar_volume_swap,planarTorusPerimeter_swap] using hp
  · obtain ⟨L,hL,hband,hin,hp⟩ := planar_radial_full_calibration hA hd h0 hout0 hout1
    exact ⟨L,hL,hband,fun y hzero hy ↦ hin y (hzero 0 (by decide)) hy,hp⟩

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.planar_radial_both_extents_oai := @OAI.CubicTorus.planar_radial_both_extents_oai
