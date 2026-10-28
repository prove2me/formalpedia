-- Prove2me | solution 1 for OAI.CubicTorus.planar_radial_strip_gain_first
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:40:04.427837+00:00
-- url     : https://prove2.me/submissions/c250097c-945e-49ba-a385-8c9219e933b9

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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_OctantVertex
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

lemma smooth_periodic_centered_primitive {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : Function.Periodic f 1) :
    ∃ ψ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ ∧ Function.Periodic ψ 1 ∧
      ∀ t,deriv ψ t=f t-∫ u in (0 : ℝ)..1,f u := by
  let c : ℝ := ∫ u in (0 : ℝ)..1,f u
  let g : ℝ → ℝ := fun t ↦ f t-c
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.sub contDiff_const
  have hgp : Function.Periodic g 1 := fun t ↦ by simp [g,hp t]
  let ψ : ℝ → ℝ := fun t ↦ ∫ u in (0 : ℝ)..t,g u
  have hd (t : ℝ) : HasDerivAt ψ (g t) t :=
    intervalIntegral.integral_hasDerivAt_right (hg.continuous.intervalIntegrable _ _)
      hg.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuous.continuousAt
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    apply contDiff_infty_iff_deriv.mpr
    exact ⟨fun t ↦ (hd t).differentiableAt,(funext fun t ↦ (hd t).deriv) ▸ hg⟩
  have hz : (∫ u in (0 : ℝ)..1,g u)=0 := by
    rw [show g=(fun t ↦ f t-c) from rfl,
      intervalIntegral.integral_sub (hf.continuous.intervalIntegrable _ _)
        intervalIntegrable_const,intervalIntegral.integral_const]
    simp [c]
  refine ⟨ψ,hψ,?_,fun t ↦ (hd t).deriv⟩
  intro t
  change (∫ u in (0 : ℝ)..t+1,g u)=∫ u in (0 : ℝ)..t,g u
  rw [hgp.intervalIntegral_add_eq_add 0 t (fun _ _ ↦ hg.continuous.intervalIntegrable _ _)]
  simp only [zero_add,hz,add_zero]

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

lemma axisCircle_norm_le_half (z : AxisCircle) : ‖z‖≤1/2 := by
  simpa using AddCircle.norm_le_half_period 1 (x := z) (by norm_num)

lemma axisCircle_norm_coe_small {t : ℝ} (ht : |t|≤1/2) : ‖(t : AxisCircle)‖=|t| := by
  apply (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr
  simpa using ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NestingEndpointBound
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

theorem planarTorusPerimeter_ge_weighted_derivative_flux
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
    : ENNReal.ofReal ((∫ y in A,(real_periodic_deriv pv).lift (y 1))+
        2*(∫ t in T,pu.lift t))≤planarTorusPerimeter A := by
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
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem planarTorusPerimeter_ge_open_derivative_flux
    {A : Set TransverseProduct} (hA : IsOpen A)
    {T : Set AxisCircle} (hT : IsCompact T)
    {u v : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (pu : Function.Periodic u 1) (pv : Function.Periodic v 1)
    (hu0 : ∀ y,0≤u y) (huv : ∀ y,(u y)^2+(v y)^2≤1)
    {a c : ℝ} (hac : a ≤ c) (hshort : c-a<1)
    (hin : ∀ y : TransverseProduct,y 0=(a : AxisCircle) →y 1∈T →y∈A)
    (hout : ∀ y : TransverseProduct,y 0=(c : AxisCircle) →y∉closure A)
    : ENNReal.ofReal ((∫ y in A,(real_periodic_deriv pv).lift (y 1))+
        2*(∫ t in T,pu.lift t))≤planarTorusPerimeter A := by
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
  apply planarTorusPerimeter_ge_weighted_derivative_flux hA.measurableSet hT.measurableSet
    hu hv pu pv hu0 huv b.contDiff_normed b.integrable_normed (fun t ↦ b.nonneg_normed t)
    b.integral_normed (r := r) (a := a) (c := c) _ hac hrc _ _
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

lemma planar_closed_edge_collar {A : Set TransverseProduct} {e : ℝ}
    (he : ∀ y∈closure A,y 1=((1/2 : ℝ) : AxisCircle) →2*‖y 0‖≤e)
    {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ y∈closure A,
      dist (y 1) ((1/2 : ℝ) : AxisCircle)<δ →2*‖y 0‖<e+ε := by
  let K : Set TransverseProduct := closure A∩{y | e+ε≤2*‖y 0‖}
  have hK : IsCompact K := (isClosed_closure.inter
    (isClosed_le continuous_const (continuous_const.mul (continuous_apply 0).norm))).isCompact
  have ho : IsOpen (Function.eval (1 : Fin 2) '' K)ᶜ :=
    (hK.image (continuous_apply 1)).isClosed.isOpen_compl
  have hh : ((1/2 : ℝ) : AxisCircle)∈(Function.eval (1 : Fin 2) '' K)ᶜ := by
    rintro ⟨y,hy,hy1⟩
    have hh := he y hy.1 hy1
    have hh' := hy.2
    change e+ε≤2*‖y 0‖ at hh'
    linarith
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp ho _ hh
  refine ⟨δ,hδ,fun y hy hyd ↦ ?_⟩
  by_contra h
  exact hball hyd ⟨y,⟨hy,le_of_not_gt h⟩,rfl⟩

lemma planar_seam_probability_bound {A : Set TransverseProduct}
    (hA : MeasurableSet A) {β : AxisCircle →ℝ} (hβ : Continuous β)
    (hβ0 : ∀ t,0≤β t) (hβ1 : (∫ t,β t)=1) {r : ℝ} (hr : 0 ≤ r)
    (hband : ∀ y∈A,β (y 1)≠0 →2*‖y 0‖ ≤ r) :
    (∫ y in A,β (y 1)) ≤ r := by
  let B : Set AxisCircle := Metric.closedBall 0 (r/2)
  have hB : MeasurableSet B := measurableSet_closedBall
  have hi : Integrable (fun y : TransverseProduct ↦ β (y 1)) :=
    (hβ.comp (continuous_apply (1 : Fin 2))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun y : TransverseProduct ↦ B.indicator (fun _ ↦ (1 : ℝ)) (y 0)*β (y 1)) := by
    apply (hi.indicator (hB.preimage (measurable_pi_apply 0))).congr
    filter_upwards [] with y
    by_cases hy : y 0∈B <;> simp [hy]
  have hle : (fun y : TransverseProduct ↦ A.indicator (fun y ↦ β (y 1)) y)≤
      (fun y : TransverseProduct ↦ B.indicator (fun _ ↦ (1 : ℝ)) (y 0)*β (y 1)) := by
    intro y
    dsimp only
    by_cases hy : y∈A
    · rw [indicator_of_mem hy]
      by_cases hz : β (y 1)=0
      · simp [hz]
      have hyB : y 0∈B := by
        change dist (y 0) 0 ≤ r/2
        rw [dist_zero_right]
        linarith [hband y hy hz]
      simp only [indicator_of_mem hyB,one_mul,le_refl]
    · rw [indicator_of_notMem hy]
      exact mul_nonneg (indicator_nonneg (fun _ _ ↦ zero_le_one) _) (hβ0 _)
  have h := integral_mono (hi.indicator hA) hj hle
  rw [integral_indicator hA,transverse_integral_mul,hβ1,mul_one,integral_indicator hB,
    setIntegral_const,smul_eq_mul,mul_one] at h
  apply h.trans
  change (volume B).toReal ≤ r
  rw [AddCircle.volume_closedBall]
  have he : 2*(r/2)=r := by ring
  rw [he,ENNReal.toReal_ofReal (le_min zero_le_one hr)]
  exact min_le_right _ _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem planarTorusPerimeter_ge_strip_seam_calibration
    {A : Set TransverseProduct} (hA : IsOpen A)
    {T : Set AxisCircle} (hT : IsCompact T)
    {u v : ℝ →ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (pu : Function.Periodic u 1) (pv : Function.Periodic v 1)
    (hu0 : ∀ t,0≤u t) (huv : ∀ t,(u t)^2+(v t)^2≤1)
    (hin : ∀ y : TransverseProduct,y 0=0 →y 1∈T →y∈A)
    (hout : ∀ y : TransverseProduct,y 0=((1/2 : ℝ) : AxisCircle) →y∉closure A)
    {β : AxisCircle →ℝ} (hβ : Continuous β) (hβ0 : ∀ t,0≤β t)
    (hβ1 : (∫ t,β t)=1) {k r : ℝ} (hk : 0≤k) (hr : 0 ≤ r)
    (hd : ∀ t,deriv v t=2*k*(1-β (t : AxisCircle)))
    (hband : ∀ y∈A,β (y 1)≠0 →2*‖y 0‖ ≤ r) :
    ENNReal.ofReal (2*k*(volume.real A-r)+2*(∫ t in T,pu.lift t))≤planarTorusPerimeter A := by
  have hseam := planar_seam_probability_bound hA.measurableSet hβ hβ0 hβ1 hr hband
  have hβi : Integrable (fun y : TransverseProduct ↦ β (y 1)) :=
    (hβ.comp (continuous_apply (1 : Fin 2))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hd' (t : AxisCircle) : (real_periodic_deriv pv).lift t=2*k*(1-β t) := by
    induction t using Quotient.inductionOn with | h t => exact hd t
  have hid : (∫ y in A,(real_periodic_deriv pv).lift (y 1))=
      2*k*(volume.real A-∫ y in A,β (y 1)) := by
    simp_rw [hd']
    rw [integral_const_mul,integral_sub (integrable_const (1 : ℝ)).integrableOn hβi.integrableOn,
      setIntegral_const,smul_eq_mul,mul_one]
  have hcal := planarTorusPerimeter_ge_open_derivative_flux hA hT hu hv pu pv hu0 huv
    (a := 0) (c := 1/2) (by norm_num) (by norm_num) (by simpa only [AddCircle.coe_zero] using hin) hout
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hcal
  rw [hid]
  have h := mul_le_mul_of_nonneg_left (sub_le_sub_left hseam (volume.real A))
    (show 0≤2*k by positivity)
  linarith

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SmoothSeamProbability
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

theorem exists_smooth_seam_probability {L : ℝ} (hL : L∈Ioo 0 (1/2)) :
    ∃ β : ℝ →ℝ,ContDiff ℝ (⊤ : ℕ∞) β ∧Function.Periodic β 1 ∧
      (∀ t,0≤β t) ∧(∫ t in (0 : ℝ)..1,β t)=1 ∧
      (∀ t,|t|≤L →β t=0) ∧
      (∀ t : ℝ,β t≠0 →dist (t : AxisCircle) ((1/2 : ℝ) : AxisCircle)<1/2-L) := by
  let r : ℝ := 1/2-L
  have hr : 0 < r := by dsimp only [r]; linarith [hL.2]
  let b : ContDiffBump (0 : ℝ) := ⟨r/2,r,half_pos hr,by linarith⟩
  let B : ℝ →ℝ := fun t ↦ b.normed volume (t-1/2)
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := b.contDiff_normed.comp (contDiff_id.sub contDiff_const)
  have hBs : tsupport B ⊆ Ioo ((1/2 : ℝ)-1/2) (1/2+1/2) := by
    intro t ht
    have hh := tsupport_comp_subset_preimage (b.normed volume) (continuous_id.sub continuous_const) ht
    change t-1/2∈tsupport (b.normed volume) at hh
    rw [b.tsupport_normed_eq,Real.closedBall_eq_Icc] at hh
    change 0-r≤t-1/2 ∧ t-1/2≤0+r at hh
    dsimp only [r] at hh
    constructor <;> linarith [hh.1,hh.2,hL.1]
  have hBc : HasCompactSupport B := IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport B)
    (fun _ ht ↦ ⟨(hBs ht).1.le,(hBs ht).2.le⟩)
  let β := circlePeriodize B
  have hβ : ContDiff ℝ (⊤ : ℕ∞) β := circlePeriodize_contDiff hB hBc
  have pβ : Function.Periodic β 1 := circlePeriodize_periodic B
  have he (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) : β t=B t :=
    (circlePeriodize_eventuallyEq hBc hBs (by convert ht using 1; norm_num)).eq_of_nhds
  have hnB (t : ℝ) (ht : B t≠0) : |t-1/2| < r := by
    have hh : t-1/2∈Metric.ball (0 : ℝ) r := by
      rw [←b.support_normed_eq (μ := volume)]
      exact ht
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hh
  have hmean : (∫ t : AxisCircle,pβ.lift t)=1 := by
    rw [circlePeriodize_integral_short hBc hBs]
    exact (integral_sub_right_eq_self (b.normed volume) (1/2)).trans b.integral_normed
  refine ⟨β,hβ,pβ,fun t ↦ tsum_nonneg (fun n : ℤ ↦ b.nonneg_normed (t+n-1/2)),?_,?_,?_⟩
  · have hh := AddCircle.intervalIntegral_preimage (1 : ℝ) (0 : ℝ) pβ.lift
    simpa only [zero_add,pβ.lift_coe,hmean] using hh
  · intro t ht
    rcases le_total (0 : ℝ) t with ht0 | ht0
    · rw [he t ⟨ht0,by linarith [(abs_le.mp ht).2,hL.2]⟩]
      by_contra hh
      have hb := hnB t hh
      dsimp only [r] at hb
      have ha := (abs_lt.mp hb).1
      linarith [(abs_le.mp ht).2]
    · rw [←pβ t,he (t+1) ⟨by linarith [(abs_le.mp ht).1,hL.2],by linarith⟩]
      by_contra hh
      have hb := hnB (t+1) hh
      dsimp only [r] at hb
      have ha := (abs_lt.mp hb).2
      linarith [(abs_le.mp ht).1]
  · intro t ht
    let x : ℝ := ((AddCircle.equivIco (1 : ℝ) 0) (t : AxisCircle) : ℝ)
    have hx := ((AddCircle.equivIco (1 : ℝ) 0) (t : AxisCircle)).property
    change 0≤x ∧ x<0+1 at hx
    have hxt : (x : AxisCircle)=(t : AxisCircle) := (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply _
    have hβx : β x≠0 := by
      have heq : β x=β t := by rw [←pβ.lift_coe x,←pβ.lift_coe t,hxt]
      rwa [heq]
    rw [he x ⟨hx.1,by linarith [hx.2]⟩] at hβx
    have hnorm : dist (x : AxisCircle) ((1/2 : ℝ) : AxisCircle)≤|x-1/2| := by
      rw [dist_eq_norm,←QuotientAddGroup.mk_sub]
      exact QuotientAddGroup.norm_mk_le_norm
    rw [←hxt]
    exact hnorm.trans_lt (hnB x hβx)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem exists_smooth_saw_primitive {β : ℝ →ℝ}
    (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (pβ : Function.Periodic β 1)
    (hβ0 : ∀ t,0≤β t) (hβ1 : (∫ t in (0 : ℝ)..1,β t)=1)
    {L k : ℝ} (hL : L∈Ioo 0 (1/2)) (hk : 0≤k)
    (hb : ∀ t,|t|≤L →β t=0) :
    ∃ v : ℝ →ℝ,ContDiff ℝ (⊤ : ℕ∞) v ∧Function.Periodic v 1 ∧
      (∀ t,deriv v t=2*k*(1-β t)) ∧
      (∀ t,|t|≤L →v t=2*k*t) ∧(∀ t,|v t|≤2*k*(1-L)) := by
  obtain ⟨ψ,hψ,pψ,hdψ⟩ := smooth_periodic_centered_primitive hβ pβ
  let v : ℝ →ℝ := fun t ↦ -2*k*(ψ t-ψ 0)
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := contDiff_const.mul (hψ.sub contDiff_const)
  have pv : Function.Periodic v 1 := fun t ↦ by dsimp only [v]; rw [pψ t]
  have hd (t : ℝ) : deriv v t=2*k*(1-β t) := by
    dsimp only [v]
    rw [deriv_const_mul _ ((hψ.differentiable (by simp) t).sub_const _),deriv_sub_const,hdψ,hβ1]
    ring
  have hcentral (t : ℝ) (ht : |t|≤L) : v t=2*k*t := by
    have he : (∫ x in (0 : ℝ)..t,deriv v x)=2*k*t := by
      calc
        _=∫ x in (0 : ℝ)..t,(2*k : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hxL : |x|≤L := by
            rcases le_total (0 : ℝ) t with ht0 | ht0
            · rw [uIcc_of_le ht0] at hx
              exact abs_le.mpr ⟨by linarith [hx.1,hL.1],hx.2.trans (le_trans (le_abs_self t) ht)⟩
            · rw [uIcc_of_ge ht0] at hx
              exact abs_le.mpr ⟨by linarith [(abs_le.mp ht).1,hx.1],by linarith [hx.2,hL.1]⟩
          rw [hd,hb x hxL]
          ring
        _=2*k*t := by rw [intervalIntegral.integral_const]; simp only [sub_zero,smul_eq_mul]; ring
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ ↦ hv.differentiable (by simp) x)
      ((hv.continuous_deriv (by simp)).intervalIntegrable _ _)] at he
    simpa only [v,sub_self,mul_zero,sub_zero] using he
  have hm : Antitone (fun t ↦ v t-2*k*t) := by
    apply antitone_of_deriv_nonpos (hv.differentiable (by simp) |>.sub (differentiable_id.const_mul (2*k)))
    intro t
    rw [deriv_sub (hv.differentiable (by simp) t) ((differentiable_id.const_mul (2*k)) t),
      hd,deriv_const_mul _ (differentiableAt_id),deriv_id,mul_one]
    nlinarith [hβ0 t,mul_nonneg hk (hβ0 t)]
  have hs (a b : ℝ) (hab : a≤b) : v b-v a≤2*k*(b-a) := by
    have hh := hm hab
    dsimp only at hh
    linarith
  refine ⟨v,hv,pv,hd,hcentral,fun t ↦ ?_⟩
  let x : ℝ := ((AddCircle.equivIco (1 : ℝ) (-L)) (t : AxisCircle) : ℝ)
  have hx := ((AddCircle.equivIco (1 : ℝ) (-L)) (t : AxisCircle)).property
  change -L≤x ∧ x< -L+1 at hx
  have hxt : (x : AxisCircle)=(t : AxisCircle) :=
    (AddCircle.equivIco (1 : ℝ) (-L)).symm_apply_apply _
  have hvt : v t=v x := by rw [←pv.lift_coe t,←pv.lift_coe x,hxt]
  rw [hvt]
  by_cases hxc : x≤L
  · rw [hcentral x (abs_le.mpr ⟨hx.1,hxc⟩),abs_mul,abs_of_nonneg (by positivity : 0≤2*k)]
    exact mul_le_mul_of_nonneg_left ((abs_le.mpr ⟨hx.1,hxc⟩).trans (by linarith [hL.2])) (by positivity)
  · have hvL : v L=2*k*L := hcentral L (by rw [abs_of_pos hL.1])
    have hvR : v (1-L)= -2*k*L := by
      rw [show 1-L= -L+1 by ring,pv (-L),hcentral (-L) (by rw [abs_neg,abs_of_pos hL.1])]
      ring
    have h1 := hs L x (le_of_not_ge hxc)
    have h2 := hs x (1-L) (by linarith [hx.2,hL.1])
    rw [hvL] at h1
    rw [hvR] at h2
    apply abs_le.mpr
    constructor
    · have h := mul_le_mul_of_nonneg_left (show L≤x from (le_of_not_ge hxc)) (show 0≤2*k by positivity)
      nlinarith
    · have h := mul_le_mul_of_nonneg_left (show x≤1-L by linarith [hx.2,hL.1]) (show 0≤2*k by positivity)
      nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem planarTorusPerimeter_ge_strip_calibration
    {A : Set TransverseProduct} (hA : IsOpen A)
    (hin : ∀ y : TransverseProduct,y 0=0 →y∈A)
    (hout : ∀ y : TransverseProduct,y 0=((1/2 : ℝ) : AxisCircle) →y∉closure A)
    {e k : ℝ} (he : 0≤e) (hk : k∈Ico 0 1)
    (hedge : ∀ y∈closure A,y 1=((1/2 : ℝ) : AxisCircle) →2*‖y 0‖≤e) :
    ENNReal.ofReal (2*k*(volume.real A-e)+
      2*(∫ t in (-(1/2 : ℝ))..(1/2),Real.sqrt (1-(2*k*t)^2)))≤planarTorusPerimeter A := by
  let f : ℝ →ℝ := fun t ↦ Real.sqrt (1-(2*k*t)^2)
  have hf : Continuous f := (continuous_const.sub ((continuous_const.mul continuous_id).pow 2)).sqrt
  have hp : Continuous (fun z : ℝ ↦ ∫ t in (0 : ℝ)..z,f t) :=
    intervalIntegral.continuous_primitive (fun _ _ ↦ hf.intervalIntegrable _ _) 0
  have hI : Continuous (fun L : ℝ ↦ ∫ t in (-L)..L,f t) := by
    have heq (L : ℝ) : (∫ t in (-L)..L,f t)=(∫ t in (0 : ℝ)..L,f t)-(∫ t in (0 : ℝ)..(-L),f t) :=
      (intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)).symm
    simp_rw [heq]
    exact hp.sub (hp.comp continuous_neg)
  have happrox (ε : ℝ) (hε : 0<ε) :
      ENNReal.ofReal (2*k*(volume.real A-(e+ε))+2*(∫ t in (-(1/2 : ℝ))..(1/2),f t))≤planarTorusPerimeter A := by
    obtain ⟨δ,hδ,hcollar⟩ := planar_closed_edge_collar hedge hε
    let U : Set ℝ := {L | 0<L ∧1/2-L<δ ∧2*k*(1-L)<1}
    have hU : IsOpen U := (isOpen_lt continuous_const continuous_id).inter
      ((isOpen_lt (continuous_const.sub continuous_id) continuous_const).inter
        (isOpen_lt (continuous_const.mul (continuous_const.sub continuous_id)) continuous_const))
    have hhalf : (1/2 : ℝ)∈U := by
      change 0<(1/2 : ℝ) ∧1/2-1/2<δ ∧2*k*(1-1/2)<1
      constructor
      · norm_num
      constructor
      · simpa using hδ
      · nlinarith [hk.2]
    obtain ⟨η,hη,hηU⟩ := Metric.isOpen_iff.mp hU _ hhalf
    have hfinite (L : ℝ) (hL : L∈Ioo (1/2-η) (1/2)) :
        ENNReal.ofReal (2*k*(volume.real A-(e+ε))+2*(∫ t in (-L)..L,f t))≤planarTorusPerimeter A := by
      have hLU : L∈U := hηU (show dist L (1/2 : ℝ)<η from by
        rw [Real.dist_eq,abs_of_neg (by linarith [hL.2])]; linarith [hL.1])
      have hLL : L∈Ioo 0 (1/2) := ⟨hLU.1,hL.2⟩
      obtain ⟨β,hβ,pβ,hβ0,hβ1,hβcentral,hβsupport⟩ := exists_smooth_seam_probability hLL
      obtain ⟨v,hv,pv,hd,hcentral,hbound⟩ := exists_smooth_saw_primitive hβ pβ hβ0 hβ1 hLL hk.1 hβcentral
      have hvb (t : ℝ) : |v t|<1 := (hbound t).trans_lt hLU.2.2
      have hpos (t : ℝ) : 0<1-(v t)^2 := by
        nlinarith [hvb t,sq_abs (v t),abs_nonneg (v t)]
      let u : ℝ →ℝ := fun t ↦ Real.sqrt (1-(v t)^2)
      have hu : ContDiff ℝ (⊤ : ℕ∞) u := (contDiff_const.sub (hv.pow 2)).sqrt (fun t ↦ (hpos t).ne')
      have pu : Function.Periodic u 1 := fun t ↦ by dsimp only [u]; rw [pv t]
      have huv (t : ℝ) : (u t)^2+(v t)^2≤1 := by
        dsimp only [u]
        rw [Real.sq_sqrt (hpos t).le]
        linarith
      have hβC : Continuous (pβ.lift : AxisCircle →ℝ) := continuous_periodic_lift pβ hβ.continuous
      have hβC0 (t : AxisCircle) : 0≤pβ.lift t := by
        induction t using Quotient.inductionOn with | h t => exact hβ0 t
      have hβC1 : (∫ t : AxisCircle,pβ.lift t)=1 := by
        rw [←AddCircle.intervalIntegral_preimage (1 : ℝ) (0 : ℝ)]
        simpa only [zero_add,pβ.lift_coe] using hβ1
      have hβCS (t : AxisCircle) (ht : pβ.lift t≠0) : dist t ((1/2 : ℝ) : AxisCircle)<δ := by
        induction t using Quotient.inductionOn with
        | h t => exact (hβsupport t ht).trans hLU.2.1
      have hcal := planarTorusPerimeter_ge_strip_seam_calibration hA (closedCentralArc_isCompact L)
        hu hv pu pv (fun t ↦ Real.sqrt_nonneg _) huv (fun y hy _ ↦ hin y hy) hout
        hβC hβC0 hβC1 hk.1 (show 0≤e+ε by linarith)
        (fun t ↦ hd t) (fun y hy hn ↦ (hcollar y (subset_closure hy) (hβCS (y 1) hn)).le)
      have hi : (∫ t in closedCentralArc L,pu.lift t)=∫ t in (-L)..L,f t := by
        rw [integral_closedCentralArc ⟨hLL.1.le,hLL.2⟩]
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by linarith [hLL.1])] at ht
        change Real.sqrt (1-(v t)^2)=Real.sqrt (1-(2*k*t)^2)
        rw [hcentral t (abs_le.mpr ht)]
      rwa [hi] at hcal
    have hc : Continuous (fun L : ℝ ↦ ENNReal.ofReal (2*k*(volume.real A-(e+ε))+2*(∫ t in (-L)..L,f t))) :=
      ENNReal.continuous_ofReal.comp (continuous_const.add (continuous_const.mul hI))
    have hs : IsClosed {L : ℝ | ENNReal.ofReal (2*k*(volume.real A-(e+ε))+2*(∫ t in (-L)..L,f t))≤planarTorusPerimeter A} :=
      isClosed_le hc continuous_const
    have hh : (1/2 : ℝ)∈closure (Ioo (1/2-η) (1/2)) := by
      rw [closure_Ioo (by linarith : (1/2 : ℝ)-η≠1/2)]
      exact ⟨by linarith,le_rfl⟩
    exact closure_minimal (fun L hL ↦ hfinite L hL) hs hh
  have hc : Continuous (fun ε : ℝ ↦ ENNReal.ofReal
      (2*k*(volume.real A-(e+ε))+2*(∫ t in (-(1/2 : ℝ))..(1/2),f t))) :=
    ENNReal.continuous_ofReal.comp
      ((continuous_const.mul (continuous_const.sub (continuous_const.add continuous_id))).add continuous_const)
  have hs : IsClosed {ε : ℝ | ENNReal.ofReal
      (2*k*(volume.real A-(e+ε))+2*(∫ t in (-(1/2 : ℝ))..(1/2),f t))≤planarTorusPerimeter A} :=
    isClosed_le hc continuous_const
  have h0 : (0 : ℝ)∈closure (Ioi (0 : ℝ)) := by rw [closure_Ioi]; exact (le_rfl : (0 : ℝ)≤0)
  have hh := closure_minimal (fun ε hε ↦ happrox ε hε) hs h0
  change ENNReal.ofReal (2*k*(volume.real A-(e+0))+2*(∫ t in (-(1/2 : ℝ))..(1/2),f t))≤planarTorusPerimeter A at hh
  simpa only [add_zero] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma strip_sqrt_polynomial_lower {w : ℝ} (hw : w∈Icc 0 ((21/40 : ℝ)^2)) :
    1-w/2-w^2/5≤Real.sqrt (1-w) := by
  have hw2 : w^2≤((21/40 : ℝ)^2)^2 := by nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
  have hc : -3/20+w/5+w^2/25≤0 := by nlinarith [hw.2,hw2]
  have hh := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg w) hc
  apply Real.le_sqrt_of_sq_le
  nlinarith

lemma strip_round_integral_lower {k : ℝ} (hk : k∈Icc 0 (21/40 : ℝ)) :
    1-k^2/6-k^4/25≤∫ t in (-(1/2 : ℝ))..(1/2),Real.sqrt (1-(2*k*t)^2) := by
  let f : ℝ →ℝ := fun t ↦ 1-(2*k*t)^2/2-(2*k*t)^4/5
  have hf : Continuous f := (continuous_const.sub (((continuous_const.mul continuous_id).pow 2).div_const 2)).sub
    (((continuous_const.mul continuous_id).pow 4).div_const 5)
  have hg : Continuous (fun t : ℝ ↦ Real.sqrt (1-(2*k*t)^2)) :=
    (continuous_const.sub ((continuous_const.mul continuous_id).pow 2)).sqrt
  have hb := intervalIntegral.integral_mono_on (μ := volume) (show -(1/2 : ℝ)≤1/2 by norm_num)
    (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _) (fun t ht ↦ ?_)
  · have hpoly : f=(fun t : ℝ ↦ 1-(2*k^2)*t^2-((16/5)*k^4)*t^4) := by funext t; dsimp only [f]; ring
    have h2 : IntervalIntegrable (fun t : ℝ ↦ (2*k^2)*t^2) volume (-(1/2 : ℝ)) (1/2) :=
      (show Continuous (fun t : ℝ ↦ (2*k^2)*t^2) by fun_prop).intervalIntegrable _ _
    have h4 : IntervalIntegrable (fun t : ℝ ↦ ((16/5)*k^4)*t^4) volume (-(1/2 : ℝ)) (1/2) :=
      (show Continuous (fun t : ℝ ↦ ((16/5)*k^4)*t^4) by fun_prop).intervalIntegrable _ _
    rw [hpoly,intervalIntegral.integral_sub (intervalIntegrable_const.sub h2) h4,
      intervalIntegral.integral_sub intervalIntegrable_const h2,
      intervalIntegral.integral_const,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
      integral_pow,integral_pow] at hb
    norm_num at hb
    nlinarith [hb]
  · have hm : |2*k*t|≤21/40 := by
      calc
        _=2*k*|t| := by rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ)≤2),abs_of_nonneg hk.1]
        _≤2*k*(1/2) := mul_le_mul_of_nonneg_left (abs_le.mpr ht) (mul_nonneg (by norm_num) hk.1)
        _≤21/40 := by linarith [hk.2]
    have hw : (2*k*t)^2∈Icc 0 ((21/40 : ℝ)^2) := ⟨sq_nonneg _,by nlinarith [sq_abs (2*k*t),abs_nonneg (2*k*t)]⟩
    have hh := strip_sqrt_polynomial_lower hw
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [f]
    ring

theorem planarTorusPerimeter_ge_strip_gain
    {A : Set TransverseProduct} (hA : IsOpen A)
    (hin : ∀ y : TransverseProduct,y 0=0 →y∈A)
    (hout : ∀ y : TransverseProduct,y 0=((1/2 : ℝ) : AxisCircle) →y∉closure A)
    {e j : ℝ} (he : 0≤e) (hj : j∈Icc 0 (21/100 : ℝ))
    (hedge : ∀ y∈closure A,y 1=((1/2 : ℝ) : AxisCircle) →2*‖y 0‖≤e)
    (hgap : j≤volume.real A-e) :
    ENNReal.ofReal (2*(1+(27/20)*j^2))≤planarTorusPerimeter A := by
  let k : ℝ := (5/2)*j
  have hk : k∈Icc 0 (21/40 : ℝ) := by dsimp only [k]; constructor <;> linarith [hj.1,hj.2]
  have hcal := planarTorusPerimeter_ge_strip_calibration hA hin hout he ⟨hk.1,by linarith [hk.2]⟩ hedge
  have hint := strip_round_integral_lower hk
  have hj2 : j^2≤(21/100 : ℝ)^2 := by nlinarith [mul_nonneg hj.1 (sub_nonneg.mpr hj.2)]
  have hq : 0≤13/120-(25/16)*j^2 := by nlinarith [hj2]
  have hqq := mul_nonneg (sq_nonneg j) hq
  have ha := mul_le_mul_of_nonneg_left hgap hk.1
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hcal
  dsimp only [k] at hint ha ⊢
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_radial_strip_gain_first_oai {A : Set TransverseProduct} (hA : IsOpen A)
    (hd : PlanarRadialDownset A) (hin : planarAxisPoint (1/2)∈A)
    (hout : planarFirstAxisPoint (1/2)∉closure A)
    {e j : ℝ} (he : 0≤e) (hj : j∈Icc 0 (21/100 : ℝ))
    (hedge : ∀ y∈closure A,y 1=((1/2 : ℝ) : AxisCircle) →2*‖y 0‖≤e)
    (hgap : j≤volume.real A-e) :
    ENNReal.ofReal (2*(1+(27/20)*j^2))≤planarTorusPerimeter A := by
  apply planarTorusPerimeter_ge_strip_gain hA ?_ (planar_radial_empty_fiber hd hout) he hj hedge hgap
  intro y hy
  apply hd y (planarAxisPoint (1/2)) ?_ hin
  intro k
  fin_cases k
  · simp [hy,planarAxisPoint]
  · change ‖y 1‖≤‖((1/2 : ℝ) : AxisCircle)‖
    rw [axisCircle_norm_coe_small (by norm_num : |(1/2 : ℝ)|≤1/2),abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
    exact axisCircle_norm_le_half (y 1)

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.planar_radial_strip_gain_first_oai := @OAI.CubicTorus.planar_radial_strip_gain_first_oai
