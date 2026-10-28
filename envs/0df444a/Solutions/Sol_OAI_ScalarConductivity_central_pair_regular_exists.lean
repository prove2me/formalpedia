-- Prove2me | solution 1 for OAI.ScalarConductivity.central_pair_regular_exists
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:07:10.6674+00:00
-- url     : https://prove2.me/submissions/c7d4941f-447e-49a4-b6a4-90715720b061

import Mathlib
import Definitions.Def_Conductivity
import Definitions.Def_OAIQ059C005
import Definitions.Def_OAIQ059C006

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_IntervalTraceEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma interval_integral_sq_le {a b : ℝ} (hab : a≤b) {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ t in a..b, f t)^2≤(b-a)*(∫ t in a..b, f t^2) := by
  have h := integral_sq_le_mass_mul
    (μ := volume.restrict (Ioc a b)) (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((hf.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  simpa only [intervalIntegral.integral_of_le hab,Measure.restrict_apply_univ,
    Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using h

lemma smooth_interval_poincare_point {q : ℝ → ℝ}
    (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) {a b : ℝ} (hab : a≤b) :
    (q b-q a)^2≤(b-a)*(∫ t in a..b, (deriv q t)^2) := by
  have hd : Continuous (deriv q) := hq.continuous_deriv (by simp)
  have hFTC := intervalIntegral.integral_deriv_eq_sub
    (fun x _ => hq.differentiable (by simp) x) (hd.intervalIntegrable a b)
  rw [←hFTC]
  exact interval_integral_sq_le hab hd

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_IntervalMeanPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma smooth_interval_oscillation {q : ℝ → ℝ}
    (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) {a b x y : ℝ} (hab : a ≤ b)
    (hx : x∈Icc a b) (hy : y∈Icc a b) :
    (q x-q y)^2 ≤ (b-a)*(∫ t in a..b, (deriv q t)^2) := by
  have hd := hq.continuous_deriv (by simp)
  have hD : 0 ≤ ∫ t in a..b, (deriv q t)^2 :=
    intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
  have haux (u v : ℝ) (hu : u∈Icc a b) (hv : v∈Icc a b) (huv : u ≤ v) :
      (q v-q u)^2 ≤ (b-a)*(∫ t in a..b, (deriv q t)^2) := by
    have h := smooth_interval_poincare_point hq huv
    have hi : (∫ t in u..v, (deriv q t)^2) ≤ ∫ t in a..b, (deriv q t)^2 :=
      intervalIntegral.integral_mono_interval hu.1 huv hv.2
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) ((hd.pow 2).intervalIntegrable _ _)
    calc
      _ ≤ (v-u)*(∫ t in u..v, (deriv q t)^2) := h
      _ ≤ (v-u)*(∫ t in a..b, (deriv q t)^2) := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr huv)
      _ ≤ (b-a)*(∫ t in a..b, (deriv q t)^2) :=
        mul_le_mul_of_nonneg_right (by linarith [hu.1,hv.2]) hD
  rcases le_total x y with hxy|hyx
  · have he : (q x-q y)^2=(q y-q x)^2 := by ring
    rw [he]; exact haux x y hx hy hxy
  · exact haux y x hy hx hyx

theorem smooth_interval_mean_point {q : ℝ → ℝ}
    (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) {a b x : ℝ} (hab : a<b) (hx : x∈Icc a b) :
    (q x-(∫ t in a..b, q t)/(b-a))^2 ≤ (b-a)*(∫ t in a..b, (deriv q t)^2) := by
  let L := b-a
  let D := ∫ t in a..b, (deriv q t)^2
  let M := (∫ t in a..b, q t)/L
  have hL : 0<L := sub_pos.mpr hab
  have hcs := interval_integral_sq_le hab.le (continuous_const.sub hq.continuous : Continuous (fun t => q x-q t))
  have hi : (∫ t in a..b, (q x-q t)^2) ≤ L^2*D := by
    have hh := intervalIntegral.integral_mono_on (μ := volume) (f := fun t => (q x-q t)^2)
      (g := fun _ => L*D) hab.le
      ((continuous_const.sub hq.continuous).pow 2 |>.intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b)
      (fun t ht => smooth_interval_oscillation hq hab.le hx ht)
    rw [intervalIntegral.integral_const,smul_eq_mul] at hh
    dsimp [L] at hh ⊢
    nlinarith
  change (∫ t in a..b, q x-q t)^2 ≤ (b-a)*(∫ t in a..b, (q x-q t)^2) at hcs
  rw [intervalIntegral.integral_sub (f := fun _ => q x) (g := q)
    (continuous_const.intervalIntegrable a b) (hq.continuous.intervalIntegrable a b),
    intervalIntegral.integral_const,smul_eq_mul] at hcs
  have hM : L*M=∫ t in a..b, q t := mul_div_cancel₀ _ hL.ne'
  change (q x-M)^2 ≤ L*D
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hL)).mp
  have hc : (L*q x-L*M)^2 ≤ L*(L^2*D) := by
    rw [hM]
    exact hcs.trans (mul_le_mul_of_nonneg_left hi hL.le)
  nlinarith

lemma smooth_interval_mean_poincare {q : ℝ → ℝ}
    (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) {a b : ℝ} (hab : a<b) :
    (∫ x in a..b, (q x-(∫ t in a..b, q t)/(b-a))^2) ≤
      (b-a)^2*(∫ t in a..b, (deriv q t)^2) := by
  have hi := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun x => (q x-(∫ t in a..b, q t)/(b-a))^2)
    (g := fun _ => (b-a)*(∫ t in a..b, (deriv q t)^2)) hab.le
    ((hq.continuous.sub continuous_const).pow 2 |>.intervalIntegrable a b)
    (continuous_const.intervalIntegrable a b)
    (fun x hx => smooth_interval_mean_point hq hab hx)
  rw [intervalIntegral.integral_const,smul_eq_mul] at hi
  nlinarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_UnitBoxAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace G] in
lemma unitAverage_eq_interval (f : ℝ → G) :
    unitAverage f = ∫ t in (0:ℝ)..1, f t := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  exact integral_Icc_eq_integral_Ioc

lemma unitAverage_const (c : G) : unitAverage (fun _ => c)=c := by
  rw [unitAverage_eq_interval,intervalIntegral.integral_const]
  simp

omit [CompleteSpace G] in
lemma unitAverage_add {f g : ℝ → G} (hf : Continuous f) (hg : Continuous g) :
    unitAverage (fun t => f t+g t)=unitAverage f+unitAverage g :=
  integral_add hf.integrableOn_Icc hg.integrableOn_Icc

lemma unitAverage_mul (c : ℝ) (f : ℝ → ℝ) :
    unitAverage (fun t => c*f t)=c*unitAverage f := integral_const_mul c f

lemma unitAverage_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t∈Icc (0:ℝ) 1, f t ≤ g t) : unitAverage f ≤ unitAverage g := by
  apply integral_mono_ae hf.integrableOn_Icc hg.integrableOn_Icc
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact h t ht

lemma unitAverage_nonneg {f : ℝ → ℝ} (hf : ∀ t∈Icc (0:ℝ) 1, 0 ≤ f t) :
    0 ≤ unitAverage f := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hf t ht

lemma unitAverage_sq_le {f : ℝ → ℝ} (hf : Continuous f) :
    (unitAverage f)^2 ≤ unitAverage (fun t => (f t)^2) := by
  simpa only [unitAverage_eq_interval,sub_zero,one_mul] using
    interval_integral_sq_le (by norm_num : (0:ℝ) ≤ 1) hf

omit [NormedSpace ℝ E] [CompleteSpace G] in
lemma continuous_unitAverage {f : E×ℝ → G} (hf : Continuous f) :
    Continuous (fun x => unitAverage (fun t => f (x,t))) :=
  by
    exact continuous_parametric_integral_of_continuous (f := fun x t => f (x,t)) hf isCompact_Icc

lemma contDiff_unitAverage {f : E×ℝ → G} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => unitAverage (fun t => f (x,t))) :=
  contDiff_compact_integral hf isCompact_Icc

omit [CompleteSpace G] in
lemma fderiv_unitAverage {f : E×ℝ → G} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (x v : E) :
    fderiv ℝ (fun y => unitAverage (fun t => f (y,t))) x v =
      unitAverage (fun t => fderiv ℝ f (x,t) (v,0)) := by
  let D : E×ℝ → E →L[ℝ] G := fun z =>
    (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hD : Continuous D := (hf.fderiv_right (m := 0) (by simp)).continuous.clm_comp continuous_const
  have hd (y : E) (t : ℝ) : HasFDerivAt (fun w => f (w,t)) (D (y,t)) y := by
    exact ((hf.differentiable (by simp) (y,t)).hasFDerivAt).comp y
      ((hasFDerivAt_id y).prodMk (hasFDerivAt_const t y))
  have hi := hasFDerivAt_compact_integral (μ := volume) hf.continuous hD hd
    (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)) x
  change (fderiv ℝ (fun y => ∫ t in Icc (0:ℝ) 1, f (y,t)) x) v = _
  rw [hi.fderiv]
  exact ContinuousLinearMap.integral_apply (hD.comp (continuous_const.prodMk continuous_id) |>.integrableOn_Icc) v

lemma unitAverage_mean_poincare {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    unitAverage (fun t => (f t-unitAverage f)^2) ≤
      unitAverage (fun t => (deriv f t)^2) := by
  simpa only [unitAverage_eq_interval,sub_zero,one_pow,one_mul,div_one] using
    smooth_interval_mean_poincare hf (by norm_num : (0:ℝ)<1)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_UnitSquarePoincare
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

lemma continuous_squarePartial {f : ℝ×ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (v : ℝ×ℝ) : Continuous (squarePartial f v) :=
  (hf.fderiv_right (m := 0) (by simp)).continuous.clm_apply continuous_const

lemma deriv_fiber_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E×ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (y : E) (x : ℝ) :
    deriv (fun t => f (y,t)) x=fderiv ℝ f (y,x) (0,1) := by
  exact (((hf.differentiable (by simp) (y,x)).hasFDerivAt).comp_hasDerivAt x
    ((hasDerivAt_const x y).prodMk (hasDerivAt_id x))).deriv

theorem smooth_unit_square_poincare {f : ℝ×ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    unitSquareAverage (fun z => (f z-unitSquareAverage f)^2) ≤
      2*unitSquareAverage (fun z => (squarePartial f (1,0) z)^2+
        (squarePartial f (0,1) z)^2) := by
  let m : ℝ → ℝ := fun y => unitAverage (fun x => f (y,x))
  let d₁ := squarePartial f (1,0)
  let d₂ := squarePartial f (0,1)
  have hm : ContDiff ℝ (↑(⊤ : ℕ∞)) m := contDiff_unitAverage hf
  have hd₁ : Continuous d₁ := continuous_squarePartial hf _
  have hd₂ : Continuous d₂ := continuous_squarePartial hf _
  have hd₁av : Continuous (fun y => unitAverage (fun x => (d₁ (y,x))^2)) :=
    continuous_unitAverage (hd₁.pow 2)
  have hd₂av : Continuous (fun y => unitAverage (fun x => (d₂ (y,x))^2)) :=
    continuous_unitAverage (hd₂.pow 2)
  have hd (y : ℝ) : deriv m y=unitAverage (fun x => d₁ (y,x)) := by
    exact fderiv_unitAverage hf y 1
  have hdm (y : ℝ) : (deriv m y)^2 ≤ unitAverage (fun x => (d₁ (y,x))^2) := by
    rw [hd]
    exact unitAverage_sq_le (hd₁.comp (continuous_const.prodMk continuous_id))
  have hvarm : unitAverage (fun y => (m y-unitAverage m)^2) ≤
      unitAverage (fun y => unitAverage (fun x => (d₁ (y,x))^2)) :=
    (unitAverage_mean_poincare hm).trans
      (unitAverage_mono ((hm.continuous_deriv (by simp)).pow 2) hd₁av (fun y _ => hdm y))
  have hvarf (y : ℝ) : unitAverage (fun x => (f (y,x)-m y)^2) ≤
      unitAverage (fun x => (d₂ (y,x))^2) := by
    have h := unitAverage_mean_poincare
      (hf.comp (contDiff_const.prodMk contDiff_id) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => f (y,x)))
    change unitAverage (fun x => (f (y,x)-m y)^2) ≤
      unitAverage (fun x => (deriv (fun t => f (y,t)) x)^2) at h
    simpa only [deriv_fiber_right hf, d₂,squarePartial] using h
  have hp (y : ℝ) : unitAverage (fun x => (f (y,x)-unitAverage m)^2) ≤
      2*unitAverage (fun x => (d₂ (y,x))^2)+2*(m y-unitAverage m)^2 := by
    have hc := hf.continuous.comp (continuous_const.prodMk continuous_id : Continuous (fun x : ℝ => (y,x)))
    have h := unitAverage_mono ((hc.sub continuous_const).pow 2)
      (((continuous_const.mul ((hc.sub continuous_const).pow 2))).add continuous_const)
      (fun x _ => show (f (y,x)-unitAverage m)^2 ≤
        2*(f (y,x)-m y)^2+2*(m y-unitAverage m)^2 by nlinarith [sq_nonneg (f (y,x)-2*m y+unitAverage m)])
    change unitAverage (fun x => (f (y,x)-unitAverage m)^2) ≤
      unitAverage (fun x => 2*(f (y,x)-m y)^2+2*(m y-unitAverage m)^2) at h
    rw [unitAverage_add (f := fun x => 2*(f (y,x)-m y)^2)
      (g := fun _ => 2*(m y-unitAverage m)^2)
      (continuous_const.mul ((hc.sub continuous_const).pow 2)) continuous_const,
      unitAverage_mul,unitAverage_const] at h
    exact h.trans (by linarith [hvarf y])
  have hi := unitAverage_mono
    (continuous_unitAverage ((hf.continuous.sub continuous_const).pow 2))
    ((continuous_const.mul hd₂av).add (continuous_const.mul ((hm.continuous.sub continuous_const).pow 2)))
    (fun y _ => hp y)
  change unitAverage (fun y => unitAverage (fun x => (f (y,x)-unitAverage m)^2)) ≤
    unitAverage (fun y => 2*unitAverage (fun x => (d₂ (y,x))^2)+2*(m y-unitAverage m)^2) at hi
  rw [unitAverage_add (f := fun y => 2*unitAverage (fun x => (d₂ (y,x))^2))
      (g := fun y => 2*(m y-unitAverage m)^2) (continuous_const.mul hd₂av)
      (continuous_const.mul ((hm.continuous.sub continuous_const).pow 2)),
    unitAverage_mul,unitAverage_mul] at hi
  have he : unitSquareAverage (fun z => (d₁ z)^2+(d₂ z)^2)=
      unitAverage (fun y => unitAverage (fun x => (d₁ (y,x))^2))+
      unitAverage (fun y => unitAverage (fun x => (d₂ (y,x))^2)) := by
    dsimp [unitSquareAverage]
    have hh (y : ℝ) := unitAverage_add
      (f := fun x => (d₁ (y,x))^2) (g := fun x => (d₂ (y,x))^2)
      (hd₁.comp (continuous_const.prodMk continuous_id) |>.pow 2)
      (hd₂.comp (continuous_const.prodMk continuous_id) |>.pow 2)
    simp_rw [hh]
    exact unitAverage_add hd₁av hd₂av
  change unitAverage (fun y => unitAverage (fun x => (f (y,x)-unitAverage m)^2)) ≤
    2*unitSquareAverage (fun z => (d₁ z)^2+(d₂ z)^2)
  rw [he]
  linarith

lemma unitSquareAverage_add {f g : ℝ×ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    unitSquareAverage (fun z => f z+g z)=unitSquareAverage f+unitSquareAverage g := by
  dsimp [unitSquareAverage]
  have hh (y : ℝ) := unitAverage_add (f := fun x => f (y,x)) (g := fun x => g (y,x))
    (hf.comp (continuous_const.prodMk continuous_id)) (hg.comp (continuous_const.prodMk continuous_id))
  simp_rw [hh]
  exact unitAverage_add (continuous_unitAverage hf) (continuous_unitAverage hg)

lemma unitSquareAverage_mul (c : ℝ) (f : ℝ×ℝ → ℝ) :
    unitSquareAverage (fun z => c*f z)=c*unitSquareAverage f := by
  simp only [unitSquareAverage,unitAverage_mul]

lemma unitSquareAverage_mono {f g : ℝ×ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ y∈Icc (0:ℝ) 1, ∀ x∈Icc (0:ℝ) 1, f (y,x) ≤ g (y,x)) :
    unitSquareAverage f ≤ unitSquareAverage g := by
  apply unitAverage_mono (continuous_unitAverage hf) (continuous_unitAverage hg)
  intro y hy
  exact unitAverage_mono (hf.comp (continuous_const.prodMk continuous_id))
    (hg.comp (continuous_const.prodMk continuous_id)) (fun x hx => h y hy x hx)

lemma unitSquareAverage_nonneg {f : ℝ×ℝ → ℝ}
    (h : ∀ y∈Icc (0:ℝ) 1, ∀ x∈Icc (0:ℝ) 1, 0 ≤ f (y,x)) :
    0 ≤ unitSquareAverage f :=
  unitAverage_nonneg (fun y hy => unitAverage_nonneg (fun x hx => h y hy x hx))

theorem smooth_unit_cube_poincare {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    unitCubeAverage (fun z => (f z-unitCubeAverage f)^2) ≤
      4*unitCubeAverage (fun z =>
        (cubePartial f ((1,0),0) z)^2+(cubePartial f ((0,1),0) z)^2+
        (cubePartial f ((0,0),1) z)^2) := by
  let m : ℝ×ℝ → ℝ := fun y => unitAverage (fun x => f (y,x))
  let d₁ := cubePartial f ((1,0),0)
  let d₂ := cubePartial f ((0,1),0)
  let d₃ := cubePartial f ((0,0),1)
  have hm : ContDiff ℝ (↑(⊤ : ℕ∞)) m := contDiff_unitAverage hf
  have hd₁ : Continuous d₁ := continuous_cubePartial hf _
  have hd₂ : Continuous d₂ := continuous_cubePartial hf _
  have hd₃ : Continuous d₃ := continuous_cubePartial hf _
  have ha₁ := continuous_unitAverage (hd₁.pow 2)
  have ha₂ := continuous_unitAverage (hd₂.pow 2)
  have ha₃ := continuous_unitAverage (hd₃.pow 2)
  have hdm₁ (y : ℝ×ℝ) : (squarePartial m (1,0) y)^2 ≤
      unitAverage (fun x => (d₁ (y,x))^2) := by
    change (fderiv ℝ m y (1,0))^2 ≤ _
    rw [fderiv_unitAverage hf]
    exact unitAverage_sq_le (hd₁.comp (continuous_const.prodMk continuous_id))
  have hdm₂ (y : ℝ×ℝ) : (squarePartial m (0,1) y)^2 ≤
      unitAverage (fun x => (d₂ (y,x))^2) := by
    change (fderiv ℝ m y (0,1))^2 ≤ _
    rw [fderiv_unitAverage hf]
    exact unitAverage_sq_le (hd₂.comp (continuous_const.prodMk continuous_id))
  have hvarm : unitSquareAverage (fun y => (m y-unitSquareAverage m)^2) ≤
      2*(unitCubeAverage (fun z => (d₁ z)^2)+unitCubeAverage (fun z => (d₂ z)^2)) := by
    have hi := unitSquareAverage_mono
      (((continuous_squarePartial hm (1,0)).pow 2).add ((continuous_squarePartial hm (0,1)).pow 2))
      (ha₁.add ha₂) (fun y _ x _ => add_le_add (hdm₁ (y,x)) (hdm₂ (y,x)))
    change unitSquareAverage (fun y => (squarePartial m (1,0) y)^2+(squarePartial m (0,1) y)^2) ≤
      unitSquareAverage (fun y => unitAverage (fun x => (d₁ (y,x))^2)+unitAverage (fun x => (d₂ (y,x))^2)) at hi
    rw [unitSquareAverage_add (f := fun y => unitAverage (fun x => (d₁ (y,x))^2))
      (g := fun y => unitAverage (fun x => (d₂ (y,x))^2)) ha₁ ha₂] at hi
    exact (smooth_unit_square_poincare hm).trans (mul_le_mul_of_nonneg_left hi (by norm_num))
  have hvarf (y : ℝ×ℝ) : unitAverage (fun x => (f (y,x)-m y)^2) ≤
      unitAverage (fun x => (d₃ (y,x))^2) := by
    have hi := unitAverage_mean_poincare
      (hf.comp (contDiff_const.prodMk contDiff_id) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => f (y,x)))
    change unitAverage (fun x => (f (y,x)-m y)^2) ≤ unitAverage (fun x => (deriv (fun t => f (y,t)) x)^2) at hi
    simpa only [deriv_fiber_right hf,d₃,cubePartial,Prod.zero_eq_mk] using hi
  have hp (y : ℝ×ℝ) : unitAverage (fun x => (f (y,x)-unitSquareAverage m)^2) ≤
      2*unitAverage (fun x => (d₃ (y,x))^2)+2*(m y-unitSquareAverage m)^2 := by
    have hc := hf.continuous.comp (continuous_const.prodMk continuous_id : Continuous (fun x : ℝ => (y,x)))
    have hi := unitAverage_mono ((hc.sub continuous_const).pow 2)
      ((continuous_const.mul ((hc.sub continuous_const).pow 2)).add continuous_const)
      (fun x _ => show (f (y,x)-unitSquareAverage m)^2 ≤
        2*(f (y,x)-m y)^2+2*(m y-unitSquareAverage m)^2 by
          nlinarith [sq_nonneg (f (y,x)-2*m y+unitSquareAverage m)])
    change unitAverage (fun x => (f (y,x)-unitSquareAverage m)^2) ≤
      unitAverage (fun x => 2*(f (y,x)-m y)^2+2*(m y-unitSquareAverage m)^2) at hi
    rw [unitAverage_add (f := fun x => 2*(f (y,x)-m y)^2)
      (g := fun _ => 2*(m y-unitSquareAverage m)^2)
      (continuous_const.mul ((hc.sub continuous_const).pow 2)) continuous_const,
      unitAverage_mul,unitAverage_const] at hi
    exact hi.trans (by linarith [hvarf y])
  have hi := unitSquareAverage_mono
    (continuous_unitAverage ((hf.continuous.sub continuous_const).pow 2))
    ((continuous_const.mul ha₃).add (continuous_const.mul ((hm.continuous.sub continuous_const).pow 2)))
    (fun y _ x _ => hp (y,x))
  change unitSquareAverage (fun y => unitAverage (fun x => (f (y,x)-unitSquareAverage m)^2)) ≤
    unitSquareAverage (fun y => 2*unitAverage (fun x => (d₃ (y,x))^2)+2*(m y-unitSquareAverage m)^2) at hi
  rw [unitSquareAverage_add (f := fun y => 2*unitAverage (fun x => (d₃ (y,x))^2))
    (g := fun y => 2*(m y-unitSquareAverage m)^2) (continuous_const.mul ha₃)
    (continuous_const.mul ((hm.continuous.sub continuous_const).pow 2)),
    unitSquareAverage_mul,unitSquareAverage_mul] at hi
  have he : unitCubeAverage (fun z => (d₁ z)^2+(d₂ z)^2+(d₃ z)^2)=
      unitCubeAverage (fun z => (d₁ z)^2)+unitCubeAverage (fun z => (d₂ z)^2)+
      unitCubeAverage (fun z => (d₃ z)^2) := by
    dsimp [unitCubeAverage]
    have hh (y : ℝ×ℝ) := unitAverage_add (f := fun x => (d₁ (y,x))^2+(d₂ (y,x))^2)
      (g := fun x => (d₃ (y,x))^2)
      ((hd₁.comp (continuous_const.prodMk continuous_id) |>.pow 2).add
        (hd₂.comp (continuous_const.prodMk continuous_id) |>.pow 2))
      (hd₃.comp (continuous_const.prodMk continuous_id) |>.pow 2)
    have hh' (y : ℝ×ℝ) := unitAverage_add (f := fun x => (d₁ (y,x))^2)
      (g := fun x => (d₂ (y,x))^2)
      (hd₁.comp (continuous_const.prodMk continuous_id) |>.pow 2)
      (hd₂.comp (continuous_const.prodMk continuous_id) |>.pow 2)
    simp_rw [hh,hh']
    rw [unitSquareAverage_add (f := fun y => unitAverage (fun x => (d₁ (y,x))^2)+unitAverage (fun x => (d₂ (y,x))^2))
      (g := fun y => unitAverage (fun x => (d₃ (y,x))^2)) (ha₁.add ha₂) ha₃,
      unitSquareAverage_add (f := fun y => unitAverage (fun x => (d₁ (y,x))^2))
      (g := fun y => unitAverage (fun x => (d₂ (y,x))^2)) ha₁ ha₂]
  have hnonneg : 0 ≤ unitCubeAverage (fun z => (d₃ z)^2) :=
    unitSquareAverage_nonneg (fun y _ x _ => unitAverage_nonneg (fun t _ => sq_nonneg _))
  change unitSquareAverage (fun y => unitAverage (fun x => (f (y,x)-unitSquareAverage m)^2)) ≤
    4*unitCubeAverage (fun z => (d₁ z)^2+(d₂ z)^2+(d₃ z)^2)
  rw [he]
  change unitSquareAverage (fun y => unitAverage (fun x => (f (y,x)-unitSquareAverage m)^2)) ≤
    2*unitCubeAverage (fun z => (d₃ z)^2)+2*unitSquareAverage (fun y => (m y-unitSquareAverage m)^2) at hi
  linarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_AffineBoxPoincare
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

lemma boxRescale_smooth (a r : Box3) : ContDiff ℝ (↑(⊤ : ℕ∞)) (boxRescale a r) := by
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : Box3 =>
    ((a.1.1+r.1.1*z.1.1,a.1.2+r.1.2*z.1.2),a.2+r.2*z.2))
  fun_prop

lemma boxRescale_fderiv (a r z v : Box3) :
    fderiv ℝ (boxRescale a r) z v=((r.1.1*v.1.1,r.1.2*v.1.2),r.2*v.2) := by
  let D : Box3 →L[ℝ] Box3 :=
    ((r.1.1 • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) ℝ)).prod
      (r.1.2 • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) ℝ))).prod
      (r.2 • ContinuousLinearMap.snd ℝ (ℝ×ℝ) ℝ)
  have he : boxRescale a r=fun z => a+D z := by rfl
  rw [he,fderiv_const_add,D.fderiv]
  rfl

lemma box_partial_one {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a r z : Box3) :
    cubePartial (f ∘ boxRescale a r) ((1,0),0) z=
      r.1.1*cubePartial f ((1,0),0) (boxRescale a r z) := by
  rw [cubePartial,fderiv_comp z (hf.differentiable (by simp) _) ((boxRescale_smooth a r).differentiable (by simp) _)]
  change fderiv ℝ f (boxRescale a r z) (fderiv ℝ (boxRescale a r) z ((1,0),0)) = _
  rw [boxRescale_fderiv]
  have he : ((r.1.1*(1:ℝ),r.1.2*0),r.2*0)=r.1.1 • (((1,0),0) : Box3) := by simp
  rw [he,map_smul]
  rfl

lemma box_partial_two {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a r z : Box3) :
    cubePartial (f ∘ boxRescale a r) ((0,1),0) z=
      r.1.2*cubePartial f ((0,1),0) (boxRescale a r z) := by
  rw [cubePartial,fderiv_comp z (hf.differentiable (by simp) _) ((boxRescale_smooth a r).differentiable (by simp) _)]
  change fderiv ℝ f (boxRescale a r z) (fderiv ℝ (boxRescale a r) z ((0,1),0)) = _
  rw [boxRescale_fderiv]
  have he : ((r.1.1*(0:ℝ),r.1.2*1),r.2*0)=r.1.2 • (((0,1),0) : Box3) := by simp
  rw [he,map_smul]
  rfl

lemma box_partial_three {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a r z : Box3) :
    cubePartial (f ∘ boxRescale a r) ((0,0),1) z=
      r.2*cubePartial f ((0,0),1) (boxRescale a r z) := by
  rw [cubePartial,fderiv_comp z (hf.differentiable (by simp) _) ((boxRescale_smooth a r).differentiable (by simp) _)]
  change fderiv ℝ f (boxRescale a r z) (fderiv ℝ (boxRescale a r) z ((0,0),1)) = _
  rw [boxRescale_fderiv]
  have he : ((r.1.1*(0:ℝ),r.1.2*0),r.2*1)=r.2 • (((0,0),1) : Box3) := by simp
  rw [he,map_smul]
  rfl

theorem smooth_box_poincare {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a r : Box3) :
    boxAverage a r (fun z => (f z-boxAverage a r f)^2) ≤
      4*boxAverage a r (fun z =>
        r.1.1^2*(cubePartial f ((1,0),0) z)^2+
        r.1.2^2*(cubePartial f ((0,1),0) z)^2+
        r.2^2*(cubePartial f ((0,0),1) z)^2) := by
  have h := smooth_unit_cube_poincare (hf.comp (boxRescale_smooth a r))
  change unitCubeAverage (fun z => (f (boxRescale a r z)-boxAverage a r f)^2) ≤
    4*unitCubeAverage (fun z => _) at h
  simpa only [box_partial_one hf,box_partial_two hf,box_partial_three hf,mul_pow,boxAverage] using h

lemma isCompact_closedBox (a r : Box3) : IsCompact (closedBox a r) :=
  (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc

lemma unitAverage_comp_affine (f : ℝ → ℝ) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    unitAverage (fun t => f (a+r*t))=r⁻¹*(∫ x in Icc a (a+r), f x) := by
  rw [unitAverage_eq_interval]
  have h := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) f hr.ne' a
  simp only [mul_zero,mul_one,zero_add,smul_eq_mul] at h
  rw [add_comm r a,intervalIntegral.integral_of_le (by linarith : a≤a+r),
    ← integral_Icc_eq_integral_Ioc] at h
  simpa only [add_comm a] using h

lemma box_volume_integral_iterated {f : Box3 → ℝ} (hf : Continuous f) (a r : Box3) :
    (∫ z in closedBox a r, f z)=
      ∫ x in Icc a.1.1 (a.1.1+r.1.1), ∫ y in Icc a.1.2 (a.1.2+r.1.2),
        ∫ t in Icc a.2 (a.2+r.2), f ((x,y),t) := by
  have hc : Continuous (fun p : ℝ×ℝ => ∫ t in Icc a.2 (a.2+r.2), f (p,t)) :=
    continuous_parametric_integral_of_continuous (f := fun p t => f (p,t)) hf isCompact_Icc
  calc
    _ = ∫ p in Icc a.1.1 (a.1.1+r.1.1) ×ˢ Icc a.1.2 (a.1.2+r.1.2),
        ∫ t in Icc a.2 (a.2+r.2), f (p,t) :=
      setIntegral_prod f (hf.continuousOn.integrableOn_compact (isCompact_closedBox a r))
    _ = _ := setIntegral_prod _ (hc.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc))

lemma boxAverage_eq_integral {f : Box3 → ℝ} (hf : Continuous f) (a r : Box3)
    (h₁ : 0 < r.1.1) (h₂ : 0 < r.1.2) (h₃ : 0 < r.2) :
    boxAverage a r f=(r.1.1*r.1.2*r.2)⁻¹*(∫ z in closedBox a r, f z) := by
  have hx (v w : ℝ) := unitAverage_comp_affine
    (fun t => f ((a.1.1+r.1.1*v,a.1.2+r.1.2*w),t)) a.2 h₃
  have hy (v : ℝ) := unitAverage_comp_affine
    (fun w => ∫ t in Icc a.2 (a.2+r.2), f ((a.1.1+r.1.1*v,w),t)) a.1.2 h₂
  have hz := unitAverage_comp_affine
    (fun v => ∫ w in Icc a.1.2 (a.1.2+r.1.2),
      ∫ t in Icc a.2 (a.2+r.2), f ((v,w),t)) a.1.1 h₁
  simp only [boxAverage,unitCubeAverage,unitSquareAverage,boxRescale]
  simp_rw [hx,unitAverage_mul,hy,unitAverage_mul,hz]
  rw [box_volume_integral_iterated hf,mul_inv,mul_inv]
  ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_OverlapPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

lemma localVariance_mono {Q R : Set X} {f : X → ℝ} {m : ℝ}
    (h : IntegrableOn (fun x => (f x-m)^2) R μ) (hQR : Q⊆R) :
    localVariance μ Q f m ≤ localVariance μ R f m :=
  setIntegral_mono_set h (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall (fun _ hx => hQR hx))

lemma overlap_means_bound {Q R : Set X} {f : X → ℝ} {a b : ℝ}
    (hfQ : IntegrableOn (fun x => (f x-a)^2) Q μ)
    (hfR : IntegrableOn (fun x => (f x-b)^2) R μ)
    (hfin : μ (Q∩R) ≠ ⊤) :
    (μ.real (Q∩R))*(a-b)^2 ≤
      2*localVariance μ Q f a+2*localVariance μ R f b := by
  let : IsFiniteMeasure (μ.restrict (Q∩R)) := ⟨by simpa using hfin.lt_top⟩
  have hQ := hfQ.mono_set (inter_subset_left : Q∩R⊆Q)
  have hR := hfR.mono_set (inter_subset_right : Q∩R⊆R)
  have hi := integral_mono (μ := μ.restrict (Q∩R)) (integrable_const ((a-b)^2))
    ((hQ.const_mul 2).add (hR.const_mul 2))
    (fun x => show (a-b)^2 ≤ 2*(f x-a)^2+2*(f x-b)^2 by
      nlinarith [sq_nonneg (2*f x-a-b)])
  change (∫ x in Q∩R, (a-b)^2 ∂μ) ≤ ∫ x in Q∩R, 2*(f x-a)^2+2*(f x-b)^2 ∂μ at hi
  rw [integral_add (hQ.const_mul 2) (hR.const_mul 2),integral_const_mul,integral_const_mul,
    integral_const] at hi
  simp only [measureReal_def,Measure.restrict_apply_univ,smul_eq_mul] at hi
  apply hi.trans
  exact add_le_add (mul_le_mul_of_nonneg_left (localVariance_mono μ hfQ inter_subset_left) (by norm_num))
    (mul_le_mul_of_nonneg_left (localVariance_mono μ hfR inter_subset_right) (by norm_num))

lemma localVariance_change_mean {Q : Set X} {f : X → ℝ} {a b : ℝ}
    (hf : IntegrableOn (fun x => (f x-b)^2) Q μ)
    (hfa : IntegrableOn (fun x => (f x-a)^2) Q μ) (hfin : μ Q≠⊤) :
    localVariance μ Q f a ≤ 2*localVariance μ Q f b+2*(μ.real Q)*(b-a)^2 := by
  let : IsFiniteMeasure (μ.restrict Q) := ⟨by simpa using hfin.lt_top⟩
  have hi := integral_mono (μ := μ.restrict Q) hfa
    ((hf.const_mul 2).add (integrable_const (2*(b-a)^2)))
    (fun x => show (f x-a)^2 ≤ 2*(f x-b)^2+2*(b-a)^2 by
      nlinarith [sq_nonneg (f x-2*b+a)])
  change (∫ x in Q, (f x-a)^2 ∂μ) ≤ ∫ x in Q, 2*(f x-b)^2+2*(b-a)^2 ∂μ at hi
  rw [integral_add (hf.const_mul 2) (integrable_const _),integral_const_mul,integral_const] at hi
  simp only [measureReal_def,Measure.restrict_apply_univ,smul_eq_mul] at hi
  change localVariance μ Q f a ≤ 2*localVariance μ Q f b+μ.real Q*(2*(b-a)^2) at hi
  nlinarith

lemma localVariance_union_le {Q R : Set X} {f : X → ℝ} {a : ℝ}
    (hfQ : IntegrableOn (fun x => (f x-a)^2) Q μ)
    (hfR : IntegrableOn (fun x => (f x-a)^2) R μ) :
    localVariance μ (Q∪R) f a ≤ localVariance μ Q f a+localVariance μ R f a := by
  change (∫ x, (f x-a)^2 ∂μ.restrict (Q∪R)) ≤ _
  apply le_trans (integral_mono_measure (Measure.restrict_union_le (μ := μ) Q R)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) (Integrable.add_measure hfQ hfR))
  rw [integral_add_measure hfQ hfR]
  exact le_rfl

theorem overlap_poincare_glue {Q R : Set X} {f : X → ℝ} {a b E A B : ℝ}
    (_ : 0≤E) (_ : 0≤A) (_ : 0≤B)
    (hfinQ : μ Q≠⊤) (hfinR : μ R≠⊤) (hpos : 0<μ.real (Q∩R))
    (hfQ : IntegrableOn (fun x => (f x-a)^2) Q μ)
    (hfR : IntegrableOn (fun x => (f x-b)^2) R μ)
    (hfRa : IntegrableOn (fun x => (f x-a)^2) R μ)
    (hQa : localVariance μ Q f a≤A*E) (hRb : localVariance μ R f b≤B*E) :
    localVariance μ (Q∪R) f a ≤
      (A+2*B+4*(μ.real R)/(μ.real (Q∩R))*(A+B))*E := by
  have hfinQR : μ (Q∩R)≠⊤ := ne_top_of_le_ne_top hfinQ (measure_mono inter_subset_left)
  have hi := overlap_means_bound μ hfQ hfR hfinQR
  have hid : (a-b)^2 ≤ 2*(A+B)*E/(μ.real (Q∩R)) := by
    apply (le_div_iff₀ hpos).2
    nlinarith
  have hc := localVariance_change_mean μ hfR hfRa hfinR
  have hμ : 0≤μ.real R := ENNReal.toReal_nonneg
  have hmul := mul_le_mul_of_nonneg_left hid (show 0≤2*μ.real R by positivity)
  have hu := localVariance_union_le μ hfQ hfRa
  have hs : (b-a)^2=(a-b)^2 := by ring
  rw [hs] at hc
  calc localVariance μ (Q∪R) f a
      ≤ A*E+2*B*E+2*μ.real R*(2*(A+B)*E/μ.real (Q∩R)) := by linarith
    _ = (A+2*B+4*(μ.real R)/(μ.real (Q∩R))*(A+B))*E := by ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_BoxEnergyPoincare
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

lemma continuous_cubeEnergyDensity {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) : Continuous (cubeEnergyDensity f) :=
  (((continuous_cubePartial hf _).pow 2).add ((continuous_cubePartial hf _).pow 2)).add
    ((continuous_cubePartial hf _).pow 2)

lemma cubeEnergyDensity_nonneg (f : Box3 → ℝ) (z : Box3) : 0 ≤ cubeEnergyDensity f z := by
  unfold cubeEnergyDensity; positivity

theorem smooth_box_volume_poincare {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a r : Box3)
    (h₁ : 0 < r.1.1) (h₂ : 0 < r.1.2) (h₃ : 0 < r.2) :
    localVariance volume (closedBox a r) f (boxAverage a r f) ≤
      (4*(r.1.1^2+r.1.2^2+r.2^2))*(∫ z in closedBox a r, cubeEnergyDensity f z) := by
  let R := r.1.1^2+r.1.2^2+r.2^2
  let e : Box3 → ℝ := fun z => r.1.1^2*(cubePartial f ((1,0),0) z)^2+
    r.1.2^2*(cubePartial f ((0,1),0) z)^2+r.2^2*(cubePartial f ((0,0),1) z)^2
  have he : Continuous e :=
    ((continuous_const.mul ((continuous_cubePartial hf _).pow 2)).add
      (continuous_const.mul ((continuous_cubePartial hf _).pow 2))).add
        (continuous_const.mul ((continuous_cubePartial hf _).pow 2))
  have hP := smooth_box_poincare hf a r
  rw [boxAverage_eq_integral (f := fun z => (f z-boxAverage a r f)^2) ((hf.continuous.sub continuous_const).pow 2) a r h₁ h₂ h₃,
    boxAverage_eq_integral (f := e) he a r h₁ h₂ h₃] at hP
  have hV : 0 < r.1.1*r.1.2*r.2 := by positivity
  have hPi : localVariance volume (closedBox a r) f (boxAverage a r f) ≤
      4*(∫ z in closedBox a r, e z) := by
    apply (mul_le_mul_iff_right₀ (inv_pos.mpr hV)).mp
    change _ ≤ _ at hP
    dsimp [localVariance]
    nlinarith [hP]
  have hi := integral_mono (μ := volume.restrict (closedBox a r))
    (f := e) (g := fun z => R*cubeEnergyDensity f z)
    (he.continuousOn.integrableOn_compact (isCompact_closedBox a r))
    ((continuous_const.mul (continuous_cubeEnergyDensity hf)).continuousOn.integrableOn_compact
      (isCompact_closedBox a r))
    (fun z => show e z ≤ R*cubeEnergyDensity f z by
      dsimp [e,R,cubeEnergyDensity]
      have hx := mul_nonneg (sq_nonneg r.1.1)
        (add_nonneg (sq_nonneg (cubePartial f ((0,1),0) z)) (sq_nonneg (cubePartial f ((0,0),1) z)))
      have hy := mul_nonneg (sq_nonneg r.1.2)
        (add_nonneg (sq_nonneg (cubePartial f ((1,0),0) z)) (sq_nonneg (cubePartial f ((0,0),1) z)))
      have ht := mul_nonneg (sq_nonneg r.2)
        (add_nonneg (sq_nonneg (cubePartial f ((1,0),0) z)) (sq_nonneg (cubePartial f ((0,1),0) z)))
      nlinarith)
  rw [integral_const_mul] at hi
  change _ ≤ 4*R*(∫ z in closedBox a r, cubeEnergyDensity f z)
  nlinarith

lemma RectFootprint.prism_closedBox (Q : RectFootprint) (lo hi : ℝ) :
    Q.prism lo hi = closedBox ((Q.xl,Q.yl),lo) ((Q.xu-Q.xl,Q.yu-Q.yl),hi-lo) := by
  simp [RectFootprint.prism,RectFootprint.carrier,closedBox]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_WeightedSpectralSpace
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology
open scoped ENNReal

lemma spectralTraceGraph_closed {ι : Type*} (w : ι → ℝ) :
    IsClosed (spectralTraceGraph w : Set (SpectralJet ι)) := by
  change IsClosed {z : SpectralJet ι | ∀ i, (z 1) i=(Real.sqrt (w i):ℂ)*(z 0) i}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_eq ((lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i).continuous.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => SpectralL2 ι) 1))
    (continuous_const.mul ((lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i).continuous.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => SpectralL2 ι) 0)))

instance spectralTraceGraph_complete {ι : Type*} (w : ι → ℝ) :
    CompleteSpace (spectralTraceGraph w) := (spectralTraceGraph_closed w).completeSpace_coe

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_RectanglePoincare
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

lemma RectFootprint.prism_volume (Q : RectFootprint) (lo hi : ℝ) :
    volume (Q.prism lo hi)=ENNReal.ofReal (Q.xu-Q.xl)*ENNReal.ofReal (Q.yu-Q.yl)*
      ENNReal.ofReal (hi-lo) := by
  simp only [RectFootprint.prism,RectFootprint.carrier,Measure.volume_eq_prod,
    Measure.prod_prod,Real.volume_Icc]

lemma RectFootprint.prism_volume_pos (Q : RectFootprint) (lo hi : ℝ) :
    0 < volume (Q.prism lo hi) ↔ Q.xl<Q.xu ∧ Q.yl<Q.yu ∧ lo<hi := by
  rw [Q.prism_volume]
  simp only [ENNReal.mul_pos_iff,ENNReal.ofReal_pos,sub_pos]
  tauto

lemma RectFootprint.prism_real_pos (Q : RectFootprint) (lo hi : ℝ)
    (hx : Q.xl<Q.xu) (hy : Q.yl<Q.yu) (hz : lo<hi) :
    0 < volume.real (Q.prism lo hi) := by
  exact ENNReal.toReal_pos ((Q.prism_volume_pos lo hi).mpr ⟨hx,hy,hz⟩).ne'
    (Q.prism_compact lo hi).measure_ne_top

lemma RectFootprint.poincareConstant_nonneg (Q : RectFootprint) (lo hi : ℝ) :
    0 ≤ Q.poincareConstant lo hi := by unfold RectFootprint.poincareConstant; positivity

theorem RectFootprint.poincare (Q : RectFootprint) (lo hi : ℝ) {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    localVariance volume (Q.prism lo hi) f (Q.average lo hi f) ≤
      Q.poincareConstant lo hi*(∫ z in Q.prism lo hi,cubeEnergyDensity f z) := by
  by_cases h : Q.xl<Q.xu ∧ Q.yl<Q.yu ∧ lo<hi
  · rw [Q.prism_closedBox]
    exact smooth_box_volume_poincare hf _ _ (sub_pos.mpr h.1) (sub_pos.mpr h.2.1) (sub_pos.mpr h.2.2)
  · have hz : volume (Q.prism lo hi)=0 := by
      exact nonpos_iff_eq_zero.mp (le_of_not_gt (fun hp => h ((Q.prism_volume_pos lo hi).mp hp)))
    simp [localVariance,Measure.restrict_eq_zero.mpr hz]

lemma rectangle_energy_mono {Q R : Set Box3} {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hR : IsCompact R) (hQR : Q⊆R) :
    (∫ z in Q,cubeEnergyDensity f z) ≤ ∫ z in R,cubeEnergyDensity f z := by
  exact setIntegral_mono_set ((continuous_cubeEnergyDensity hf).continuousOn.integrableOn_compact hR)
    (Filter.Eventually.of_forall (fun _ => cubeEnergyDensity_nonneg f _))
    (Filter.Eventually.of_forall (fun _ hx => hQR hx))

theorem RectFootprint.poincare_in (Q : RectFootprint) (lo hi : ℝ) {R : Set Box3}
    (hR : IsCompact R) (hQR : Q.prism lo hi⊆R) {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    localVariance volume (Q.prism lo hi) f (Q.average lo hi f) ≤
      Q.poincareConstant lo hi*(∫ z in R,cubeEnergyDensity f z) := by
  exact (Q.poincare lo hi hf).trans (mul_le_mul_of_nonneg_left (rectangle_energy_mono hf hR hQR)
    (Q.poincareConstant_nonneg lo hi))

open Set MeasureTheory

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
lemma patchCluster_mono (Q : ℕ → Set X) {n m : ℕ} (h : n ≤ m) :
    patchCluster Q n ⊆ patchCluster Q m := by
  induction h with
  | refl => exact Subset.rfl
  | @step m h ih => exact ih.trans (subset_union_left (t := Q (m+1)))

omit [MeasurableSpace X] in
lemma subset_patchCluster (Q : ℕ → Set X) (n : ℕ) : Q n ⊆ patchCluster Q n := by
  cases n with
  | zero => exact Subset.rfl
  | succ n => exact subset_union_right

lemma patchPoincareConstant_nonneg (μ : Measure X) (Q : ℕ → Set X) (A : ℕ → ℝ)
    (hA : ∀ n, 0≤A n) (n : ℕ) : 0≤patchPoincareConstant μ Q A n := by
  induction n with
  | zero => exact hA 0
  | succ n ih =>
    dsimp [patchPoincareConstant]
    have hQ : 0≤μ.real (Q (n+1)) := ENNReal.toReal_nonneg
    have hO : 0≤μ.real (patchCluster Q n ∩ Q (n+1)) := ENNReal.toReal_nonneg
    have hn := hA (n+1)
    positivity

theorem connected_patch_poincare (μ : Measure X) (Q : ℕ → Set X) (A : ℕ → ℝ)
    (hA : ∀ n, 0≤A n) {f : X → ℝ} (m : ℕ → ℝ) (E : ℝ) (hE : 0≤E) (N : ℕ)
    (hfin : ∀ n≤N, μ (Q n)≠⊤)
    (hover : ∀ n<N, 0<μ.real (patchCluster Q n ∩ Q (n+1)))
    (hint : ∀ n≤N, ∀ c : ℝ, IntegrableOn (fun x => (f x-c)^2) (Q n) μ)
    (hloc : ∀ n≤N, localVariance μ (Q n) f (m n) ≤ A n*E) :
    localVariance μ (patchCluster Q N) f (m 0) ≤ patchPoincareConstant μ Q A N*E := by
  have hi : ∀ n≤N, ∀ c : ℝ, IntegrableOn (fun x => (f x-c)^2) (patchCluster Q n) μ := by
    intro n hn
    induction n with
    | zero => exact hint 0 (by omega)
    | succ n ih =>
      intro c
      exact (ih (by omega) c).union (hint (n+1) hn c)
  have hfinite : ∀ n≤N, μ (patchCluster Q n)≠⊤ := by
    intro n hn
    induction n with
    | zero => exact hfin 0 (by omega)
    | succ n ih =>
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ih (by omega),hfin (n+1) hn⟩)
        (measure_union_le _ _)
  have hall : ∀ n≤N, localVariance μ (patchCluster Q n) f (m 0) ≤ patchPoincareConstant μ Q A n*E := by
    intro n hn
    induction n with
    | zero => exact hloc 0 (by omega)
    | succ n ih =>
      exact overlap_poincare_glue μ hE (patchPoincareConstant_nonneg μ Q A hA n) (hA (n+1))
        (hfinite n (by omega)) (hfin (n+1) hn) (hover n (by omega))
        (hi n (by omega) (m 0)) (hint (n+1) hn (m (n+1))) (hint (n+1) hn (m 0))
        (ih (by omega)) (hloc (n+1) hn)
  exact hall N le_rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralAnchor
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma centralTop_subset (i : Fin 4) : centralTop i⊆centralClosed := by
  rw [centralClosed_cover]
  exact (subset_iUnion (fun i => centralTop i) i).trans (subset_union_left.trans subset_union_left)

lemma centralBottom_subset (i : Fin 4) : centralBottom i⊆centralClosed := by
  rw [centralClosed_cover]
  exact (subset_iUnion (fun i => centralBottom i) i).trans (subset_union_right.trans subset_union_left)

lemma centralColumn_subset (i : Fin 4) (j k : Fin 5) :
    (centralColumn i j k).prism (-centralHeight) centralHeight⊆centralClosed := by
  intro z hz
  rw [centralClosed_cover]
  exact Or.inr (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨k,hz⟩⟩⟩)

lemma centralConnector_subset : centralConnector.prism (-centralHeight) centralHeight⊆centralClosed := by
  intro z hz
  obtain ⟨⟨hx,hy⟩,ht⟩ := hz
  have hp : centralParentFootprint z.1 := by
    apply centralParentStrip_mem.mp
    refine ⟨0,?_⟩
    change (centralInnerX ≤ z.1.1 ∧ z.1.1 ≤ centralOuterX) ∧
      -centralOuterY ≤ z.1.2 ∧ z.1.2 ≤ centralOuterY
    refine ⟨⟨?_,hx.2⟩,hy⟩
    have hh : centralInnerX ≤ 3/2 := by norm_num [centralInnerX,sourceLength,sourceHole,sourceRadialWidth,centralThickness]
    exact hh.trans hx.1
  refine ⟨hp,abs_le.mpr ht,Or.inr ⟨?_,?_⟩⟩
  all_goals
    apply Or.inl
    apply le_abs.mpr
    apply Or.inl
    change centralChildOuterX ≤ z.1.1-_
    have hh := hx.1
    change (3/2:ℝ) ≤ z.1.1 at hh
    norm_num [centralChildOuterX,sourceScale,sourceRadialWidth,sourceHole,centralThickness,sourceOffset]
    linarith

lemma centralAnchorPiece_compact (n : ℕ) : IsCompact (centralAnchorPiece n) :=
  (centralAnchorData n).1.prism_compact _ _

lemma centralAnchorPiece_subset (n : ℕ) (hn : n ≤ 8) : centralAnchorPiece n⊆centralClosed := by
  interval_cases n
  · exact centralTop_subset 0
  · exact centralTop_subset 1
  · exact centralTop_subset 2
  · exact centralTop_subset 3
  · exact centralConnector_subset
  · exact centralBottom_subset 0
  · exact centralBottom_subset 1
  · exact centralBottom_subset 2
  · exact centralBottom_subset 3

lemma RectFootprint.prism_inter (Q R : RectFootprint) (lo hi lo' hi' : ℝ) :
    Q.prism lo hi∩R.prism lo' hi'=(Q.inter R).prism (max lo lo') (min hi hi') := by
  ext z
  simp only [RectFootprint.prism,RectFootprint.inter_carrier,mem_prod,mem_Icc,
    mem_inter_iff,max_le_iff,le_min_iff]
  tauto

lemma centralAnchor_adjacent (n : ℕ) (hn : n<8) :
    0<volume.real (centralAnchorPiece n∩centralAnchorPiece (n+1)) := by
  unfold centralAnchorPiece
  rw [RectFootprint.prism_inter]
  apply RectFootprint.prism_real_pos
  all_goals
    interval_cases n <;> norm_num [centralAnchorData,centralParentStrip,centralConnector,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
      RectFootprint.inter,centralOuterX,centralInnerX,centralOuterY,centralInnerY,
      centralHeight,centralChildHeight,sourceScale,sourceLength,sourceHole,sourceRadialWidth,
      centralThickness]

lemma centralCluster_compact (n : ℕ) : IsCompact (patchCluster centralAnchorPiece n) := by
  induction n with
  | zero => exact centralAnchorPiece_compact 0
  | succ n ih => exact ih.union (centralAnchorPiece_compact (n+1))

lemma centralAnchor_hover (n : ℕ) (hn : n<8) :
    0<volume.real (patchCluster centralAnchorPiece n∩centralAnchorPiece (n+1)) := by
  apply (centralAnchor_adjacent n hn).trans_le
  exact measureReal_mono (inter_subset_inter_left _ (subset_patchCluster centralAnchorPiece n))
    (((centralCluster_compact n).inter (centralAnchorPiece_compact (n+1))).measure_ne_top)

lemma centralAnchorConstant_nonneg : 0 ≤ centralAnchorConstant := by
  exact patchPoincareConstant_nonneg volume centralAnchorPiece centralAnchorLocalConstant
    (fun n => (centralAnchorData n).1.poincareConstant_nonneg _ _) 8

theorem centralAnchor_poincare {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    localVariance volume centralAnchor f (centralAnchorAverage 0 f) ≤
      centralAnchorConstant*(∫ z in centralClosed,cubeEnergyDensity f z) := by
  apply connected_patch_poincare volume centralAnchorPiece centralAnchorLocalConstant
    (fun n => (centralAnchorData n).1.poincareConstant_nonneg _ _)
    (fun n => centralAnchorAverage n f) _ (integral_nonneg (cubeEnergyDensity_nonneg f)) 8
  · intro n hn; exact (centralAnchorPiece_compact n).measure_ne_top
  · exact centralAnchor_hover
  · intro n hn c
    exact ((hf.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_compact
      (centralAnchorPiece_compact n)
  · intro n hn
    exact (centralAnchorData n).1.poincare_in _ _ centralClosed_compact (centralAnchorPiece_subset n hn) hf

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalCollarTrace
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory

lemma sourcePair_central_image : sourcePairMeasurable '' centralPhysical=centralClosed := by
  exact sourcePairMeasurable.image_preimage centralClosed

lemma integral_centralPhysical (g : Box3 → ℝ) :
    (∫ x in centralPhysical,g (sourcePairCoordinates x))=(∫ z in centralClosed,g z) := by
  have h := sourcePair_volume.setIntegral_image_emb sourcePairMeasurable.measurableEmbedding g centralPhysical
  rw [sourcePair_central_image] at h
  exact h.symm

lemma sourcePair_energy {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (x : Fin 3 → ℝ) :
    sourcePhysicalEnergy (f ∘ sourcePairCoordinates) x≤
      192*cubeEnergyDensity f (sourcePairCoordinates x)+2*(f (sourcePairCoordinates x))^2 := by
  have he : fderiv ℝ (f ∘ sourcePairCoordinates) x=
      (fderiv ℝ f (sourcePairCoordinates x)).comp sourcePairCLE.toContinuousLinearMap := by
    exact ((hf.differentiable (by simp) _).hasFDerivAt.comp x sourcePairCLE.hasFDerivAt).fderiv
  have hb := linear_three_bound (fderiv ℝ (f ∘ sourcePairCoordinates) x)
  rw [he] at hb
  change ‖(fderiv ℝ f (sourcePairCoordinates x)).comp sourcePairCLE.toContinuousLinearMap‖^2≤
    3*(cubeEnergyDensity f (sourcePairCoordinates x)) at hb
  dsimp [sourcePhysicalEnergy]
  rw [he]
  linarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralPhysicalTrace
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory UnitAddTorus

lemma centralTraceConstant_pos : 0 < centralTraceConstant := by
  have := physicalRayConstant_pos
  dsimp [centralTraceConstant,centralThickness,sourceScale]
  positivity

lemma centralTraceConstant_parent : (1+1/centralThickness)*physicalRayConstant ≤ centralTraceConstant := by
  have hh := physicalRayConstant_pos
  dsimp [centralTraceConstant,centralThickness,sourceScale]
  nlinarith

lemma central_parent_trace {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    (∫ x : UnitAddTorus (Fin 2),(f (sourceAngularCollar centralThickness x))^2)≤
      centralTraceConstant*(∫ y in centralPhysical,sourcePhysicalEnergy f y) := by
  have hh := sourceAngular_physical_trace_forward hf centralPhysical_compact centralThickness
    (η:=centralThickness) (by norm_num [centralThickness]) (by norm_num [centralThickness])
    (by norm_num [centralThickness]) (fun i j y hy => by
      obtain ⟨x,hx,rfl⟩ := hy
      apply sourceParentCollar_central i j
      simpa [two_mul] using hx)
  have hn : 0≤∫ y in centralPhysical,sourcePhysicalEnergy f y := integral_nonneg (sourcePhysicalEnergy_nonneg f)
  exact hh.trans (mul_le_mul_of_nonneg_right centralTraceConstant_parent hn)

lemma central_child_trace {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    {σ : ℝ} (hσ : σ=1 ∨ σ= -1) :
    (∫ x : UnitAddTorus (Fin 2),(f (sourceChildCoordinates σ (sourceAngularCollar (-centralThickness) x)))^2)≤
      centralTraceConstant*(∫ y in centralPhysical,sourcePhysicalEnergy f y) := by
  let K := sourceChildCoordinates σ ⁻¹' centralPhysical
  have hK : IsCompact K := (sourceChildHomeomorph σ).isCompact_preimage.mpr centralPhysical_compact
  have hfc := hf.comp (sourceChildCoordinates_contDiff σ)
  have hh := sourceAngular_physical_trace_backward hfc hK (-centralThickness)
    (η:=centralThickness) (by norm_num [centralThickness]) (by norm_num [centralThickness])
    (by norm_num [centralThickness]) (fun i j y hy => by
      obtain ⟨x,hx,rfl⟩ := hy
      apply sourceChildCollar_central i j hσ
      convert hx using 1; ring_nf)
  have hmono : (∫ y in K,sourcePhysicalEnergy (f ∘ sourceChildCoordinates σ) y)≤
      ∫ y in K,sourcePhysicalEnergy f (sourceChildCoordinates σ y) := by
    apply integral_mono
      ((continuous_sourcePhysicalEnergy hfc).continuousOn.integrableOn_compact hK)
      (((continuous_sourcePhysicalEnergy hf).comp (sourceChildCoordinates_contDiff σ).continuous).continuousOn.integrableOn_compact hK)
      (sourceChild_energy hf σ)
  have he := integral_sourceChild_preimage σ centralPhysical_compact (sourcePhysicalEnergy f)
  change (∫ y in K,sourcePhysicalEnergy f (sourceChildCoordinates σ y))=_ at he
  rw [he] at hmono
  exact hh.trans (by
    have hm := mul_le_mul_of_nonneg_left hmono (show 0≤(1+1/centralThickness)*physicalRayConstant by
      have := physicalRayConstant_pos; norm_num [centralThickness]; positivity)
    simpa [centralTraceConstant,mul_assoc] using hm)

lemma central_physical_trace {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (i : Fin 3) :
    (∫ x : UnitAddTorus (Fin 2),(f (centralBoundary i x))^2)≤
      centralTraceConstant*(∫ z in centralClosed,192*cubeEnergyDensity f z+2*(f z)^2) := by
  have hfc : ContDiff ℝ (↑(⊤ : ℕ∞)) (f ∘ sourcePairCoordinates) := hf.comp sourcePairCLE.contDiff
  have ht : (∫ x : UnitAddTorus (Fin 2),(f (centralBoundary i x))^2)≤
      centralTraceConstant*(∫ y in centralPhysical,sourcePhysicalEnergy (f ∘ sourcePairCoordinates) y) := by
    fin_cases i
    · exact central_parent_trace hfc
    · exact central_child_trace hfc (Or.inl rfl)
    · exact central_child_trace hfc (Or.inr rfl)
  have hm : (∫ y in centralPhysical,sourcePhysicalEnergy (f ∘ sourcePairCoordinates) y)≤
      ∫ y in centralPhysical,192*cubeEnergyDensity f (sourcePairCoordinates y)+2*(f (sourcePairCoordinates y))^2 := by
    apply integral_mono
      ((continuous_sourcePhysicalEnergy hfc).continuousOn.integrableOn_compact centralPhysical_compact)
      (((continuous_const.mul ((continuous_cubeEnergyDensity hf).comp sourcePairCLE.continuous)).add
        (continuous_const.mul ((hf.continuous.comp sourcePairCLE.continuous).pow 2))).continuousOn.integrableOn_compact centralPhysical_compact)
      (sourcePair_energy hf)
  rw [integral_centralPhysical (fun z => 192*cubeEnergyDensity f z+2*(f z)^2)] at hm
  exact ht.trans (mul_le_mul_of_nonneg_left hm centralTraceConstant_pos.le)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralPoincare
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

lemma centralTop_subset_anchor (i : Fin 4) : centralTop i ⊆ centralAnchor := by
  have h : centralTop i=centralAnchorPiece i.val := by fin_cases i <;> rfl
  rw [h]
  exact (subset_patchCluster centralAnchorPiece i.val).trans (patchCluster_mono _ (by omega))

lemma centralBottom_subset_anchor (i : Fin 4) : centralBottom i ⊆ centralAnchor := by
  have h : centralBottom i=centralAnchorPiece (i.val+5) := by fin_cases i <;> rfl
  rw [h]
  exact (subset_patchCluster centralAnchorPiece (i.val+5)).trans (patchCluster_mono _ (by omega))

lemma centralColumn_overlaps_anchor (i : Fin 4) (j k : Fin 5)
    (hx : (centralColumn i j k).xl < (centralColumn i j k).xu)
    (hy : (centralColumn i j k).yl < (centralColumn i j k).yu) :
    0 < volume.real (centralAnchor ∩ (centralColumn i j k).prism (-centralHeight) centralHeight) := by
  have hh : centralChildHeight < centralHeight := by
    norm_num [centralChildHeight,centralHeight,sourceScale,centralThickness]
  apply ((centralColumn i j k).prism_real_pos _ _ hx hy hh).trans_le
  refine measureReal_mono ?_ ?_
  · rintro z ⟨hz,ht⟩
    refine ⟨centralTop_subset_anchor i ⟨?_,ht⟩,hz,?_,ht.2⟩
    · have hh := hz
      simp only [centralColumn,RectFootprint.inter_carrier,mem_inter_iff] at hh
      exact hh.1.1
    · have hp : 0 ≤ centralChildHeight+centralHeight := by
        norm_num [centralChildHeight,centralHeight,sourceScale,centralThickness]
      linarith [ht.1]
  · exact ((centralCluster_compact 8).inter ((centralColumn i j k).prism_compact _ _)).measure_ne_top

lemma centralColumnConstant_nonneg (i : Fin 4) (j k : Fin 5) : 0 ≤ centralColumnConstant i j k := by
  have hA := centralAnchorConstant_nonneg
  have hB := (centralColumn i j k).poincareConstant_nonneg (-centralHeight) centralHeight
  dsimp [centralColumnConstant]
  positivity

lemma centralColumn_poincare (i : Fin 4) (j k : Fin 5) {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    localVariance volume ((centralColumn i j k).prism (-centralHeight) centralHeight) f
      (centralAnchorAverage 0 f) ≤ centralColumnConstant i j k*(∫ z in centralClosed,cubeEnergyDensity f z) := by
  let R := (centralColumn i j k).prism (-centralHeight) centralHeight
  have hc : IsCompact R := (centralColumn i j k).prism_compact _ _
  have hint : ∀ c : ℝ, IntegrableOn (fun z => (f z-c)^2) R := fun c =>
    ((hf.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_compact hc
  by_cases h : (centralColumn i j k).xl<(centralColumn i j k).xu ∧
      (centralColumn i j k).yl<(centralColumn i j k).yu
  · have hiA : IntegrableOn (fun z => (f z-centralAnchorAverage 0 f)^2) centralAnchor :=
      ((hf.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_compact (centralCluster_compact 8)
    have hglue := overlap_poincare_glue volume (integral_nonneg (cubeEnergyDensity_nonneg f))
      centralAnchorConstant_nonneg ((centralColumn i j k).poincareConstant_nonneg (-centralHeight) centralHeight)
      (centralCluster_compact 8).measure_ne_top hc.measure_ne_top (centralColumn_overlaps_anchor i j k h.1 h.2)
      hiA (hint _) (hint _) (centralAnchor_poincare hf)
      ((centralColumn i j k).poincare_in _ _ centralClosed_compact (centralColumn_subset i j k) hf)
    exact (localVariance_mono volume (hiA.union (hint _)) (subset_union_right : R⊆centralAnchor∪R)).trans hglue
  · have hz : volume R=0 := by
      apply nonpos_iff_eq_zero.mp
      apply le_of_not_gt
      intro hp
      have hh := ((centralColumn i j k).prism_volume_pos _ _).mp hp
      exact h ⟨hh.1,hh.2.1⟩
    have hv : localVariance volume R f (centralAnchorAverage 0 f)=0 := by
      simp [localVariance,Measure.restrict_eq_zero.mpr hz]
    change localVariance volume R f (centralAnchorAverage 0 f) ≤ _
    rw [hv]
    exact mul_nonneg (centralColumnConstant_nonneg i j k) (integral_nonneg (cubeEnergyDensity_nonneg f))

lemma localVariance_finset_union_le {X ι : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Finset ι) (Q : ι → Set X) {f : X → ℝ} {a : ℝ}
    (hi : ∀ i∈s,IntegrableOn (fun z => (f z-a)^2) (Q i) μ) :
    localVariance μ (⋃ i∈s,Q i) f a ≤ ∑ i∈s,localVariance μ (Q i) f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [localVariance]
  | @insert i s hin ih =>
    have his : ∀ j∈s,IntegrableOn (fun z => (f z-a)^2) (Q j) μ := fun j hj => hi j (Finset.mem_insert_of_mem hj)
    have h_union : IntegrableOn (fun z => (f z-a)^2) (⋃ j∈s,Q j) μ := by
      exact integrableOn_finset_iUnion.mpr his
    simpa only [Finset.set_biUnion_insert,Finset.sum_insert hin] using
      (localVariance_union_le μ (hi i (Finset.mem_insert_self _ _)) h_union).trans
        (add_le_add_right (ih his) _)

lemma centralPoincareConstant_nonneg : 0 ≤ centralPoincareConstant := by
  apply add_nonneg centralAnchorConstant_nonneg
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    Finset.sum_nonneg (fun k _ => centralColumnConstant_nonneg i j k)))

theorem central_physical_poincare {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    localVariance volume centralClosed f (centralAnchorAverage 0 f) ≤
      centralPoincareConstant*(∫ z in centralClosed,cubeEnergyDensity f z) := by
  let Q : (Fin 4×Fin 5×Fin 5) → Set Box3 := fun p =>
    (centralColumn p.1 p.2.1 p.2.2).prism (-centralHeight) centralHeight
  let U := ⋃ p,Q p
  have hu : IsCompact U := isCompact_iUnion (fun p => (centralColumn p.1 p.2.1 p.2.2).prism_compact _ _)
  have hiu : IntegrableOn (fun z => (f z-centralAnchorAverage 0 f)^2) U :=
    ((hf.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_compact hu
  have hia : IntegrableOn (fun z => (f z-centralAnchorAverage 0 f)^2) centralAnchor :=
    ((hf.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_compact (centralCluster_compact 8)
  have hsub : centralClosed⊆centralAnchor∪U := by
    rw [centralClosed_cover]
    rintro z ((ht|hb)|hc)
    · obtain ⟨i,hi⟩ := mem_iUnion.mp ht
      exact Or.inl (centralTop_subset_anchor i hi)
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hb
      exact Or.inl (centralBottom_subset_anchor i hi)
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hc
      obtain ⟨j,hj⟩ := mem_iUnion.mp hi
      obtain ⟨k,hk⟩ := mem_iUnion.mp hj
      exact Or.inr (mem_iUnion.mpr ⟨(i,j,k),hk⟩)
  have hv := localVariance_finset_union_le volume Finset.univ Q
    (fun p _ => ((hf.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_compact
      ((centralColumn p.1 p.2.1 p.2.2).prism_compact _ _)) (a := centralAnchorAverage 0 f)
  simp only [Finset.mem_univ,iUnion_true, Fintype.sum_prod_type] at hv
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun k _ => centralColumn_poincare i j k hf)))
  calc localVariance volume centralClosed f (centralAnchorAverage 0 f)
      ≤ localVariance volume centralAnchor f (centralAnchorAverage 0 f)+localVariance volume U f (centralAnchorAverage 0 f) :=
        (localVariance_mono volume (hia.union hiu) hsub).trans (localVariance_union_le volume hia hiu)
    _ ≤ centralAnchorConstant*(∫ z in centralClosed,cubeEnergyDensity f z)+
        (∑ i : Fin 4,∑ j : Fin 5,∑ k : Fin 5,centralColumnConstant i j k*(∫ z in centralClosed,cubeEnergyDensity f z)) :=
      add_le_add (centralAnchor_poincare hf) (hv.trans hb)
    _ = centralPoincareConstant*(∫ z in centralClosed,cubeEnergyDensity f z) := by
      simp only [centralPoincareConstant,add_mul,Finset.sum_mul]

open Set MeasureTheory
open scoped ENNReal

lemma centralSmoothJet_norm_coordinate (f : centralSmoothFunctions) (i : Fin 4) :
    ‖centralSmoothJet f i‖^2=∫ z in centralClosed,(centralJetField f i z)^2 := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [centralSmoothJet_ae f i] with z hz
  simp [hz,pow_two]

lemma centralSmoothJet_gradient_norm (f : centralSmoothFunctions) :
    ‖centralJetD (centralSmoothJet f)‖^2=∫ z in centralClosed,cubeEnergyDensity f z := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ i : Fin 3,‖centralSmoothJet f i.succ‖^2)=_
  simp only [centralSmoothJet_norm_coordinate]
  have h0 := (central_continuous_memLp (continuous_cubePartial (central_smooth f) ((1,0),0))).integrable_sq
  have h1 := (central_continuous_memLp (continuous_cubePartial (central_smooth f) ((0,1),0))).integrable_sq
  have h2 := (central_continuous_memLp (continuous_cubePartial (central_smooth f) ((0,0),1))).integrable_sq
  dsimp [centralMeasure] at h0 h1 h2
  simp only [Fin.sum_univ_succ,Fin.isValue,centralJetField,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,add_zero]
  unfold cubeEnergyDensity
  have ha := integral_add h0 h1
  have hb := integral_add (h0.add h1) h2
  simp only [Pi.add_apply] at ha hb
  rw [hb,ha]
  ring

lemma centralSmoothJet_norm (f : centralSmoothFunctions) :
    ‖centralSmoothJet f‖^2=(∫ z in centralClosed,(f z)^2)+‖centralJetD (centralSmoothJet f)‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2,Fin.sum_univ_succ]
  rw [centralSmoothJet_norm_coordinate]
  congr 1
  exact (PiLp.norm_sq_eq_of_L2 _ (centralJetD (centralSmoothJet f))).symm

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralVariational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

variable {V G : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

theorem solve_form_mod_constants [CompleteSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (M F : V →L[ℝ] ℝ) (oneV : V)
    (hM : M oneV=1) (hF : F oneV=0)
    (hB : ∀ u : V,B u oneV=0) (hB' : ∀ v : V,B oneV v=0)
    (hcoer : IsCoercive (((B.comp M.ker.subtypeL).flip.comp M.ker.subtypeL).flip)) :
    ∃ p : V, M p=0 ∧ (∀ v : V,B p v=F v) ∧
      (∀ q : V,(∀ v : V,B q v=F v) → q-p=M q • oneV) := by
  let K := M.ker
  have hclosed : IsClosed (K : Set V) := M.isClosed_ker
  let : CompleteSpace K := hclosed.completeSpace_coe
  let A : K →L[ℝ] K →L[ℝ] ℝ := ((B.comp K.subtypeL).flip.comp K.subtypeL).flip
  let L : K →L[ℝ] ℝ := F.comp K.subtypeL
  let p : K := hcoer.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ K).symm L)
  have hp (v : K) : B p.val v.val=F v.val := by
    change A p v=L v
    rw [←hcoer.continuousLinearEquivOfBilin_apply]
    dsimp only [p]
    rw [hcoer.continuousLinearEquivOfBilin.apply_symm_apply]
    exact congrArg (fun f : K →L[ℝ] ℝ => f v) ((InnerProductSpace.toDual ℝ K).apply_symm_apply L)
  have hpM : M p.val=0 := p.property
  have hfull (v : V) : B p.val v=F v := by
    have hv : v-M v • oneV∈K := by
      change M (v-M v • oneV)=0
      simp [hM]
    have hh := hp ⟨_,hv⟩
    change B p.val (v-M v • oneV)=F (v-M v • oneV) at hh
    simpa only [map_sub,map_smul,hB,hF,smul_zero,sub_zero] using hh
  refine ⟨p.val,hpM,hfull,?_⟩
  intro q hq
  let d : V := q-p.val-M q • oneV
  have hdK : d∈K := by
    change M (q-p.val-M q • oneV)=0
    simp [hpM,hM]
  have hd : B d d=0 := by
    dsimp only [d]
    simp only [map_sub,map_smul,sub_apply,smul_apply,
      hq,hfull,hB',smul_zero,sub_self]
  have hz : (⟨d,hdK⟩ : K)=0 := by
    apply hcoer.continuousLinearEquivOfBilin.injective
    apply ext_inner_right ℝ
    intro v
    rw [map_zero,inner_zero_left,hcoer.continuousLinearEquivOfBilin_apply]
    change B d v.val=0
    dsimp only [d]
    simp only [map_sub,map_smul,sub_apply,smul_apply,
      hq,hfull,hB',smul_zero,sub_self]
  have he : d=0 := congrArg (fun z : K => z.val) hz
  exact sub_eq_zero.mp he

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralSmoothTrace
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory UnitAddTorus
open scoped ENNReal

lemma central_physical_trace_normalized {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (i : Fin 3) :
    (∫ x : UnitAddTorus (Fin 2),(f (centralBoundary i x))^2 ∂normalizedTorusVolume)≤
      centralTraceConstant*(∫ z in centralClosed,192*cubeEnergyDensity f z+2*(f z)^2) := by
  rw [←unitTorus_volume_eq_normalized]
  exact central_physical_trace hf i

attribute [local instance] OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_3
attribute [local instance] OAI.ScalarConductivity.instIsProbabilityMeasureUnitAddCircleVolume_solutions_3
lemma centralTraceFourier_norm (f : centralSmoothFunctions) (i : Fin 3) :
    ‖centralTraceFourier f i‖^2=∫ x : UnitAddTorus (Fin 2),(f (centralBoundary i x))^2 := by
  change ‖(mFourierBasis (d:=Fin 2)).repr (ContinuousMap.toLp 2 volume ℂ (centralTraceFunction f i))‖^2=_
  rw [LinearIsometryEquiv.norm_map,←real_inner_self_eq_norm_sq]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜:=ℂ) (p:=2) volume (centralTraceFunction f i)] with x hx
  rw [hx,real_inner_self_eq_norm_sq]
  simp [centralTraceFunction,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma centralSmoothTrace_norm (s : Fin 3 → ℝ) (f : centralSmoothFunctions) (i : Fin 3) :
    ‖centralSmoothTrace s f i‖^2=‖centralTraceFourier f i‖^2+
      ‖spectralGraphWeight (torusRate s) (centralSmoothTrace s f i)‖^2 := by
  rw [←Submodule.norm_coe,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_two,centralSmoothTrace_fst]
  rfl

end

open Set MeasureTheory UnitAddTorus
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_4
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_4 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma centralOne_gradient : centralJetD (centralSmoothJet centralSmoothOne)=0 := by
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [centralSmoothJet_ae centralSmoothOne i.succ,Lp.coeFn_zero ℝ 2 centralMeasure] with z hz h0
  change centralSmoothJet centralSmoothOne i.succ z=(0 : CentralL2) z
  rw [hz,h0]
  fin_cases i <;> simp [centralJetField,centralSmoothOne,cubePartial]

lemma centralOne_traceFunction (i : Fin 3) :
    centralTraceFunction centralSmoothOne i=mFourier (0 : TorusModes) := by
  ext x
  simp [centralTraceFunction,centralSmoothOne,mFourier_zero]

lemma centralOne_fourier (i : Fin 3) :
    centralTraceFourier centralSmoothOne i=lp.single 2 (0 : TorusModes) 1 := by
  change (mFourierBasis (d:=Fin 2)).repr (ContinuousMap.toLp 2 volume ℂ
    (centralTraceFunction centralSmoothOne i))=_
  rw [centralOne_traceFunction]
  simpa only [coe_mFourierBasis] using (mFourierBasis (d:=Fin 2)).repr_self 0

lemma centralOne_weight (s : Fin 3 → ℝ) (i : Fin 3) :
    spectralGraphWeight (torusRate s) (centralSmoothTrace s centralSmoothOne i)=0 := by
  ext h
  change ((centralSmoothTrace s centralSmoothOne i).val 1) h=0
  rw [(centralSmoothTrace s centralSmoothOne i).property h,centralSmoothTrace_fst,centralOne_fourier]
  by_cases hh : h=0
  · subst h
    simp [torusRate,torusQuadratic]
  · simp [lp.single_apply,Ne.symm hh]

lemma centralOne_mean (s : Fin 3 → ℝ) (i : Fin 3) :
    spectralGraphMean (torusRate s) (centralSmoothTrace s centralSmoothOne i)=1 := by
  change (((centralSmoothTrace s centralSmoothOne i).val 0) 0).re=1
  rw [centralSmoothTrace_fst,centralOne_fourier]
  simp [lp.single_apply]

lemma centralTrace_anchor_bound (f : centralSmoothFunctions) (i : Fin 3) :
    ‖centralTraceFourier f i‖^2≤
      centralTraceConstant*(192*‖centralJetD (centralSmoothJet f)‖^2+
        2*(∫ z in centralClosed,(f z)^2)) := by
  rw [centralTraceFourier_norm]
  have hh := central_physical_trace_normalized (central_smooth f) i
  have hE : IntegrableOn (cubeEnergyDensity f) centralClosed := (continuous_cubeEnergyDensity (central_smooth f)).continuousOn.integrableOn_compact centralClosed_compact
  have hf : IntegrableOn (fun z => (f z)^2) centralClosed := ((central_smooth f).continuous.pow 2).continuousOn.integrableOn_compact centralClosed_compact
  rw [integral_add (hE.const_mul 192) (hf.const_mul 2),integral_const_mul,integral_const_mul] at hh
  rw [centralSmoothJet_gradient_norm]
  exact hh

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralEnergySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory
open scoped ENNReal

lemma centralAmbientD_embed (s : Fin 3 → ℝ) (f : centralSmoothFunctions) :
    centralAmbientD s (centralEmbedL s f)=centralJetD (centralSmoothJet f) := rfl

lemma centralAmbientT_embed (s : Fin 3 → ℝ) (f : centralSmoothFunctions) (i : Fin 3) :
    centralAmbientT s i (centralEmbedL s f)=centralSmoothTrace s f i := rfl

@[simp] lemma centralAmbientM_one (s : Fin 3 → ℝ) : centralAmbientM s (centralAmbientOne s)=1 :=
  centralOne_mean s 0

@[simp] lemma centralAmbientD_one (s : Fin 3 → ℝ) : centralAmbientD s (centralAmbientOne s)=0 :=
  centralOne_gradient

@[simp] lemma centralAmbientWeight_one (s : Fin 3 → ℝ) (i : Fin 3) :
    spectralGraphWeight (torusRate s) (centralAmbientT s i (centralAmbientOne s))=0 :=
  centralOne_weight s i

@[simp] lemma centralAmbientQ_one (s : Fin 3 → ℝ) : centralAmbientQ s (centralAmbientOne s)=0 := by
  simp [centralAmbientQ]

lemma centralAmbientQ_apply (s : Fin 3 → ℝ) (u : CentralAmbient s) :
    centralAmbientQ s u=u-centralAmbientM s u • centralAmbientOne s := rfl

lemma centralEmbed_norm (s : Fin 3 → ℝ) (f : centralSmoothFunctions) :
    ‖centralEmbedL s f‖^2=(∫ z in centralClosed,(f z)^2)+‖centralJetD (centralSmoothJet f)‖^2+
      ∑ i : Fin 3,(‖centralTraceFourier f i‖^2+
        ‖spectralGraphWeight (torusRate s) (centralSmoothTrace s f i)‖^2) := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖centralSmoothJet f‖^2+‖(WithLp.toLp 2 (fun i => centralSmoothTrace s f i) : CentralTraceFields s)‖^2=_
  rw [centralSmoothJet_norm,PiLp.norm_sq_eq_of_L2 _ (WithLp.toLp 2 (fun i => centralSmoothTrace s f i) : CentralTraceFields s)]
  simp only [centralSmoothTrace_norm]

instance centralEnergySpace_complete (s : Fin 3 → ℝ) : CompleteSpace (centralEnergySpace s) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

end

open Set MeasureTheory

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralCoercivitySmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma centralAmbientEnergy_nonneg (s : Fin 3 → ℝ) (u : CentralAmbient s) :
    0 ≤ centralAmbientEnergy s u := add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma continuous_centralAmbientEnergy (s : Fin 3 → ℝ) : Continuous (centralAmbientEnergy s) := by
  apply Continuous.add ((centralAmbientD s).continuous.norm.pow 2)
  exact continuous_finsetSum _ (fun i _ =>
    (((spectralGraphWeight (torusRate s)).comp (centralAmbientT s i)).continuous.norm.pow 2))

lemma centralAmbientD_shift (s : Fin 3 → ℝ) (u : CentralAmbient s) (a : ℝ) :
    centralAmbientD s (u-a • centralAmbientOne s)=centralAmbientD s u := by simp only [map_sub,map_smul,centralAmbientD_one,smul_zero,sub_zero]

lemma centralAmbientWeight_shift (s : Fin 3 → ℝ) (u : CentralAmbient s) (a : ℝ) (i : Fin 3) :
    spectralGraphWeight (torusRate s) (centralAmbientT s i (u-a • centralAmbientOne s))=
      spectralGraphWeight (torusRate s) (centralAmbientT s i u) := by
  simp only [map_sub,map_smul,centralAmbientWeight_one,smul_zero,sub_zero]

lemma centralAmbientQ_shift (s : Fin 3 → ℝ) (u : CentralAmbient s) (a : ℝ) :
    centralAmbientQ s (u-a • centralAmbientOne s)=centralAmbientQ s u := by
  simp only [map_sub,map_smul,centralAmbientQ_one,smul_zero,sub_zero]

lemma centralCoercivityBase_ge : 1 ≤ centralCoercivityBase := by
  have hP := centralPoincareConstant_nonneg
  have hT := centralTraceConstant_pos
  dsimp [centralCoercivityBase]
  nlinarith

lemma centralCoercivityBase_pos : 0 < centralCoercivityBase := lt_of_lt_of_le zero_lt_one centralCoercivityBase_ge

lemma central_smooth_anchor_norm (s : Fin 3 → ℝ) (f : centralSmoothFunctions) :
    ‖centralEmbedL s (f-centralAnchorAverage 0 f • centralSmoothOne)‖^2≤
      centralCoercivityBase*centralAmbientEnergy s (centralEmbedL s f) := by
  let a := centralAnchorAverage 0 f
  let g : centralSmoothFunctions := f-a • centralSmoothOne
  have hg : centralEmbedL s g=centralEmbedL s f-a • centralAmbientOne s := by
    dsimp [g,centralAmbientOne]
    simp only [map_sub,map_smul]
  have hD : centralJetD (centralSmoothJet g)=centralAmbientD s (centralEmbedL s f) := by
    rw [←centralAmbientD_embed s g,hg,centralAmbientD_shift]
  have hP : (∫ z in centralClosed,(g z)^2)≤
      centralPoincareConstant*‖centralAmbientD s (centralEmbedL s f)‖^2 := by
    rw [centralAmbientD_embed,centralSmoothJet_gradient_norm]
    simpa [g,a,centralSmoothOne,localVariance] using central_physical_poincare (central_smooth f)
  have ht (i : Fin 3) : ‖centralTraceFourier g i‖^2≤
      (centralTraceConstant*(192+2*centralPoincareConstant))*‖centralAmbientD s (centralEmbedL s f)‖^2 := by
    have hh := centralTrace_anchor_bound g i
    rw [hD] at hh
    apply hh.trans
    calc
      _ ≤ centralTraceConstant*(192*‖centralAmbientD s (centralEmbedL s f)‖^2+
          2*(centralPoincareConstant*‖centralAmbientD s (centralEmbedL s f)‖^2)) := by
        apply mul_le_mul_of_nonneg_left _ centralTraceConstant_pos.le
        linarith only [hP]
      _=_ := by ring
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => ht i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  norm_num only [Nat.cast_ofNat] at hsum
  have hw (i : Fin 3) :
      spectralGraphWeight (torusRate s) (centralSmoothTrace s g i)=
        spectralGraphWeight (torusRate s) (centralAmbientT s i (centralEmbedL s f)) := by
    rw [←centralAmbientT_embed s g i,hg,centralAmbientWeight_shift]
  change ‖centralEmbedL s g‖^2≤_
  rw [centralEmbed_norm,hD]
  simp only [hw,Finset.sum_add_distrib]
  have hW : 0≤∑ i : Fin 3,‖spectralGraphWeight (torusRate s) (centralAmbientT s i (centralEmbedL s f))‖^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hge := centralCoercivityBase_ge
  dsimp only [centralAmbientEnergy]
  have hcoef : centralCoercivityBase=1+centralPoincareConstant+
      3*(centralTraceConstant*(192+2*centralPoincareConstant)) := by unfold centralCoercivityBase; ring
  have hWW := mul_le_mul_of_nonneg_right hge hW
  rw [one_mul] at hWW
  rw [hcoef] at hWW ⊢
  nlinarith only [hP,hsum,hWW]

lemma central_smooth_projected_bound (s : Fin 3 → ℝ) (f : centralSmoothFunctions) :
    ‖centralAmbientQ s (centralEmbedL s f)‖^2≤
      (‖centralAmbientQ s‖^2*centralCoercivityBase)*centralAmbientEnergy s (centralEmbedL s f) := by
  let g : centralSmoothFunctions := f-centralAnchorAverage 0 f • centralSmoothOne
  have hh : centralAmbientQ s (centralEmbedL s g)=centralAmbientQ s (centralEmbedL s f) := by
    have hg : centralEmbedL s g=centralEmbedL s f-centralAnchorAverage 0 f • centralAmbientOne s := by
      dsimp [g,centralAmbientOne]
      simp only [map_sub,map_smul]
    rw [hg,centralAmbientQ_shift]
  have hn := (centralAmbientQ s).le_opNorm (centralEmbedL s g)
  have hn2 := mul_self_le_mul_self (norm_nonneg _) hn
  rw [hh] at hn2
  have hb := central_smooth_anchor_norm s f
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖centralAmbientQ s‖)
  nlinarith only [hn2,hm]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralPhysicalVariational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma centralCoercivityConstant_pos (s : Fin 3 → ℝ) : 0 < centralCoercivityConstant s := by
  have := centralCoercivityBase_pos
  dsimp [centralCoercivityConstant]
  positivity

lemma central_graph_projected_bound (s : Fin 3 → ℝ) (u : centralEnergySpace s) :
    ‖centralAmbientQ s u.val‖^2≤
      (‖centralAmbientQ s‖^2*centralCoercivityBase)*centralAmbientEnergy s u.val := by
  have hc : IsClosed {v : CentralAmbient s | ‖centralAmbientQ s v‖^2≤
      (‖centralAmbientQ s‖^2*centralCoercivityBase)*centralAmbientEnergy s v} :=
    isClosed_le ((centralAmbientQ s).continuous.norm.pow 2)
      (continuous_const.mul (continuous_centralAmbientEnergy s))
  have hr : (LinearMap.range (centralEmbedL s) : Set (CentralAmbient s))⊆
      {v : CentralAmbient s | ‖centralAmbientQ s v‖^2≤
        (‖centralAmbientQ s‖^2*centralCoercivityBase)*centralAmbientEnergy s v} := by
    rintro v ⟨f,rfl⟩
    exact central_smooth_projected_bound s f
  exact closure_minimal hr hc u.property

lemma central_graph_coercivity (s : Fin 3 → ℝ) (u : (centralM s).ker) :
    ‖u‖^2 ≤ centralCoercivityConstant s*(‖centralD s u.val‖^2+
      ∑ i : Fin 3,‖spectralGraphWeight (torusRate s) (centralT s i u.val)‖^2) := by
  have hm : centralAmbientM s u.val.val=0 := u.property
  have hq : centralAmbientQ s u.val.val=u.val.val := by
    rw [centralAmbientQ_apply,hm,zero_smul,sub_zero]
  have hh := central_graph_projected_bound s u.val
  rw [hq] at hh
  have hn := centralAmbientEnergy_nonneg s u.val.val
  change ‖u.val.val‖^2 ≤ centralCoercivityConstant s*centralAmbientEnergy s u.val.val
  dsimp only [centralCoercivityConstant]
  nlinarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_CentralWeightedVariational
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralEnergySpace_complete _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

variable {V G : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

lemma centralWeightedForm_apply {ι : Type*} (κ : ℝ) (w : ι → ℝ) (D : V →L[ℝ] G)
    (T : Fin 3 → V →L[ℝ] spectralTraceGraph w) (u v : V) :
    centralWeightedForm κ w D T u v=inner ℝ (D u) (D v)+
      κ*(∑ i : Fin 3,inner ℝ (spectralGraphWeight w (T i u)) (spectralGraphWeight w (T i v))) := by
  simp [centralWeightedForm,smul_eq_mul]

theorem central_variational_exists_graph_weighted [CompleteSpace V] {ι : Type*} [Zero ι]
    (κ : ℝ) (hκ : 1≤κ) (w : ι → ℝ) (D : V →L[ℝ] G)
    (T : Fin 3 → V →L[ℝ] spectralTraceGraph w)
    (M : V →L[ℝ] ℝ) (oneV : V) (hM : M oneV=1) (hD : D oneV=0)
    (hT : ∀ i,spectralGraphWeight w (T i oneV)=0)
    (havg : ∀ i,spectralGraphMean w (T i oneV)=1)
    {C : ℝ} (hC : 0<C)
    (hP : ∀ u : M.ker,‖u‖^2≤C*(‖D u.val‖^2+
      ∑ i : Fin 3,‖spectralGraphWeight w (T i u.val)‖^2))
    (s : Fin 3 → ℝ) (hs : ∑ i,s i=0) :
    ∃ p : V,M p=0 ∧
      (∀ v : V,inner ℝ (D p) (D v)+
        κ*(∑ i : Fin 3,inner ℝ (spectralGraphWeight w (T i p))
          (spectralGraphWeight w (T i v)))=
        κ*(∑ i : Fin 3,s i*spectralGraphMean w (T i v))) ∧
      (∀ q : V,(∀ v : V,inner ℝ (D q) (D v)+
        κ*(∑ i : Fin 3,inner ℝ (spectralGraphWeight w (T i q))
          (spectralGraphWeight w (T i v)))=
        κ*(∑ i : Fin 3,s i*spectralGraphMean w (T i v))) → q-p=M q • oneV) := by
  let B := centralWeightedForm κ w D T
  let F : V →L[ℝ] ℝ := κ • ∑ i : Fin 3,s i • (spectralGraphMean w).comp (T i)
  have hFa (v : V) : F v=κ*(∑ i : Fin 3,s i*spectralGraphMean w (T i v)) := by
    simp [F,smul_eq_mul]
  have hF : F oneV=0 := by rw [hFa]; simp only [havg,mul_one,hs,mul_zero]
  have hB (u : V) : B u oneV=0 := by
    simp only [B,centralWeightedForm_apply,hD,inner_zero_right,hT,Finset.sum_const_zero,mul_zero,add_zero]
  have hB' (v : V) : B oneV v=0 := by
    simp only [B,centralWeightedForm_apply,hD,inner_zero_left,hT,Finset.sum_const_zero,mul_zero,zero_add]
  have hcoer : IsCoercive (((B.comp M.ker.subtypeL).flip.comp M.ker.subtypeL).flip) := by
    refine ⟨C⁻¹,inv_pos.mpr hC,?_⟩
    intro u
    change C⁻¹*‖u‖*‖u‖≤B u.val u.val
    have hn : 0≤∑ i : Fin 3,‖spectralGraphWeight w (T i u.val)‖^2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hb : ‖D u.val‖^2+∑ i : Fin 3,‖spectralGraphWeight w (T i u.val)‖^2≤B u.val u.val := by
      simp only [B,centralWeightedForm_apply,real_inner_self_eq_norm_sq]
      nlinarith [mul_le_mul_of_nonneg_right hκ hn]
    have hh := (hP u).trans (mul_le_mul_of_nonneg_left hb hC.le)
    calc
      _=‖u‖^2/C := by ring
      _≤B u.val u.val := (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hh)
  obtain ⟨p,hp,hfull,huniq⟩ := solve_form_mod_constants B M F oneV hM hF hB hB' hcoer
  refine ⟨p,hp,?_,?_⟩
  · intro v
    exact (centralWeightedForm_apply κ w D T p v).symm.trans ((hfull v).trans (hFa v))
  · intro q hq
    apply huniq q
    intro v
    exact (centralWeightedForm_apply κ w D T q v).trans ((hq v).trans (hFa v).symm)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralUnnormalizedVariational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

theorem central_unnormalized_variational_exists (s slopes : Fin 3 → ℝ)
    (hs : ∑ i,slopes i=0) :
    ∃ p : centralEnergySpace s,centralM s p=0 ∧
      (∀ v : centralEnergySpace s,
        inner ℝ (centralD s p) (centralD s v)+
          angularArea*(∑ i : Fin 3,inner ℝ (spectralGraphWeight (torusRate s) (centralT s i p))
            (spectralGraphWeight (torusRate s) (centralT s i v)))=
          angularArea*(∑ i : Fin 3,slopes i*spectralGraphMean (torusRate s) (centralT s i v))) ∧
      (∀ q : centralEnergySpace s,(∀ v : centralEnergySpace s,
        inner ℝ (centralD s q) (centralD s v)+
          angularArea*(∑ i : Fin 3,inner ℝ (spectralGraphWeight (torusRate s) (centralT s i q))
            (spectralGraphWeight (torusRate s) (centralT s i v)))=
          angularArea*(∑ i : Fin 3,slopes i*spectralGraphMean (torusRate s) (centralT s i v))) →
        q-p=centralM s q • centralOne s) := by
  exact @central_variational_exists_graph_weighted (centralEnergySpace s) CentralGradients
    inferInstance (centralEnergy_inner s) inferInstance inferInstance inferInstance
    TorusModes inferInstance angularArea angularArea_ge_one (torusRate s) (centralD s) (centralT s)
    (centralM s) (centralOne s)
    (centralAmbientM_one s) (centralAmbientD_one s) (centralAmbientWeight_one s)
    (centralOne_mean s) (centralCoercivityConstant s) (centralCoercivityConstant_pos s)
    (central_graph_coercivity s) slopes hs

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CentralDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma central_smooth_integration_by_parts {f ψ : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆centralClosed) (v : Box3) :
    (∫ x,ψ x*fderiv ℝ f x v ∂centralMeasure)=
      -(∫ x,fderiv ℝ ψ x v*f x ∂centralMeasure) := by
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψ : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  let : (volume : Measure Box3).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (ℝ×ℝ)) (volume : Measure ℝ)
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := ψ) (g := f) (v := v)
    ((hdψ.mul hf.continuous).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_right)
    ((hψ.continuous.mul hdf).integrable_of_hasCompactSupport hc.mul_right)
    ((hψ.continuous.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_right)
    (fun x _ => hψ.differentiable (by simp) x)
    (fun x _ => hf.differentiable (by simp) x)
  have hl : (∫ x,ψ x*fderiv ℝ f x v ∂centralMeasure)=∫ x,ψ x*fderiv ℝ f x v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hs hh)),zero_mul]
  have hr : (∫ x,fderiv ℝ ψ x v*f x ∂centralMeasure)=∫ x,fderiv ℝ ψ x v*f x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun hh => hx (hs hh))]
    simp
  rw [hl,hr]
  exact he

theorem central_distributional_derivative (s : Fin 3 → ℝ)
    (u : centralEnergySpace s) (ψ : centralSmoothFunctions)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆centralClosed) (i : Fin 3) :
    inner ℝ (centralSmoothJet ψ 0) (centralAmbientComponent s i.succ u.val)=
      -inner ℝ (centralSmoothJet ψ i.succ) (centralAmbientComponent s 0 u.val) := by
  have hclosed : IsClosed {z : CentralAmbient s |
      inner ℝ (centralSmoothJet ψ 0) (centralAmbientComponent s i.succ z)=
        -inner ℝ (centralSmoothJet ψ i.succ) (centralAmbientComponent s 0 z)} :=
    isClosed_eq (continuous_const.inner (centralAmbientComponent s i.succ).continuous)
      ((continuous_const.inner (centralAmbientComponent s 0).continuous).neg)
  apply closure_minimal _ hclosed u.property
  rintro z ⟨f,rfl⟩
  change inner ℝ (centralSmoothJet ψ 0) (centralSmoothJet f i.succ)=
    -inner ℝ (centralSmoothJet ψ i.succ) (centralSmoothJet f 0)
  rw [L2.inner_def,L2.inner_def]
  have hl : (∫ x,inner ℝ (centralSmoothJet ψ 0 x) (centralSmoothJet f i.succ x) ∂centralMeasure)=
      ∫ x,ψ x*fderiv ℝ f x (centralDirection i) ∂centralMeasure := by
    apply integral_congr_ae
    filter_upwards [centralSmoothJet_ae ψ 0,centralSmoothJet_ae f i.succ] with x hx hy
    rw [hx,hy,centralJetField_succ]
    simp only [centralJetField,Matrix.cons_val_zero,Real.inner_apply,cubePartial]
  have hr : (∫ x,inner ℝ (centralSmoothJet ψ i.succ x) (centralSmoothJet f 0 x) ∂centralMeasure)=
      ∫ x,fderiv ℝ ψ x (centralDirection i)*f x ∂centralMeasure := by
    apply integral_congr_ae
    filter_upwards [centralSmoothJet_ae ψ i.succ,centralSmoothJet_ae f 0] with x hx hy
    rw [hx,hy,centralJetField_succ]
    simp only [centralJetField,Matrix.cons_val_zero,Real.inner_apply,cubePartial,mul_comm]
  rw [hl,hr]
  exact central_smooth_integration_by_parts (central_smooth f) (central_smooth ψ) hc hs _

lemma central_trace_zero (s : Fin 3 → ℝ) (ψ : centralSmoothFunctions) (i : Fin 3)
    (hz : ∀ x,ψ (centralBoundary i x)=0) : centralT s i (centralSmoothElement s ψ)=0 := by
  apply spectralTraceGraph_fst_injective (torusRate s)
  change (centralSmoothTrace s ψ i).val 0=0
  rw [centralSmoothTrace_fst]
  apply norm_eq_zero.mp
  have hn := centralTraceFourier_norm ψ i
  simp only [hz,zero_pow (by decide : 2≠0),integral_zero] at hn
  nlinarith only [hn,norm_nonneg (centralTraceFourier ψ i)]

theorem central_variational_weak_interior (s slopes : Fin 3 → ℝ)
    (hs : ∑ i,slopes i=0) :
    ∃ p : centralEnergySpace s,centralM s p=0 ∧ CentralVariationalEquation s slopes p ∧
      ∀ ψ : centralSmoothFunctions,(∀ (i : Fin 3) x,ψ (centralBoundary i x)=0) →
        inner ℝ (centralD s p) (centralJetD (centralSmoothJet ψ))=0 := by
  obtain ⟨p,hp,hvar,_⟩ := central_unnormalized_variational_exists s slopes hs
  refine ⟨p,hp,hvar,?_⟩
  intro ψ hψ
  have he := hvar (centralSmoothElement s ψ)
  have ht (i : Fin 3) := central_trace_zero s ψ i (hψ i)
  have hd : centralD s (centralSmoothElement s ψ)=centralJetD (centralSmoothJet ψ) := rfl
  rw [hd] at he
  simpa only [ht,map_zero,inner_zero_right,mul_zero,Finset.sum_const_zero,add_zero] using he

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CentralDistributionLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma centralSmoothPartial_jet_zero (f : centralSmoothFunctions) (i : Fin 3) :
    centralSmoothJet (centralSmoothPartial f i) 0=centralSmoothJet f i.succ := by
  apply Lp.ext
  filter_upwards [centralSmoothJet_ae (centralSmoothPartial f i) 0,
    centralSmoothJet_ae f i.succ] with x hx hy
  rw [hx,hy,centralJetField_succ]
  rfl

theorem central_variational_distributional_laplacian (s slopes : Fin 3 → ℝ)
    (hs : ∑ i,slopes i=0) :
    ∃ p : centralEnergySpace s,centralM s p=0 ∧ CentralVariationalEquation s slopes p ∧
      ∀ ψ : centralSmoothFunctions,HasCompactSupport ψ → tsupport ψ⊆centralClosed →
        (∀ (i : Fin 3) x,ψ (centralBoundary i x)=0) →
        (∫ x,(centralAmbientComponent s 0 p.val) x*centralLaplacian ψ x ∂centralMeasure)=0 := by
  obtain ⟨p,hp,hvar,hweak⟩ := central_variational_weak_interior s slopes hs
  refine ⟨p,hp,hvar,?_⟩
  intro ψ hc hsp hboundary
  have he := hweak ψ hboundary
  rw [PiLp.inner_apply] at he
  have hparts (i : Fin 3) :
      inner ℝ (centralSmoothJet ψ i.succ) (centralAmbientComponent s i.succ p.val)=
        -inner ℝ (centralSmoothJet (centralSmoothPartial ψ i) i.succ)
          (centralAmbientComponent s 0 p.val) := by
    have hd := central_distributional_derivative s p (centralSmoothPartial ψ i)
      (cubePartial_compact hc _) ((tsupport_fderiv_apply_subset ℝ _).trans hsp) i
    rwa [centralSmoothPartial_jet_zero] at hd
  have hsum : (∑ i : Fin 3,inner ℝ (centralSmoothJet (centralSmoothPartial ψ i) i.succ)
        (centralAmbientComponent s 0 p.val))=0 := by
    have hrew (i : Fin 3) :
        inner ℝ (centralD s p i) (centralJetD (centralSmoothJet ψ) i)=
          -inner ℝ (centralSmoothJet (centralSmoothPartial ψ i) i.succ)
            (centralAmbientComponent s 0 p.val) := by
      rw [real_inner_comm]
      exact hparts i
    simp only [hrew,Finset.sum_neg_distrib,neg_eq_zero] at he
    exact he
  have hint (i : Fin 3) :
      inner ℝ (centralSmoothJet (centralSmoothPartial ψ i) i.succ) (centralAmbientComponent s 0 p.val)=
        ∫ x,(centralAmbientComponent s 0 p.val) x*
          cubePartial (cubePartial ψ (centralDirection i)) (centralDirection i) x ∂centralMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [centralSmoothJet_ae (centralSmoothPartial ψ i) i.succ] with x hx
    rw [hx,centralJetField_succ,Real.inner_apply]
    exact mul_comm _ _
  have hInt (i : Fin 3) : Integrable (fun x => (centralAmbientComponent s 0 p.val) x*
      cubePartial (cubePartial ψ (centralDirection i)) (centralDirection i) x) centralMeasure :=
    (Lp.memLp _).integrable_mul (central_continuous_memLp
      (cubePartial_smooth (cubePartial_smooth (central_smooth ψ) _) _).continuous)
  simp only [hint] at hsum
  simpa only [centralLaplacian,Finset.mul_sum,integral_finsetSum _ (fun i _ => hInt i)] using hsum

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_KernelParamDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory
open scoped Convolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [BorelSpace E]

theorem convolution_param_hasDerivAt [FiniteDimensional ℝ E]
    [Measure.IsAddHaarMeasure (volume : Measure E)] {f : E → ℝ} (hf : LocallyIntegrable f)
    {K : ℝ → E → ℝ} {S : Set ℝ} {C : Set E} (hS : IsOpen S) (hC : IsCompact C)
    (hK : ContDiffOn ℝ 1 (Function.uncurry K) (S ×ˢ univ))
    (hzero : ∀ s y, s∈S → y∉C → K s y=0)
    {s : ℝ} (hs : s∈S) {D : E → ℝ} (hD : ∀ y, HasDerivAt (fun r => K r y) (D y) s)
    (x : E) :
    HasDerivAt (fun r => (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] K r) x)
      ((f ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] D) x) s := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  let J : E → (ℝ × E →L[ℝ] ℝ) := fun y => fderiv ℝ (Function.uncurry K) (s,y)
  have hJ : Continuous J := by
    apply (hK.continuousOn_fderiv_of_isOpen (hS.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id)
    intro y
    exact ⟨hs,mem_univ _⟩
  have hJzero {y : E} (hy : y∉C) : J y=0 := by
    apply (hasFDerivAt_zero_of_eventually_const 0 ?_).fderiv
    have he : S ×ˢ Cᶜ ∈ 𝓝 (s,y) :=
      (hS.prod hC.isClosed.isOpen_compl).mem_nhds ⟨hs,hy⟩
    filter_upwards [he] with z hz
    exact hzero z.1 z.2 hz.1 hz.2
  have hJc : HasCompactSupport J :=
    HasCompactSupport.of_support_subset_isCompact hC (by
      intro y hy
      by_contra hn
      exact hy (hJzero hn))
  have hi : Integrable (fun y => L.precompR (ℝ × E) (f y) (J (x-y))) :=
    hJc.convolutionExists_right (L.precompR (ℝ × E)) hf hJ x
  have hdiff := hasFDerivAt_convolution_right_with_param L hS hC hzero hf hK (s,x) hs
  have hcurve := ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have hout := hdiff.comp_hasDerivAt s hcurve
  have hJval (y : E) : J y (1,0)=D y := by
    have ha : DifferentiableAt ℝ (Function.uncurry K) (s,y) := (hK.contDiffAt ((hS.prod isOpen_univ).mem_nhds ⟨hs,mem_univ y⟩)).differentiableAt (by norm_num)
    have he := ha.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))
    exact (he.unique (hD y))
  convert hout using 1 <;> try rfl
  change (∫ y, f y*D (x-y))=(∫ y, L.precompR (ℝ × E) (f y) (J (x-y))) (1,0)
  rw [ContinuousLinearMap.integral_apply hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by simp [L,hJval])
end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_RadialLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open InnerProductSpace Laplacian
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma radial_fderiv {f g : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (g t) t) (x : E) :
    fderiv ℝ (fun y : E => f (‖y‖^2)) x = (2*g (‖x‖^2)) • innerSL ℝ x := by
  have h := (hf (‖x‖^2)).comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  apply h.fderiv.trans
  ext v
  simp [two_smul,smul_eq_mul,innerSL_apply_apply]
  ring

lemma radial_second {f g h : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, HasDerivAt g (h t) t)
    (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y : E => f (‖y‖^2))) x v w =
      4*h (‖x‖^2)*⟪x,v⟫*⟪x,w⟫ + 2*g (‖x‖^2)*⟪v,w⟫ := by
  have he : fderiv ℝ (fun y : E => f (‖y‖^2)) =
      (fun y : E => (2*g (‖y‖^2)) • innerSL ℝ y) := funext (radial_fderiv hf)
  rw [he]
  have hd := (((hg (‖x‖^2)).comp_hasFDerivAt x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul 2).smul
      ((innerSL ℝ (E := E)).hasFDerivAt (x := x))
  have he' := congrArg (fun T : E →L[ℝ] E →L[ℝ] ℝ => T v w) hd.fderiv
  dsimp only [Pi.smul_apply,Function.comp_apply] at he'
  apply he'.trans
  simp [two_smul,smul_eq_mul,innerSL]
  ring

lemma radial_laplacian [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {f g h : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, HasDerivAt g (h t) t)
    (x : E) :
    Δ (fun y : E => f (‖y‖^2)) x =
      4*‖x‖^2*h (‖x‖^2) + 2*(Fintype.card ι : ℝ)*g (‖x‖^2) := by
  have hl : Δ (fun y : E => f (‖y‖^2)) x =
      ∑ i, fderiv ℝ (fderiv ℝ (fun y : E => f (‖y‖^2))) x (b i) (b i) := by
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
    apply Finset.sum_congr rfl
    intro i hi
    exact (bilinearIteratedFDerivTwo_eq_iteratedFDeriv (𝕜 := ℝ) _ x (b i) (b i)).symm
  rw [hl]
  simp_rw [radial_second hf hg]
  have hi : ∑ i, ⟪x,b i⟫*⟪x,b i⟫ = ‖x‖^2 := by
    simpa only [real_inner_comm (b _) x,real_inner_self_eq_norm_sq] using b.sum_inner_mul_inner x x
  calc
    _ = 4*h (‖x‖^2)*(∑ i, ⟪x,b i⟫*⟪x,b i⟫) +
        ∑ i, 2*g (‖x‖^2)*⟪b i,b i⟫ := by
      rw [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 4*‖x‖^2*h (‖x‖^2)+2*(Fintype.card ι : ℝ)*g (‖x‖^2) := by
      rw [hi]
      simp only [real_inner_self_eq_norm_sq,b.norm_eq_one,one_pow,mul_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring

end

section
open MeasureTheory Set InnerProductSpace Laplacian
open scoped RealInnerProductSpace

lemma hasDerivAt_radialEta {χ χ' : ℝ → ℝ} (hχ : ∀ t, HasDerivAt χ (χ' t) t)
    {s : ℝ} (hs : s≠0) (x : WeylSpace) :
    HasDerivAt (fun r => radialEta χ r x)
      (-(3*χ (‖x‖^2/s^2)/s^4+2*‖x‖^2*χ' (‖x‖^2/s^2)/s^6)) s := by
  have hd := ((hχ _).comp s ((hasDerivAt_const s (‖x‖^2)).div ((hasDerivAt_id s).pow 2) (pow_ne_zero _ hs))).div
    ((hasDerivAt_id s).pow 3) (pow_ne_zero _ hs)
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try dsimp [radialEta,Function.comp_def]
  all_goals try rfl
  all_goals try field_simp [hs]
  all_goals ring

lemma radialTheta_laplacian {χ χ' Ψ : ℝ → ℝ}
    (hΨ : ∀ t, HasDerivAt Ψ (-χ t) t) (hχ : ∀ t, HasDerivAt χ (χ' t) t)
    {s : ℝ} (hs : s≠0) (x : WeylSpace) :
    Δ (radialTheta Ψ s) x = -(3*χ (‖x‖^2/s^2)/s^4+2*‖x‖^2*χ' (‖x‖^2/s^2)/s^6) := by
  have hf (t : ℝ) : HasDerivAt (fun z => Ψ (z/s^2)/(2*s^2))
      (-χ (t/s^2)/(2*s^4)) t := by
    convert ((hΨ _).comp t ((hasDerivAt_id t).div_const (s^2))).div_const (2*s^2) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals try dsimp [Function.comp_def]
    all_goals try field_simp [hs]
  have hg (t : ℝ) : HasDerivAt (fun z => -χ (z/s^2)/(2*s^4))
      (-χ' (t/s^2)/(2*s^6)) t := by
    convert (((hχ _).comp t ((hasDerivAt_id t).div_const (s^2))).neg).div_const (2*s^4) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals try dsimp [Function.comp_def]
    all_goals try field_simp [hs]
  have hh := radial_laplacian (EuclideanSpace.basisFun (Fin 3) ℝ) hf hg x
  apply hh.trans
  simp only [Fintype.card_fin,Nat.cast_ofNat]
  field_simp [hs]
  ring

theorem radial_scale_laplacian {χ χ' Ψ : ℝ → ℝ}
    (hΨ : ∀ t, HasDerivAt Ψ (-χ t) t) (hχ : ∀ t, HasDerivAt χ (χ' t) t)
    {s : ℝ} (hs : s≠0) (x : WeylSpace) :
    HasDerivAt (fun r => radialEta χ r x) (Δ (radialTheta Ψ s) x) s := by
  rw [radialTheta_laplacian hΨ hχ hs]
  exact hasDerivAt_radialEta hχ hs x

end

open Set MeasureTheory Filter Topology InnerProductSpace Laplacian
open scoped RealInnerProductSpace

lemma normsq_smooth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : E => ‖x‖^2) := by
  simpa only [id_eq,real_inner_self_eq_norm_sq] using (contDiff_id.inner ℝ contDiff_id :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : E => ⟪x,x⟫))

lemma radialRaw_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) radialRaw :=
  radialOneBump.contDiff.comp normsq_smooth

lemma radialOneBump_zero {t : ℝ} (ht : 1≤t) : radialOneBump t=0 := by
  apply Function.notMem_support.mp
  rw [radialOneBump.support_eq]
  change ¬dist t 0<1
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by linarith)]
  exact not_lt.mpr ht

lemma radialRaw_zero {x : WeylSpace} (hx : 1≤‖x‖) : radialRaw x=0 := by
  apply radialOneBump_zero
  nlinarith [norm_nonneg x]

lemma radialRaw_compact : HasCompactSupport radialRaw := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:WeylSpace) 1)
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  exact le_of_not_gt (fun hn => hx (radialRaw_zero hn.le))

lemma radialRaw_zero_value : radialRaw 0=1 := by
  apply radialOneBump.one_of_mem_closedBall
  norm_num [radialOneBump]

lemma radialRaw_nonneg (x : WeylSpace) : 0 ≤ radialRaw x := radialOneBump.nonneg

lemma radialMass_pos : 0 < radialMass := by
  apply (integral_pos_iff_support_of_nonneg radialRaw_nonneg
    (radialRaw_smooth.continuous.integrable_of_hasCompactSupport radialRaw_compact)).2
  exact radialRaw_smooth.continuous.isOpen_support.measure_pos volume
    ⟨0,by rw [Function.mem_support,radialRaw_zero_value]; norm_num⟩

lemma radialProfile_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) radialProfile :=
  radialOneBump.contDiff.div_const _

lemma radialProfile_nonneg (t : ℝ) : 0 ≤ radialProfile t :=
  div_nonneg radialOneBump.nonneg radialMass_pos.le

lemma radialProfile_zero {t : ℝ} (ht : 1≤t) : radialProfile t=0 := by
  simp [radialProfile,radialOneBump_zero ht]

lemma radialProfilePrimitive_deriv (t : ℝ) :
    HasDerivAt radialProfilePrimitive (-radialProfile t) t :=
  intervalIntegral.integral_hasDerivAt_left (radialProfile_smooth.continuous.intervalIntegrable _ _)
    (radialProfile_smooth.continuous.stronglyMeasurableAtFilter _ _) radialProfile_smooth.continuous.continuousAt

lemma radialProfilePrimitive_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) radialProfilePrimitive := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (radialProfilePrimitive_deriv t).differentiableAt,?_⟩
  have he : deriv radialProfilePrimitive = -radialProfile :=
    funext (fun t => (radialProfilePrimitive_deriv t).deriv)
  rw [he]
  exact radialProfile_smooth.neg

lemma radialProfilePrimitive_zero {t : ℝ} (ht : 1≤t) : radialProfilePrimitive t=0 := by
  change (∫ r in t..1, radialProfile r)=0
  rw [←intervalIntegral.integral_zero (a := t) (b := 1) (μ := volume)]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_ge ht] at hr
  exact radialProfile_zero hr.1

lemma radialEta_smooth (s : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (radialEta radialProfile s) :=
  (radialProfile_smooth.comp (normsq_smooth.div_const _)).div_const _

lemma radialTheta_smooth (s : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (radialTheta radialProfilePrimitive s) :=
  (radialProfilePrimitive_smooth.comp (normsq_smooth.div_const _)).div_const _

lemma radialEta_zero {s : ℝ} (hs : 0 < s) {x : WeylSpace} (hx : s≤‖x‖) :
    radialEta radialProfile s x=0 := by
  have h : 1≤‖x‖^2/s^2 := (le_div_iff₀ (sq_pos_of_pos hs)).mpr (by nlinarith [norm_nonneg x])
  simp [radialEta,radialProfile_zero h]

lemma radialTheta_zero {s : ℝ} (hs : 0 < s) {x : WeylSpace} (hx : s≤‖x‖) :
    radialTheta radialProfilePrimitive s x=0 := by
  have h : 1≤‖x‖^2/s^2 := (le_div_iff₀ (sq_pos_of_pos hs)).mpr (by nlinarith [norm_nonneg x])
  simp [radialTheta,radialProfilePrimitive_zero h]

lemma radialEta_compact {s : ℝ} (hs : 0 < s) : HasCompactSupport (radialEta radialProfile s) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:WeylSpace) s)
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  exact le_of_not_gt (fun hn => hx (radialEta_zero hs hn.le))

lemma radialTheta_compact {s : ℝ} (hs : 0 < s) : HasCompactSupport (radialTheta radialProfilePrimitive s) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:WeylSpace) s)
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  exact le_of_not_gt (fun hn => hx (radialTheta_zero hs hn.le))

lemma radialEta_nonneg {s : ℝ} (hs : 0 < s) (x : WeylSpace) :
    0 ≤ radialEta radialProfile s x := div_nonneg (radialProfile_nonneg _) (by positivity)

lemma radialEta_integral {s : ℝ} (hs : 0 < s) : (∫ x, radialEta radialProfile s x)=1 := by
  have he : radialEta radialProfile s = fun x => (radialRaw (s⁻¹ • x)/radialMass)/s^3 := by
    ext x
    simp [radialEta,radialProfile,radialRaw,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,div_eq_mul_inv,mul_comm]
  rw [he,integral_div,integral_div,Measure.integral_comp_smul volume]
  simp only [WeylSpace, finrank_euclideanSpace, Fintype.card_fin,inv_pow,inv_inv,smul_eq_mul]
  rw [abs_of_pos (pow_pos hs 3)]
  change (s^3*radialMass)/radialMass/s^3=1
  field_simp [radialMass_pos.ne',hs.ne']

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_RadialWeylScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set Filter Topology MeasureTheory Laplacian InnerProductSpace
open scoped Convolution

lemma radialEta_joint_smooth : ContDiffOn ℝ (↑(⊤ : ℕ∞))
    (Function.uncurry (radialEta radialProfile)) (Ioi 0 ×ˢ univ) := by
  apply ContDiffOn.div
  · exact radialProfile_smooth.comp_contDiffOn
      ((normsq_smooth.comp contDiff_snd).contDiffOn.div
        (contDiff_fst.pow 2).contDiffOn (fun p hp => pow_ne_zero _ (ne_of_gt hp.1)))
  · exact (contDiff_fst.pow 3).contDiffOn
  · intro p hp
    exact pow_ne_zero _ (ne_of_gt hp.1)

lemma laplacian_sub_right (f : WeylSpace → ℝ) (a y : WeylSpace) :
    Δ (fun z => f (z-a)) y=Δ f (y-a) := by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_comp_sub]

lemma radialTheta_laplacian_sub_left (s : ℝ) (x y : WeylSpace) :
    Δ (fun z => radialTheta radialProfilePrimitive s (x-z)) y=
      Δ (radialTheta radialProfilePrimitive s) (x-y) := by
  have he : (fun z => radialTheta radialProfilePrimitive s (x-z))=
      (fun z => radialTheta radialProfilePrimitive s (z-x)) := by
    ext z
    simp only [radialTheta,norm_sub_rev]
  rw [he,laplacian_sub_right]
  by_cases hs : s=0
  · subst s
    have hz : radialTheta radialProfilePrimitive 0=(fun _ : WeylSpace => (0:ℝ)) := by
      ext z
      simp [radialTheta]
    rw [hz]
    simp only [laplacian_const,Pi.zero_apply]
  · rw [radialTheta_laplacian radialProfilePrimitive_deriv
      (fun t => (radialProfile_smooth.differentiable (by simp) t).hasDerivAt) hs,
      radialTheta_laplacian radialProfilePrimitive_deriv
      (fun t => (radialProfile_smooth.differentiable (by simp) t).hasDerivAt) hs]
    simp only [norm_sub_rev]

lemma radialMollify_smooth {f : WeylSpace → ℝ} (hf : LocallyIntegrable f)
    {s : ℝ} (hs : 0 < s) : ContDiff ℝ (↑(⊤ : ℕ∞)) (radialMollify f s) :=
  (radialEta_compact hs).contDiff_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hf (radialEta_smooth s)

lemma radialMollify_hasDerivAt {f : WeylSpace → ℝ} (hf : LocallyIntegrable f)
    {s : ℝ} (hs : 0 < s) (x : WeylSpace) :
    HasDerivAt (fun r => radialMollify f r x)
      (∫ y, f y*Δ (radialTheta radialProfilePrimitive s) (x-y)) s := by
  apply convolution_param_hasDerivAt hf isOpen_Ioo (isCompact_closedBall (0:WeylSpace) (2*s))
    (S := Ioo (s/2) (2*s))
  · apply (radialEta_joint_smooth.of_le (by simp)).mono
    rintro ⟨r,y⟩ ⟨⟨hr₁,hr₂⟩,_⟩
    exact ⟨(half_pos hs).trans hr₁,mem_univ _⟩
  · intro r y hr hy
    apply radialEta_zero (by linarith [hr.1])
    have hn : 2*s<‖y‖ := by simpa [Metric.mem_closedBall,dist_zero_right] using hy
    exact hr.2.le.trans hn.le
  · constructor <;> linarith
  · intro y
    exact radial_scale_laplacian radialProfilePrimitive_deriv
      (fun t => (radialProfile_smooth.differentiable (by simp) t).hasDerivAt) hs.ne' y

lemma radialMollify_hasDerivAt_zero {f : WeylSpace → ℝ} (hf : LocallyIntegrable f)
    {U : Set WeylSpace} (hw : WeaklyHarmonicOn f U)
    {s : ℝ} (hs : 0 < s) {x : WeylSpace} (hx : Metric.closedBall x s⊆U) :
    HasDerivAt (fun r => radialMollify f r x) 0 s := by
  have hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y => radialTheta radialProfilePrimitive s (x-y)) :=
    (radialTheta_smooth s).comp (contDiff_const.sub contDiff_id)
  have hc : HasCompactSupport (fun y => radialTheta radialProfilePrimitive s (x-y)) :=
    (radialTheta_compact hs).comp_homeomorph (Homeomorph.subLeft x)
  have hv : tsupport (fun y => radialTheta radialProfilePrimitive s (x-y))⊆Metric.closedBall x s := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro y hy
    rw [Metric.mem_closedBall,dist_eq_norm]
    by_contra hn
    exact hy (radialTheta_zero hs (by simpa only [norm_sub_rev] using (not_le.mp hn).le))
  have he := hw _ hψ hc (hv.trans hx)
  simp_rw [radialTheta_laplacian_sub_left] at he
  simpa only [he] using radialMollify_hasDerivAt hf hs x

theorem radialMollify_scale_independent {f : WeylSpace → ℝ} (hf : LocallyIntegrable f)
    {U : Set WeylSpace} (hw : WeaklyHarmonicOn f U) {x : WeylSpace}
    {R : ℝ} (hR : Metric.closedBall x R⊆U) {s t : ℝ}
    (hs : 0 < s ∧ s<R) (ht : 0<t ∧ t<R) : radialMollify f s x=radialMollify f t x := by
  have hd (r : ℝ) (hr : r∈Ioo 0 R) : HasDerivAt (fun a => radialMollify f a x) 0 r :=
    radialMollify_hasDerivAt_zero hf hw hr.1
      ((Metric.closedBall_subset_closedBall hr.2.le).trans hR)
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0:ℝ) R).isPreconnected
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hd r hr).deriv) hs ht

end

open Set MeasureTheory

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_L2TranslationAverage
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

open Set MeasureTheory Filter Topology
open scoped Convolution

lemma radialProbability_probability {s : ℝ} (hs : 0 < s) : IsProbabilityMeasure (radialProbability s) where
  measure_univ := by
    rw [radialProbability,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ←ofReal_integral_eq_lintegral_ofReal
        ((radialEta_smooth s).continuous.integrable_of_hasCompactSupport (radialEta_compact hs))
        (ae_of_all _ (radialEta_nonneg hs)),radialEta_integral hs]
    simp

lemma radialProbability_integral {s : ℝ} (hs : 0 < s) (f : WeylSpace → ℝ) :
    (∫ y, f y ∂radialProbability s)=∫ y, radialEta radialProfile s y*f y := by
  rw [radialProbability,integral_withDensity_eq_integral_toReal_smul
    (radialEta_smooth s).continuous.measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (radialEta_nonneg hs _),smul_eq_mul]

lemma radialProbability_ball {s : ℝ} (hs : 0 < s) :
    ∀ᵐ y ∂radialProbability s, ‖y‖ < s := by
  rw [radialProbability,ae_withDensity_iff (radialEta_smooth s).continuous.measurable.ennreal_ofReal]
  filter_upwards with y hy
  by_contra hn
  have he := radialEta_zero hs (not_lt.mp hn)
  exact hy (by rw [he]; simp)

lemma radialMollify_eq_average {s : ℝ} (hs : 0 < s) (f : WeylSpace → ℝ) (x : WeylSpace) :
    radialMollify f s x=∫ y, f (x-y) ∂radialProbability s := by
  rw [radialProbability_integral hs,radialMollify,convolution_eq_swap]
  congr 1
  ext y
  simp [mul_comm]

lemma radialMollify_sub {s : ℝ} (hs : 0 < s) (f : WholeL2) (x : WeylSpace) :
    radialMollify f s x-f x=∫ y, (f (x-y)-f x) ∂radialProbability s := by
  rw [radialProbability_integral hs]
  simp_rw [mul_sub]
  have hi : Integrable (fun y => radialEta radialProfile s y*f (x-y)) :=
    (radialEta_compact hs).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (radialEta_smooth s).continuous ((Lp.memLp f).locallyIntegrable (by norm_num)) x
  rw [integral_sub hi (((radialEta_smooth s).continuous.integrable_of_hasCompactSupport
    (radialEta_compact hs)).mul_const _),integral_mul_const,radialEta_integral hs,one_mul]
  rw [radialMollify_eq_average hs,radialProbability_integral hs]

lemma radialMollify_memLp {s : ℝ} (hs : 0 < s) (f : WholeL2) :
    MemLp (radialMollify f s) 2 volume := by
  let := radialProbability_probability hs
  obtain ⟨hm,_⟩ := memLp_probability_average (whole_translation_memLp (μ := radialProbability s) f)
  exact MemLp.ae_eq (ae_of_all _ (fun x => (radialMollify_eq_average hs f x).symm)) hm

theorem radialMollify_approx (f : WholeL2) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ s : ℝ, 0 < s → s≤δ →
      (∫ x, (radialMollify f s x-f x)^2) ≤ ε := by
  obtain ⟨δ,hδ,hd⟩ := small_translation_radius f hε
  refine ⟨δ,hδ,fun s hs hsd => ?_⟩
  let := radialProbability_probability hs
  obtain ⟨_,he⟩ := translation_average_sq_le (μ := radialProbability s) f
    (show ∀ᵐ y ∂radialProbability s, ‖translateL2 y f-f‖^2≤ε from by
      filter_upwards [radialProbability_ball hs] with y hy
      exact (hd y (hy.trans_le hsd)).le)
  simpa only [radialMollify_sub hs] using he

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_WeakWeyl
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma closedBall_near_subset {a x : WeylSpace} {R : ℝ} (hR : 0<R)
    (hx : x∈Metric.ball a (R/4)) : Metric.closedBall x (R/2)⊆Metric.closedBall a R := by
  intro y hy
  rw [Metric.mem_closedBall] at hy ⊢
  have hxa : dist x a<R/4 := hx
  exact (dist_triangle y x a).trans (by linarith)

theorem weakWeyl_local {f : WholeL2} {U : Set WeylSpace}
    (hw : WeaklyHarmonicOn f U) {a : WeylSpace} {R : ℝ} (hR : 0<R)
    (hball : Metric.closedBall a R⊆U) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (radialMollify f (R/4)) ∧
    (f : WeylSpace → ℝ) =ᵐ[volume.restrict (Metric.ball a (R/4))] radialMollify f (R/4) := by
  have hf : LocallyIntegrable (f : WeylSpace → ℝ) := (Lp.memLp f).locallyIntegrable (by norm_num)
  have hs : 0<R/4 := by linarith
  refine ⟨radialMollify_smooth hf hs,?_⟩
  let V := Metric.ball a (R/4)
  let g := radialMollify f (R/4)
  have he (r : ℝ) (hr : 0 < r ∧ r<R/2) (x : WeylSpace) (hx : x∈V) :
      g x=radialMollify f r x :=
    radialMollify_scale_independent hf hw ((closedBall_near_subset hR hx).trans hball)
      ⟨hs,by linarith⟩ hr
  have hi : Integrable (fun x => (g x-f x)^2) :=
    ((radialMollify_memLp hs f).sub (Lp.memLp f)).integrable_sq
  have hbound (ε : ℝ) (hε : 0<ε) : (∫ x in V, (g x-f x)^2)≤ε := by
    obtain ⟨δ,hδ,hd⟩ := radialMollify_approx f hε
    let r := min δ (R/4)/2
    have hr : 0 < r := by dsimp [r]; positivity
    have hrδ : r≤δ := by dsimp [r]; have := min_le_left δ (R/4); linarith [lt_min hδ hs]
    have hrR : r<R/2 := by dsimp [r]; have := min_le_right δ (R/4); linarith
    have heq : (∫ x in V, (g x-f x)^2)=∫ x in V, (radialMollify f r x-f x)^2 := by
      apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
      intro x hx
      change (g x-f x)^2=(radialMollify f r x-f x)^2
      rw [he r ⟨hr,hrR⟩ x hx]
    rw [heq]
    exact (setIntegral_le_integral ((radialMollify_memLp hr f).sub (Lp.memLp f)).integrable_sq
      (ae_of_all _ (fun x => sq_nonneg _))).trans (hd r hr hrδ)
  have hz : (∫ x in V, (g x-f x)^2)=0 := by
    apply le_antisymm _ (integral_nonneg (fun x => sq_nonneg _))
    by_contra hn
    have hp : 0<(∫ x in V, (g x-f x)^2) := lt_of_not_ge hn
    have hh := hbound ((∫ x in V, (g x-f x)^2)/2) (by linarith)
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun x => sq_nonneg (g x-f x)))
    hi.restrict).mp hz
  filter_upwards [hae] with x hx
  exact (sub_eq_zero.mp (sq_eq_zero_iff.mp hx)).symm

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped Convolution

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F]

lemma radialAverageF_fderiv {f : WeylSpace → F} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) {s : ℝ} (_ : 0 < s) (x : WeylSpace) :
    fderiv ℝ (radialAverageF f s) x=radialAverageF (fderiv ℝ f) s x := by
  have hd := hc.hasFDerivAt_convolution_right (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    (radialEta_smooth s).continuous.locallyIntegrable (hf.of_le (by simp)) x
  unfold radialAverageF
  rw [hd.fderiv]
  congr 1

lemma RadialMeanOn.derivative {f : WeylSpace → F} {a : WeylSpace} {R : ℝ}
    (hm : RadialMeanOn f a R) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) : RadialMeanOn (fderiv ℝ f) a R := by
  intro s hs x hx
  have he : f =ᶠ[𝓝 x] radialAverageF f s := by
    have ho : IsOpen {y : WeylSpace | dist y a+s<R} := isOpen_lt (by fun_prop) continuous_const
    filter_upwards [ho.mem_nhds hx] with y hy
    exact hm s hs y hy
  rw [he.fderiv_eq,radialAverageF_fderiv hf hc hs]

lemma RadialMeanOn.derivative_bound {f : WeylSpace → F} {a x : WeylSpace} {R s M : ℝ}
    (hm : RadialMeanOn f a R) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hs : 0 < s) (hx : dist x a+s<R) (_ : 0≤M)
    (hb : ∀ y∈Metric.closedBall x s, ‖f y‖≤M) :
    ‖fderiv ℝ f x‖≤M*(∫ y, ‖fderiv ℝ (radialEta radialProfile s) y‖) := by
  have he : f =ᶠ[𝓝 x] radialAverageF f s := by
    have ho : IsOpen {y : WeylSpace | dist y a+s<R} := isOpen_lt (by fun_prop) continuous_const
    filter_upwards [ho.mem_nhds hx] with y hy
    exact hm s hs y hy
  have hd := (radialEta_compact hs).hasFDerivAt_convolution_left (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℝ) ((radialEta_smooth s).of_le (by simp))
    hf.continuous.locallyIntegrable x
  rw [he.fderiv_eq]
  unfold radialAverageF
  rw [hd.fderiv]
  let L : (WeylSpace →L[ℝ] ℝ) →L[ℝ] F →L[ℝ] (WeylSpace →L[ℝ] F) := (ContinuousLinearMap.lsmul ℝ ℝ).precompL WeylSpace
  have hi := ((radialEta_compact hs).fderiv ℝ).convolutionExists_left (μ := volume) L
    ((radialEta_smooth s).continuous_fderiv (by simp)) hf.continuous.locallyIntegrable x
  have hn : Integrable (fun y => M*‖fderiv ℝ (radialEta radialProfile s) y‖) :=
    (((radialEta_smooth s).continuous_fderiv (by simp)).integrable_of_hasCompactSupport
      ((radialEta_compact hs).fderiv ℝ)).norm.const_mul M
  calc
    _ ≤ ∫ y, ‖L (fderiv ℝ (radialEta radialProfile s) y) (f (x-y))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, M*‖fderiv ℝ (radialEta radialProfile s) y‖ := by
      apply integral_mono_ae hi.norm hn
      filter_upwards with y
      by_cases hy : ‖y‖ ≤ s
      · have hb' : ‖f (x-y)‖≤M := hb _ (by simpa [Metric.mem_closedBall,dist_eq_norm] using hy)
        change ‖(fderiv ℝ (radialEta radialProfile s) y).smulRight (f (x-y))‖ ≤ _
        rw [ContinuousLinearMap.norm_smulRight_apply]
        exact (mul_le_mul_of_nonneg_left hb' (norm_nonneg _)).trans_eq (mul_comm _ _)
      · have hz : fderiv ℝ (radialEta radialProfile s) y=0 := by
          apply Function.notMem_support.mp
          intro hd
          have ht := support_fderiv_subset ℝ hd
          revert ht
          intro ht
          have hsub : tsupport (radialEta radialProfile s)⊆Metric.closedBall (0:WeylSpace) s := by
            apply closure_minimal _ Metric.isClosed_closedBall
            intro z hz
            rw [Metric.mem_closedBall,dist_zero_right]
            exact le_of_not_gt (fun hh => hz (radialEta_zero hs hh.le))
          exact hy (by simpa [Metric.mem_closedBall,dist_zero_right] using hsub ht)
        simp [hz,L]
    _ = M*(∫ y, ‖fderiv ℝ (radialEta radialProfile s) y‖) := integral_const_mul _ _

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_WeakHarmonicMean
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace
open scoped Convolution

lemma WeaklyHarmonicOn.congr_ae {f g : WeylSpace → ℝ} {U : Set WeylSpace}
    (he : f =ᵐ[volume] g) (hf : WeaklyHarmonicOn f U) : WeaklyHarmonicOn g U := by
  intro ψ hψ hc hs
  rw [←hf ψ hψ hc hs]
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

lemma laplacian_zero_off_support {ψ : WeylSpace → ℝ} {x : WeylSpace}
    (hx : x∉tsupport ψ) : Δ ψ x=0 := by
  have he : ψ =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
    filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [(laplacian_congr_nhds he).eq_of_nhds]
  simp

lemma WeaklyHarmonicOn.congr_restrict {f g : WeylSpace → ℝ} {U : Set WeylSpace}
    (hU : MeasurableSet U) (he : f =ᵐ[volume.restrict U] g)
    (hf : WeaklyHarmonicOn f U) : WeaklyHarmonicOn g U := by
  intro ψ hψ hc hs
  rw [←hf ψ hψ hc hs]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hU).mp he] with x hx
  by_cases h : x∈U
  · rw [hx h]
  · have he : Δ ψ x=0 := laplacian_zero_off_support (fun hy => h (hs hy))
    simp [he]

lemma weaklyHarmonic_smooth_mean {f : WeylSpace → ℝ} {a : WeylSpace} {R : ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hc : HasCompactSupport f)
    (hw : WeaklyHarmonicOn f (Metric.ball a R)) : RadialMeanOn f a (R/4) := by
  have hm : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport hc
  let fl : WholeL2 := hm.toLp f
  have hw' : WeaklyHarmonicOn fl (Metric.ball a R) := .congr_ae hm.coeFn_toLp.symm hw
  intro s hs x hx
  have hball : Metric.closedBall x (4*s)⊆Metric.ball a R := by
    intro y hy
    have hy' : dist y x ≤ 4*s := hy
    have hd := dist_triangle y x a
    change dist y a<R
    have hx' : 0≤dist x a := dist_nonneg
    linarith
  obtain ⟨hsm,he⟩ := weakWeyl_local hw' (by positivity : 0<4*s) hball
  have hcvg : radialMollify fl s=radialMollify f s :=
    convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) hm.coeFn_toLp Filter.EventuallyEq.rfl
  have he' : f =ᵐ[volume.restrict (Metric.ball x s)] radialMollify f s := by
    have hh : f =ᵐ[volume.restrict (Metric.ball x (4*s/4))] fl :=
      ae_restrict_of_ae hm.coeFn_toLp.symm
    have h := hh.trans he
    have hs4 : 4*s/4=s := by ring
    simpa only [hs4,hcvg] using h
  have hp := Measure.eqOn_open_of_ae_eq he' Metric.isOpen_ball hf.continuous.continuousOn
    (radialMollify_smooth hf.continuous.locallyIntegrable hs).continuous.continuousOn (Metric.mem_ball_self hs)
  rw [hp,radialMollify_eq_average hs,radialProbability_integral hs]
  rfl

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma radialEta_as_scale {s : ℝ} (_ : 0 < s) :
    radialEta radialProfile s = fun x => s⁻¹^3 * radialEta radialProfile 1 (s⁻¹ • x) := by
  ext x
  simp [radialEta,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,div_eq_mul_inv,mul_comm]

lemma radialEta_fderiv_scale {s : ℝ} (hs : 0 < s) (x : WeylSpace) :
    fderiv ℝ (radialEta radialProfile s) x =
      s⁻¹^4 • fderiv ℝ (radialEta radialProfile 1) (s⁻¹ • x) := by
  have hd := (((radialEta_smooth 1).differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul s⁻¹)).const_smul (s⁻¹^3)
  rw [radialEta_as_scale hs]
  refine hd.fderiv.trans ?_
  ext v
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_smul]
  congr 1

lemma radialGradientMass_nonneg : 0 ≤ radialGradientMass := integral_nonneg (fun _ => norm_nonneg _)

lemma radialEta_gradient_integral {s : ℝ} (hs : 0 < s) :
    (∫ x, ‖fderiv ℝ (radialEta radialProfile s) x‖)=radialGradientMass/s := by
  simp_rw [radialEta_fderiv_scale hs,norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ s⁻¹^4)]
  rw [integral_const_mul,Measure.integral_comp_smul volume (fun x : WeylSpace => ‖fderiv ℝ (radialEta radialProfile 1) x‖)]
  simp only [WeylSpace,finrank_euclideanSpace,Fintype.card_fin,inv_pow,inv_inv,smul_eq_mul]
  rw [abs_of_pos (pow_pos hs 3)]
  change (s^4)⁻¹ * (s^3*radialGradientMass)=radialGradientMass/s
  field_simp [hs.ne']

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AnalyticDerivativeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology
open scoped NNReal ENNReal

theorem analyticAt_of_factorial_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {a : E} {R M C : ℝ} (hR : 0<R) (hM : 0≤M) (hC : 0<C)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞)) f (Metric.ball a R))
    (hb : ∀ n : ℕ, ∀ x∈Metric.ball a R,
      ‖iteratedFDeriv ℝ n f x‖≤M*C^n*(n.factorial : ℝ)) : AnalyticAt ℝ f a := by
  let p : FormalMultilinearSeries ℝ E F := fun n => (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n f a
  let r : ℝ≥0 := ⟨min R (1/C)/2,by positivity⟩
  have hr : 0<(r : ℝ) := by change 0 < min R (1/C)/2; positivity
  have hrR : (r : ℝ)<R := by
    change min R (1/C)/2<R
    have := min_le_left R (1/C)
    linarith
  have hrC : (r : ℝ)<1/C := by
    change min R (1/C)/2<1/C
    have := min_le_right R (1/C)
    have : 0<1/C := by positivity
    linarith
  have hp (n : ℕ) : ‖p n‖≤M*C^n := by
    dsimp [p]
    rw [norm_smul,Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (n.factorial : ℝ)⁻¹*(M*C^n*(n.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (hb n a (by simpa using hR)) (by positivity)
      _ = M*C^n := by
        have hn : (n.factorial : ℝ)≠0 := by positivity
        field_simp
  have hrad : (r : ℝ≥0∞)≤p.radius := by
    apply p.le_radius_of_bound M
    intro n
    calc
      ‖p n‖*(r : ℝ)^n ≤ M*C^n*(r : ℝ)^n := mul_le_mul_of_nonneg_right (hp n) (by positivity)
      _ = M*(C*(r : ℝ))^n := by rw [mul_pow]; ring
      _ ≤ M*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity)
        (by nlinarith [(lt_div_iff₀ hC).mp hrC])) hM
      _ = M := mul_one _
  refine ⟨p,⟨r,⟨hrad,by exact_mod_cast hr,?_⟩⟩⟩
  intro y hy
  have hyr : ‖y‖<(r : ℝ) := by
    rw [Metric.eball_coe] at hy
    simpa using hy
  have hyR : ‖y‖<R := hyr.trans hrR
  have hyC : C*‖y‖<1 := by nlinarith [(lt_div_iff₀ hC).mp hrC]
  have hseg (t : ℝ) (ht : t∈Icc 0 1) : a+t•y∈Metric.ball a R := by
    rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt hyR
  have hdiff (n : ℕ) (t : ℝ) (ht : t∈Icc 0 1) : ContDiffAt ℝ (n+1) f (a+t•y) :=
    ((hf _ (hseg t ht)).contDiffAt (Metric.isOpen_ball.mem_nhds (hseg t ht))).of_le (by exact_mod_cast (show (↑n+1 : ℕ∞)≤⊤ from le_top))
  have he (n : ℕ) :
      ‖f (a+y)-∑ k∈Finset.range (n+1), p k (fun _ => y)‖≤
        M*((n+1 : ℕ) : ℝ)*(C*‖y‖)^(n+1) := by
    rw [map_add_eq_sum_add_integral_iteratedFDeriv (hdiff n)]
    simp only [p,smul_apply,add_sub_cancel_left]
    rw [norm_smul,Real.norm_of_nonneg (by positivity)]
    have hi : ‖∫ t in (0:ℝ)..1, (1-t)^n •
        iteratedFDeriv ℝ (n+1) f (a+t•y) (fun _ => y)‖≤
        M*C^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1) := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := M*C^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1)) ?_).trans (by simp)
      intro t ht
      have ht' : t∈Icc (0:ℝ) 1 := by
        simp only [uIoc_of_le zero_le_one,mem_Ioc] at ht
        exact ⟨ht.1.le,ht.2⟩
      rw [norm_smul,Real.norm_of_nonneg (pow_nonneg (by linarith [ht'.2]) _)]
      calc
          _ ≤ 1*(‖iteratedFDeriv ℝ (n+1) f (a+t•y)‖*‖y‖^(n+1)) :=
            mul_le_mul (pow_le_one₀ (by linarith [ht'.2]) (by linarith [ht'.1]))
              (by simpa using (iteratedFDeriv ℝ (n+1) f (a+t•y)).le_opNorm (fun _ => y))
              (norm_nonneg _) (by positivity)
          _ ≤ M*C^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1) := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right (hb (n+1) _ (hseg t ht')) (by positivity : 0≤‖y‖^(n+1))
    calc
      _ ≤ (n.factorial : ℝ)⁻¹*(M*C^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1)) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by
        rw [Nat.factorial_succ,Nat.cast_mul,mul_pow]
        have hn : (n.factorial : ℝ)≠0 := by positivity
        field_simp
  have ht : Tendsto (fun n : ℕ => M*((n+1 : ℕ) : ℝ)*(C*‖y‖)^(n+1)) atTop (𝓝 0) := by
    have hh := (tendsto_self_mul_const_pow_of_lt_one (show 0≤C*‖y‖ by positivity) hyC).comp
      (tendsto_add_atTop_nat 1)
    simpa only [mul_zero,mul_assoc,Function.comp_apply] using hh.const_mul M
  have hlim : Tendsto (fun n : ℕ => ∑ k∈Finset.range (n+1), p k (fun _ => y)) atTop (𝓝 (f (a+y))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp_rw [norm_sub_rev]
    exact squeeze_zero (fun _ => norm_nonneg _) he ht
  apply (hasSum_iff_tendsto_nat_of_summable_norm ?_).mpr
  · exact (tendsto_add_atTop_iff_nat 1).mp hlim
  · apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => ?_) ((summable_geometric_of_lt_one (show 0≤C*‖y‖ by positivity) hyC).mul_left M)
    calc
      ‖p n (fun _ => y)‖≤‖p n‖*‖y‖^n := by simpa using (p n).le_opNorm (fun _ => y)
      _≤M*C^n*‖y‖^n := mul_le_mul_of_nonneg_right (hp n) (by positivity)
      _=M*(C*‖y‖)^n := by rw [mul_pow]; ring

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped Convolution

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

lemma RadialMeanOn.linearIsometry {f : WeylSpace → F} {a : WeylSpace} {R : ℝ}
    (hm : RadialMeanOn f a R) (L : F →ₗᵢ[ℝ] G) : RadialMeanOn (L ∘ f) a R := by
  intro s hs x hx
  change L (f x)=∫ y, (radialEta radialProfile s y) • L (f (x-y))
  simp_rw [←L.map_smul]
  rw [L.integral_comp_comm]
  exact congrArg L (hm s hs x hx)

lemma RadialMeanOn.iterated {f : WeylSpace → F} {a : WeylSpace} {R : ℝ}
    (hm : RadialMeanOn f a R) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) (n : ℕ) : RadialMeanOn (iteratedFDeriv ℝ n f) a R := by
  induction n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact hm.linearIsometry (continuousMultilinearCurryFin0 ℝ WeylSpace F).symm.toLinearIsometry
  | succ n ih =>
    have : CompleteSpace (WeylSpace →L[ℝ] WeylSpace [×n]→L[ℝ] F) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => WeylSpace) F).symm.toIsometryEquiv.completeSpace
    rw [iteratedFDeriv_succ_eq_comp_left]
    exact (ih.derivative (hf.iteratedFDeriv_right (by exact_mod_cast (show (⊤ : ℕ∞)+n≤⊤ from le_top))) (hc.iteratedFDeriv n)).linearIsometry
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => WeylSpace) F).symm.toLinearIsometry

lemma RadialMeanOn.iterated_bound {f : WeylSpace → F} {a : WeylSpace} {R M s : ℝ}
    (hm : RadialMeanOn f a R) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) (hM : 0≤M) (hs : 0 < s)
    (hb : ∀ x∈Metric.ball a R, ‖f x‖≤M) (n : ℕ) :
    ∀ x : WeylSpace, dist x a+(n : ℝ)*s<R →
      ‖iteratedFDeriv ℝ n f x‖≤M*(radialGradientMass/s)^n := by
  induction n with
  | zero =>
    intro x hx
    simp only [Nat.cast_zero,zero_mul,add_zero] at hx
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hb x hx
  | succ n ih =>
    intro x hx
    have hx' : dist x a+s<R := by
      have hn : 0≤(n : ℝ)*s := mul_nonneg (Nat.cast_nonneg _) hs.le
      push_cast at hx
      nlinarith
    rw [←norm_fderiv_iteratedFDeriv]
    have he := (hm.iterated hf hc n).derivative_bound
      (hf.iteratedFDeriv_right (by exact_mod_cast (show (⊤ : ℕ∞)+n≤⊤ from le_top))) hs hx'
      (mul_nonneg hM (pow_nonneg (div_nonneg radialGradientMass_nonneg hs.le) n)) (fun y hy => by
        apply ih
        have hh : dist y x ≤ s := hy
        have ht := dist_triangle y x a
        push_cast at hx
        nlinarith)
    rw [radialEta_gradient_integral hs] at he
    simpa only [pow_succ,mul_assoc] using he

lemma RadialMeanOn.factorial_bound {f : WeylSpace → F} {a x : WeylSpace} {R M : ℝ}
    (hm : RadialMeanOn f a R) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) (hR : 0<R) (hM : 0≤M)
    (hb : ∀ y∈Metric.ball a R, ‖f y‖≤M) (hx : x∈Metric.ball a (R/2)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n f x‖≤M*(2*Real.exp 1*(radialGradientMass+1)/R)^n*(n.factorial : ℝ) := by
  rcases n with _ | n
  · simpa using hb x (Metric.ball_subset_ball (by linarith) hx)
  let N : ℕ := n+1
  have hN : 0<(N : ℝ) := by dsimp [N]; positivity
  let s := R/(2*(N : ℝ))
  have hs : 0 < s := by dsimp [s]; positivity
  have he := hm.iterated_bound hf hc hM hs hb N x (by
    have hn : (N : ℝ)*s=R/2 := by dsimp [s]; field_simp
    rw [hn]
    have hx' : dist x a<R/2 := hx
    linarith)
  have hn : (N : ℝ)^N≤(Real.exp 1)^N*(N.factorial : ℝ) := by
    have hh := Real.pow_div_factorial_le_exp (N : ℝ) hN.le N
    rw [div_le_iff₀ (by positivity : 0<(N.factorial : ℝ))] at hh
    simpa only [←Real.exp_nat_mul, mul_one] using hh
  have hbase : radialGradientMass/s≤(2*(radialGradientMass+1)/R)*(N : ℝ) := by
    dsimp [s]
    field_simp
    nlinarith [radialGradientMass_nonneg]
  calc
    _ ≤ M*(radialGradientMass/s)^N := he
    _ ≤ M*((2*(radialGradientMass+1)/R)*(N : ℝ))^N := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity [radialGradientMass_nonneg]) hbase _) hM
    _ = M*(2*(radialGradientMass+1)/R)^N*(N : ℝ)^N := by rw [mul_pow]; ring
    _ ≤ M*(2*(radialGradientMass+1)/R)^N*((Real.exp 1)^N*(N.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hn (by positivity [radialGradientMass_nonneg])
    _ = _ := by
      have heq : 2*Real.exp 1*(radialGradientMass+1)/R = (2*(radialGradientMass+1)/R)*Real.exp 1 := by ring
      rw [heq,mul_pow]
      dsimp [N]
      ring

lemma RadialMeanOn.analyticAt {f : WeylSpace → F} {a : WeylSpace} {R : ℝ}
    (hm : RadialMeanOn f a R) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) (hR : 0<R) : AnalyticAt ℝ f a := by
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hf.continuous
  have hM' : 0≤M := (norm_nonneg (f a)).trans (hM a)
  refine analyticAt_of_factorial_bound (R := R/2) (M := M)
    (C := 2*Real.exp 1*(radialGradientMass+1)/R) (by positivity) hM'
    (by positivity [radialGradientMass_nonneg]) hf.contDiffOn ?_
  intro n x hx
  exact hm.factorial_bound hf hc hR hM' (fun y _ => hM y) hx n

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AnalyticNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter MeasureTheory Topology

section LocalNull
variable {E : Type*} [TopologicalSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] (μ : Measure E)

lemma measure_inter_zero_of_local {U Z : Set E}
    (h : ∀ x ∈ U, ∃ V : Set E, x ∈ V ∧ IsOpen V ∧ μ (V ∩ Z) = 0) :
    μ (U ∩ Z) = 0 := by
  choose V hmem hopen hnull using (fun x : U => h x x.property)
  obtain ⟨I,hIc,hcov⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover
    V hopen (by intro x hx; exact mem_iUnion.mpr ⟨⟨x,hx⟩,hmem ⟨x,hx⟩⟩)
  apply measure_mono_null (t := ⋃ x ∈ I, V x ∩ Z)
  · intro x hx
    rcases mem_iUnion₂.mp (hcov hx.1) with ⟨y,hy,hxy⟩
    exact mem_iUnion₂.mpr ⟨y,hy,hxy,hx.2⟩
  · exact (measure_biUnion_null_iff hIc).mpr (fun x _ => hnull x)
end LocalNull

lemma analyticNull_real : AnalyticNullProperty ℝ volume := by
  intro U f hU hc hf ⟨x,hx,hfx⟩
  have hd : IsDiscrete (f ⁻¹' {0} ∩ U) := isDiscrete_of_codiscreteWithin
    (by simpa only [preimage_compl] using
      hf.preimage_zero_mem_codiscreteWithin hfx hx ⟨⟨x,hx⟩,hc⟩)
  rw [inter_comm]
  exact ((HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hd).measure_zero volume

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology E] [SecondCountableTopology F]

omit [SecondCountableTopology E] in
lemma analytic_zero_measurable {U : Set E} {f : E → ℝ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℝ f U) :
    MeasurableSet (U ∩ f ⁻¹' {0}) := by
  have ho := hf.continuousOn.isOpen_inter_preimage hU (isClosed_singleton.isOpen_compl : IsOpen ({0}ᶜ : Set ℝ))
  convert hU.measurableSet.diff ho.measurableSet using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,Set.mem_sdiff,mem_compl_iff]
  tauto

omit [SecondCountableTopology E] in
lemma analytic_null_rectangle (μ : Measure E) (ν : Measure F) [SFinite ν]
    (hE : AnalyticNullProperty E μ) (hF : AnalyticNullProperty F ν)
    {U : Set E} {V : Set F} {f : E × F → ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hcU : IsPreconnected U) (hcV : IsPreconnected V)
    (hf : AnalyticOnNhd ℝ f (U ×ˢ V)) (hx : ∃ x ∈ U ×ˢ V, f x ≠ 0) :
    μ.prod ν ((U ×ˢ V) ∩ f ⁻¹' {0}) = 0 := by
  obtain ⟨⟨x₀,y₀⟩,hxy,hfxy⟩ := hx
  have ha : AnalyticOnNhd ℝ (fun x => f (x,y₀)) U := by
    intro x hx
    have hg : AnalyticAt ℝ (fun t : E => (t,y₀)) x := analyticAt_id.prod analyticAt_const
    exact (hf (x,y₀) ⟨hx,hxy.2⟩).comp (f := fun t : E => (t,y₀)) hg
  have hn := hE U (fun x => f (x,y₀)) hU hcU ha ⟨x₀,hxy.1,hfxy⟩
  apply Measure.measure_prod_null_of_ae_null (analytic_zero_measurable (hU.prod hV) hf)
  filter_upwards [compl_mem_ae_iff.mpr hn] with x hx
  by_cases hxU : x ∈ U
  · have hfx : f (x,y₀) ≠ 0 := by simpa [hxU] using hx
    have hb : AnalyticOnNhd ℝ (fun y => f (x,y)) V := by
      intro y hy
      have hg : AnalyticAt ℝ (fun t : F => (x,t)) y := analyticAt_const.prod analyticAt_id
      exact (hf (x,y) ⟨hxU,hy⟩).comp (f := fun t : F => (x,t)) hg
    change ν (Prod.mk x ⁻¹' ((U ×ˢ V) ∩ f ⁻¹' {0})) = 0
    have he : Prod.mk x ⁻¹' ((U ×ˢ V) ∩ f ⁻¹' {0}) =
        V ∩ (fun y => f (x,y)) ⁻¹' {0} := by ext y; simp [hxU]
    rw [he]
    exact hF V (fun y => f (x,y)) hV hcV hb ⟨y₀,hxy.2,hfx⟩
  · simp [hxU]

lemma analyticNull_prod (μ : Measure E) (ν : Measure F) [SFinite ν]
    (hE : AnalyticNullProperty E μ) (hF : AnalyticNullProperty F ν) :
    AnalyticNullProperty (E × F) (μ.prod ν) := by
  intro U f hU hc hf ⟨x₀,hx₀,hfx₀⟩
  apply measure_inter_zero_of_local
  intro p hp
  obtain ⟨ε,hε,hsub⟩ := Metric.isOpen_iff.mp hU p hp
  let V := Metric.ball p.1 ε ×ˢ Metric.ball p.2 ε
  have hVm : p ∈ V := ⟨Metric.mem_ball_self hε,Metric.mem_ball_self hε⟩
  have hVo : IsOpen V := Metric.isOpen_ball.prod Metric.isOpen_ball
  have hVU : V ⊆ U := by
    intro q hq
    apply hsub
    rw [Metric.mem_ball,Prod.dist_eq]
    exact max_lt hq.1 hq.2
  have hne : ∃ x ∈ V, f x ≠ 0 := by
    by_contra! hn
    have he : f =ᶠ[𝓝 p] 0 := by
      filter_upwards [hVo.mem_nhds hVm] with x hx
      exact hn x hx
    exact hfx₀ (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hp he hx₀)
  refine ⟨V,hVm,hVo,?_⟩
  exact analytic_null_rectangle μ ν hE hF Metric.isOpen_ball Metric.isOpen_ball
    (convex_ball _ _).isPreconnected (convex_ball _ _).isPreconnected (hf.mono hVU) hne

end ScalarConductivity



namespace ScalarConductivity
open Set Filter MeasureTheory Topology

section Transfer
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology E] [SecondCountableTopology F]

omit [BorelSpace E] [SecondCountableTopology E] [SecondCountableTopology F] in
lemma analyticNull_of_equiv (μ : Measure E) (ν : Measure F) (e : E ≃L[ℝ] F)
    (he : MeasurePreserving e μ ν) (hF : AnalyticNullProperty F ν) :
    AnalyticNullProperty E μ := by
  intro U f hU hc hf ⟨x,hx,hfx⟩
  let V := e '' U
  have hVo : IsOpen V := e.toHomeomorph.isOpenMap _ hU
  have hg : AnalyticOnNhd ℝ (fun y => f (e.symm y)) V := by
    rintro y ⟨z,hz,rfl⟩
    apply (hf z hz).comp_of_eq (e.symm.analyticAt _) (e.symm_apply_apply z)
  have hn := hF V (fun y => f (e.symm y)) hVo
    (hc.image e e.continuous.continuousOn) hg ⟨e x,mem_image_of_mem _ hx,by simpa using hfx⟩
  rw [←he.measure_preimage (analytic_zero_measurable hVo hg).nullMeasurableSet] at hn
  have hs : U ∩ f ⁻¹' {0} = e ⁻¹' (V ∩ (fun y => f (e.symm y)) ⁻¹' {0}) := by
    ext z
    simp [V]
  rw [hs]
  exact hn
end Transfer

lemma splitFinCLE_measurePreserving (n : ℕ) :
    MeasurePreserving (splitFinCLE n) volume volume :=
  volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0

theorem analyticNull_fin (n : ℕ) : AnalyticNullProperty (Fin n → ℝ) volume := by
  induction n with
  | zero =>
    intro U f hU hc hf ⟨x,hx,hfx⟩
    have h : U ∩ f ⁻¹' {0} = ∅ := by
      apply eq_empty_of_forall_notMem
      intro y hy
      exact hfx (by simpa only [Subsingleton.elim y x, mem_preimage, mem_singleton_iff] using hy.2)
    rw [h,measure_empty]
  | succ n ih =>
    exact analyticNull_of_equiv volume volume (splitFinCLE n) (splitFinCLE_measurePreserving n)
      (analyticNull_prod volume volume analyticNull_real ih)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AnalyticNullEuclidean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma analyticNull_euclidean (n : ℕ) : AnalyticNullProperty (EuclideanSpace ℝ (Fin n)) volume :=
  analyticNull_of_equiv volume volume
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ))
    (PiLp.volume_preserving_ofLp (Fin n)) (analyticNull_fin n)

lemma analytic_directional_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {U : Set E} (hf : AnalyticOnNhd ℝ f U) (w : E) :
    AnalyticOnNhd ℝ (fun x => fderiv ℝ f x w) U :=
  (ContinuousLinearMap.apply ℝ ℝ w).comp_analyticOnNhd hf.fderiv

lemma analytic_gradient_minor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E → ℝ} {U : Set E} (hu : AnalyticOnNhd ℝ u U)
    (hv : AnalyticOnNhd ℝ v U) (p q : E) :
    AnalyticOnNhd ℝ (fun x => fderiv ℝ u x p*fderiv ℝ v x q-
      fderiv ℝ u x q*fderiv ℝ v x p) U :=
  ((analytic_directional_fderiv hu p).mul (analytic_directional_fderiv hv q)).sub
    ((analytic_directional_fderiv hu q).mul (analytic_directional_fderiv hv p))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SmoothHarmonicAnalytic
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace

lemma WeaklyHarmonicOn.mono {f : WeylSpace → ℝ} {U V : Set WeylSpace}
    (hw : WeaklyHarmonicOn f U) (hV : V⊆U) : WeaklyHarmonicOn f V := by
  intro ψ hψ hc hs
  exact hw ψ hψ hc (hs.trans hV)

theorem smooth_weak_harmonic_analyticAt {f : WeylSpace → ℝ} {U : Set WeylSpace}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hw : WeaklyHarmonicOn f U)
    (hU : IsOpen U) {a : WeylSpace} (ha : a∈U) : AnalyticAt ℝ f a := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let b : ContDiffBump a := {
    rIn := r/2, rOut := r, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let g : WeylSpace → ℝ := fun x => b x*f x
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g := b.contDiff.mul hf
  have hc : HasCompactSupport g := b.hasCompactSupport.mul_right
  have he : EqOn f g (Metric.ball a (r/2)) := by
    intro x hx
    have hb : b x=1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    simp [g,hb]
  have hwg : WeaklyHarmonicOn g (Metric.ball a (r/2)) :=
    .congr_restrict Metric.isOpen_ball.measurableSet
      ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr (ae_of_all _ he))
      (hw.mono ((Metric.ball_subset_ball (by linarith)).trans hsub))
  have hgA : AnalyticAt ℝ g a :=
    (weaklyHarmonic_smooth_mean hg hc hwg).analyticAt hg hc (by positivity)
  apply hgA.congr
  filter_upwards [Metric.ball_mem_nhds a (by positivity : 0 < r/2)] with x hx
  exact (he hx).symm

theorem weakWeyl_analytic_local {f : WholeL2} {U : Set WeylSpace}
    (hw : WeaklyHarmonicOn f U) {a : WeylSpace} {R : ℝ} (hR : 0<R)
    (hball : Metric.closedBall a R⊆U) :
    AnalyticOnNhd ℝ (radialMollify f (R/4)) (Metric.ball a (R/4)) ∧
    (f : WeylSpace → ℝ) =ᵐ[volume.restrict (Metric.ball a (R/4))] radialMollify f (R/4) := by
  obtain ⟨hg,he⟩ := weakWeyl_local hw hR hball
  refine ⟨?_,he⟩
  have hb : Metric.ball a (R/4)⊆U :=
    ((Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall).trans hball
  have hwg := WeaklyHarmonicOn.congr_restrict Metric.isOpen_ball.measurableSet he (hw.mono hb)
  intro x hx
  exact smooth_weak_harmonic_analyticAt hg hwg Metric.isOpen_ball hx

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralEuclideanBridge
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace

lemma centralEuclidean_integral (f : Box3 → ℝ) :
    (∫ x,f (centralEuclideanCLE x))=(∫ x,f x) :=
  centralEuclidean_volume.integral_comp centralEuclideanCLE.toHomeomorph.measurableEmbedding f

lemma centralEuclidean_direction (i : Fin 3) :
    centralEuclideanCLE.symm (centralDirection i)=EuclideanSpace.basisFun (Fin 3) ℝ i := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [centralEuclideanCLE,centralDirection,
    boxCoordinates,EuclideanSpace.basisFun_apply] <;> rfl

lemma centralEuclidean_partial {f : R3 → ℝ} (hf : Differentiable ℝ f)
    (i : Fin 3) (x : Box3) :
    cubePartial (fun y => f (centralEuclideanCLE.symm y)) (centralDirection i) x=
      fderiv ℝ f (centralEuclideanCLE.symm x) (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  change (fderiv ℝ (f ∘ centralEuclideanCLE.symm) x) (centralDirection i)=_
  rw [fderiv_comp x (hf _) centralEuclideanCLE.symm.differentiableAt]
  simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,centralEuclidean_direction]

lemma centralEuclidean_laplacian {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (x : Box3) :
    centralLaplacian (fun y => f (centralEuclideanCLE.symm y)) x=
      Δ f (centralEuclideanCLE.symm x) := by
  rw [centralLaplacian,laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 3) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  have hfirst : cubePartial (fun y => f (centralEuclideanCLE.symm y)) (centralDirection i)=
      fun y => fderiv ℝ f (centralEuclideanCLE.symm y) (EuclideanSpace.basisFun (Fin 3) ℝ i) :=
    funext (centralEuclidean_partial (hf.differentiable (by simp)) i)
  have hdf : ContDiff ℝ (↑(⊤ : ℕ∞)) (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [hfirst,centralEuclidean_partial ((hdf.differentiable (by simp)).clm_apply (differentiable_const _))]
  rw [iteratedFDeriv_two_apply]
  rw [fderiv_clm_apply (hdf.differentiable (by simp) _) (differentiableAt_const _)]
  simp

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace

lemma centralWholeL2_ae (f : CentralL2) : centralWholeL2 f=ᵐ[volume] centralZeroExtension f :=
  (centralZeroExtension_memLp f).coeFn_toLp

theorem central_variational_euclidean_weak (s slopes : Fin 3 → ℝ)
    (hs : ∑ i,slopes i=0) :
    ∃ p : centralEnergySpace s,centralM s p=0 ∧ CentralVariationalEquation s slopes p ∧
      WeaklyHarmonicOn (centralWholeL2 (centralAmbientComponent s 0 p.val)) centralHarmonicRegion := by
  obtain ⟨p,hp,hvar,hweak⟩ := central_variational_distributional_laplacian s slopes hs
  refine ⟨p,hp,hvar,?_⟩
  intro ψ hψ hc hsp
  let φ : centralSmoothFunctions := ⟨fun x => ψ (centralEuclideanCLE.symm x),
    hψ.comp centralEuclideanCLE.symm.contDiff⟩
  have hφc : HasCompactSupport φ := hc.comp_homeomorph centralEuclideanCLE.symm.toHomeomorph
  have hφs : tsupport φ⊆centralClosed := by
    intro x hx
    have hpre := tsupport_comp_subset_preimage ψ centralEuclideanCLE.symm.continuous hx
    have hmem := (hsp hpre).1
    simpa only [centralEuclideanCLE.apply_symm_apply] using hmem
  have hφb (i : Fin 3) x : φ (centralBoundary i x)=0 := by
    by_contra hz
    have hmem : centralEuclideanCLE.symm (centralBoundary i x)∈tsupport ψ :=
      subset_tsupport ψ hz
    have he := (hsp hmem).2 i x
    exact he (centralEuclideanCLE.apply_symm_apply _)
  have hz := hweak φ hφc hφs hφb
  let f := centralAmbientComponent s 0 p.val
  calc
    (∫ x,centralWholeL2 f x*Δ ψ x)=∫ x,centralZeroExtension f x*Δ ψ x := by
      apply integral_congr_ae
      filter_upwards [centralWholeL2_ae f] with x hx
      rw [hx]
    _ = ∫ x,centralClosed.indicator f (centralEuclideanCLE x)*centralLaplacian φ (centralEuclideanCLE x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      have he := centralEuclidean_laplacian hψ (centralEuclideanCLE x)
      simpa only [centralEuclideanCLE.symm_apply_apply,centralZeroExtension] using
        congrArg (fun t => centralClosed.indicator f (centralEuclideanCLE x)*t) he.symm
    _ = ∫ x,centralClosed.indicator f x*centralLaplacian φ x := centralEuclidean_integral (fun x => centralClosed.indicator f x*centralLaplacian φ x)
    _ = ∫ x,f x*centralLaplacian φ x ∂centralMeasure := by
      change _=∫ x in centralClosed,f x*centralLaplacian φ x
      rw [←integral_indicator centralClosed_compact.measurableSet]
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x∈centralClosed <;> simp [hx]
    _ = 0 := hz

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_HarmonicRankAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Laplacian InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

lemma laplacian_trace_fderiv (b : OrthonormalBasis ι ℝ E) (f : E → ℝ) (x : E) :
    Δ f x = ∑ i, fderiv ℝ (fderiv ℝ f) x (b i) (b i) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  apply Finset.sum_congr rfl
  intro i hi
  exact (bilinearIteratedFDerivTwo_eq_iteratedFDeriv (𝕜 := ℝ) _ x (b i) (b i)).symm

omit [FiniteDimensional ℝ E] in
lemma clm_sum_sq_positive (b : OrthonormalBasis ι ℝ E) (L : E →L[ℝ] ℝ)
    {w : E} (hw : L w ≠ 0) : 0 < ∑ i, (L (b i))^2 := by
  have hnon : 0 ≤ ∑ i, (L (b i))^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  apply lt_of_le_of_ne hnon
  intro hz
  have he : ∀ i, L (b i)=0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i∈Finset.univ) => sq_nonneg (L (b i)))).mp hz.symm i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp this
  apply hw
  rw [←b.sum_repr w,map_sum]
  simp [he]

theorem harmonic_gradient_multiplier_fderiv_zero (b : OrthonormalBasis ι ℝ E)
    {u v lam : E → ℝ} {x w : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x)
    (hlam : DifferentiableAt ℝ lam x)
    (he : (fun y => fderiv ℝ v y) =ᶠ[𝓝 x] (fun y => lam y • fderiv ℝ u y))
    (hlu : Δ u x=0) (hlv : Δ v x=0) (hw : fderiv ℝ u x w ≠ 0) :
    fderiv ℝ lam x=0 := by
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (by norm_num)).differentiableAt one_ne_zero
  have hdv : DifferentiableAt ℝ (fderiv ℝ v) x :=
    (hv.fderiv_right (by norm_num)).differentiableAt one_ne_zero
  have hh (p q : E) :
      fderiv ℝ (fderiv ℝ v) x p q =
        fderiv ℝ lam x p * fderiv ℝ u x q +
        lam x * fderiv ℝ (fderiv ℝ u) x p q := by
    have hd := (hlam.hasFDerivAt.smul hdu.hasFDerivAt).congr_of_eventuallyEq he
    have hp := congrArg (fun T : E →L[ℝ] E →L[ℝ] ℝ => T p q) hd.fderiv
    simpa only [add_apply,ContinuousLinearMap.smulRight_apply,
      smul_apply,smul_eq_mul,add_comm] using hp
  have hs (p q : E) :
      fderiv ℝ lam x p * fderiv ℝ u x q = fderiv ℝ lam x q * fderiv ℝ u x p := by
    have huv := hv.isSymmSndFDerivAt (by norm_num) p q
    have huu := hu.isSymmSndFDerivAt (by norm_num) p q
    change fderiv ℝ (fderiv ℝ v) x p q = fderiv ℝ (fderiv ℝ v) x q p at huv
    change fderiv ℝ (fderiv ℝ u) x p q = fderiv ℝ (fderiv ℝ u) x q p at huu
    rw [hh,hh,huu] at huv
    linarith
  let k := fderiv ℝ lam x w / fderiv ℝ u x w
  have hk (p : E) : fderiv ℝ lam x p = k*fderiv ℝ u x p := by
    dsimp [k]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hw).2
    simpa only [div_mul_eq_mul_div] using hs p w
  have htrace : Δ v x = k*(∑ i, (fderiv ℝ u x (b i))^2)+lam x*Δ u x := by
    simp_rw [laplacian_trace_fderiv b,hh,hk]
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hk0 : k=0 := by
    rw [hlu,hlv,mul_zero,add_zero] at htrace
    exact (mul_eq_zero.mp htrace.symm).resolve_right
      (ne_of_gt (clm_sum_sq_positive b (fderiv ℝ u x) hw))
  ext p
  simp [hk,hk0]

theorem harmonic_rank_one_affine (b : OrthonormalBasis ι ℝ E)
    {u v : E → ℝ} {U : Set E} {w : E}
    (hU : IsOpen U) (hc : IsPreconnected U)
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (hlu : ∀ x∈U, Δ u x=0) (hlv : ∀ x∈U, Δ v x=0)
    (hw : ∀ x∈U, fderiv ℝ u x w ≠ 0)
    (hr : ∀ x∈U, ∀ p q, fderiv ℝ u x p*fderiv ℝ v x q =
      fderiv ℝ u x q*fderiv ℝ v x p) :
    ∃ α β : ℝ, ∀ x∈U, v x=α*u x+β := by
  let lam : E → ℝ := fun x => fderiv ℝ v x w / fderiv ℝ u x w
  have hua (x : E) (hx : x∈U) : ContDiffAt ℝ 2 u x :=
    (hu x hx).contDiffAt (hU.mem_nhds hx)
  have hva (x : E) (hx : x∈U) : ContDiffAt ℝ 2 v x :=
    (hv x hx).contDiffAt (hU.mem_nhds hx)
  have hdlam (x : E) (hx : x∈U) : DifferentiableAt ℝ lam x := by
    have hn : DifferentiableAt ℝ (fun y => fderiv ℝ v y w) x :=
      ((hva x hx).fderiv_right (by norm_num) |>.differentiableAt one_ne_zero).clm_apply (differentiableAt_const w)
    have hd : DifferentiableAt ℝ (fun y => fderiv ℝ u y w) x :=
      ((hua x hx).fderiv_right (by norm_num) |>.differentiableAt one_ne_zero).clm_apply (differentiableAt_const w)
    simpa only [lam,div_eq_mul_inv,Pi.mul_def,Function.comp_def] using
      hn.mul ((hasDerivAt_inv (hw x hx)).differentiableAt.comp x hd)
  have hprop (x : E) (hx : x∈U) : fderiv ℝ v x=lam x • fderiv ℝ u x := by
    ext p
    simp only [smul_apply,smul_eq_mul,lam,div_mul_eq_mul_div]
    apply (eq_div_iff (hw x hx)).2
    nlinarith [hr x hx p w]
  have hzero : EqOn (fderiv ℝ lam) 0 U := by
    intro x hx
    apply harmonic_gradient_multiplier_fderiv_zero b (hua x hx) (hva x hx) (hdlam x hx)
      _ (hlu x hx) (hlv x hx) (hw x hx)
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hprop y hy
  obtain ⟨α,hα⟩ := hU.exists_is_const_of_fderiv_eq_zero hc
    (fun x hx => (hdlam x hx).differentiableWithinAt) hzero
  obtain ⟨β,hβ⟩ := hU.exists_eq_add_of_fderiv_eq hc
    (hv.differentiableOn (by norm_num))
    ((hu.differentiableOn (by norm_num)).const_mul α) (by
      intro x hx
      rw [hprop x hx,hα x hx]
      simpa using (((hua x hx).differentiableAt (by norm_num)).hasFDerivAt.const_mul α).fderiv.symm)
  exact ⟨α,β,hβ⟩

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

omit [MeasurableSpace E] [BorelSpace E] in
lemma noncritical_harmonic_rank_patch (b : OrthonormalBasis ι ℝ E)
    {u v : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hu : AnalyticOnNhd ℝ u U) (hv : AnalyticOnNhd ℝ v U)
    (hlu : ∀ x∈U, Δ u x=0) (hlv : ∀ x∈U, Δ v x=0)
    (hr : ∀ x∈U, ∀ p q, fderiv ℝ u x p*fderiv ℝ v x q=
      fderiv ℝ u x q*fderiv ℝ v x p)
    {x w : E} (hx : x∈U) (hw : fderiv ℝ u x w ≠ 0) :
    ∃ r>0, Metric.ball x r⊆U ∧ ∃ α β : ℝ,
      ∀ y∈Metric.ball x r, fderiv ℝ u y w ≠ 0 ∧ v y=α*u y+β := by
  have hn := ((analytic_directional_fderiv hu w) x hx).continuousAt.eventually_ne hw
  obtain ⟨r,hr0,hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hx) hn)
  have hbU : Metric.ball x r⊆U := fun y hy => (hball hy).1
  have hbn : ∀ y∈Metric.ball x r, fderiv ℝ u y w ≠ 0 := fun y hy => (hball hy).2
  obtain ⟨α,β,he⟩ := harmonic_rank_one_affine b Metric.isOpen_ball
    (convex_ball x r).isPreconnected (hu.contDiffOn_of_completeSpace.mono hbU) (hv.contDiffOn_of_completeSpace.mono hbU)
    (fun y hy => hlu y (hbU hy)) (fun y hy => hlv y (hbU hy)) hbn
    (fun y hy => hr y (hbU hy))
  exact ⟨r,hr0,hbU,α,β,fun y hy => ⟨hbn y hy,he y hy⟩⟩

omit [BorelSpace E] in
theorem analytic_harmonic_ae_regular (b : OrthonormalBasis ι ℝ E)
    (μ : Measure E) (hnull : AnalyticNullProperty E μ)
    {u v : E → ℝ} {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    (hu : AnalyticOnNhd ℝ u U) (hv : AnalyticOnNhd ℝ v U)
    (hlu : ∀ x∈U, Δ u x=0) (hlv : ∀ x∈U, Δ v x=0) :
    ∀ᵐ x∂μ, x∈U → ∃ r>0, Metric.ball x r⊆U ∧
      HarmonicPairRegularOn u v (Metric.ball x r) := by
  classical
  by_cases hminor : ∃ x∈U, ∃ p q : E,
    fderiv ℝ u x p*fderiv ℝ v x q-fderiv ℝ u x q*fderiv ℝ v x p ≠ 0
  · obtain ⟨a,ha,p,q,hne⟩ := hminor
    let M : E → ℝ := fun x => fderiv ℝ u x p*fderiv ℝ v x q-
      fderiv ℝ u x q*fderiv ℝ v x p
    have hM : AnalyticOnNhd ℝ M U := analytic_gradient_minor hu hv p q
    have hz := hnull U M hU hc hM ⟨a,ha,hne⟩
    filter_upwards [compl_mem_ae_iff.mpr hz] with x hx hxu
    have hMx : M x ≠ 0 := by simpa [hxu] using hx
    have hn := (hM x hxu).continuousAt.eventually_ne hMx
    obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hxu) hn)
    exact ⟨r,hr,fun y hy => (hb hy).1,Or.inl ⟨p,q,fun y hy => (hb hy).2⟩⟩
  have hr : ∀ x∈U, ∀ p q, fderiv ℝ u x p*fderiv ℝ v x q=
      fderiv ℝ u x q*fderiv ℝ v x p := by
    intro x hx p q
    by_contra hn
    exact hminor ⟨x,hx,p,q,sub_ne_zero.mpr hn⟩
  by_cases hdu : ∃ x∈U, ∃ w, fderiv ℝ u x w ≠ 0
  · obtain ⟨a,ha,w,hw⟩ := hdu
    have hz := hnull U (fun x => fderiv ℝ u x w) hU hc
      (analytic_directional_fderiv hu w) ⟨a,ha,hw⟩
    filter_upwards [compl_mem_ae_iff.mpr hz] with x hx hxu
    have hn : fderiv ℝ u x w ≠ 0 := by simpa [hxu] using hx
    obtain ⟨r,hr0,hb,α,β,he⟩ := noncritical_harmonic_rank_patch b hU hu hv hlu hlv hr hxu hn
    exact ⟨r,hr0,hb,Or.inr (Or.inl ⟨w,α,β,he⟩)⟩
  by_cases hdv : ∃ x∈U, ∃ w, fderiv ℝ v x w ≠ 0
  · obtain ⟨a,ha,w,hw⟩ := hdv
    have hz := hnull U (fun x => fderiv ℝ v x w) hU hc
      (analytic_directional_fderiv hv w) ⟨a,ha,hw⟩
    filter_upwards [compl_mem_ae_iff.mpr hz] with x hx hxu
    have hn : fderiv ℝ v x w ≠ 0 := by simpa [hxu] using hx
    have hr' : ∀ x∈U, ∀ p q, fderiv ℝ v x p*fderiv ℝ u x q=
        fderiv ℝ v x q*fderiv ℝ u x p := by
      intro x hx p q
      nlinarith [hr x hx p q]
    obtain ⟨r,hr0,hb,α,β,he⟩ := noncritical_harmonic_rank_patch b hU hv hu hlv hlu hr' hxu hn
    exact ⟨r,hr0,hb,Or.inr (Or.inr (Or.inl ⟨w,α,β,he⟩))⟩
  have hdu0 : EqOn (fderiv ℝ u) 0 U := by
    intro x hx
    ext w
    by_contra hn
    exact hdu ⟨x,hx,w,hn⟩
  have hdv0 : EqOn (fderiv ℝ v) 0 U := by
    intro x hx
    ext w
    by_contra hn
    exact hdv ⟨x,hx,w,hn⟩
  obtain ⟨α,hα⟩ := hU.exists_is_const_of_fderiv_eq_zero hc hu.differentiableOn hdu0
  obtain ⟨β,hβ⟩ := hU.exists_is_const_of_fderiv_eq_zero hc hv.differentiableOn hdv0
  exact ae_of_all μ (fun x hx => by
    obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    exact ⟨r,hr,hb,Or.inr (Or.inr (Or.inr ⟨α,β,fun y hy => ⟨hα y (hb hy),hβ y (hb hy)⟩⟩))⟩)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_WeakHarmonicClassical
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace

lemma compact_weak_harmonic_laplacian {f : WeylSpace → ℝ} {U : Set WeylSpace}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hc : HasCompactSupport f)
    (hw : WeaklyHarmonicOn f U) (hU : IsOpen U) {x : WeylSpace} (hx : x∈U) :
    Δ f x=0 := by
  let F := hc.toSchwartzMap hf
  have hcont : Continuous (Δ f) := by
    change Continuous (fun y => Δ (F : WeylSpace → ℝ) y)
    simpa only [←SchwartzMap.laplacian_apply] using (Δ F).continuous
  have hz : ∀ᵐ y∂volume, y∈U → Δ f y=0 :=
    hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hcont.locallyIntegrable.locallyIntegrableOn U) (by
      intro ψ hψ hcψ hs
      let G := hcψ.toSchwartzMap hψ
      have he := SchwartzMap.integral_mul_laplacian_right_eq_left (μ := volume) F G
      have hwψ := hw ψ hψ hcψ hs
      have he' : (∫ y, f y*Δ ψ y)=(∫ y, Δ f y*ψ y) := by
        have hF : (F : WeylSpace → ℝ) = f := rfl
        have hG : (G : WeylSpace → ℝ) = ψ := rfl
        simp only [SchwartzMap.laplacian_apply] at he
        rw [hF, hG] at he
        exact he
      simpa only [smul_eq_mul,mul_comm] using he'.symm.trans hwψ)
  have he : (fun y => Δ f y) =ᵐ[volume.restrict U] (fun _ => (0:ℝ)) :=
    (ae_restrict_iff' hU.measurableSet).mpr hz
  exact Measure.eqOn_open_of_ae_eq he hU hcont.continuousOn continuous_const.continuousOn hx

lemma smooth_weak_harmonic_laplacian {f : WeylSpace → ℝ} {U : Set WeylSpace}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hw : WeaklyHarmonicOn f U)
    (hU : IsOpen U) {x : WeylSpace} (hx : x∈U) : Δ f x=0 := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let b : ContDiffBump x := {
    rIn := r/2, rOut := r, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let g : WeylSpace → ℝ := fun y => b y*f y
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g := b.contDiff.mul hf
  have hc : HasCompactSupport g := b.hasCompactSupport.mul_right
  have he : EqOn f g (Metric.ball x (r/2)) := by
    intro y hy
    have hb : b y=1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    simp [g,hb]
  have hwg : WeaklyHarmonicOn g (Metric.ball x (r/2)) :=
    .congr_restrict Metric.isOpen_ball.measurableSet
      ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr (ae_of_all _ he))
      (hw.mono ((Metric.ball_subset_ball (by linarith)).trans hsub))
  have hh := compact_weak_harmonic_laplacian hg hc hwg Metric.isOpen_ball
    (Metric.mem_ball_self (by positivity : 0 < r/2))
  have he' : f =ᶠ[𝓝 x] g := by
    filter_upwards [Metric.ball_mem_nhds x (by positivity : 0 < r/2)] with y hy
    exact he hy
  rw [(laplacian_congr_nhds he').eq_of_nhds]
  exact hh

theorem weakWeyl_pair_ae_regular {f g : WholeL2} {U : Set WeylSpace}
    (hf : WeaklyHarmonicOn f U) (hg : WeaklyHarmonicOn g U)
    {a : WeylSpace} {R : ℝ} (hR : 0<R) (hball : Metric.closedBall a R⊆U) :
    ∀ᵐ x∂volume, x∈Metric.ball a (R/4) → ∃ r>0,
      Metric.ball x r⊆Metric.ball a (R/4) ∧
      HarmonicPairRegularOn (radialMollify f (R/4)) (radialMollify g (R/4)) (Metric.ball x r) := by
  obtain ⟨hfA,hfe⟩ := weakWeyl_analytic_local hf hR hball
  obtain ⟨hgA,hge⟩ := weakWeyl_analytic_local hg hR hball
  have hb : Metric.ball a (R/4)⊆U :=
    ((Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall).trans hball
  have hfw := WeaklyHarmonicOn.congr_restrict Metric.isOpen_ball.measurableSet hfe (hf.mono hb)
  have hgw := WeaklyHarmonicOn.congr_restrict Metric.isOpen_ball.measurableSet hge (hg.mono hb)
  exact analytic_harmonic_ae_regular (EuclideanSpace.basisFun (Fin 3) ℝ) volume
    (analyticNull_euclidean 3) Metric.isOpen_ball (convex_ball _ _).isPreconnected hfA hgA
    (fun x hx => smooth_weak_harmonic_laplacian (weakWeyl_local hf hR hball).1 hfw Metric.isOpen_ball hx)
    (fun x hx => smooth_weak_harmonic_laplacian (weakWeyl_local hg hR hball).1 hgw Metric.isOpen_ball hx)

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralPairRegularity
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma centralBasisSlopes_sum (j : Fin 2) : ∑ i,centralBasisSlopes j i=0 := by
  fin_cases j <;> norm_num [centralBasisSlopes,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]

theorem central_pair_regular_exists_oai (s : Fin 3 → ℝ) :
    ∃ p : Fin 2 → centralEnergySpace s,
      (∀ j,centralM s (p j)=0) ∧
      (∀ j,CentralVariationalEquation s (centralBasisSlopes j) (p j)) ∧
      (∀ j,WeaklyHarmonicOn (centralWholeL2 (centralAmbientComponent s 0 (p j).val)) centralHarmonicRegion) ∧
      ∀ (a : R3) (R : ℝ),0<R → Metric.closedBall a R⊆centralHarmonicRegion →
        (∀ j,AnalyticOnNhd ℝ
          (radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p j).val)) (R/4)) (Metric.ball a (R/4)) ∧
          (centralWholeL2 (centralAmbientComponent s 0 (p j).val) : R3 → ℝ)
            =ᵐ[volume.restrict (Metric.ball a (R/4))]
            radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p j).val)) (R/4)) ∧
        ∀ᵐ x∂volume,x∈Metric.ball a (R/4) → ∃ r>0,
          Metric.ball x r⊆Metric.ball a (R/4) ∧
          HarmonicPairRegularOn
            (radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p 0).val)) (R/4))
            (radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p 1).val)) (R/4))
            (Metric.ball x r) := by
  classical
  have hp (j : Fin 2) := central_variational_euclidean_weak s (centralBasisSlopes j)
    (centralBasisSlopes_sum j)
  choose p hm hv hw using hp
  refine ⟨p,hm,hv,hw,?_⟩
  intro a R hR hball
  exact ⟨fun j => weakWeyl_analytic_local (hw j) hR hball,
    weakWeyl_pair_ae_regular (hw 0) (hw 1) hR hball⟩

end ScalarConductivity

end
end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.central_pair_regular_exists_oai := @OAI.ScalarConductivity.central_pair_regular_exists_oai
