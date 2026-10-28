-- Prove2me | solution 1 for OAI.CoulombBarrier.original_finite_barrier_iteration
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:37:23.933607+00:00
-- url     : https://prove2.me/submissions/3c6eb989-f807-4c30-a75d-76d824f7ed2a

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C009

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_SommerfeldCoefficient
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
namespace CoulombPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

lemma laplacian_comp_isometry {f : E → ℝ} (e : E ≃ₗᵢ[ℝ] E) (x : E)
    (hf : ContDiffAt ℝ 2 f (e x)) : Δ (fun y => f (e y)) x = Δ f (e x) := by
  have hc : ContDiffAt ℝ 2 (fun y => f (e y)) x := hf.comp x e.contDiff.contDiffAt
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_orthonormalBasis f ((stdOrthonormalBasis ℝ E).map e)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, OrthonormalBasis.map_apply]
  rw [← second_deriv_line hc, ← second_deriv_line hf]
  congr 2
  funext t
  simp only [map_add, map_smul]

end CoulombPDE

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierSmoothMaxBarrier
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter Laplacian InnerProductSpace MeasureTheory
open scoped Topology BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE

lemma second_fderiv_scalar_comp {u : TFSpace → ℝ} {g : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (hg : ContDiff ℝ 2 g) (x v : TFSpace) :
    fderiv ℝ (fderiv ℝ (g ∘ u)) x v v =
      deriv (deriv g) (u x)*(fderiv ℝ u x v)^2+
        deriv g (u x)*fderiv ℝ (fderiv ℝ u) x v v := by
  have hud (z : TFSpace) := (hu.differentiable (by norm_num) z)
  have hgd (z : ℝ) := (hg.differentiable (by norm_num) z)
  have hud' (z : TFSpace) := ((hu.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).differentiable (by norm_num) z)
  have hgd' (z : ℝ) := differentiableAt_deriv_of_contDiffAt (hg.contDiffAt (x := z))
  have hcu := hg.comp hu
  have hcu' := (hcu.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).differentiable (by norm_num) x
  have he : (fun z => fderiv ℝ (g ∘ u) z v) =
      fun z => deriv g (u z)*fderiv ℝ u z v := by
    funext z
    rw [((hgd (u z)).hasDerivAt.comp_hasFDerivAt z (hud z).hasFDerivAt).fderiv]
    rfl
  rw [← fderiv_apply_const_scalar hcu' v v,he]
  have h1 := (hgd' (u x)).hasDerivAt.comp_hasFDerivAt x (hud x).hasFDerivAt
  have h2 : DifferentiableAt ℝ (fun z => fderiv ℝ u z v) x :=
    (hud' x).clm_apply (differentiableAt_const v)
  rw [show (fun z => deriv g (u z)*fderiv ℝ u z v) =
      (deriv g ∘ u)*(fun z => fderiv ℝ u z v) from rfl,
    fderiv_mul h1.differentiableAt h2]
  simp only [add_apply,smul_apply,smul_eq_mul,
    Function.comp_apply]
  rw [h1.fderiv,fderiv_apply_const_scalar (hud' x)]
  simp only [smul_apply,smul_eq_mul]
  ring

lemma laplacian_scalar_comp_lower {u : TFSpace → ℝ} {g : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (hg : ContDiff ℝ 2 g) (x : TFSpace)
    (hpos : 0 ≤ deriv (deriv g) (u x)) :
    deriv g (u x)*Δ u x ≤ Δ (g ∘ u) x := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [second_fderiv_scalar_comp hu hg]
  exact le_add_of_nonneg_left (mul_nonneg hpos (sq_nonneg _))

lemma smoothPositive_contDiff {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 2 (smoothPositive ε) := by
  exact (contDiff_id.add (((contDiff_id.pow 2).add contDiff_const).sqrt
    (fun t => ne_of_gt (by positivity)))).div_const 2

lemma smoothRoot_hasDerivAt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (fun z : ℝ => Real.sqrt (z^2+ε^2))
      (t/Real.sqrt (t^2+ε^2)) t := by
  have hq : t^2+ε^2 ≠ 0 := ne_of_gt (by positivity)
  have hd : HasDerivAt (fun z : ℝ => Real.sqrt (z^2+ε^2))
      (2*t/(2*Real.sqrt (t^2+ε^2))) t := by
    simpa only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one] using
      ((((hasDerivAt_id t).pow 2).add_const (ε^2)).sqrt hq)
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma smoothPositive_deriv {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    deriv (smoothPositive ε) t = (1+t/Real.sqrt (t^2+ε^2))/2 := by
  have hh := ((hasDerivAt_id t).add (smoothRoot_hasDerivAt hε t)).div_const 2
  exact hh.deriv

lemma smoothPositive_deriv_bounds {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 ≤ deriv (smoothPositive ε) t ∧ deriv (smoothPositive ε) t ≤ 1 := by
  have hq : 0 < Real.sqrt (t^2+ε^2) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (by positivity : 0 ≤ t^2+ε^2)
  have ha : |t| ≤ Real.sqrt (t^2+ε^2) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg ε]
  have hlo : -1 ≤ t/Real.sqrt (t^2+ε^2) := (le_div_iff₀ hq).mpr (by linarith [(abs_le.mp ha).1])
  have hhi : t/Real.sqrt (t^2+ε^2) ≤ 1 := (div_le_iff₀ hq).mpr (by linarith [(abs_le.mp ha).2])
  rw [smoothPositive_deriv hε]
  constructor <;> linarith

lemma smoothPositive_second_nonneg {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 ≤ deriv (deriv (smoothPositive ε)) t := by
  have hq : t^2+ε^2 ≠ 0 := ne_of_gt (by positivity)
  have hqs : 0 < Real.sqrt (t^2+ε^2) := Real.sqrt_pos.mpr (by positivity)
  have hd' := smoothRoot_hasDerivAt hε t
  have he : deriv (smoothPositive ε) = fun z => (1+z/Real.sqrt (z^2+ε^2))/2 :=
    funext (smoothPositive_deriv hε)
  rw [he]
  have hquot := (hasDerivAt_id t).div hd' hqs.ne'
  have hh : HasDerivAt (fun z => (1+z/Real.sqrt (z^2+ε^2))/2)
      (((Real.sqrt (t^2+ε^2)-t*(t/Real.sqrt (t^2+ε^2)))/Real.sqrt (t^2+ε^2)^2)/2) t := by
    simpa only [Pi.add_apply,Pi.div_apply,id_eq,one_mul,zero_add] using
      ((hasDerivAt_const t 1).add hquot |>.div_const 2)
  rw [hh.deriv]
  have hnum : 0 ≤ Real.sqrt (t^2+ε^2)-t*(t/Real.sqrt (t^2+ε^2)) := by
    rw [← mul_div_assoc,sub_nonneg,div_le_iff₀ hqs]
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ t^2+ε^2),sq_nonneg ε]
  exact div_nonneg (div_nonneg (by simpa only [one_mul] using hnum) (sq_nonneg _)) (by norm_num)

lemma smoothMaximum_contDiff {ε : ℝ} (hε : 0 < ε) {u v : TFSpace → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    ContDiff ℝ 2 (smoothMaximum ε u v) :=
  hv.add ((smoothPositive_contDiff hε).comp (hu.sub hv))

theorem smoothMaximum_laplacian_lower {ε : ℝ} (hε : 0 < ε) {u v : TFSpace → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (x : TFSpace) {h : ℝ}
    (huL : h ≤ Δ u x) (hvL : h ≤ Δ v x) :
    h ≤ Δ (smoothMaximum ε u v) x := by
  have hd := laplacian_scalar_comp_lower (hu.sub hv) (smoothPositive_contDiff hε) x
    (smoothPositive_second_nonneg hε (u x-v x))
  obtain ⟨hp0,hp1⟩ := smoothPositive_deriv_bounds hε (u x-v x)
  change deriv (smoothPositive ε) (u x-v x)*Δ (u-v) x ≤ Δ (smoothPositive ε ∘ (u-v)) x at hd
  rw [(hu.contDiffAt (x := x)).laplacian_sub hv.contDiffAt] at hd
  change deriv (smoothPositive ε) (u x-v x)*(Δ u x-Δ v x) ≤ _ at hd
  change h ≤ Δ (v+smoothPositive ε ∘ (u-v)) x
  have hc : ContDiff ℝ 2 (smoothPositive ε ∘ (u-v)) :=
    (smoothPositive_contDiff hε).comp (hu.sub hv)
  rw [hv.contDiffAt.laplacian_add hc.contDiffAt]
  nlinarith [mul_nonneg hp0 (sub_nonneg.mpr huL),
    mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hvL)]

lemma smoothPositive_bounds {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    max t 0 ≤ smoothPositive ε t ∧ smoothPositive ε t ≤ max t 0+ε/2 := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ t^2+ε^2)
  have hp := Real.sqrt_nonneg (t^2+ε^2)
  have hlo : |t| ≤ Real.sqrt (t^2+ε^2) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg ε]
  have hhi : Real.sqrt (t^2+ε^2) ≤ |t|+ε := by
    nlinarith [abs_nonneg t,sq_abs t,mul_nonneg (abs_nonneg t) hε]
  by_cases ht : 0 ≤ t
  · rw [max_eq_left ht,abs_of_nonneg ht] at *
    dsimp [smoothPositive]
    constructor <;> linarith
  · have ht' := le_of_not_ge ht
    rw [max_eq_right ht',abs_of_nonpos ht'] at *
    dsimp [smoothPositive]
    constructor <;> linarith

lemma smoothMaximum_bounds {ε : ℝ} (hε : 0 ≤ ε) (u v : TFSpace → ℝ) (x : TFSpace) :
    max (u x) (v x) ≤ smoothMaximum ε u v x ∧
    smoothMaximum ε u v x ≤ max (u x) (v x)+ε/2 := by
  obtain ⟨hl,hh⟩ := smoothPositive_bounds hε (u x-v x)
  dsimp [smoothMaximum]
  by_cases hvu : v x ≤ u x
  · rw [max_eq_left hvu,max_eq_left (sub_nonneg.mpr hvu)] at *
    constructor <;> linarith
  · have huv := le_of_not_ge hvu
    rw [max_eq_right huv,max_eq_right (sub_nonpos.mpr huv)] at *
    constructor <;> linarith

lemma smoothMaximum_norm_bound {ε C : ℝ} (hε : 0 ≤ ε) {u v : TFSpace → ℝ}
    (x : TFSpace) (hu : ‖u x‖ ≤ C) (hv : ‖v x‖ ≤ C) :
    ‖smoothMaximum ε u v x‖ ≤ C+ε/2 := by
  have hb := smoothMaximum_bounds hε u v x
  have hu' := abs_le.mp hu
  have hv' := abs_le.mp hv
  rw [Real.norm_eq_abs,abs_le]
  constructor
  · linarith [le_max_left (u x) (v x)]
  · linarith [max_le hu'.2 hv'.2]

lemma smoothMaximum_tendsto {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    {u v : ι → TFSpace → ℝ} {a b : ℝ} (x : TFSpace)
    (hε0 : ∀ᶠ i in l, 0 ≤ ε i) (hε : Tendsto ε l (𝓝 0))
    (hu : Tendsto (fun i => u i x) l (𝓝 a))
    (hv : Tendsto (fun i => v i x) l (𝓝 b)) :
    Tendsto (fun i => smoothMaximum (ε i) (u i) (v i) x) l (𝓝 (max a b)) := by
  have hm := hu.max hv
  have he := hm.add (hε.div_const 2)
  simp only [zero_div,add_zero] at he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hm he
  · filter_upwards [hε0] with i hi
    exact (smoothMaximum_bounds hi (u i) (v i) x).1
  · filter_upwards [hε0] with i hi
    exact (smoothMaximum_bounds hi (u i) (v i) x).2

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierWeakMaxBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology Convolution

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

lemma newtonMul_flip_eq : newtonMul.flip = newtonMul := by
  exact ContinuousLinearMap.flip_mul

lemma laplacian_sub_left {k : TFSpace → ℝ} (hk : ContDiff ℝ 2 k)
    (x y : TFSpace) : Δ (fun z => k (x-z)) y = Δ k (x-y) := by
  have hd : ContDiff ℝ 2 (fun z : TFSpace => k (x+z)) :=
    hk.comp (contDiff_const.add contDiff_id)
  have hh := laplacian_comp_isometry (LinearIsometryEquiv.neg ℝ) y hd.contDiffAt
  simpa only [LinearIsometryEquiv.coe_neg,sub_eq_add_neg,tfLaplacian_translate] using hh

lemma tsupport_sub_left {k : TFSpace → ℝ} {r : ℝ}
    (hk : ∀ z, k z ≠ 0 → ‖z‖ ≤ r) (x : TFSpace) :
    tsupport (fun y => k (x-y)) ⊆ closedBall x r := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  rw [mem_closedBall,dist_eq_norm_sub']
  exact hk (x-y) hy

lemma weak_lower_convolution {U : Set TFSpace} {u h k : TFSpace → ℝ}
    (hu : Continuous u) (hw : WeakLaplacianLowerOn U u h)
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (hk0 : ∀ y, 0 ≤ k y)
    {x : TFSpace} (hs : tsupport (fun y => k (x-y)) ⊆ U) :
    (k ⋆[newtonMul] h) x ≤ Δ (k ⋆[newtonMul] u) x := by
  have hd : ContDiff ℝ 2 (fun y => k (x-y)) := hk.comp (contDiff_const.sub contDiff_id)
  have hc : HasCompactSupport (fun y => k (x-y)) := hkc.comp_homeomorph (Homeomorph.subLeft x)
  have hi := hw _ hd hc hs (fun y => hk0 (x-y))
  have he : k ⋆[newtonMul] u = u ⋆[newtonMul] k := by
    simpa only [newtonMul_flip_eq] using (convolution_flip newtonMul (f := u) (g := k))
  rw [he,laplacian_convolution hu.locallyIntegrable hkc hk]
  simp_rw [laplacian_sub_left hk] at hi
  rw [convolution_eq_swap]
  simpa only [newtonMul,ContinuousLinearMap.mul_apply',mul_comm] using hi

lemma maxKernel_radius (n : ℕ) : (shrinkingBump (E := TFSpace) n).rOut ≤ 2 := by
  dsimp [shrinkingBump]
  have hn : (1:ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have ht := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hn
  norm_num only [one_div_one] at ht
  linarith

lemma maxKernel_support (n : ℕ) {z : TFSpace} (hz : maxKernel n z ≠ 0) :
    ‖z‖ ≤ (shrinkingBump (E := TFSpace) n).rOut := by
  have ht : z ∈ Function.support ((shrinkingBump (E := TFSpace) n).normed volume) := hz
  rw [ContDiffBump.support_normed_eq] at ht
  exact (by simpa only [mem_ball,dist_zero_right] using ht : ‖z‖ < _).le

lemma maxMollify_contDiff {u : TFSpace → ℝ} (hu : LocallyIntegrable u) (n : ℕ) :
    ContDiff ℝ 2 (maxMollify n u) :=
  (shrinkingBump n).hasCompactSupport_normed.contDiff_convolution_left newtonMul
    (shrinkingBump n).contDiff_normed hu

lemma maxMollify_tendsto {u : TFSpace → ℝ} (hu : Continuous u) (x : TFSpace) :
    Tendsto (fun n => maxMollify n u x) atTop (𝓝 (u x)) := by
  exact ContDiffBump.convolution_tendsto_right_of_continuous shrinkingBump_tendsto hu x

lemma maxMollify_bound {u : TFSpace → ℝ} {R C : ℝ}
    (hC : ∀ y, ‖y‖ ≤ R+2 → ‖u y‖ ≤ C) (n : ℕ) {x : TFSpace} (hx : ‖x‖ ≤ R) :
    ‖maxMollify n u x‖ ≤ C := by
  have hi : Integrable (maxKernel n) :=
    (shrinkingBump n).continuous_normed.integrable_of_hasCompactSupport
      (shrinkingBump n).hasCompactSupport_normed
  change ‖∫ z, maxKernel n z*u (x-z)‖ ≤ C
  calc
    _ ≤ ∫ z, C*maxKernel n z := norm_integral_le_of_norm_le (hi.const_mul C)
      (Eventually.of_forall fun z => by
        by_cases hz : maxKernel n z = 0
        · simp only [hz,zero_mul,mul_zero,norm_zero,le_refl]
        · rw [norm_mul,Real.norm_of_nonneg (show 0 ≤ maxKernel n z from (shrinkingBump n).nonneg_normed z)]
          have hb : ‖u (x-z)‖ ≤ C := hC (x-z)
            ((norm_sub_le x z).trans (add_le_add hx ((maxKernel_support n hz).trans (maxKernel_radius n))))
          nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ maxKernel n z from (shrinkingBump n).nonneg_normed z)])
    _ = C := by rw [integral_const_mul]; change C*(∫ z, (shrinkingBump n).normed volume z) = C; rw [ContDiffBump.integral_normed,mul_one]

lemma continuous_ball_bound {u : TFSpace → ℝ} (hu : Continuous u) (R : ℝ) :
    ∃ C > 0, ∀ x, ‖x‖ ≤ R → ‖u x‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := ((isCompact_closedBall (0 : TFSpace) R).image hu).isBounded.exists_pos_norm_lt
  exact ⟨C,hC,fun x hx => (hb _ ⟨x,by simpa using hx,rfl⟩).le⟩

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierWeakMaxGeneralBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierWeakMaxGeneral_barrier_scope

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology Convolution

open CoulombAnalysis CoulombPDE CoulombAtom

lemma maxMollify_test_pairing {h φ : TFSpace → ℝ} (hh : LocallyIntegrable h)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (n : ℕ) :
    (∫ x, maxMollify n h x * φ x) =
      maxMollify n (h ⋆[newtonMul] (fun x => φ (-x))) 0 := by
  let φ' : TFSpace → ℝ := fun x => φ (-x)
  have hd : Continuous φ' := hφ.comp continuous_neg
  have hc : HasCompactSupport φ' := hcφ.comp_homeomorph (Homeomorph.neg TFSpace)
  have hk : Continuous (maxKernel n) := (shrinkingBump n).continuous_normed
  have hkc : HasCompactSupport (maxKernel n) := (shrinkingBump n).hasCompactSupport_normed
  have hhn : LocallyIntegrable (fun x => ‖h x‖) := fun x => (hh x).norm
  have hfg := hkc.convolutionExists_left newtonMul hk hh
  have hgk := hc.norm.convolutionExists_right newtonMul hhn hd.norm
  have hgkc := hc.norm.continuous_convolution_right newtonMul hhn hd.norm
  have hfgk := hkc.norm.convolutionExists_left_of_continuous_right (μ := volume) newtonMul
    hk.norm.locallyIntegrable hgkc 0
  have ha := convolution_assoc newtonMul newtonMul newtonMul newtonMul
    (fun x y z : ℝ => mul_assoc x y z) hk.aestronglyMeasurable
    hh.aestronglyMeasurable hd.aestronglyMeasurable
    (Eventually.of_forall hfg) (Eventually.of_forall hgk) hfgk
  simpa only [maxMollify,convolution_def, newtonMul, ContinuousLinearMap.mul_apply',zero_sub,φ',neg_neg] using ha

lemma maxMollify_test_tendsto {h φ : TFSpace → ℝ} (hh : LocallyIntegrable h)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, maxMollify n h x * φ x) atTop (𝓝 (∫ x, h x*φ x)) := by
  let φ' : TFSpace → ℝ := fun x => φ (-x)
  have hd : Continuous φ' := hφ.comp continuous_neg
  have hc : HasCompactSupport φ' := hcφ.comp_homeomorph (Homeomorph.neg TFSpace)
  have ht := maxMollify_tendsto (hc.continuous_convolution_right newtonMul hh hd) 0
  simp_rw [maxMollify_test_pairing hh hφ hcφ]
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  simp only [convolution_def,newtonMul,ContinuousLinearMap.mul_apply',zero_sub,φ',neg_neg]

theorem weak_maximum_common_locallyIntegrable_source {U : Set TFSpace} (hU : IsOpen U)
    {u v h : TFSpace → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hh : LocallyIntegrable h)
    (hwu : WeakLaplacianLowerOn U u h) (hwv : WeakLaplacianLowerOn U v h) :
    WeakLaplacianLowerOn U (fun x => max (u x) (v x)) h := by
  intro φ hφ hcφ hsφ hnφ
  obtain ⟨δ,hδ,hsδ⟩ := hcφ.isCompact.exists_cthickening_subset_open hU hsφ
  obtain ⟨R,hR,hbR⟩ := hcφ.isCompact.isBounded.exists_pos_norm_lt
  obtain ⟨Cu,hCu,hbu⟩ := continuous_ball_bound hu (R+2)
  obtain ⟨Cv,hCv,hbv⟩ := continuous_ball_bound hv (R+2)
  let D := max Cu Cv
  let ε : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεle (n : ℕ) : ε n ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℝ) < (n:ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let w : ℕ → TFSpace → ℝ := fun n => smoothMaximum (ε n) (maxMollify n u) (maxMollify n v)
  have hwd (n : ℕ) : ContDiff ℝ 2 (w n) := smoothMaximum_contDiff (hε n)
    (maxMollify_contDiff hu.locallyIntegrable n) (maxMollify_contDiff hv.locallyIntegrable n)
  have hwb (n : ℕ) {x : TFSpace} (hx : x ∈ tsupport φ) : ‖w n x‖ ≤ D+1 := by
    have hux : ‖maxMollify n u x‖ ≤ D :=
      (maxMollify_bound hbu n (hbR x hx).le).trans (le_max_left _ _)
    have hvx : ‖maxMollify n v x‖ ≤ D :=
      (maxMollify_bound hbv n (hbR x hx).le).trans (le_max_right _ _)
    have hw := smoothMaximum_norm_bound (hε n).le x hux hvx
    change ‖w n x‖ ≤ D+ε n/2 at hw
    linarith [hεle n]
  have hwlim (x : TFSpace) : Tendsto (fun n => w n x) atTop (𝓝 (max (u x) (v x))) :=
    smoothMaximum_tendsto x (Eventually.of_forall fun n => (hε n).le) hε0
      (maxMollify_tendsto hu x) (maxMollify_tendsto hv x)
  have hΔφ := tfLaplacian_continuous hφ
  have hcΔφ := tfLaplacian_compact hφ hcφ
  have htR : Tendsto (fun n => ∫ x, w n x*Δ φ x) atTop
      (𝓝 (∫ x, max (u x) (v x)*Δ φ x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => (D+1)*‖Δ φ x‖)
    · intro n
      exact ((hwd n).continuous.mul hΔφ).aestronglyMeasurable
    · exact (hΔφ.norm.integrable_of_hasCompactSupport hcΔφ.norm).const_mul _
    · intro n
      exact Eventually.of_forall fun x => by
        by_cases hx : Δ φ x = 0
        · simp only [hx,mul_zero,norm_zero,le_refl]
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hwb n (tfLaplacian_support hφ hx)) (norm_nonneg _)
    · exact Eventually.of_forall fun x => (hwlim x).mul_const (Δ φ x)
  have htL := maxMollify_test_tendsto hh hφ.continuous hcφ
  apply le_of_tendsto_of_tendsto htL htR
  filter_upwards [(shrinkingBump_tendsto (E := TFSpace)).eventually (gt_mem_nhds hδ)] with n hn
  have hks (x : TFSpace) (hx : x ∈ tsupport φ) :
      tsupport (fun y => maxKernel n (x-y)) ⊆ U := by
    intro y hy
    have hxy := tsupport_sub_left (fun z hz => maxKernel_support n hz) x hy
    apply hsδ
    exact mem_cthickening_of_dist_le y x δ (tsupport φ) hx ((mem_closedBall.mp hxy).trans hn.le)
  have hlow (x : TFSpace) (hx : x ∈ tsupport φ) : maxMollify n h x ≤ Δ (w n) x := by
    apply smoothMaximum_laplacian_lower (hε n) (maxMollify_contDiff hu.locallyIntegrable n)
      (maxMollify_contDiff hv.locallyIntegrable n)
    · exact weak_lower_convolution hu hwu (shrinkingBump n).contDiff_normed
        (shrinkingBump n).hasCompactSupport_normed (shrinkingBump n).nonneg_normed (hks x hx)
    · exact weak_lower_convolution hv hwv (shrinkingBump n).contDiff_normed
        (shrinkingBump n).hasCompactSupport_normed (shrinkingBump n).nonneg_normed (hks x hx)
  rw [compact_laplacian_green (hwd n) hφ hcφ]
  apply integral_mono
    (((maxMollify_contDiff hh n).continuous.mul hφ.continuous).integrable_of_hasCompactSupport hcφ.mul_left)
    (((tfLaplacian_continuous (hwd n)).mul hφ.continuous).integrable_of_hasCompactSupport hcφ.mul_left)
  intro x
  change maxMollify n h x * φ x ≤ Δ (w n) x * φ x
  by_cases hx : φ x = 0
  · simp only [hx,mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right (hlow x (subset_tsupport φ hx)) (hnφ x)

end Work_BarrierWeakMaxGeneral_barrier_scope

open Set Filter MeasureTheory Laplacian Metric InnerProductSpace
open scoped Topology Convolution BigOperators Manifold

open CoulombAnalysis CoulombPDE CoulombAtom

lemma locallyIntegrable_mul_test {h φ : TFSpace → ℝ} (hh : LocallyIntegrable h)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Integrable (fun x => h x*φ x) :=
  hh.integrable_smul_right_of_hasCompactSupport hφ hcφ

lemma laplacian_finset_sum {ι : Type*} (s : Finset ι) (f : ι → TFSpace → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i)) (x : TFSpace) :
    Δ (∑ i ∈ s, f i) x = ∑ i ∈ s, Δ (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Pi.zero_def,laplacian_const]
  | @insert i s hi ih =>
    have hi' := hf i (Finset.mem_insert_self _ _)
    have hs' : ∀ j ∈ s, ContDiff ℝ 2 (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hsD : ContDiff ℝ 2 (∑ j ∈ s, f j) := by
      simpa only [←Finset.sum_apply] using ContDiff.sum hs'
    rw [Finset.sum_insert hi,hi'.contDiffAt.laplacian_add hsD.contDiffAt,
      ih hs',Finset.sum_insert hi]

theorem weak_lower_open_cover {ι : Type*} {V : ι → Set TFSpace}
    (hV : ∀ i, IsOpen (V i)) {u h : TFSpace → ℝ}
    (hu : LocallyIntegrable u) (hh : LocallyIntegrable h)
    (hw : ∀ i, WeakLaplacianLowerOn (V i) u h) :
    WeakLaplacianLowerOn (⋃ i, V i) u h := by
  classical
  intro φ hφ hcφ hsφ hnφ
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ,TFSpace))
    (isClosed_tsupport φ) V hV hsφ
  let s := (ρ.locallyFinite.finite_nonempty_inter_compact hcφ.isCompact).toFinset
  let ψ : ι → TFSpace → ℝ := fun i x => ρ i x*φ x
  have hψd (i : ι) : ContDiff ℝ 2 (ψ i) :=
    ((ρ i).contMDiff.contDiff.of_le (by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)).mul hφ
  have hψc (i : ι) : HasCompactSupport (ψ i) := hcφ.mul_left
  have hψs (i : ι) : tsupport (ψ i) ⊆ V i := tsupport_mul_subset_left.trans (hρ i)
  have hψn (i : ι) (x : TFSpace) : 0 ≤ ψ i x := mul_nonneg (ρ.nonneg i x) (hnφ x)
  have hψzero {i : ι} (hi : i ∉ s) (x : TFSpace) : ψ i x = 0 := by
    dsimp [ψ]
    by_cases h1 : ρ i x = 0
    · rw [h1,zero_mul]
    · have h2 : φ x = 0 := by
        by_contra h2
        apply hi
        exact (Set.Finite.mem_toFinset _).mpr ⟨x,h1,subset_tsupport φ h2⟩
      rw [h2,mul_zero]
  have hsum : ∑ i ∈ s, ψ i = φ := by
    funext x
    rw [Finset.sum_apply]
    calc
      ∑ i ∈ s, ψ i x = ∑ᶠ i, ψ i x :=
        (finsum_eq_sum_of_support_subset (fun i => ψ i x) (s := s) fun i hi => by
          by_contra hn
          exact hi (hψzero hn x)).symm
      _ = φ x := by
        dsimp only [ψ]
        rw [←finsum_mul]
        by_cases hx : φ x = 0
        · rw [hx,mul_zero]
        · rw [ρ.sum_eq_one (subset_tsupport φ hx),one_mul]
  have hLp : (∫ x, h x*φ x) = ∑ i ∈ s, ∫ x, h x*ψ i x := by
    conv_lhs => rw [←hsum]
    simp only [Finset.sum_apply,Finset.mul_sum]
    exact integral_finsetSum s (fun i _ => locallyIntegrable_mul_test hh (hψd i).continuous (hψc i))
  have hRp : (∫ x, u x*Δ φ x) = ∑ i ∈ s, ∫ x, u x*Δ (ψ i) x := by
    conv_lhs => rw [←hsum]
    simp_rw [laplacian_finset_sum s ψ (fun i _ => hψd i),Finset.mul_sum]
    exact integral_finsetSum s (fun i _ => locallyIntegrable_mul_test hu
      (tfLaplacian_continuous (hψd i)) (tfLaplacian_compact (hψd i) (hψc i)))
  rw [hLp,hRp]
  exact Finset.sum_le_sum fun i _ => hw i _ (hψd i) (hψc i) (hψs i) (hψn i)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierNonlinearBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology Convolution BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

lemma WeakLaplacianLowerOn.mono_set {U V : Set TFSpace} {u h : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (hVU : V ⊆ U) : WeakLaplacianLowerOn V u h :=
  fun φ hφ hc hs hn => hw φ hφ hc (hs.trans hVU) hn

lemma WeakLaplacianLowerOn.congr_field {U : Set TFSpace} {u v h : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (he : ∀ x ∈ U, u x = v x) :
    WeakLaplacianLowerOn U v h := by
  intro φ hφ hc hs hn
  calc
    _ ≤ ∫ x, u x*Δ φ x := hw φ hφ hc hs hn
    _ = _ := integral_congr_ae (Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : Δ φ x = 0
      · rw [hx,mul_zero,mul_zero]
      · rw [he x (hs (tfLaplacian_support hφ hx))])

lemma WeakLaplacianLowerOn.source_mono_ae {U : Set TFSpace} {u h h' : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (hh : LocallyIntegrable h)
    (hh' : LocallyIntegrable h') (hle : ∀ᵐ x, x ∈ U → h' x ≤ h x) :
    WeakLaplacianLowerOn U u h' := by
  intro φ hφ hc hs hn
  apply le_trans _ (hw φ hφ hc hs hn)
  apply integral_mono_ae (locallyIntegrable_mul_test hh' hφ.continuous hc)
    (locallyIntegrable_mul_test hh hφ.continuous hc)
  filter_upwards [hle] with x hx
  by_cases hφx : φ x = 0
  · simp only [hφx,mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right (hx (hs (subset_tsupport φ hφx))) (hn x)

lemma WeakLaplacianLowerOn.source_mono {U : Set TFSpace} {u h h' : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (hh : LocallyIntegrable h)
    (hh' : LocallyIntegrable h') (hle : ∀ x ∈ U, h' x ≤ h x) :
    WeakLaplacianLowerOn U u h' := hw.source_mono_ae hh hh' (Eventually.of_forall hle)

lemma weak_lower_local {U : Set TFSpace} {u h : TFSpace → ℝ}
    (hu : LocallyIntegrable u) (hh : LocallyIntegrable h)
    (hw : ∀ x ∈ U, ∃ V : Set TFSpace, IsOpen V ∧ x ∈ V ∧ WeakLaplacianLowerOn V u h) :
    WeakLaplacianLowerOn U u h := by
  choose V hV hxV hW using fun x : U => hw x x.property
  apply (weak_lower_open_cover hV hu hh hW).mono_set
  intro x hx
  exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩

lemma weak_lower_of_constant_errors {U : Set TFSpace} {u h : TFSpace → ℝ}
    (hh : LocallyIntegrable h)
    (hw : ∀ ε > 0, WeakLaplacianLowerOn U u (fun x => h x-ε)) :
    WeakLaplacianLowerOn U u h := by
  intro φ hφ hc hs hn
  have hi := locallyIntegrable_mul_test hh hφ.continuous hc
  have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hc
  have he (ε : ℝ) (hε : 0 < ε) :
      (∫ x, h x*φ x)-ε*(∫ x, φ x) ≤ ∫ x, u x*Δ φ x := by
    have ht := hw ε hε φ hφ hc hs hn
    simp_rw [sub_mul] at ht
    rwa [integral_sub hi (hφi.const_mul ε),integral_const_mul] at ht
  have ht := (tendsto_const_nhds (x := ∫ x, h x*φ x)).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (∫ x, φ x))
  have hb := le_of_tendsto ht (Eventually.of_forall fun n : ℕ =>
    he (1/((n:ℝ)+1)) (by positivity))
  simpa only [zero_mul,sub_zero] using hb

lemma semilinear_source_locallyIntegrable {g χ u : TFSpace → ℝ} {F : ℝ → ℝ}
    (hg : LocallyIntegrable g) (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hF : Continuous F) (hu : Continuous u) :
    LocallyIntegrable (fun x => g x+χ x*F (u x)) := by
  have hχl : LocallyIntegrable χ :=
    (memLp_top_of_bound hχ.aestronglyMeasurable 1 (Eventually.of_forall hbχ)).locallyIntegrable le_top
  exact hg.add (LocallyIntegrable.mul_continuous (hF.comp hu) hχl)

lemma weighted_max_reaction_le {F : ℝ → ℝ} {a b χ ε : ℝ}
    (hχ : ‖χ‖ ≤ 1) (hε : 0 ≤ ε) (hF : ‖F a-F b‖ ≤ ε) :
    χ*F (max a b)-ε ≤ χ*F a := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    have hb : χ*(F b-F a) ≤ ε := by
      calc
        _ ≤ ‖χ*(F b-F a)‖ := le_abs_self _
        _ = ‖χ‖*‖F a-F b‖ := by rw [norm_mul,norm_sub_rev]
        _ ≤ 1*ε := mul_le_mul hχ hF (norm_nonneg _) (by norm_num)
        _ = ε := one_mul _
    nlinarith
  · rw [max_eq_left hba]
    linarith

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_BarrierConditionalBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CoulombBarrier

lemma reaction_nonneg {k : ℝ} (hk : 0 ≤ k) (t : ℝ) : 0 ≤ reaction k t := by
  unfold reaction
  positivity

lemma reaction_monotone {k : ℝ} (hk : 0 ≤ k) : Monotone (reaction k) := by
  intro s t hst
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (le_max_right _ _) (max_le_max hst le_rfl) (by norm_num))
    (by positivity)

lemma reaction_continuous (k : ℝ) : Continuous (reaction k) := by
  apply continuous_const.mul
  exact (continuous_id.max continuous_const).rpow_const (fun _ => Or.inr (by norm_num))

lemma reaction_convex {k : ℝ} (hk : 0 ≤ k) : ConvexOn ℝ univ (reaction k) := by
  have hm : ConvexOn ℝ (univ : Set ℝ) (fun t : ℝ => max t 0) :=
    (convexOn_id convex_univ).sup (convexOn_const 0 convex_univ)
  have him : (fun t : ℝ => max t 0) '' univ = Ici 0 := by
    ext t
    constructor
    · rintro ⟨s,_,rfl⟩
      exact le_max_right (s : ℝ) 0
    · intro ht
      exact ⟨t,mem_univ _,max_eq_left ht⟩
  have hp : ConvexOn ℝ ((fun t : ℝ => max t 0) '' univ)
      (fun t : ℝ => t^(3/2:ℝ)) := by
    rw [him]
    exact convexOn_rpow (by norm_num)
  have hmono : MonotoneOn (fun t : ℝ => t^(3/2:ℝ))
      ((fun t : ℝ => max t 0) '' univ) := by
    rw [him]
    intro s hs t _ hst
    exact Real.rpow_le_rpow hs hst (by norm_num)
  exact (hp.comp hm hmono).smul (by positivity : 0 ≤ 4*Real.pi*k)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierSpatialBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology Convolution BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

lemma spatial_source_locallyIntegrable {g χ u : TFSpace → ℝ} {F : TFSpace → ℝ → ℝ}
    (hg : LocallyIntegrable g) (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hF : Continuous (fun p : TFSpace × ℝ => F p.1 p.2)) (hu : Continuous u) :
    LocallyIntegrable (fun x => g x+χ x*F x (u x)) := by
  have hχl : LocallyIntegrable χ :=
    (memLp_top_of_bound hχ.aestronglyMeasurable 1 (Eventually.of_forall hbχ)).locallyIntegrable le_top
  exact hg.add (LocallyIntegrable.mul_continuous (hF.comp (continuous_id.prodMk hu)) hχl)

theorem weak_maximum_spatial {U : Set TFSpace} (hU : IsOpen U)
    {u v g χ : TFSpace → ℝ} {F : TFSpace → ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hg : LocallyIntegrable g)
    (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1) (hF : Continuous (fun p : TFSpace × ℝ => F p.1 p.2))
    (hwu : WeakLaplacianLowerOn U u (fun x => g x+χ x*F x (u x)))
    (hwv : WeakLaplacianLowerOn U v (fun x => g x+χ x*F x (v x))) :
    WeakLaplacianLowerOn U (fun x => max (u x) (v x))
      (fun x => g x+χ x*F x (max (u x) (v x))) := by
  let w : TFSpace → ℝ := fun x => max (u x) (v x)
  have hwc : Continuous w := hu.max hv
  have hgu := spatial_source_locallyIntegrable hg hχ hbχ hF hu
  have hgv := spatial_source_locallyIntegrable hg hχ hbχ hF hv
  have hgw := spatial_source_locallyIntegrable hg hχ hbχ hF hwc
  apply weak_lower_of_constant_errors hgw
  intro ε hε
  have hge : LocallyIntegrable (fun x => (g x+χ x*F x (w x))-ε) :=
    hgw.sub (locallyIntegrable_const ε)
  apply weak_lower_local hwc.locallyIntegrable hge
  intro x hx
  by_cases heq : u x = v x
  · let V := U ∩ {y | ‖F y (u y)-F y (v y)‖ < ε}
    have hVo : IsOpen V := hU.inter (isOpen_lt ((hF.comp (continuous_id.prodMk hu)).sub (hF.comp (continuous_id.prodMk hv))).norm continuous_const)
    have hxV : x ∈ V := ⟨hx,by simp only [mem_ofPred_eq,heq,sub_self,norm_zero]; exact hε⟩
    have hcu : WeakLaplacianLowerOn V u (fun x => (g x+χ x*F x (w x))-ε) := by
      apply (hwu.mono_set inter_subset_left).source_mono hgu hge
      intro y hy
      have he := weighted_max_reaction_le (hbχ y) hε.le hy.2.le
      change χ y*F y (w y)-ε ≤ χ y*F y (u y) at he
      linarith
    have hcv : WeakLaplacianLowerOn V v (fun x => (g x+χ x*F x (w x))-ε) := by
      apply (hwv.mono_set inter_subset_left).source_mono hgv hge
      intro y hy
      have he := weighted_max_reaction_le (F := F y) (a := v y) (b := u y)
        (hbχ y) hε.le (by rw [norm_sub_rev]; exact hy.2.le)
      rw [max_comm] at he
      change χ y*F y (w y)-ε ≤ χ y*F y (v y) at he
      linarith
    exact ⟨V,hVo,hxV,weak_maximum_common_locallyIntegrable_source hVo hu hv hge hcu hcv⟩
  · rcases lt_or_gt_of_ne heq with huv | hvu
    · let V := U ∩ {y | u y < v y}
      have hVo : IsOpen V := hU.inter (isOpen_lt hu hv)
      have hvw : ∀ y ∈ V, v y = w y := fun y hy => (max_eq_right hy.2.le).symm
      have he : WeakLaplacianLowerOn V v (fun x => (g x+χ x*F x (w x))-ε) := by
        apply (hwv.mono_set inter_subset_left).source_mono hgv hge
        intro y hy
        rw [←hvw y hy]
        linarith
      exact ⟨V,hVo,⟨hx,huv⟩,he.congr_field hvw⟩
    · let V := U ∩ {y | v y < u y}
      have hVo : IsOpen V := hU.inter (isOpen_lt hv hu)
      have huw : ∀ y ∈ V, u y = w y := fun y hy => (max_eq_left hy.2.le).symm
      have he : WeakLaplacianLowerOn V u (fun x => (g x+χ x*F x (w x))-ε) := by
        apply (hwu.mono_set inter_subset_left).source_mono hgu hge
        intro y hy
        rw [←huw y hy]
        linarith
      exact ⟨V,hVo,⟨hx,hvu⟩,he.congr_field huw⟩

theorem weak_finset_maximum_spatial {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {U : Set TFSpace} (hU : IsOpen U) (u : ι → TFSpace → ℝ)
    (hu : ∀ i ∈ s, Continuous (u i)) {g χ : TFSpace → ℝ} {F : TFSpace → ℝ → ℝ}
    (hg : LocallyIntegrable g) (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hF : Continuous (fun p : TFSpace × ℝ => F p.1 p.2))
    (hw : ∀ i ∈ s, WeakLaplacianLowerOn U (u i) (fun x => g x+χ x*F x (u i x))) :
    WeakLaplacianLowerOn U (fun x => s.sup' hs (fun i => u i x))
      (fun x => g x+χ x*F x (s.sup' hs (fun i => u i x))) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact False.elim (Finset.not_nonempty_empty hs)
  | @insert i s hi ih =>
    by_cases hs' : s.Nonempty
    · have hu' : ∀ j ∈ s, Continuous (u j) := fun j hj => hu j (Finset.mem_insert_of_mem hj)
      have hw' : ∀ j ∈ s, WeakLaplacianLowerOn U (u j) (fun x => g x+χ x*F x (u j x)) :=
        fun j hj => hw j (Finset.mem_insert_of_mem hj)
      have hh := weak_maximum_spatial hU (hu i (Finset.mem_insert_self _ _))
        (Continuous.finset_sup'_apply hs' hu') hg hχ hbχ hF
        (hw i (Finset.mem_insert_self _ _)) (ih hs' hu' hw')
      simpa only [Finset.sup'_insert hs'] using hh
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst s
      simpa only [Finset.insert_empty,Finset.sup'_singleton] using hw i (Finset.mem_singleton_self i)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierNuclearBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

lemma nuclearField_locallyIntegrable (Z : ℝ) : LocallyIntegrable (nuclearField Z) := by
  change LocallyIntegrable (fun x : TFSpace => Z*‖x‖⁻¹)
  exact newtonInverse_locallyIntegrable.smul Z

lemma clippedNuclearField_continuous (Z : ℝ) {R : ℝ} (hR : 0 < R) :
    Continuous (clippedNuclearField Z R) := by
  exact continuous_const.div (continuous_const.max continuous_norm)
    (fun x => ne_of_gt (hR.trans_le (le_max_left R ‖x‖)))

lemma weighted_clipped_reaction (Z R : ℝ) {χ : TFSpace → ℝ}
    (hχ : ∀ x, ‖x‖ < R → χ x = 0) (F : ℝ → ℝ) (t : ℝ) (x : TFSpace) :
    χ x*F (nuclearField Z x+t) = χ x*F (clippedNuclearField Z R x+t) := by
  by_cases hx : ‖x‖ < R
  · rw [hχ x hx,zero_mul,zero_mul]
  · simp only [clippedNuclearField,max_eq_right (le_of_not_gt hx),nuclearField]

lemma nuclearField_weak_laplacian (Z : ℝ) {φ : TFSpace → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, nuclearField Z x*Δ φ x) = -(4*Real.pi*Z)*φ 0 := by
  have h := tfPotential_laplacian hφ hc (0 : TFSpace)
  have he : (fun x => nuclearField Z x*Δ φ x) = fun x => Z*(Δ φ x/‖x‖) := by
    funext x
    dsimp only [nuclearField]
    ring
  rw [he,integral_const_mul]
  simp only [tfPotential,zero_sub,norm_neg] at h
  rw [h]
  ring

theorem weakNuclearLower_add_iff {U : Set TFSpace} (Z : ℝ) {u h : TFSpace → ℝ}
    (hu : LocallyIntegrable u) :
    WeakNuclearLowerOn U Z (fun x => nuclearField Z x+u x) h ↔
      WeakLaplacianLowerOn U u h := by
  have he (φ : TFSpace → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
      (∫ x, (nuclearField Z x+u x)*Δ φ x) =
        -(4*Real.pi*Z)*φ 0+(∫ x, u x*Δ φ x) := by
    simp_rw [add_mul]
    rw [integral_add
      (locallyIntegrable_mul_test (nuclearField_locallyIntegrable Z)
        (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc))
      (locallyIntegrable_mul_test hu (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc)),
      nuclearField_weak_laplacian Z hφ hc]
  constructor
  · intro hw φ hφ hc hs hn
    have ht := hw φ hφ hc hs hn
    rw [he φ hφ hc] at ht
    exact (add_le_add_iff_left _).mp ht
  · intro hw φ hφ hc hs hn
    rw [he φ hφ hc]
    exact add_le_add_right (hw φ hφ hc hs hn) _

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_UnorderedObservations
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_UnorderedObservations_scope

open MeasureTheory Set
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation

lemma unorderedConfiguration_measurable {N : ℕ} :
    Measurable (unorderedConfiguration (N := N)) := measurable_quotient_mk''

lemma physicalObservedConfiguration_measurable {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) :
    Measurable (physicalObservedConfiguration (N := N) ell k) := by
  apply Measurable.of_eval
  intro i
  apply (Continuous.measurable (by fun_prop : Continuous (WithLp.toLp 2 : (Fin 3 → ℝ) → Space))).comp
  apply Measurable.of_eval
  intro a
  exact (((EuclideanSpace.proj a : Space →L[ℝ] ℝ).measurable.comp
    ((measurable_pi_apply i).comp measurable_fst)).add
    (((measurable_pi_apply (k,i,a)).comp measurable_snd).const_mul _))

lemma unorderedObservedConfiguration_measurable {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) :
    Measurable (unorderedObservedConfiguration (N := N) ell k) :=
  unorderedConfiguration_measurable.comp (physicalObservedConfiguration_measurable ell k)

lemma observationInformation_le {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    observationInformation (N := N) ell j ≤
      (inferInstance : MeasurableSpace (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))) := by
  apply iSup_le
  intro k
  split_ifs
  · exact (unorderedObservedConfiguration_measurable ell k).comap_le
  · exact bot_le

lemma observationInformation_antitone {N K : ℕ} (ell : Fin K → ℝ) :
    Antitone (observationInformation (N := N) ell) := by
  intro i j hij
  apply iSup_le
  intro k
  split_ifs with hk
  · exact le_iSup_of_le k (by rw [ite_eq_left (hij.trans hk)])
  · exact bot_le

end CoulombAtom

end Work_UnorderedObservations_scope

open MeasureTheory Set Filter Metric
open scoped BigOperators NNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ConditionalSandwich
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter

open MeasureTheory Filter Set Metric
open scoped BigOperators NNReal

namespace CoulombAtom
open CoulombObservation

lemma posteriorTestValue_tower {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) {j k : ℕ} (hjk : j ≤ k) (g : Space → ℝ) :
    (physicalObservationLaw μ K)[posteriorTestValue μ ell j g | observationInformation ell k] =ᵐ[
      physicalObservationLaw μ K] posteriorTestValue μ ell k g :=
  condExp_condExp_of_le (observationInformation_antitone ell hjk) (observationInformation_le ell j)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_OriginalPosteriorKernel
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation ProbabilityTheory

lemma originalDatum_measurable {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    Measurable (originalDatum (N := N) ell j) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap id (observationInformation ell j) ≤ _
  simpa only [MeasurableSpace.comap_id] using (observationInformation_le (N := N) ell j)

lemma originalDatum_comap {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    MeasurableSpace.comap (originalDatum (N := N) ell j) inferInstance =
      observationInformation ell j := MeasurableSpace.comap_id

lemma kernelPosteriorTest_eq {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {g : Space → ℝ} (hg : Measurable g)
    (hi : Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
      ∑ i, g (z.1 i)) (physicalObservationLaw μ K)) :
    posteriorTestValue μ ell j g =ᵐ[physicalObservationLaw μ K]
      fun z => kernelPosteriorTest μ ell j g (originalDatum ell j z) := by
  have h := condExp_ae_eq_integral_condDistrib (originalDatum_measurable (N := N) ell j)
    measurable_fst.aemeasurable
    ((Finset.measurable_sum _ (fun i _ => hg.comp (measurable_pi_apply i))).stronglyMeasurable) hi
  simpa only [originalDatum_comap,posteriorTestValue,kernelPosteriorTest,originalRawKernel,Function.comp_def] using h

lemma kernelPosteriorTest_tower {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) {j k : ℕ} (hjk : j ≤ k)
    {g : Space → ℝ} (hg : Measurable g)
    (hi : Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
      ∑ i, g (z.1 i)) (physicalObservationLaw μ K)) :
    (physicalObservationLaw μ K)[(fun z => kernelPosteriorTest μ ell j g (originalDatum ell j z)) |
      observationInformation ell k] =ᵐ[physicalObservationLaw μ K]
      fun z => kernelPosteriorTest μ ell k g (originalDatum ell k z) := by
  exact (condExp_congr_ae (kernelPosteriorTest_eq μ ell j hg hi).symm).trans
    ((posteriorTestValue_tower μ ell hjk g).trans (kernelPosteriorTest_eq μ ell k hg hi))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_MasterWidth
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Metric
open scoped NNReal

lemma masterWidth_lower {c₁ r₀ s : ℝ} (hc : 0 ≤ c₁) (hr : 0 < r₀) (hrs : r₀ ≤ s)
    (x : Space) : c₁*r₀^(1+masterExponent) ≤ masterWidth c₁ r₀ s x := by
  have hD : r₀ ≤ masterBaseDistance r₀ x := le_max_right _ _
  rw [Real.rpow_one_add' hr.le (by linarith [masterExponent_pos])]
  simpa only [masterWidth,mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul hD (Real.rpow_le_rpow hr.le (le_min hD hrs) masterExponent_nonneg)
      (Real.rpow_nonneg hr.le _) (hr.le.trans hD)) hc

open Set Metric
open scoped NNReal

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_LocalWidthKernel
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped NNReal ContDiff

lemma masterKernel_nonneg (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) :
    0 ≤ masterKernel c₁ r₀ s g x y := sq_nonneg _

lemma masterKernel_mass {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hgn : ∫ z, (g z)^2 = 1) (x : Space) :
    ∫ y, masterKernel c₁ r₀ s g x y = 1 := by
  unfold masterKernel
  rw [integral_sub_right_eq_self (fun z => (scaledRealPacket (masterWidth c₁ r₀ s x) g z)^2) x,
    scaledRealPacket_mass (masterWidth_pos hc hr hs x) g,hgn]

lemma masterKernel_joint_continuous {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) :
    Continuous (fun p : Space × Space => masterKernel c₁ r₀ s g p.1 p.2) := by
  rw [masterKernel_eq_widthKernel hc hr hs g]
  have ht := (masterWidth_lipschitz hc.le hr hs).continuous.comp (continuous_fst : Continuous (Prod.fst : Space × Space → Space))
  have hi := ht.inv₀ (fun p => (masterWidth_pos hc hr hs p.1).ne')
  exact (hi.pow 3).mul ((hg.pow 2).comp (hi.smul (continuous_snd.sub continuous_fst)))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_Average
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators
open CoulombAnalysis CoulombPDE CoulombAtom
section Average
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma deterministicBound_integrable_section {u : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u) (x : TFSpace) :
    Integrable (fun sample => u sample x) P := by
  obtain ⟨C,hC⟩ := hb {x} (isCompact_singleton)
  exact Integrable.of_bound (hu.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable C
    (Eventually.of_forall fun sample => hC sample x (mem_singleton x))

lemma deterministicBound_integrable_test {u : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u)
    {φ : TFSpace → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun p : Ω × TFSpace => u p.1 p.2*φ p.2) (P.prod volume) := by
  obtain ⟨C,hC⟩ := hb (tsupport φ) hc.isCompact
  have hi : Integrable (fun p : Ω × TFSpace => C*‖φ p.2‖) (P.prod volume) :=
    ((hφ.integrable_of_hasCompactSupport hc (μ := volume)).norm.const_mul C).comp_snd P
  apply hi.mono' (hu.mul (hφ.measurable.comp measurable_snd)).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    change ‖u p.1 p.2*φ p.2‖ ≤ C*‖φ p.2‖
    rw [norm_mul]
    by_cases hp : φ p.2 = 0
    · simp only [hp,norm_zero,mul_zero,le_refl]
    · exact mul_le_mul_of_nonneg_right (hC p.1 p.2 (subset_tsupport φ hp)) (norm_nonneg _)

lemma average_measurable {u : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) : Measurable (fun x => ∫ sample, u sample x ∂P) := by
  have hm : StronglyMeasurable (Function.uncurry fun x sample => u sample x) :=
    (hu.comp measurable_swap).stronglyMeasurable
  exact hm.integral_prod_right.measurable

lemma average_deterministic_bound {u : Ω → TFSpace → ℝ}
    (hb : DeterministicLocalBound u) :
    DeterministicLocalBound (fun _ : Unit => fun x => ∫ sample, u sample x ∂P) := by
  intro K hK
  obtain ⟨C,hC⟩ := hb K hK
  refine ⟨C,fun _ x hx => ?_⟩
  calc
    _ ≤ ∫ _ : Ω, C ∂P := norm_integral_le_of_norm_le (integrable_const C)
      (Eventually.of_forall fun sample => hC sample x hx)
    _ = C := by simp

lemma average_continuous {u : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u)
    (hc : ∀ᵐ sample ∂P, Continuous (u sample)) : Continuous (fun x => ∫ sample, u sample x ∂P) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨C,hC⟩ := hb (closedBall x 1) (isCompact_closedBall x 1)
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => C)
  · exact Eventually.of_forall fun y =>
      (hu.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds x (by norm_num : (0:ℝ)<1)] with y hy
    exact Eventually.of_forall fun sample => hC sample y (ball_subset_closedBall hy)
  · exact integrable_const C
  · exact hc.mono fun _ h => h.continuousAt

theorem weak_lower_average {U : Set TFSpace} {u h : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u)
    (hh : Measurable (Function.uncurry h)) (hhb : DeterministicLocalBound h)
    (hw : ∀ᵐ sample ∂P, WeakLaplacianLowerOn U (u sample) (h sample)) :
    WeakLaplacianLowerOn U (fun x => ∫ sample, u sample x ∂P) (fun x => ∫ sample, h sample x ∂P) := by
  intro φ hφ hc hs hn
  have h1 := deterministicBound_integrable_test (P := P) hh hhb hφ.continuous hc
  have h2 := deterministicBound_integrable_test (P := P) hu hb
    (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc)
  calc
    (∫ x, (∫ sample, h sample x ∂P)*φ x) = ∫ sample, (∫ x, h sample x*φ x) ∂P := by
      simp_rw [←integral_mul_const]
      exact (integral_integral_swap (f := fun sample x => h sample x*φ x) h1).symm
    _ ≤ ∫ sample, (∫ x, u sample x*Δ φ x) ∂P :=
      integral_mono_ae h1.integral_prod_left h2.integral_prod_left
        (hw.mono fun sample hω => hω φ hφ hc hs hn)
    _ = ∫ x, (∫ sample, u sample x ∂P)*Δ φ x := by
      rw [integral_integral_swap (f := fun sample x => u sample x*Δ φ x) h2]
      simp_rw [integral_mul_const]

end Average

theorem conditional_all_properties {Ω D : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace D]
    (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → D} (hX : Measurable X)
    {p : Ω → Prop} (hp : ∀ᵐ sample ∂P, p sample) :
    ∀ᵐ d ∂P.map X, ∀ᵐ sample ∂condDistrib id X P d, p sample := by
  apply Measure.ae_ae_of_ae_comp
  rw [condDistrib_comp_map hX.aemeasurable measurable_id.aemeasurable,Measure.map_id]
  exact hp

open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators

open CoulombAnalysis CoulombPDE CoulombAtom

lemma DeterministicLocalBound.add {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalBound u) (hv : DeterministicLocalBound v) :
    DeterministicLocalBound (fun sample x => u sample x+v sample x) := by
  intro K hK
  obtain ⟨A,hA⟩ := hu K hK
  obtain ⟨B,hB⟩ := hv K hK
  exact ⟨A+B,fun sample x hx => (norm_add_le _ _).trans (add_le_add (hA sample x hx) (hB sample x hx))⟩

lemma DeterministicLocalBound.spatial_comp {Ω : Type*} {u : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalBound u) {F : TFSpace → ℝ → ℝ}
    (hF : Continuous (fun p : TFSpace × ℝ => F p.1 p.2)) :
    DeterministicLocalBound (fun sample x => F x (u sample x)) := by
  intro K hK
  obtain ⟨C,hC⟩ := hu K hK
  obtain ⟨D,_,hD⟩ := ((hK.prod (isCompact_closedBall (0:ℝ) C)).image hF).isBounded.exists_pos_norm_lt
  refine ⟨D,fun sample x hx => ?_⟩
  exact (hD _ ⟨(x,u sample x),⟨hx,by simpa only [mem_closedBall,dist_zero_right] using hC sample x hx⟩,rfl⟩).le

lemma DeterministicLocalBound.bounded_mul {Ω : Type*} {u : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalBound u) {χ : TFSpace → ℝ} (hχ : ∀ x, ‖χ x‖ ≤ 1) :
    DeterministicLocalBound (fun sample x => χ x*u sample x) := by
  intro K hK
  obtain ⟨C,hC⟩ := hu K hK
  refine ⟨C,fun sample x hx => ?_⟩
  calc
    ‖χ x*u sample x‖ = ‖χ x‖*‖u sample x‖ := norm_mul _ _
    _ ≤ 1*‖u sample x‖ := mul_le_mul_of_nonneg_right (hχ x) (norm_nonneg _)
    _ ≤ C := by simpa only [one_mul] using hC sample x hx

lemma deterministicBound_locallyIntegrable {u : TFSpace → ℝ}
    (hu : Measurable u) (hb : DeterministicLocalBound (fun _ : Unit => u)) :
    LocallyIntegrable u := by
  intro x
  obtain ⟨C,hC⟩ := hb (closedBall x 1) (isCompact_closedBall x 1)
  refine ⟨closedBall x 1,closedBall_mem_nhds x (by norm_num : (0:ℝ)<1),?_⟩
  apply (integrableOn_const (C := C) (isCompact_closedBall x 1).measure_lt_top.ne).mono'
    hu.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy
  exact hC () y hy

lemma average_locallyIntegrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {u : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u) :
    LocallyIntegrable (fun x => ∫ sample, u sample x ∂P) :=
  deterministicBound_locallyIntegrable (average_measurable hu) (average_deterministic_bound hb)

theorem weak_spatial_average {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {U : Set TFSpace} {u g : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hub : DeterministicLocalBound u)
    (huc : ∀ᵐ sample ∂P, Continuous (u sample))
    (hg : Measurable (Function.uncurry g)) (hgb : DeterministicLocalBound g)
    {χ : TFSpace → ℝ} (hχ : Measurable χ) (hχb : ∀ x, ‖χ x‖ ≤ 1) (hχn : ∀ x, 0 ≤ χ x)
    {F : TFSpace → ℝ → ℝ} (hF : Continuous (fun p : TFSpace × ℝ => F p.1 p.2))
    (hFc : ∀ x, ConvexOn ℝ univ (F x))
    (hw : ∀ᵐ sample ∂P, WeakLaplacianLowerOn U (u sample) (fun x => g sample x+χ x*F x (u sample x))) :
    WeakLaplacianLowerOn U (fun x => ∫ sample, u sample x ∂P)
      (fun x => (∫ sample, g sample x ∂P)+χ x*F x (∫ sample, u sample x ∂P)) := by
  have hfm : Measurable (Function.uncurry fun sample x => F x (u sample x)) :=
    hF.measurable.comp (measurable_snd.prodMk hu)
  have hfb := hub.spatial_comp hF
  have hsm : Measurable (Function.uncurry fun sample x => g sample x+χ x*F x (u sample x)) :=
    hg.add ((hχ.comp measurable_snd).mul hfm)
  have hsb := hgb.add (hfb.bounded_mul hχb)
  have hsl := average_locallyIntegrable (P := P) hsm hsb
  have hgl := average_locallyIntegrable (P := P) hg hgb
  have huc' := average_continuous hu hub huc
  have htl := spatial_source_locallyIntegrable hgl hχ hχb hF huc'
  apply (weak_lower_average hu hub hsm hsb hw).source_mono hsl htl
  intro x _
  have hiu := deterministicBound_integrable_section (P := P) hu hub x
  have hig := deterministicBound_integrable_section (P := P) hg hgb x
  have hif := deterministicBound_integrable_section (P := P) hfm hfb x
  have hj := (hFc x).map_integral_le
    (hF.comp (continuous_const.prodMk continuous_id)).continuousOn isClosed_univ
    (Eventually.of_forall fun _ => mem_univ _) hiu hif
  rw [integral_add hig (hif.const_mul (χ x)),integral_const_mul]
  exact add_le_add_right (mul_le_mul_of_nonneg_left hj (hχn x)) _

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierForgettingBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

lemma shifted_reaction_convex {k : ℝ} (hk : 0 ≤ k) (c : ℝ) :
    ConvexOn ℝ univ (fun t => reaction k (c+t)) := by
  simpa only [preimage_univ,Function.comp_def] using (reaction_convex hk).translate_right c

theorem weak_nuclear_average {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {U : Set TFSpace} (Z : ℝ)
    {u g : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hub : DeterministicLocalBound u)
    (huc : ∀ᵐ sample ∂P, Continuous (u sample))
    (hg : Measurable (Function.uncurry g)) (hgb : DeterministicLocalBound g)
    {χ : TFSpace → ℝ} (hχ : Measurable χ) (hχb : ∀ x, ‖χ x‖ ≤ 1) (hχn : ∀ x, 0 ≤ χ x)
    {R k : ℝ} (hR : 0 < R) (hk : 0 ≤ k) (hzero : ∀ x, ‖x‖ < R → χ x = 0)
    (hw : ∀ᵐ sample ∂P, WeakNuclearLowerOn U Z (fun x => nuclearField Z x+u sample x)
      (fun x => g sample x+χ x*reaction k (nuclearField Z x+u sample x))) :
    WeakNuclearLowerOn U Z (fun x => nuclearField Z x+∫ sample, u sample x ∂P)
      (fun x => (∫ sample, g sample x ∂P)+χ x*reaction k (nuclearField Z x+∫ sample, u sample x ∂P)) := by
  rw [weakNuclearLower_add_iff Z (average_locallyIntegrable hu hub)]
  simp_rw [weighted_clipped_reaction Z R hzero]
  apply weak_spatial_average hu hub huc hg hgb hχ hχb hχn
    (F := fun x t => reaction k (clippedNuclearField Z R x+t))
    ((reaction_continuous k).comp (((clippedNuclearField_continuous Z hR).comp continuous_fst).add continuous_snd))
    (fun x => shifted_reaction_convex hk _)
  filter_upwards [hw,huc] with sample hw hc
  have hw' := (weakNuclearLower_add_iff Z hc.locallyIntegrable).mp hw
  simpa only [weighted_clipped_reaction Z R hzero] using hw'

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_Conditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators
namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom
variable {Ω D : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
variable [MeasurableSpace D] (P : Measure Ω) [IsProbabilityMeasure P]
variable (X : Ω → D) (hX : Measurable X)

lemma conditionalField_measurable {u : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) :
    Measurable (Function.uncurry (conditionalField P X u)) := by
  have hm : StronglyMeasurable (fun p : (D × TFSpace) × Ω => u p.2 p.1.2) :=
    (hu.comp (measurable_snd.prodMk measurable_fst.snd)).stronglyMeasurable
  exact (hm.integral_kernel_prod_right'
    (κ := (condDistrib id X P).comap Prod.fst measurable_fst)).measurable

lemma conditionalField_bound {u : Ω → TFSpace → ℝ} (hb : DeterministicLocalBound u) :
    DeterministicLocalBound (conditionalField P X u) := by
  intro K hK
  obtain ⟨C,hC⟩ := hb K hK
  refine ⟨C,fun d x hx => ?_⟩
  calc
    _ ≤ ∫ _ : Ω, C ∂condDistrib id X P d := norm_integral_le_of_norm_le (integrable_const C)
      (Eventually.of_forall fun sample => hC sample x hx)
    _ = C := by simp

include hX

lemma conditionalField_continuous {u : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u)
    (hc : ∀ᵐ sample ∂P, Continuous (u sample)) :
    ∀ᵐ d ∂P.map X, Continuous (conditionalField P X u d) := by
  filter_upwards [conditional_all_properties P hX hc] with d hd
  exact average_continuous hu hb hd

theorem weak_nuclear_conditional {U : Set TFSpace} (Z : ℝ)
    {u g : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hub : DeterministicLocalBound u)
    (huc : ∀ᵐ sample ∂P, Continuous (u sample))
    (hg : Measurable (Function.uncurry g)) (hgb : DeterministicLocalBound g)
    {χ : TFSpace → ℝ} (hχ : Measurable χ) (hχb : ∀ x, ‖χ x‖ ≤ 1) (hχn : ∀ x, 0 ≤ χ x)
    {R k : ℝ} (hR : 0 < R) (hk : 0 ≤ k) (hzero : ∀ x, ‖x‖ < R → χ x = 0)
    (hw : ∀ᵐ sample ∂P, WeakNuclearLowerOn U Z (fun x => nuclearField Z x+u sample x)
      (fun x => g sample x+χ x*reaction k (nuclearField Z x+u sample x))) :
    ∀ᵐ d ∂P.map X, WeakNuclearLowerOn U Z
      (fun x => nuclearField Z x+conditionalField P X u d x)
      (fun x => conditionalField P X g d x+
        χ x*reaction k (nuclearField Z x+conditionalField P X u d x)) := by
  filter_upwards [conditional_all_properties P hX huc,conditional_all_properties P hX hw] with d hc hw
  exact weak_nuclear_average Z hu hub hc hg hgb hχ hχb hχn hR hk hzero hw

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_MasterJointPosterior
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombObservation ProbabilityTheory

lemma jointMasterPosterior_nonneg {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (c₁ r₀ s : ℝ) (g : Space → ℝ)
    (z : OriginalDatum N K ell j) (y : Space) :
    0 ≤ jointMasterPosterior μ ell j c₁ r₀ s g z y :=
  integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => masterKernel_nonneg c₁ r₀ s g (x i) y))

lemma jointMasterPosterior_measurable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) :
    Measurable (fun p : OriginalDatum N K ell j × Space =>
      jointMasterPosterior μ ell j c₁ r₀ s g p.1 p.2) := by
  have hm := (masterKernel_joint_continuous hc hr hs hg).measurable
  have h : StronglyMeasurable (fun p : (OriginalDatum N K ell j × Space) × Configuration N =>
      ∑ i, masterKernel c₁ r₀ s g (p.2 i) p.1.2) :=
    (Finset.measurable_sum _ (fun i _ => hm.comp
      (((measurable_pi_apply i).comp measurable_snd).prodMk measurable_fst.snd))).stronglyMeasurable
  exact (h.integral_kernel_prod_right' (κ := (originalRawKernel μ ell j).comap Prod.fst measurable_fst)).measurable

lemma masterKernel_integrable {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hgn : ∫ z, (g z)^2 = 1) (x : Space) :
    Integrable (masterKernel c₁ r₀ s g x) := by
  by_contra h
  have hm := masterKernel_mass hc hr hs hgn x
  rw [integral_undef h] at hm
  norm_num at hm

lemma masterConfigurationKernel_integrable {N : ℕ} (ν : Measure (Configuration N)) [IsFiniteMeasure ν]
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) (hgn : ∫ z, (g z)^2 = 1) :
    Integrable (fun p : Configuration N × Space => ∑ i, masterKernel c₁ r₀ s g (p.1 i) p.2)
      (ν.prod volume) := by
  have hm := (masterKernel_joint_continuous hc hr hs hg).measurable
  apply (integrable_prod_iff ((Finset.measurable_sum _ (fun i _ => hm.comp
    (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd))).aestronglyMeasurable)).mpr
  refine ⟨ae_of_all _ (fun x => integrable_finsetSum _ (fun i _ => masterKernel_integrable hc hr hs hgn (x i))),?_⟩
  have he (x : Configuration N) :
      (∫ y, ‖∑ i, masterKernel c₁ r₀ s g (x i) y‖) = (N:ℝ) := by
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun i _ => masterKernel_nonneg c₁ r₀ s g (x i) _))]
    rw [integral_finsetSum _ (fun i _ => masterKernel_integrable hc hr hs hgn (x i))]
    simp only [masterKernel_mass hc hr hs hgn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  change Integrable (fun x : Configuration N => ∫ y, ‖∑ i, masterKernel c₁ r₀ s g (x i) y‖) ν
  simpa only [he] using (integrable_const (N:ℝ) : Integrable (fun _ : Configuration N => (N:ℝ)) ν)

lemma jointMasterPosterior_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) (hgn : ∫ z, (g z)^2 = 1)
    (z : OriginalDatum N K ell j) :
    Integrable (jointMasterPosterior μ ell j c₁ r₀ s g z) :=
  (masterConfigurationKernel_integrable (originalRawKernel μ ell j z) hc hr hs hg hgn).integral_prod_right

lemma jointMasterPosterior_mass {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) (hgn : ∫ z, (g z)^2 = 1)
    (z : OriginalDatum N K ell j) :
    ∫ y, jointMasterPosterior μ ell j c₁ r₀ s g z y = (N:ℝ) := by
  change (∫ y, ∫ x, ∑ i, masterKernel c₁ r₀ s g (x i) y ∂originalRawKernel μ ell j z) = _
  rw [←integral_integral_swap (masterConfigurationKernel_integrable (originalRawKernel μ ell j z) hc hr hs hg hgn)]
  have he (x : Configuration N) : (∫ y, ∑ i, masterKernel c₁ r₀ s g (x i) y) = (N:ℝ) := by
    rw [integral_finsetSum _ (fun i _ => masterKernel_integrable hc hr hs hgn (x i))]
    simp [masterKernel_mass hc hr hs hgn]
  simp_rw [he]
  simp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierMasterRegularityBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierMasterRegularity_barrier_scope

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators ContDiff Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation

lemma masterKernel_global_bound {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) {g : Space → ℝ}
    (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖masterKernel c₁ r₀ s g x y‖ ≤ C := by
  have hc2 : HasCompactSupport (fun x => (g x)^2) := hcg.mul_left
  obtain ⟨z,hz⟩ := (hg.pow 2).norm.exists_forall_ge_of_hasCompactSupport hc2.norm
  let δ := c₁*r₀^(1+masterExponent)
  have hδ : 0 < δ := mul_pos hc (Real.rpow_pos_of_pos hr _)
  refine ⟨δ⁻¹^3*‖(g z)^2‖,by positivity,fun x y => ?_⟩
  have hi : (masterWidth c₁ r₀ s x)⁻¹ ≤ δ⁻¹ := by
    apply inv_anti₀ hδ
    exact masterWidth_lower hc.le hr hrs x
  rw [masterKernel,scaledRealPacket_sq (masterWidth_pos hc hr hs x),norm_mul,
    Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (masterWidth_pos hc hr hs x).le) 3)]
  exact mul_le_mul (pow_le_pow_left₀ (inv_nonneg.mpr (masterWidth_pos hc hr hs x).le) hi 3)
    (hz _) (norm_nonneg _) (by positivity)

attribute [local irreducible] masterKernel masterWidth scaledRealPacket

lemma masterConfigurationDensity_measurable {N : ℕ} {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) :
    Measurable (Function.uncurry (masterConfigurationDensity (N := N) c₁ r₀ s g)) := by
  have hm (i : Fin N) : Measurable (fun p : Configuration N × Space =>
      masterKernel c₁ r₀ s g (p.1 i) p.2) :=
    (masterKernel_joint_continuous hc hr hs hg).measurable.comp
      (f := fun p : Configuration N × Space => (p.1 i,p.2))
      (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd)
  exact Finset.measurable_sum Finset.univ (fun i _ => hm i)

lemma masterConfigurationDensity_continuous {N : ℕ} {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g)
    (z : Configuration N) : Continuous (masterConfigurationDensity c₁ r₀ s g z) := by
  have ht (i : Fin N) : Continuous (fun y : Space => masterKernel c₁ r₀ s g (z i) y) :=
    (masterKernel_joint_continuous hc hr hs hg).comp
      (f := fun y : Space => (z i,y)) (continuous_const.prodMk continuous_id)
  exact continuous_finsetSum Finset.univ (fun i _ => ht i)

lemma masterConfigurationDensity_bound {N : ℕ} {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z y, ‖masterConfigurationDensity (N := N) c₁ r₀ s g z y‖ ≤ C := by
  obtain ⟨C,hCn,hC⟩ := masterKernel_global_bound hc hr hs hrs hg hcg
  refine ⟨N*C,by positivity,fun z y => ?_⟩
  calc
    _ ≤ ∑ i : Fin N, ‖masterKernel c₁ r₀ s g (z i) y‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, C := Finset.sum_le_sum (fun i _ => hC (z i) y)
    _ = N*C := by simp

lemma masterConfigurationDensity_deterministicBound {N : ℕ} {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    DeterministicLocalBound (masterConfigurationDensity (N := N) c₁ r₀ s g) := by
  obtain ⟨C,_,hC⟩ := masterConfigurationDensity_bound (N := N) hc hr hs hrs hg hcg
  exact fun _ _ => ⟨C,fun z y _ => hC z y⟩

lemma jointMasterPosterior_continuous {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (d : OriginalDatum N K ell j) :
    Continuous (jointMasterPosterior μ ell j c₁ r₀ s g d) := by
  exact average_continuous (masterConfigurationDensity_measurable hc hr hs hg)
    (masterConfigurationDensity_deterministicBound hc hr hs hrs hg hcg)
    (Eventually.of_forall (masterConfigurationDensity_continuous hc hr hs hg))

lemma jointMasterPosterior_global_bound {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d y, ‖jointMasterPosterior μ ell j c₁ r₀ s g d y‖ ≤ C := by
  obtain ⟨C,hCn,hC⟩ := masterConfigurationDensity_bound (N := N) hc hr hs hrs hg hcg
  refine ⟨C,hCn,fun d y => ?_⟩
  calc
    _ ≤ ∫ _ : Configuration N, C ∂originalRawKernel μ ell j d :=
      norm_integral_le_of_norm_le (integrable_const C) (Eventually.of_forall fun z => hC z y)
    _ = C := by simp

end CoulombBarrier

end Work_BarrierMasterRegularity_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierObservationTowerBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterKernel masterWidth scaledRealPacket

lemma ae_forall_eq_of_continuous {D : Type*} [MeasurableSpace D] {P : Measure D}
    {u v : D → TFSpace → ℝ} (hu : ∀ᵐ d ∂P, Continuous (u d))
    (hv : ∀ᵐ d ∂P, Continuous (v d))
    (he : ∀ x, ∀ᵐ d ∂P, u d x = v d x) :
    ∀ᵐ d ∂P, ∀ x, u d x = v d x := by
  obtain ⟨S,hSc,hSd⟩ := TopologicalSpace.exists_countable_dense TFSpace
  let : Countable S := hSc.to_subtype
  have hS : ∀ᵐ d ∂P, ∀ x : S, u d x = v d x := ae_all_iff.mpr (fun x => he x)
  filter_upwards [hu,hv,hS] with d hud hvd hSd'
  have hfun : u d = v d := Continuous.ext_on hSd hud hvd (fun x hx => hSd' ⟨x,hx⟩)
  exact congrFun hfun

lemma conditionalField_eq_condExp {Ω D : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace D]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → D} (hX : Measurable X)
    {u : Ω → TFSpace → ℝ} (hu : Measurable (Function.uncurry u))
    (hub : DeterministicLocalBound u) (x : TFSpace) :
    P[(fun sample => u sample x) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun sample => conditionalField P X u (X sample) x := by
  have hm : StronglyMeasurable (fun sample => u sample x) :=
    (hu.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable
  have hi := deterministicBound_integrable_section (P := P) hu hub x
  simpa only [conditionalField,Function.comp_def,id_eq] using
    (condExp_ae_eq_integral_condDistrib hX measurable_id.aemeasurable hm hi)

lemma originalMasterField_measurable {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) :
    Measurable (Function.uncurry (originalMasterField μ ell j c₁ r₀ s g)) :=
  (jointMasterPosterior_measurable μ ell j hc hr hs hg).comp
    (((originalDatum_measurable ell j).comp measurable_fst).prodMk measurable_snd)

lemma originalMasterField_deterministicBound {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    DeterministicLocalBound (originalMasterField μ ell j c₁ r₀ s g) := by
  obtain ⟨C,_,hC⟩ := jointMasterPosterior_global_bound μ ell j hc hr hs hrs hg hcg
  exact fun _ _ => ⟨C,fun z y _ => hC (originalDatum ell j z) y⟩

lemma originalMasterField_continuous {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) :
    Continuous (originalMasterField μ ell j c₁ r₀ s g z) :=
  jointMasterPosterior_continuous μ ell j hc hr hs hrs hg hcg (originalDatum ell j z)

theorem originalMasterField_tower {N K : ℕ} (μ : Measure (Configuration N))
    [IsProbabilityMeasure μ] (ell : Fin K → ℝ) {j k : ℕ} (hjk : j ≤ k) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∀ᵐ z ∂physicalObservationLaw μ K, ∀ y,
      conditionalField (physicalObservationLaw μ K) (originalDatum ell k)
        (originalMasterField μ ell j c₁ r₀ s g) (originalDatum ell k z) y =
      originalMasterField μ ell k c₁ r₀ s g z y := by
  let P := physicalObservationLaw μ K
  have hPm := originalMasterField_measurable μ ell j hc hr hs hg
  have hPb := originalMasterField_deterministicBound μ ell j hc hr hs hrs hg hcg
  have hPc := originalMasterField_continuous μ ell j hc hr hs hrs hg hcg
  apply ae_forall_eq_of_continuous
  · have hh := conditionalField_continuous P (originalDatum ell k)
      (originalDatum_measurable ell k) hPm hPb (Eventually.of_forall hPc)
    exact ae_of_ae_map (originalDatum_measurable ell k).aemeasurable hh
  · exact Eventually.of_forall (originalMasterField_continuous μ ell k hc hr hs hrs hg hcg)
  intro y
  have hce := conditionalField_eq_condExp P (originalDatum_measurable ell k) hPm hPb y
  rw [originalDatum_comap] at hce
  have hquery : Measurable (fun x => masterKernel c₁ r₀ s g x y) :=
    (masterKernel_joint_continuous hc hr hs hg).measurable.comp (measurable_id.prodMk measurable_const)
  have hrawm : Measurable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
      ∑ i, masterKernel c₁ r₀ s g (z.1 i) y) :=
    Finset.measurable_sum _ (fun i _ => hquery.comp ((measurable_pi_apply i).comp measurable_fst))
  obtain ⟨C,_,hC⟩ := masterConfigurationDensity_bound (N := N) hc hr hs hrs hg hcg
  have hrawi : Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
      ∑ i, masterKernel c₁ r₀ s g (z.1 i) y) P :=
    Integrable.of_bound hrawm.aestronglyMeasurable C (Eventually.of_forall fun z => hC z.1 y)
  exact hce.symm.trans (kernelPosteriorTest_tower μ ell hjk hquery hrawi)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BoundedL1PotentialBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma bounded_coulomb_majorant {ρ : TFSpace → ℝ} {M : ℝ}
    (_hM : 0 ≤ M) (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x z : TFSpace) :
    ρ z/‖x-z‖ ≤ M*truncatedCoulomb 1 (x-z)+ρ z := by
  by_cases hd : ‖x-z‖ < 1
  · rw [truncatedCoulomb,indicator_of_mem (mem_ball_zero_iff.mpr hd)]
    have hh := mul_le_mul_of_nonneg_right (hb z) (inv_nonneg.mpr (norm_nonneg (x-z)))
    simp only [div_eq_mul_inv,one_mul] at hh ⊢
    linarith [hn z]
  · rw [truncatedCoulomb,indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hd),mul_zero,zero_add]
    have hd' : 1 ≤ ‖x-z‖ := le_of_not_gt hd
    exact (div_le_self (hn z) hd')

lemma bounded_invSquare_majorant {ρ : TFSpace → ℝ} {M : ℝ}
    (_hM : 0 ≤ M) (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x z : TFSpace) :
    ρ z*‖x-z‖⁻¹^2 ≤ M*truncatedInvSquare 1 (x-z)+ρ z := by
  by_cases hd : ‖x-z‖ < 1
  · rw [truncatedInvSquare,indicator_of_mem (mem_ball_zero_iff.mpr hd)]
    have hh := mul_le_mul_of_nonneg_right (hb z) (sq_nonneg ‖x-z‖⁻¹)
    linarith [hn z]
  · rw [truncatedInvSquare,indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hd),mul_zero,zero_add]
    have hi : ‖x-z‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (le_of_not_gt hd)
    have hi0 := inv_nonneg.mpr (norm_nonneg (x-z))
    have hs : ‖x-z‖⁻¹^2 ≤ 1 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hs (hn z)).trans_eq (mul_one _)

lemma bounded_L1_potential_integrable {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x : TFSpace) :
    Integrable (fun z => ρ z/‖x-z‖) := by
  have hk : Integrable (fun z => truncatedCoulomb 1 (x-z)) :=
    (tfSubMap_preserving x).integrable_comp (truncatedCoulomb_integrable 1).aestronglyMeasurable
      |>.mpr (truncatedCoulomb_integrable 1)
  apply ((hk.const_mul M).add hi).mono' (hm.div (measurable_const.sub measurable_id).norm).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖ρ z/‖x-z‖‖ ≤ M*truncatedCoulomb 1 (x-z)+ρ z
    rw [Real.norm_of_nonneg (div_nonneg (hn z) (norm_nonneg _))]
    exact bounded_coulomb_majorant hM hn hb x z

lemma bounded_L1_potential_le {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x : TFSpace) :
    tfPotential ρ x ≤ 2*Real.pi*M+∫ z, ρ z := by
  have hk : Integrable (fun z => truncatedCoulomb 1 (x-z)) :=
    (tfSubMap_preserving x).integrable_comp (truncatedCoulomb_integrable 1).aestronglyMeasurable
      |>.mpr (truncatedCoulomb_integrable 1)
  calc
    _ ≤ ∫ z, M*truncatedCoulomb 1 (x-z)+ρ z := integral_mono
      (bounded_L1_potential_integrable hm hi hM hn hb x) ((hk.const_mul M).add hi)
      (bounded_coulomb_majorant hM hn hb x)
    _ = _ := by
      rw [integral_add (hk.const_mul M) hi,integral_const_mul,integral_sub_left_eq_self,
        truncatedCoulomb,integral_indicator measurableSet_ball]
      simp only [one_div]
      rw [integral_coulomb_ball (by norm_num : (0:ℝ) < 1)]
      ring

lemma bounded_L1_potential_difference {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x y : TFSpace) :
    |tfPotential ρ x-tfPotential ρ y| ≤ (4*Real.pi*M+∫ z, ρ z)*‖x-y‖ := by
  have hpi (w : TFSpace) := bounded_L1_potential_integrable hm hi hM hn hb w
  let A (w z : TFSpace) := M*truncatedInvSquare 1 (w-z)+ρ z
  have hk (w : TFSpace) : Integrable (fun z => truncatedInvSquare 1 (w-z)) :=
    (tfSubMap_preserving w).integrable_comp (truncatedInvSquare_integrable 1).aestronglyMeasurable
      |>.mpr (truncatedInvSquare_integrable 1)
  have hAi (w : TFSpace) : Integrable (A w) := ((hk w).const_mul M).add hi
  have hAm (w : TFSpace) : (∫ z, A w z) = 4*Real.pi*M+∫ z, ρ z := by
    dsimp only [A]
    rw [integral_add ((hk w).const_mul M) hi,integral_const_mul,integral_sub_left_eq_self,
      truncatedInvSquare_integral (by norm_num : (0:ℝ) < 1)]
    ring
  have he : (∫ z, ρ z/‖x-z‖-ρ z/‖y-z‖) = tfPotential ρ x-tfPotential ρ y :=
    integral_sub (hpi x) (hpi y)
  rw [←he]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ z, (‖x-y‖/2)*(A x z+A y z) := by
      apply integral_mono_ae ((hpi x).sub (hpi y)).abs (((hAi x).add (hAi y)).const_mul _)
      filter_upwards [volume.ae_ne x,volume.ae_ne y] with z hzx hzy
      change |ρ z/‖x-z‖-ρ z/‖y-z‖| ≤ _
      rw [div_eq_mul_inv,div_eq_mul_inv,←mul_sub,abs_mul,abs_of_nonneg (hn z)]
      calc
        _ ≤ ρ z*(‖x-y‖*(‖x-z‖⁻¹^2+‖y-z‖⁻¹^2)/2) :=
          mul_le_mul_of_nonneg_left (coulomb_inv_difference hzx hzy) (hn z)
        _ = (‖x-y‖/2)*(ρ z*‖x-z‖⁻¹^2+ρ z*‖y-z‖⁻¹^2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
          (bounded_invSquare_majorant hM hn hb x z) (bounded_invSquare_majorant hM hn hb y z)) (by positivity)
    _ = _ := by
      rw [integral_const_mul,integral_add (hAi x) (hAi y),hAm,hAm]
      ring

lemma bounded_L1_potential_lipschitz {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) :
    LipschitzWith ⟨4*Real.pi*M+∫ z, ρ z,add_nonneg (by positivity) (integral_nonneg hn)⟩ (tfPotential ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖tfPotential ρ x-tfPotential ρ y‖ ≤ (4*Real.pi*M+∫ z, ρ z)*‖x-y‖
  simpa only [Real.norm_eq_abs] using bounded_L1_potential_difference hm hi hM hn hb x y

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BoundedL1PoissonBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BoundedL1Poisson_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology ContDiff

namespace CoulombAnalysis
open CoulombAtom

lemma bounded_L1_laplacian_pair_integrable {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    {φ : TFSpace → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z : TFSpace × TFSpace => ρ z.2/‖z.1-z.2‖*Δ φ z.1) (volume.prod volume) := by
  have hΔ := tfLaplacian_continuous hφ
  have hΔc := tfLaplacian_compact hφ hc
  have hj : Measurable (fun z : TFSpace × TFSpace => ρ z.2/‖z.1-z.2‖*Δ φ z.1) :=
    ((hm.comp measurable_snd).div (measurable_fst.sub measurable_snd).norm).mul (hΔ.measurable.comp measurable_fst)
  apply (integrable_prod_iff hj.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun x => (bounded_L1_potential_integrable hm hi hM hn hb x).mul_const (Δ φ x)),?_⟩
  have hp := (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous
  have htest := CoulombBarrier.locallyIntegrable_mul_test hp.locallyIntegrable hΔ.norm hΔc.norm
  have he (x : TFSpace) : (∫ y, ‖ρ y/‖x-y‖*Δ φ x‖) = tfPotential ρ x*‖Δ φ x‖ := by
    simp_rw [norm_mul,Real.norm_of_nonneg (div_nonneg (hn _) (norm_nonneg _))]
    exact integral_mul_const _ _
  simpa only [he] using htest

theorem bounded_L1_weak_poisson {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    {φ : TFSpace → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, tfPotential ρ x*Δ φ x) = -(4*Real.pi)*(∫ x, ρ x*φ x) := by
  calc
    _ = ∫ x, ∫ y, ρ y/‖x-y‖*Δ φ x := by simp only [integral_mul_const,tfPotential]
    _ = ∫ y, ∫ x, ρ y/‖x-y‖*Δ φ x :=
      integral_integral_swap (bounded_L1_laplacian_pair_integrable hm hi hM hn hb hφ hc)
    _ = ∫ y, ρ y*tfPotential (Δ φ) y := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        change (∫ x, ρ y/‖x-y‖*Δ φ x) = ρ y*(∫ x, Δ φ x/‖y-x‖)
        rw [←integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun x => by dsimp only; rw [norm_sub_rev]; ring
    _ = _ := by
      simp_rw [tfPotential_laplacian hφ hc]
      rw [←integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by ring

end CoulombAnalysis
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma meanFieldOffset_weak_nuclear {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (Z lam : ℝ) :
    WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+meanFieldOffset lam ρ x)
      (fun x => 4*Real.pi*ρ x) := by
  have hp := (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous
  apply (weakNuclearLower_add_iff Z (hp.neg.sub continuous_const).locallyIntegrable).mpr
  intro φ hφ hc _ _
  have hiΔ : Integrable (Δ φ) := (tfLaplacian_continuous hφ).integrable_of_hasCompactSupport (tfLaplacian_compact hφ hc)
  have hiq := locallyIntegrable_mul_test hp.locallyIntegrable (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc)
  change (∫ x, 4*Real.pi*ρ x*φ x) ≤ ∫ x, (-tfPotential ρ x-lam)*Δ φ x
  simp_rw [sub_mul,neg_mul]
  have hneg : Integrable (fun x => -(tfPotential ρ x * Δ φ x)) := hiq.neg
  have hlam : Integrable (fun x => lam * Δ φ x) := hiΔ.const_mul lam
  rw [integral_sub hneg hlam,integral_neg,bounded_L1_weak_poisson hm hi hM hn hb hφ hc,
    integral_const_mul,compact_laplacian_mass hφ hc,mul_zero,sub_zero]
  have he : (∫ x, 4*Real.pi*ρ x*φ x) = 4*Real.pi*∫ x, ρ x*φ x := by
    simpa only [mul_assoc] using
      (integral_const_mul (4*Real.pi) (fun x : TFSpace => ρ x*φ x))
  rw [he]
  nlinarith

end CoulombBarrier

end Work_BoundedL1Poisson_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_Error
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma compactBound_integrable_prod {p : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry p)) (hb : DeterministicLocalBound p)
    {R : ℝ} (hs : ∀ sample x, R < ‖x‖ → p sample x = 0) :
    Integrable (Function.uncurry p) (P.prod volume) := by
  obtain ⟨C,hC⟩ := hb (closedBall 0 R) (isCompact_closedBall 0 R)
  have hi : Integrable ((closedBall (0 : TFSpace) R).indicator (fun _ => C)) volume :=
    (integrableOn_const (C := C) (isCompact_closedBall (0 : TFSpace) R).measure_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  apply (hi.comp_snd P).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    by_cases hz : z.2 ∈ closedBall (0 : TFSpace) R
    · rw [indicator_of_mem hz]
      exact hC z.1 z.2 hz
    · rw [indicator_of_notMem hz,Function.uncurry_apply_pair,
        hs z.1 z.2 (lt_of_not_ge (by simpa only [mem_closedBall,dist_zero_right] using hz)),norm_zero]

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_Conditional2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators Topology
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis
variable {Ω D : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
variable [MeasurableSpace D] (P : Measure Ω) [IsProbabilityMeasure P]
variable (X : Ω → D) (hX : Measurable X)

lemma conditionalField_nonneg {p : Ω → TFSpace → ℝ} (hn : ∀ sample x, 0 ≤ p sample x)
    (d : D) (x : TFSpace) : 0 ≤ conditionalField P X p d x :=
  integral_nonneg (fun sample => hn sample x)

lemma conditionalField_support {p : Ω → TFSpace → ℝ} {R : ℝ}
    (hs : ∀ sample x, R < ‖x‖ → p sample x = 0) (d : D) (x : TFSpace) (hx : R < ‖x‖) :
    conditionalField P X p d x = 0 := by
  simp only [conditionalField,hs _ x hx,integral_zero]

include hX

lemma conditionalField_expectation {p : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry p)) (hb : DeterministicLocalBound p) (x : TFSpace) :
    (∫ sample, conditionalField P X p (X sample) x ∂P) = ∫ sample, p sample x ∂P := by
  rw [←integral_congr_ae (conditionalField_eq_condExp P hX hm hb x)]
  exact integral_condExp hX.comap_le

theorem conditionalField_totalMass {p : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry p)) (hb : DeterministicLocalBound p)
    {R : ℝ} (hs : ∀ sample x, R < ‖x‖ → p sample x = 0) :
    (∫ sample, (∫ x, conditionalField P X p (X sample) x) ∂P) = ∫ sample, (∫ x, p sample x) ∂P := by
  have hcm : Measurable (fun z : Ω × TFSpace => conditionalField P X p (X z.1) z.2) :=
    (conditionalField_measurable P X hm).comp ((hX.comp measurable_fst).prodMk measurable_snd)
  have hcb : DeterministicLocalBound (fun sample x => conditionalField P X p (X sample) x) := by
    intro K hK
    obtain ⟨C,hC⟩ := conditionalField_bound P X hb K hK
    exact ⟨C,fun sample x hx => hC (X sample) x hx⟩
  have hcs : ∀ sample x, R < ‖x‖ → conditionalField P X p (X sample) x = 0 :=
    fun sample x hx => conditionalField_support P X hs (X sample) x hx
  rw [integral_integral_swap (compactBound_integrable_prod hcm hcb hcs),
    integral_integral_swap (compactBound_integrable_prod hm hb hs)]
  exact integral_congr_ae (Eventually.of_forall fun x => conditionalField_expectation P X hX hm hb x)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierRetainedComparisonBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierRetainedComparison_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma pow_four_three_halves {d : ℝ} (hd : 0 ≤ d) :
    (d^4)^(3/2:ℝ) = d^6 := by
  rw [←Real.rpow_natCast d 4,←Real.rpow_mul hd]
  norm_num

lemma scaled_positive_reaction {d u : ℝ} (hd : 0 ≤ d) (hu : 0 ≤ u) :
    (d^4*u)^(3/2:ℝ) = d^6*u^(3/2:ℝ) := by
  rw [Real.mul_rpow (by positivity) hu,pow_four_three_halves hd]

lemma inverse_high_unscaled {d H μ κ hₗ hₕ ξ C u : ℝ} (hd : 0 < d)
    (hu : 0 ≤ u) (hh : d^4*u ∈ Icc hₗ hₕ)
    (hi : InverseComparisonAt d H μ κ hₗ hₕ ξ C)
    (hμ : reaction κ u < 4*Real.pi*μ) : u-ξ/d^4 ≤ H := by
  have hπ : 0 < 4*Real.pi := by positivity
  have he : reaction κ u = (4*Real.pi)*(κ*u^(3/2:ℝ)) := by
    simp only [reaction,max_eq_left hu]
    ring
  rw [he] at hμ
  have hm := (mul_lt_mul_iff_right₀ hπ).mp hμ
  have ht : κ*(d^4*u)^(3/2:ℝ) < d^6*μ := by
    rw [scaled_positive_reaction hd.le hu]
    nlinarith [mul_lt_mul_of_pos_left hm (pow_pos hd 6)]
  have hb := hi.2.1 (d^4*u) hh ht
  have hq : d^4*(ξ/d^4) = ξ := by field_simp
  have hp : 0 < d^4 := pow_pos hd 4
  nlinarith

lemma inverse_low_unscaled {d H μ κ hₗ hₕ ξ C u : ℝ} (hd : 0 < d)
    (hu : 0 ≤ u) (hh : d^4*u ∈ Icc hₗ hₕ)
    (hi : InverseComparisonAt d H μ κ hₗ hₕ ξ C)
    (hμ : 4*Real.pi*μ < reaction κ u) : H ≤ u+ξ/d^4 := by
  have hπ : 0 < 4*Real.pi := by positivity
  have he : reaction κ u = (4*Real.pi)*(κ*u^(3/2:ℝ)) := by
    simp only [reaction,max_eq_left hu]
    ring
  rw [he] at hμ
  have hm := (mul_lt_mul_iff_right₀ hπ).mp hμ
  have ht : d^6*μ < κ*(d^4*u)^(3/2:ℝ) := by
    rw [scaled_positive_reaction hd.le hu]
    nlinarith [mul_lt_mul_of_pos_left hm (pow_pos hd 6)]
  have hb := hi.2.2 (d^4*u) hh ht
  have hq : d^4*(ξ/d^4) = ξ := by field_simp
  have hp : 0 < d^4 := pow_pos hd 4
  nlinarith

lemma dyadic_inverse_four_bound {R d ξ : ℝ} (hR : 0 < R) (hd : R/2 ≤ d)
    (hξ : 0 ≤ ξ) : ξ/d^4 ≤ 16*ξ/R^4 := by
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < R/2) hd
  apply (div_le_div_iff₀ (pow_pos hd0 4) (pow_pos hR 4)).mpr
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ R/2) hd 4
  have he : (R/2)^4 = R^4/16 := by ring
  rw [he] at hp
  nlinarith [mul_le_mul_of_nonneg_left hp hξ]

theorem retained_old_source {R d H μ κ hₗ hₕ ξ C u lam1 lam2 e : ℝ}
    (hR : 0 < R) (hd : R/2 ≤ d) (hξ : 0 ≤ ξ)
    (hu : 0 ≤ u) (hh : d^4*u ∈ Icc hₗ hₕ)
    (hi : InverseComparisonAt d H μ κ hₗ hₕ ξ C)
    (hp : 16*ξ+2*e < lam1-lam2)
    (hr : H-lam2/R^4 < (u-lam1/R^4)+2*e/R^4) :
    4*Real.pi*μ ≤ reaction κ u := by
  by_contra hn
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < R/2) hd
  have hlo := inverse_high_unscaled hd0 hu hh hi (lt_of_not_ge hn)
  have hq := dyadic_inverse_four_bound hR hd hξ
  have hs : (16*ξ+2*e)/R^4 < (lam1-lam2)/R^4 :=
    div_lt_div_of_pos_right hp (pow_pos hR 4)
  simp only [add_div,sub_div,mul_div_assoc] at hs hq hr
  linarith

theorem retained_field_source {R d H μ κ hₗ hₕ ξ C lam2 : ℝ}
    (hR : 0 < R) (hd : R ≤ d) (hξ : 0 ≤ ξ) (hshift : ξ < lam2)
    (hu : 0 ≤ H-lam2/R^4) (hh : d^4*(H-lam2/R^4) ∈ Icc hₗ hₕ)
    (hi : InverseComparisonAt d H μ κ hₗ hₕ ξ C) :
    reaction κ (H-lam2/R^4) ≤ 4*Real.pi*μ := by
  by_contra hn
  have hd0 := hR.trans_le hd
  have hlo := inverse_low_unscaled hd0 hu hh hi (lt_of_not_ge hn)
  have hq : ξ/d^4 ≤ ξ/R^4 := div_le_div_of_nonneg_left hξ
    (pow_pos hR 4) (pow_le_pow_left₀ hR.le hd 4)
  have hs := div_lt_div_of_pos_right hshift (pow_pos hR 4)
  linarith

end Work_BarrierRetainedComparison_barrier_scope

open Set Filter MeasureTheory Laplacian Metric InnerProductSpace
open scoped Topology ContDiff

open CoulombAnalysis CoulombPDE CoulombAtom

lemma classical_weak_lower {U : Set TFSpace} (hU : IsOpen U)
    {u h : TFSpace → ℝ} (hu : Continuous u) (hh : LocallyIntegrable h)
    (hd : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hle : ∀ x ∈ U, h x ≤ Δ u x) :
    WeakLaplacianLowerOn U u h := by
  apply weak_lower_local hu.locallyIntegrable hh
  intro x hx
  obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hU x hx
  let b : ContDiffBump x := ⟨r/2,3*r/4,by positivity,by linarith⟩
  let v : TFSpace → ℝ := fun y => b y*u y
  have hv : ContDiff ℝ 2 v := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact b.contDiffAt.mul (hd y hy)
    · have hyb : y ∉ tsupport b := by
        intro hyb
        have hb : dist y x ≤ 3*r/4 := by
          simpa only [ContDiffBump.tsupport_eq,mem_closedBall] using hyb
        exact hy (hsub (mem_ball.mpr (by linarith)))
      apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hyb] with z hz
      simp only [v,image_eq_zero_of_notMem_tsupport hz,zero_mul]
  have he {y : TFSpace} (hy : y ∈ ball x (r/2)) : v =ᶠ[𝓝 y] u := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    simp only [v,b.one_of_mem_closedBall (ball_subset_closedBall hz),one_mul]
  refine ⟨ball x (r/2),isOpen_ball,mem_ball_self (by positivity),?_⟩
  intro φ hφ hc hs hn
  calc
    _ ≤ ∫ y, Δ v y*φ y := by
      apply integral_mono (locallyIntegrable_mul_test hh hφ.continuous hc)
        (locallyIntegrable_mul_test (tfLaplacian_continuous hv).locallyIntegrable hφ.continuous hc)
      intro y
      dsimp only
      by_cases hy : φ y = 0
      · simp only [hy,mul_zero,le_refl]
      · have hym := hs (subset_tsupport φ hy)
        rw [(laplacian_congr_nhds (he hym)).eq_of_nhds]
        exact mul_le_mul_of_nonneg_right (hle y (hsub (ball_subset_ball (by linarith) hym))) (hn y)
    _ = ∫ y, v y*Δ φ y := (compact_laplacian_green hv hφ hc).symm
    _ = _ := integral_congr_ae (ae_of_all _ fun y => by
      dsimp only
      by_cases hy : Δ φ y = 0
      · simp only [hy,mul_zero]
      · rw [(he (hs (tfLaplacian_support hφ hy))).eq_of_nhds])

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierTowerBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierSourceTower_barrier_scope

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators Topology

open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterKernel masterWidth scaledRealPacket

lemma outerCoefficient_measurable (R : ℝ) : Measurable (outerCoefficient R) :=
  Measurable.ite (measurableSet_le measurable_const continuous_norm.measurable)
    measurable_const measurable_const

lemma outerCoefficient_bound (R : ℝ) (x : TFSpace) : ‖outerCoefficient R x‖ ≤ 1 := by
  unfold outerCoefficient
  split_ifs <;> norm_num

lemma outerCoefficient_nonneg (R : ℝ) (x : TFSpace) : 0 ≤ outerCoefficient R x := by
  unfold outerCoefficient
  split_ifs <;> norm_num

lemma outerCoefficient_zero (R : ℝ) (x : TFSpace) (hx : ‖x‖ < R) :
    outerCoefficient R x = 0 := ite_eq_right (not_le_of_gt hx)

lemma innerSource_measurable {Ω : Type*} [MeasurableSpace Ω]
    {μ p : Ω → TFSpace → ℝ} (hμ : Measurable (Function.uncurry μ))
    (hp : Measurable (Function.uncurry p)) (R : ℝ) :
    Measurable (fun z : Ω × TFSpace => innerSource R (μ z.1) (p z.1) z.2) := by
  exact (Measurable.ite (measurableSet_lt (continuous_norm.measurable.comp measurable_snd)
    measurable_const) hμ measurable_const |>.sub hp).const_mul (4*Real.pi)

lemma innerSource_bound {Ω : Type*} {μ p : Ω → TFSpace → ℝ}
    (hμ : DeterministicLocalBound μ) (hp : DeterministicLocalBound p) (R : ℝ) :
    DeterministicLocalBound (fun sample => innerSource R (μ sample) (p sample)) := by
  intro K hK
  obtain ⟨C,hC⟩ := hμ K hK
  obtain ⟨D,hD⟩ := hp K hK
  refine ⟨|4*Real.pi| *(|C|+|D|),fun sample x hx => ?_⟩
  have hi : ‖if ‖x‖ < R then μ sample x else 0‖ ≤ |C| := by
    split_ifs
    · exact (hC sample x hx).trans (le_abs_self C)
    · simpa only [norm_zero] using abs_nonneg C
  calc
    _ = |4*Real.pi| *‖(if ‖x‖ < R then μ sample x else 0)-p sample x‖ := norm_mul _ _
    _ ≤ |4*Real.pi| *(‖if ‖x‖ < R then μ sample x else 0‖+‖p sample x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add hi ((hD sample x hx).trans (le_abs_self D))) (abs_nonneg _)

lemma conditionalField_innerSource {Ω D : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace D]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → D)
    {μ p : Ω → TFSpace → ℝ} (hμm : Measurable (Function.uncurry μ))
    (hμb : DeterministicLocalBound μ) (hpm : Measurable (Function.uncurry p))
    (hpb : DeterministicLocalBound p) (R : ℝ) (d : D) (x : TFSpace) :
    conditionalField P X (fun sample => innerSource R (μ sample) (p sample)) d x =
      innerSource R (conditionalField P X μ d) (conditionalField P X p d) x := by
  unfold conditionalField innerSource
  rw [integral_const_mul]
  by_cases hx : ‖x‖ < R
  · simp only [ite_eq_left hx]
    rw [integral_sub (deterministicBound_integrable_section hμm hμb x)
      (deterministicBound_integrable_section hpm hpb x)]
  · simp only [ite_eq_right hx,zero_sub,integral_neg]

end Work_BarrierSourceTower_barrier_scope

open Set Filter Laplacian InnerProductSpace
open scoped Topology

open CoulombPDE

lemma radialPower_neg_two (x : Space) : radialPower (-2) x = (‖x‖^4)⁻¹ := by
  unfold radialPower
  rw [Real.rpow_neg (sq_nonneg _),Real.rpow_two]
  congr 1
  ring

lemma radialPower_neg_three (x : Space) : radialPower (-3) x = (‖x‖^6)⁻¹ := by
  unfold radialPower
  rw [Real.rpow_neg (sq_nonneg _),show (3:ℝ) = (3:ℕ) by norm_num,Real.rpow_natCast]
  congr 1
  ring

lemma outerBarrier_eq_combination (B r : ℝ) {x : Space} (hx : x ≠ 0) :
    outerBarrier B r x = radialCombination B (-B*r/8) (1/2) 0 x := by
  rw [radialCombination_factor _ _ _ _ hx,radialPower_half_inv,radialPower_neg_two]
  unfold outerBarrier
  ring

lemma outerBarrier_contDiffAt (B r : ℝ) {x : Space} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (outerBarrier B r) x := by
  apply (radialCombination_contDiffAt B (-B*r/8) (1/2) 0 hx).congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds hx] with y hy
  exact outerBarrier_eq_combination B r hy

lemma outerBarrier_laplacian (B r : ℝ) {x : Space} (hx : x ≠ 0) :
    Δ (outerBarrier B r) x = B/‖x‖^6*(12-20*r/(8*‖x‖)) := by
  have he : outerBarrier B r =ᶠ[𝓝 x] radialCombination B (-B*r/8) (1/2) 0 := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact outerBarrier_eq_combination B r hy
  rw [(laplacian_congr_nhds he).eq_of_nhds,radialCombination_laplacian _ _ _ _ hx,
    radialPower_half_inv,radialPower_neg_three]
  ring

lemma outerBarrier_bounds {B r : ℝ} (hB : 0 ≤ B) (hr : 0 < r)
    {x : Space} (hx : r ≤ ‖x‖) :
    (7*B/8)/‖x‖^4 ≤ outerBarrier B r x ∧ outerBarrier B r x ≤ B/‖x‖^4 := by
  have hd : 0 < ‖x‖ := hr.trans_le hx
  have hq0 : 0 ≤ r/(8*‖x‖) := by positivity
  have hq1 : r/(8*‖x‖) ≤ 1/8 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hb : 0 ≤ B/‖x‖^4 := by positivity
  unfold outerBarrier
  constructor
  · calc
      _ = (B/‖x‖^4)*(7/8) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hb
  · calc
      _ ≤ (B/‖x‖^4)*1 := mul_le_mul_of_nonneg_left (by linarith) hb
      _ = _ := mul_one _

theorem outerBarrier_subsolution {B r k : ℝ} (hB : 0 < B) (hr : 0 < r)
    (hk : 0 ≤ k) (hsmall : 4*Real.pi*k*Real.sqrt B ≤ 19/2)
    {x : Space} (hx : r ≤ ‖x‖) :
    4*Real.pi*k*(max (outerBarrier B r x) 0)^(3/2:ℝ) ≤ Δ (outerBarrier B r) x := by
  have hd : 0 < ‖x‖ := hr.trans_le hx
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp hd.ne'
  obtain ⟨hl,hu⟩ := outerBarrier_bounds hB.le hr hx
  have hn : 0 ≤ outerBarrier B r x := (by positivity : 0 ≤ (7*B/8)/‖x‖^4).trans hl
  have hc : 0 ≤ 4*Real.pi*k := by positivity
  have hreact : (B/‖x‖^4)^(3/2:ℝ) = radialPower (-3) x*B^(3/2:ℝ) := by
    rw [← radial_scaled_reaction hB.le x,radialPower_neg_two]
    congr 1
    ring
  have hq : r/(8*‖x‖) ≤ 1/8 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  calc
    _ ≤ 4*Real.pi*k*(B/‖x‖^4)^(3/2:ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (max_le hu (by positivity)) (by norm_num)) hc
    _ = (4*Real.pi*k*Real.sqrt B)*B/‖x‖^6 := by
      rw [hreact,rpow_three_halves B hB.le,← Real.sqrt_eq_rpow,radialPower_neg_three]
      ring
    _ ≤ (19/2)*B/‖x‖^6 := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsmall hB.le) (by positivity)
    _ ≤ B/‖x‖^6*(12-20*r/(8*‖x‖)) := by
      have hp : 0 ≤ B/‖x‖^6 := by positivity
      have hq' : 20*r/(8*‖x‖) ≤ 5/2 := by
        calc
          _ = 20*(r/(8*‖x‖)) := by ring
          _ ≤ _ := by linarith
      calc
        _ = (B/‖x‖^6)*(19/2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hp
    _ = _ := (outerBarrier_laplacian B r hx0).symm

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierOuterWeakBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierOuterWeak_barrier_scope

open Set Filter MeasureTheory Laplacian Metric InnerProductSpace
open scoped Topology ContDiff

open CoulombAnalysis

lemma clippedOuterBarrier_continuous (B : ℝ) {r : ℝ} (hr : 0 < r) :
    Continuous (clippedOuterBarrier B r) := by
  have hm : Continuous (fun x : TFSpace => max r ‖x‖) := continuous_const.max continuous_norm
  have hn (x : TFSpace) : max r ‖x‖ ≠ 0 := (hr.trans_le (le_max_left _ _)).ne'
  exact (continuous_const.div (hm.pow 4) (fun x => pow_ne_zero _ (hn x))).mul
    (continuous_const.sub (continuous_const.div (continuous_const.mul hm)
      (fun x => mul_ne_zero (by norm_num) (hn x))))

lemma outerOffset_continuous (Z B : ℝ) {r : ℝ} (hr : 0 < r) :
    Continuous (outerOffset Z B r) :=
  (clippedOuterBarrier_continuous B hr).sub (clippedNuclearField_continuous Z hr)

lemma clippedOuterBarrier_eq {B r : ℝ} {x : TFSpace} (hx : r ≤ ‖x‖) :
    clippedOuterBarrier B r x = outerBarrier B r x := by
  simp only [clippedOuterBarrier,outerBarrier,max_eq_right hx]

lemma nuclear_outerOffset_eq {Z B r : ℝ} {x : TFSpace} (hx : r ≤ ‖x‖) :
    nuclearField Z x+outerOffset Z B r x = outerBarrier B r x := by
  simp only [outerOffset,clippedNuclearField,max_eq_right hx,
    clippedOuterBarrier_eq hx,nuclearField]
  ring

lemma WeakNuclearLowerOn.mono_set {U V : Set TFSpace} {Z : ℝ} {u h : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn U Z u h) (hVU : V ⊆ U) :
    WeakNuclearLowerOn V Z u h := fun φ hφ hc hs hn => hw φ hφ hc (hs.trans hVU) hn

lemma weakNuclearLower_iff_off_origin {U : Set TFSpace} (hU : (0 : TFSpace) ∉ U)
    (Z : ℝ) (u h : TFSpace → ℝ) :
    WeakNuclearLowerOn U Z u h ↔ WeakLaplacianLowerOn U u h := by
  have hzero {φ : TFSpace → ℝ} (hs : tsupport φ ⊆ U) : φ 0 = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hx => hU (hs hx))
  constructor
  · intro hw φ hφ hc hs hn
    have hh := hw φ hφ hc hs hn
    simpa only [hzero hs,mul_zero,zero_add] using hh
  · intro hw φ hφ hc hs hn
    simpa only [hzero hs,mul_zero,zero_add] using hw φ hφ hc hs hn

lemma WeakNuclearLowerOn.congr_field {U : Set TFSpace} {Z : ℝ} {u v h : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn U Z u h) (he : ∀ x ∈ U, u x = v x) :
    WeakNuclearLowerOn U Z v h := by
  intro φ hφ hc hs hn
  calc
    _ ≤ ∫ x, u x*Δ φ x := hw φ hφ hc hs hn
    _ = _ := integral_congr_ae (ae_of_all _ fun x => by
      dsimp only
      by_cases hx : Δ φ x = 0
      · simp only [hx,mul_zero]
      · rw [he x (hs (tfLaplacian_support hφ hx))])

lemma WeakNuclearLowerOn.congr_source {U : Set TFSpace} {Z : ℝ} {u h h' : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn U Z u h) (he : ∀ x ∈ U, h x = h' x) :
    WeakNuclearLowerOn U Z u h' := by
  intro φ hφ hc hs hn
  have hh : (∫ x, h' x*φ x) = ∫ x, h x*φ x := by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : φ x = 0
    · simp only [hx,mul_zero]
    · rw [he x (hs (subset_tsupport φ hx))]
  rw [hh]
  exact hw φ hφ hc hs hn

theorem outerOffset_weak_nuclear {B r k : ℝ} (hB : 0 < B) (hr : 0 < r)
    (hk : 0 ≤ k) (hsmall : 4*Real.pi*k*Real.sqrt B ≤ 19/2) (Z : ℝ) :
    WeakNuclearLowerOn {x : TFSpace | r < ‖x‖} Z
      (fun x => nuclearField Z x+outerOffset Z B r x)
      (fun x => reaction k (nuclearField Z x+outerOffset Z B r x)) := by
  have he {x : TFSpace} (hx : r < ‖x‖) :
      clippedOuterBarrier B r =ᶠ[𝓝 x] outerBarrier B r := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact clippedOuterBarrier_eq hy.le
  have hc := clippedOuterBarrier_continuous B hr
  have hw := classical_weak_lower (isOpen_lt continuous_const continuous_norm) hc
    ((reaction_continuous k).comp hc).locallyIntegrable
    (fun x hx => (outerBarrier_contDiffAt B r (norm_ne_zero_iff.mp (hr.trans hx).ne')).congr_of_eventuallyEq (he hx))
    (fun x hx => by
      dsimp only [Function.comp_def]
      rw [clippedOuterBarrier_eq hx.le,(laplacian_congr_nhds (he hx)).eq_of_nhds]
      exact outerBarrier_subsolution hB hr hk hsmall hx.le)
  have hn := (weakNuclearLower_iff_off_origin (Z := Z)
    (u := clippedOuterBarrier B r) (h := fun x => reaction k (clippedOuterBarrier B r x))
    (by change ¬ r < ‖(0:TFSpace)‖; simpa only [norm_zero,not_lt] using hr.le)).mpr hw
  apply (hn.congr_field (fun x hx => (clippedOuterBarrier_eq hx.le).trans (nuclear_outerOffset_eq hx.le).symm)).congr_source
  intro x hx
  rw [clippedOuterBarrier_eq hx.le,nuclear_outerOffset_eq hx.le]

end Work_BarrierOuterWeak_barrier_scope

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology ContDiff

open CoulombAnalysis

lemma nuclear_source_locallyIntegrable (Z k : ℝ) {r : ℝ} (hr : 0 < r)
    {g χ u : TFSpace → ℝ} (hg : LocallyIntegrable g) (hχ : Measurable χ)
    (hbχ : ∀ x, ‖χ x‖ ≤ 1) (hzero : ∀ x, ‖x‖ < r → χ x = 0)
    (hu : Continuous u) :
    LocallyIntegrable (fun x => g x+χ x*reaction k (nuclearField Z x+u x)) := by
  simp_rw [weighted_clipped_reaction Z r hzero]
  exact semilinear_source_locallyIntegrable hg hχ hbχ (reaction_continuous k)
    ((clippedNuclearField_continuous Z hr).add hu)

lemma WeakNuclearLowerOn.source_mono {U : Set TFSpace} {Z : ℝ} {u h h' : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn U Z u h) (hh : LocallyIntegrable h) (hh' : LocallyIntegrable h')
    (hle : ∀ x ∈ U, h' x ≤ h x) : WeakNuclearLowerOn U Z u h' := by
  intro φ hφ hc hs hn
  apply le_trans _ (hw φ hφ hc hs hn)
  apply add_le_add_right
  apply integral_mono (locallyIntegrable_mul_test hh' hφ.continuous hc)
    (locallyIntegrable_mul_test hh hφ.continuous hc)
  intro x
  dsimp only
  by_cases hx : φ x = 0
  · simp only [hx,mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right (hle x (hs (subset_tsupport φ hx))) (hn x)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_Cut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierGluing_barrier_scope
open Set Filter MeasureTheory Laplacian Metric
open scoped Topology ContDiff
open CoulombAnalysis
variable {r t L R : ℝ} {u v : TFSpace → ℝ}
variable (hrt : r < t) (htL : t < L) (hLR : L < R)
variable (hlo : ∀ x, r ≤ ‖x‖ → ‖x‖ < t → v x ≤ u x)
variable (hhi : ∀ x, L < ‖x‖ → ‖x‖ < R → u x ≤ v x)

include htL hLR hlo in
lemma cutMaximum_inner {x : TFSpace} (hx : ‖x‖ < t) : cutMaximum r R u v x = u x := by
  unfold cutMaximum
  split_ifs with h1 h2
  · rfl
  · exact max_eq_left (hlo x (le_of_not_gt h1) hx)
  · exact False.elim (h2 (hx.trans (htL.trans hLR)))

lemma cutMaximum_middle {x : TFSpace} (hx : r < ‖x‖) (hR : ‖x‖ < R) :
    cutMaximum r R u v x = max (u x) (v x) := by
  simp only [cutMaximum,ite_eq_right (not_lt.mpr hx.le),ite_eq_left hR]

include hrt htL hhi in
lemma cutMaximum_outer {x : TFSpace} (hx : L < ‖x‖) : cutMaximum r R u v x = v x := by
  unfold cutMaximum
  rw [ite_eq_right (not_lt.mpr ((hrt.trans htL).trans hx).le)]
  split_ifs with hR
  · exact max_eq_right (hhi x hx hR)
  · rfl

include hrt htL hLR hlo hhi in
lemma cutMaximum_continuous (hu : Continuous u) (hv : Continuous v) :
    Continuous (cutMaximum r R u v) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : ‖x‖ < t
  · apply hu.continuousAt.congr
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact (cutMaximum_inner htL hLR hlo hy).symm
  · by_cases hR : ‖x‖ < R
    · have hx' : r < ‖x‖ := hrt.trans_le (le_of_not_gt hx)
      apply (hu.max hv).continuousAt.congr
      filter_upwards [((isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨hx',hR⟩] with y hy
      exact (cutMaximum_middle hy.1 hy.2).symm
    · have hL : L < ‖x‖ := hLR.trans_le (le_of_not_gt hR)
      apply hv.continuousAt.congr
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hL] with y hy
      exact (cutMaximum_outer hrt htL hhi hy).symm

end Work_BarrierGluing_barrier_scope

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology

open CoulombAnalysis

theorem cutMaximum_weak_nuclear_of_cover {r t L R ρ : ℝ} {u v : TFSpace → ℝ}
    (hrt : r < t) (htL : t < L) (hLR : L < R)
    (hlo : ∀ x, r ≤ ‖x‖ → ‖x‖ < t → v x ≤ u x)
    (hhi : ∀ x, L < ‖x‖ → ‖x‖ < R → u x ≤ v x)
    (Z k : ℝ) (hρ : 0 < ρ) (hu : Continuous u) (hv : Continuous v)
    {g χ : TFSpace → ℝ} (hg : LocallyIntegrable g)
    (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hzero : ∀ x, ‖x‖ < ρ → χ x = 0)
    (hui : WeakNuclearLowerOn {x : TFSpace | ‖x‖ < t} Z (fun x => nuclearField Z x+u x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+u x)))
    (hwm : WeakNuclearLowerOn {x : TFSpace | r < ‖x‖ ∧ ‖x‖ < R} Z
      (fun x => nuclearField Z x+max (u x) (v x))
      (fun x => g x+χ x*reaction k (nuclearField Z x+max (u x) (v x))))
    (hvo : WeakNuclearLowerOn {x : TFSpace | L < ‖x‖} Z (fun x => nuclearField Z x+v x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+v x))) :
    WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+cutMaximum r R u v x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+cutMaximum r R u v x)) := by
  have hc := cutMaximum_continuous hrt htL hLR hlo hhi hu hv
  have hg' := nuclear_source_locallyIntegrable Z k hρ hg hχ hbχ hzero hc
  rw [weakNuclearLower_add_iff Z hc.locallyIntegrable]
  apply weak_lower_local hc.locallyIntegrable hg'
  intro x _
  have transfer {V : Set TFSpace} {w : TFSpace → ℝ}
      (hw : WeakNuclearLowerOn V Z (fun y => nuclearField Z y+w y)
        (fun y => g y+χ y*reaction k (nuclearField Z y+w y)))
      (he : ∀ y ∈ V, w y = cutMaximum r R u v y) :
      WeakLaplacianLowerOn V (cutMaximum r R u v)
        (fun y => g y+χ y*reaction k (nuclearField Z y+cutMaximum r R u v y)) := by
    have hn := hw.congr_field (fun y hy => congrArg (nuclearField Z y+·) (he y hy))
    have hn' := hn.congr_source (fun y hy => by rw [he y hy])
    exact (weakNuclearLower_add_iff Z hc.locallyIntegrable).mp hn'
  by_cases hx : ‖x‖ < t
  · exact ⟨{y | ‖y‖ < t},isOpen_lt continuous_norm continuous_const,hx,
      transfer hui (fun y hy => (cutMaximum_inner htL hLR hlo hy).symm)⟩
  · by_cases hR : ‖x‖ < R
    · have hx' : r < ‖x‖ := hrt.trans_le (le_of_not_gt hx)
      have hopen : IsOpen {y : TFSpace | r < ‖y‖ ∧ ‖y‖ < R} :=
        (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
      exact ⟨{y | r < ‖y‖ ∧ ‖y‖ < R},hopen,⟨hx',hR⟩,
        transfer hwm (fun y hy => (cutMaximum_middle hy.1 hy.2).symm)⟩
    · exact ⟨{y | L < ‖y‖},isOpen_lt continuous_const continuous_norm,hLR.trans_le (le_of_not_gt hR),
        transfer hvo (fun y hy => (cutMaximum_outer hrt htL hhi hy).symm)⟩

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierInitialLipschitzBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierInitialLipschitz_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

open CoulombAtom CoulombAnalysis

lemma locallyLipschitz_comp_contDiffAt {E : Type*} [PseudoMetricSpace E]
    {g : E → ℝ} (hg : LocallyLipschitz g) {f : ℝ → ℝ}
    (hf : ∀ x, ContDiffAt ℝ 1 f (g x)) : LocallyLipschitz (f ∘ g) := by
  intro x
  obtain ⟨Kg,t,ht,hgL⟩ := hg x
  obtain ⟨Kf,u,hu,hfL⟩ := (hf x).exists_lipschitzOnWith
  exact ⟨Kf*Kg,t ∩ g ⁻¹' u,inter_mem ht (hg.continuous.continuousAt hu),
    hfL.comp (hgL.mono inter_subset_left) ((mapsTo_preimage g u).mono_left inter_subset_right)⟩

lemma outerOffset_locallyLipschitz (Z B : ℝ) {r : ℝ} (hr : 0 < r) :
    LocallyLipschitz (outerOffset Z B r) := by
  let f : ℝ → ℝ := fun t => B/t^4*(1-r/(8*t))-Z/t
  have hm : LocallyLipschitz (fun x : TFSpace => max r ‖x‖) :=
    lipschitzWith_one_norm.locallyLipschitz.const_max r
  apply locallyLipschitz_comp_contDiffAt hm (f := f)
  intro x
  have hp : 0 < max r ‖x‖ := hr.trans_le (le_max_left _ _)
  dsimp [f]
  fun_prop (disch := positivity)

end Work_BarrierInitialLipschitz_barrier_scope

open Set Filter MeasureTheory Metric ProbabilityTheory
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma DeterministicLocalLipschitz.locallyLipschitz {Ω : Type*} {u : Ω → TFSpace → ℝ}
    (h : DeterministicLocalLipschitz u) (sample : Ω) : LocallyLipschitz (u sample) := by
  intro x
  obtain ⟨K,t,ht,hL⟩ := h x
  exact ⟨K,t,ht,hL sample⟩

lemma deterministicLip_spatial {Ω : Type*} {u : TFSpace → ℝ} (h : LocallyLipschitz u) :
    DeterministicLocalLipschitz (fun _ : Ω => u) := by
  intro x
  obtain ⟨K,t,ht,hL⟩ := h x
  exact ⟨K,t,ht,fun _ => hL⟩

lemma DeterministicLocalLipschitz.neg {Ω : Type*} {u : Ω → TFSpace → ℝ}
    (h : DeterministicLocalLipschitz u) : DeterministicLocalLipschitz (fun sample x => -u sample x) := by
  intro x
  obtain ⟨K,t,ht,hL⟩ := h x
  exact ⟨K,t,ht,fun sample => (hL sample).neg⟩

lemma DeterministicLocalLipschitz.add {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalLipschitz u) (hv : DeterministicLocalLipschitz v) :
    DeterministicLocalLipschitz (fun sample x => u sample x+v sample x) := by
  intro x
  obtain ⟨Ku,t,ht,hLu⟩ := hu x
  obtain ⟨Kv,s,hs,hLv⟩ := hv x
  refine ⟨Ku+Kv,t ∩ s,inter_mem ht hs,fun sample => ?_⟩
  exact ((hLu sample).mono inter_subset_left).add ((hLv sample).mono inter_subset_right)

lemma DeterministicLocalLipschitz.sub {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalLipschitz u) (hv : DeterministicLocalLipschitz v) :
    DeterministicLocalLipschitz (fun sample x => u sample x-v sample x) := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

lemma DeterministicLocalLipschitz.max {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalLipschitz u) (hv : DeterministicLocalLipschitz v) :
    DeterministicLocalLipschitz (fun sample x => max (u sample x) (v sample x)) := by
  intro x
  obtain ⟨Ku,t,ht,hLu⟩ := hu x
  obtain ⟨Kv,s,hs,hLv⟩ := hv x
  refine ⟨Max.max Ku Kv,t ∩ s,inter_mem ht hs,fun sample => ?_⟩
  exact lipschitzOnWith_iff_restrict.mpr
    (((hLu sample).mono inter_subset_left).to_restrict.max ((hLv sample).mono inter_subset_right).to_restrict)

lemma deterministicLip_local_congr {Ω : Type*} {u v : Ω → TFSpace → ℝ} {x : TFSpace}
    (hu : ∃ K : NNReal, ∃ t ∈ 𝓝 x, ∀ sample, LipschitzOnWith K (u sample) t)
    (he : ∀ᶠ y in 𝓝 x, ∀ sample, u sample y = v sample y) :
    ∃ K : NNReal, ∃ t ∈ 𝓝 x, ∀ sample, LipschitzOnWith K (v sample) t := by
  obtain ⟨K,t,ht,hL⟩ := hu
  refine ⟨K,t ∩ {y | ∀ sample, u sample y = v sample y},inter_mem ht he,fun sample y hy z hz => ?_⟩
  change edist (v sample y) (v sample z) ≤ _
  rw [←hy.2 sample,←hz.2 sample]
  exact hL sample hy.1 hz.1

lemma cutMaximum_deterministicLip {Ω : Type*} {u v : Ω → TFSpace → ℝ} {r t L R : ℝ}
    (hrt : r < t) (htL : t < L) (hLR : L < R)
    (hlo : ∀ sample x, r ≤ ‖x‖ → ‖x‖ < t → v sample x ≤ u sample x)
    (hhi : ∀ sample x, L < ‖x‖ → ‖x‖ < R → u sample x ≤ v sample x)
    (hu : DeterministicLocalLipschitz u) (hv : DeterministicLocalLipschitz v) :
    DeterministicLocalLipschitz (fun sample => cutMaximum r R (u sample) (v sample)) := by
  intro x
  by_cases hx : ‖x‖ < t
  · apply deterministicLip_local_congr (hu x)
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact fun sample => (cutMaximum_inner htL hLR (hlo sample) hy).symm
  · by_cases hR : ‖x‖ < R
    · have hx' : r < ‖x‖ := hrt.trans_le (le_of_not_gt hx)
      apply deterministicLip_local_congr (hu.max hv x)
      filter_upwards [((isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨hx',hR⟩] with y hy
      exact fun sample => (cutMaximum_middle hy.1 hy.2).symm
    · have hL : L < ‖x‖ := hLR.trans_le (le_of_not_gt hR)
      apply deterministicLip_local_congr (hv x)
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hL] with y hy
      exact fun sample => (cutMaximum_outer hrt htL (hhi sample) hy).symm

lemma conditionalField_deterministicLip {Ω D : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace D]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → D)
    {u : Ω → TFSpace → ℝ} (hm : Measurable (Function.uncurry u))
    (hb : DeterministicLocalBound u) (hL : DeterministicLocalLipschitz u) :
    DeterministicLocalLipschitz (conditionalField P X u) := by
  intro x
  obtain ⟨K,t,ht,hKt⟩ := hL x
  refine ⟨K,t,ht,fun d => ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro y hy z hz
  change dist (∫ sample, u sample y ∂condDistrib id X P d) (∫ sample, u sample z ∂condDistrib id X P d) ≤ _
  rw [dist_eq_norm,←integral_sub (deterministicBound_integrable_section hm hb y)
    (deterministicBound_integrable_section hm hb z)]
  calc
    _ ≤ ∫ _ : Ω, (K:ℝ)*dist y z ∂condDistrib id X P d :=
      norm_integral_le_of_norm_le (integrable_const _)
        (Eventually.of_forall fun sample => by
          simpa only [dist_eq_norm] using (hKt sample).dist_le_mul y hy z hz)
    _ = (K:ℝ)*dist y z := by simp

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierForgottenInvariantBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Metric ProbabilityTheory
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma DeterministicLocalBound.comp {Ω D : Type*} {u : D → TFSpace → ℝ}
    (hu : DeterministicLocalBound u) (X : Ω → D) : DeterministicLocalBound (fun sample => u (X sample)) := by
  intro K hK
  obtain ⟨C,hC⟩ := hu K hK
  exact ⟨C,fun sample x hx => hC (X sample) x hx⟩

lemma DeterministicLocalLipschitz.comp {Ω D : Type*} {u : D → TFSpace → ℝ}
    (hu : DeterministicLocalLipschitz u) (X : Ω → D) : DeterministicLocalLipschitz (fun sample => u (X sample)) := by
  intro x
  obtain ⟨K,s,hs,hK⟩ := hu x
  exact ⟨K,s,hs,fun sample => hK (X sample)⟩

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierStepBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Metric Laplacian InnerProductSpace
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma addedError_nonneg (good : Prop) [Decidable good] {R : ℝ} {μ p : TFSpace → ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (hp : ∀ x, 0 ≤ p x) (x : TFSpace) :
    0 ≤ addedError good R μ p x := by
  unfold addedError
  split_ifs <;> linarith [hμ x,hp x]

lemma addedError_le (good : Prop) [Decidable good] {R M L : ℝ} {μ p : TFSpace → ℝ}
    (hM : 0 ≤ M) (hμ : ∀ x, μ x ≤ M) (hp : ∀ x, p x ≤ L) (x : TFSpace) :
    addedError good R μ p x ≤ L+M := by
  unfold addedError
  split_ifs <;> linarith [hμ x,hp x]

lemma addedError_support (good : Prop) [Decidable good] {R : ℝ} (hR : 0 ≤ R)
    {μ p : TFSpace → ℝ} (hp : ∀ x, R/2 < ‖x‖ → p x = 0) {x : TFSpace} (hx : R < ‖x‖) :
    addedError good R μ p x = 0 := by
  simp only [addedError,hp x (by linarith),not_lt_of_ge hx.le,and_false,ite_false,ite_self,add_zero]

lemma addedError_measurable {Ω : Type*} [MeasurableSpace Ω] (good : Ω → Prop) [DecidablePred good]
    (hg : MeasurableSet {sample | good sample}) {μ p : Ω → TFSpace → ℝ}
    (hμ : Measurable (Function.uncurry μ)) (hp : Measurable (Function.uncurry p)) (R : ℝ) :
    Measurable (fun z : Ω × TFSpace => addedError (good z.1) R (μ z.1) (p z.1) z.2) := by
  exact hp.add (Measurable.ite (measurable_fst hg) measurable_const
    (Measurable.ite ((measurableSet_le measurable_const (continuous_norm.measurable.comp measurable_snd)).inter
      (measurableSet_lt (continuous_norm.measurable.comp measurable_snd) measurable_const)) hμ measurable_const))

lemma WeakNuclearLowerOn.sub_const {U : Set TFSpace} {Z : ℝ} {u h : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn U Z u h) (hu : LocallyIntegrable u) (c : ℝ) :
    WeakNuclearLowerOn U Z (fun x => u x-c) h := by
  intro φ hφ hc hs hn
  have he := compact_laplacian_green (f := fun _ : TFSpace => c) contDiff_const hφ hc
  simp only [laplacian_const,Pi.zero_apply,zero_mul,integral_zero] at he
  have hic : Integrable (fun x : TFSpace => c*Δ φ x) :=
    (continuous_const.mul (tfLaplacian_continuous hφ)).integrable_of_hasCompactSupport
      (tfLaplacian_compact hφ hc).mul_left
  simp_rw [sub_mul]
  rw [integral_sub (locallyIntegrable_mul_test hu (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc))
    hic,he,sub_zero]
  exact hw φ hφ hc hs hn

lemma outward_old_source (good : Prop) [Decidable good] {R κ lam1 lam2 e ξ C hl hh : ℝ}
    (hR : 0 < R) (hκ : 0 ≤ κ) (hlam : 0 ≤ lam1) (hξ : 0 ≤ ξ)
    (hgap : 16*ξ+2*e < lam1-lam2) {μ p u H w : TFSpace → ℝ}
    (hinv : good → ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < R →
      InverseComparisonAt ‖x‖ (H x) (μ x) κ hl hh ξ C)
    {x : TFSpace}
    (hheight : R/2 ≤ ‖x‖ → ‖x‖ < R → 0 ≤ u x ∧ ‖x‖^4*u x ∈ Icc hl hh)
    (hcand : good → H x-lam2/R^4 ≤ w x)
    (hnear : w x-(u x-lam1/R^4) < 2*e/R^4) :
    innerSource R μ (addedError good R μ p) x+outerCoefficient R x*reaction κ (u x-lam1/R^4) ≤
      innerSource (R/2) μ p x+outerCoefficient (R/2) x*reaction κ (u x) := by
  have hp : ‖x‖ < R/2 → ‖x‖ < R := fun hx => by linarith
  have hreact := reaction_nonneg hκ (u x)
  by_cases hx0 : ‖x‖ < R/2
  · simp [innerSource,outerCoefficient,addedError,hx0,hp hx0,not_le_of_gt hx0,not_le_of_gt (hp hx0),ite_self]
  · have hx0' := le_of_not_gt hx0
    by_cases hx1 : ‖x‖ < R
    · by_cases hg : good
      · obtain ⟨hu,hh'⟩ := hheight hx0' hx1
        have hsrc := retained_old_source hR hx0' hξ hu hh' (hinv hg x hx0' hx1) hgap
          (by linarith [hcand hg])
        simp only [innerSource,outerCoefficient,addedError,ite_eq_left hg,add_zero,ite_eq_left hx1,
          ite_eq_right hx0,ite_eq_left hx0',ite_eq_right (not_le_of_gt hx1),zero_mul,one_mul,zero_sub,add_zero]
        linarith
      · simp only [innerSource,outerCoefficient,addedError,ite_eq_right hg,ite_eq_left (show R/2 ≤ ‖x‖ ∧ ‖x‖ < R from ⟨hx0',hx1⟩),
          ite_eq_left hx1,ite_eq_right hx0,ite_eq_left hx0',ite_eq_right (not_le_of_gt hx1),zero_mul,one_mul,
          zero_sub,add_zero]
        linarith
    · have hm := reaction_monotone hκ (show u x-lam1/R^4 ≤ u x by
        have hpos : 0 ≤ lam1/R^4 := by positivity
        linarith)
      simp only [innerSource,outerCoefficient,addedError,ite_eq_right hx1,ite_eq_right hx0,ite_eq_left hx0',
        ite_eq_left (le_of_not_gt hx1),ite_eq_right (show ¬(R/2 ≤ ‖x‖ ∧ ‖x‖ < R) from fun h => hx1 h.2),
        ite_self,add_zero,zero_sub,one_mul]
      linarith

lemma outward_field_source (good : Prop) [Decidable good] {R κ lam2 ξ C hl hh : ℝ}
    (hR : 0 < R) (hξ : 0 ≤ ξ) (hshift : ξ < lam2) {μ p H : TFSpace → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hμ : ∀ x, 0 ≤ μ x) {x : TFSpace}
    (hinv : R ≤ ‖x‖ → InverseComparisonAt ‖x‖ (H x) (μ x) κ hl hh ξ C)
    (hheight : R ≤ ‖x‖ → 0 ≤ H x-lam2/R^4 ∧ ‖x‖^4*(H x-lam2/R^4) ∈ Icc hl hh) :
    innerSource R μ (addedError good R μ p) x+outerCoefficient R x*reaction κ (H x-lam2/R^4) ≤
      4*Real.pi*μ x := by
  have hp' := addedError_nonneg (R := R) good hμ hp x
  have hπ : 0 < 4*Real.pi := by positivity
  by_cases hx : ‖x‖ < R
  · simp only [innerSource,outerCoefficient,ite_eq_left hx,ite_eq_right (not_le_of_gt hx),zero_mul,add_zero]
    nlinarith
  · have hx' := le_of_not_gt hx
    obtain ⟨hv,hh'⟩ := hheight hx'
    have hm := retained_field_source hR hx' hξ hshift hv hh' (hinv hx')
    simp only [innerSource,outerCoefficient,ite_eq_right hx,ite_eq_left hx',one_mul,zero_sub]
    nlinarith

lemma retained_field_height {B C R M e hl hh H v w d lam : ℝ}
    (hB : 0 < B) (hR : 0 < R) (he : 0 < e)
    (hd : R ≤ d) (hd' : d ≤ 2*M*R) (hhl : hl < B/4) (hhh : C < hh)
    (hsmall : 2*e*(2*M)^4 < B/4) (hlam : 0 ≤ lam)
    (hv : v = H-lam/R^4) (hlo : (7*B/8)/d^4 ≤ w)
    (hhi : d^4*H ≤ C) (hnear : w-v < 2*e/R^4) :
    0 ≤ v ∧ d^4*v ∈ Icc hl hh := by
  have hd0 := hR.trans_le hd
  have hd4 : 0 < d^4 := pow_pos hd0 4
  have hR4 : 0 < R^4 := pow_pos hR 4
  have hlo' : 7*B/8 ≤ d^4*w := by
    have h := (div_le_iff₀ hd4).mp hlo
    nlinarith
  have hnear' := mul_lt_mul_of_pos_left hnear hd4
  have hpower := pow_le_pow_left₀ hd0.le hd' 4
  rw [mul_pow] at hpower
  have hratio : d^4/R^4 ≤ (2*M)^4 := (div_le_iff₀ hR4).mpr hpower
  have hscale := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 2*e)
  have hbound : hl < d^4*v := by
    have heq : d^4*(2*e/R^4) = 2*e*(d^4/R^4) := by ring
    rw [heq] at hnear'
    nlinarith
  have hvpos : 0 < v := by
    by_contra hn
    have hvn := le_of_not_gt hn
    have hprod := mul_nonpos_of_nonneg_of_nonpos hd4.le hvn
    have heq : d^4*(2*e/R^4) = 2*e*(d^4/R^4) := by ring
    rw [heq] at hnear'
    nlinarith
  refine ⟨hvpos.le,hbound.le,?_⟩
  have hsub : 0 ≤ d^4*(lam/R^4) := by positivity
  rw [hv]
  nlinarith

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_BarrierInitialDeterministicBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma potential_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Ω → TFSpace → ℝ} (hm : Measurable (Function.uncurry ρ)) :
    Measurable (fun p : Ω × TFSpace => tfPotential (ρ p.1) p.2) := by
  have h : Measurable (fun p : (Ω × TFSpace) × TFSpace => ρ p.1.1 p.2/‖p.1.2-p.2‖) :=
    (hm.comp (measurable_fst.fst.prodMk measurable_snd)).div
      (measurable_fst.snd.sub measurable_snd).norm
  exact h.stronglyMeasurable.integral_prod_right.measurable

lemma continuous_deterministicBound {Ω : Type*} {u : TFSpace → ℝ}
    (hu : Continuous u) : DeterministicLocalBound (fun _ : Ω => u) := by
  intro K hK
  obtain ⟨C,_,hC⟩ := (hK.image hu).isBounded.exists_pos_norm_lt
  exact ⟨C,fun _ x hx => (hC (u x) (mem_image_of_mem u hx)).le⟩

lemma cutMaximum_deterministicBound {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalBound u) (hv : DeterministicLocalBound v) (r R : ℝ) :
    DeterministicLocalBound (fun sample => cutMaximum r R (u sample) (v sample)) := by
  intro K hK
  obtain ⟨C,hC⟩ := hu K hK
  obtain ⟨D,hD⟩ := hv K hK
  refine ⟨max C D,fun sample x hx => ?_⟩
  have hu' := (hC sample x hx).trans (le_max_left C D)
  have hv' := (hD sample x hx).trans (le_max_right C D)
  change ‖if ‖x‖ < r then u sample x else if ‖x‖ < R then max (u sample x) (v sample x) else v sample x‖ ≤ _
  split_ifs
  · exact hu'
  · rcases le_total (u sample x) (v sample x) with hh|hh
    · simpa only [max_eq_right hh] using hv'
    · simpa only [max_eq_left hh] using hu'
  · exact hv'

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierStepGeometryBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma outerBarrier_dyadic_difference (B R : ℝ) {x : TFSpace} (hx : ‖x‖ ≠ 0) :
    outerBarrier B (R/2) x-outerBarrier B R x = B*R/(16*‖x‖^5) := by
  unfold outerBarrier
  field_simp
  ring

lemma outerBarrier_dyadic_gap {B R : ℝ} (hB : 0 ≤ B) (hR : 0 < R)
    {x : TFSpace} (hx : R ≤ ‖x‖) (hx' : ‖x‖ ≤ (11/10)*R) :
    barrierGap B/R^4 ≤ outerBarrier B (R/2) x-outerBarrier B R x := by
  have hd := hR.trans_le hx
  rw [outerBarrier_dyadic_difference B R hd.ne']
  calc
    barrierGap B/R^4 = B*R/(16*((11/10)*R)^5) := by
      unfold barrierGap
      field_simp
    _ ≤ B*R/(16*‖x‖^5) := div_le_div_of_nonneg_left (by positivity)
      (by positivity) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx' 5) (by norm_num))

lemma shifted_old_above_new_barrier {B R lam : ℝ} (hB : 0 ≤ B) (hR : 0 < R)
    (hlam : lam < barrierGap B) {u : TFSpace → ℝ} {x : TFSpace}
    (hx : R ≤ ‖x‖) (hx' : ‖x‖ ≤ (11/10)*R)
    (hu : outerBarrier B (R/2) x ≤ u x) :
    outerBarrier B R x < u x-lam/R^4 := by
  have hg := outerBarrier_dyadic_gap hB hR hx hx'
  have hl := div_lt_div_of_pos_right hlam (pow_pos hR 4)
  linarith

lemma cap_dominated_by_shift {C M R lam d : ℝ} (hC : 0 ≤ C) (hM : 0 < M)
    (hR : 0 < R) (hshift : C/M^4 < lam) (hd : M*R < d) : C/d^4 < lam/R^4 := by
  have hMR : 0 < M*R := mul_pos hM hR
  calc
    C/d^4 ≤ C/(M*R)^4 := div_le_div_of_nonneg_left hC (pow_pos hMR 4)
      (pow_le_pow_left₀ hMR.le hd.le 4)
    _ = (C/M^4)/R^4 := by rw [mul_pow,div_mul_eq_div_div]
    _ < lam/R^4 := div_lt_div_of_pos_right hshift (pow_pos hR 4)

lemma shiftedCandidates_old_le (good : Prop) [Decidable good] (a h : TFSpace → ℝ)
    (R lam1 lam2 : ℝ) (x : TFSpace) :
    a x-lam1/R^4 ≤ shiftedCandidates good a h R lam1 lam2 x := by
  unfold shiftedCandidates
  split_ifs
  · exact le_max_left _ _
  · exact le_refl _

lemma shiftedCandidates_continuous (good : Prop) [Decidable good]
    {a h : TFSpace → ℝ} (ha : Continuous a) (hh : Continuous h) (R lam1 lam2 : ℝ) :
    Continuous (shiftedCandidates good a h R lam1 lam2) := by
  unfold shiftedCandidates
  split_ifs
  · exact (ha.sub continuous_const).max (hh.sub continuous_const)
  · exact ha.sub continuous_const

lemma outward_lower_overlap (good : Prop) [Decidable good] {a h : TFSpace → ℝ}
    {Z B R lam1 lam2 : ℝ} (hB : 0 ≤ B) (hR : 0 < R) (hshift : lam1 < barrierGap B)
    (hu : ∀ x, R/2 ≤ ‖x‖ → outerBarrier B (R/2) x ≤ nuclearField Z x+a x)
    {x : TFSpace} (hx : R ≤ ‖x‖) (hx' : ‖x‖ < (27/25)*R) :
    outerOffset Z B R x ≤ shiftedCandidates good a h R lam1 lam2 x := by
  have hgap := shifted_old_above_new_barrier (u := fun y => nuclearField Z y+a y) hB hR hshift hx (by linarith)
    (hu x (by linarith : R/2 ≤ ‖x‖))
  rw [←nuclear_outerOffset_eq (Z := Z) hx] at hgap
  have hc := shiftedCandidates_old_le good a h R lam1 lam2 x
  linarith

lemma outward_upper_overlap (good : Prop) [Decidable good] {a h : TFSpace → ℝ}
    {Z B C R M lam1 lam2 : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hR : 0 < R) (hM : 2 < M) (hshifts : lam2 ≤ lam1) (hshift : C/M^4 < lam2)
    (hu : ∀ x, R/2 ≤ ‖x‖ → nuclearField Z x+a x ≤ C/‖x‖^4)
    (hh : good → ∀ x, M*R < ‖x‖ → ‖x‖ < 2*M*R → nuclearField Z x+h x ≤ C/‖x‖^4)
    {x : TFSpace} (hx : M*R < ‖x‖) (hx' : ‖x‖ < 2*M*R) :
    shiftedCandidates good a h R lam1 lam2 x ≤ outerOffset Z B R x := by
  have hxR : R ≤ ‖x‖ := by nlinarith
  have hs := cap_dominated_by_shift hC (by linarith : 0 < M) hR hshift hx
  have hb := (outerBarrier_bounds hB hR hxR).1
  have hb0 : 0 ≤ (7*B/8)/‖x‖^4 := by positivity
  rw [←nuclear_outerOffset_eq (Z := Z) hxR] at hb
  have ha := hu x (by linarith)
  have hl := div_le_div_of_nonneg_right hshifts (pow_nonneg hR.le 4)
  unfold shiftedCandidates
  split_ifs with hg
  · apply max_le
    · linarith
    · have hh' := hh hg x hx hx'; linarith
  · linarith

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma DeterministicLocalLipschitz.ite {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalLipschitz u) (hv : DeterministicLocalLipschitz v)
    (q : Ω → Prop) [DecidablePred q] :
    DeterministicLocalLipschitz (fun sample x => if q sample then u sample x else v sample x) := by
  intro x
  obtain ⟨Ku,t,ht,hLu⟩ := hu x
  obtain ⟨Kv,s,hs,hLv⟩ := hv x
  refine ⟨Max.max Ku Kv,t ∩ s,inter_mem ht hs,fun sample => ?_⟩
  by_cases hq : q sample
  · simpa only [ite_eq_left hq] using ((hLu sample).mono inter_subset_left).weaken (le_max_left _ _)
  · simpa only [ite_eq_right hq] using ((hLv sample).mono inter_subset_right).weaken (le_max_right _ _)

lemma DeterministicLocalBound.ite {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalBound u) (hv : DeterministicLocalBound v)
    (q : Ω → Prop) [DecidablePred q] :
    DeterministicLocalBound (fun sample x => if q sample then u sample x else v sample x) := by
  intro K hK
  obtain ⟨C,hC⟩ := hu K hK
  obtain ⟨D,hD⟩ := hv K hK
  refine ⟨max C D,fun sample x hx => ?_⟩
  dsimp only
  split_ifs
  · exact (hC sample x hx).trans (le_max_left _ _)
  · exact (hD sample x hx).trans (le_max_right _ _)

lemma DeterministicLocalBound.max {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalBound u) (hv : DeterministicLocalBound v) :
    DeterministicLocalBound (fun sample x => max (u sample x) (v sample x)) := by
  intro K hK
  obtain ⟨C,hC⟩ := hu K hK
  obtain ⟨D,hD⟩ := hv K hK
  refine ⟨Max.max C D,fun sample x hx => ?_⟩
  rcases le_total (u sample x) (v sample x) with h|h
  · simpa only [max_eq_right h] using (hD sample x hx).trans (le_max_right C D)
  · simpa only [max_eq_left h] using (hC sample x hx).trans (le_max_left C D)

lemma shiftedCandidates_deterministicLip {Ω : Type*} (good : Ω → Prop) [DecidablePred good]
    {a h : Ω → TFSpace → ℝ} (ha : DeterministicLocalLipschitz a)
    (hh : DeterministicLocalLipschitz h) (R lam1 lam2 : ℝ) :
    DeterministicLocalLipschitz (fun sample => shiftedCandidates (good sample) (a sample) (h sample) R lam1 lam2) := by
  have h1 := ha.sub (deterministicLip_spatial (LocallyLipschitz.const (lam1/R^4)))
  have h2 := hh.sub (deterministicLip_spatial (LocallyLipschitz.const (lam2/R^4)))
  exact (h1.max h2).ite h1 good

lemma shiftedCandidates_deterministicBound {Ω : Type*} (good : Ω → Prop) [DecidablePred good]
    {a h : Ω → TFSpace → ℝ} (ha : DeterministicLocalBound a)
    (hh : DeterministicLocalBound h) (R lam1 lam2 : ℝ) :
    DeterministicLocalBound (fun sample => shiftedCandidates (good sample) (a sample) (h sample) R lam1 lam2) := by
  have h1 : DeterministicLocalBound (fun sample x => a sample x-lam1/R^4) := by
    simpa only [sub_eq_add_neg] using
      ha.add (continuous_deterministicBound (u := fun _ => -(lam1/R^4)) continuous_const)
  have h2 : DeterministicLocalBound (fun sample x => h sample x-lam2/R^4) := by
    simpa only [sub_eq_add_neg] using
      hh.add (continuous_deterministicBound (u := fun _ => -(lam2/R^4)) continuous_const)
  exact (h1.max h2).ite h1 good

lemma shiftedCandidates_measurable {Ω : Type*} [MeasurableSpace Ω]
    (good : Ω → Prop) [DecidablePred good] (hg : MeasurableSet {sample | good sample})
    {a h : Ω → TFSpace → ℝ} (ha : Measurable (Function.uncurry a))
    (hh : Measurable (Function.uncurry h)) (R lam1 lam2 : ℝ) :
    Measurable (fun z : Ω × TFSpace => shiftedCandidates (good z.1) (a z.1) (h z.1) R lam1 lam2 z.2) :=
  Measurable.ite (measurable_fst hg) ((ha.sub measurable_const).max (hh.sub measurable_const))
    (ha.sub measurable_const)

lemma outwardOffset_measurable {Ω : Type*} [MeasurableSpace Ω]
    (good : Ω → Prop) [DecidablePred good] (hg : MeasurableSet {sample | good sample})
    {a h : Ω → TFSpace → ℝ} (ha : Measurable (Function.uncurry a))
    (hh : Measurable (Function.uncurry h)) (Z B M lam1 lam2 : ℝ) {R : ℝ} (hR : 0 < R) :
    Measurable (fun z : Ω × TFSpace => outwardOffset (good z.1) (a z.1) (h z.1) Z B R M lam1 lam2 z.2) := by
  have hc := shiftedCandidates_measurable good hg ha hh R lam1 lam2
  have hb : Measurable (fun z : Ω × TFSpace => outerOffset Z B R z.2) :=
    (outerOffset_continuous Z B hR).measurable.comp measurable_snd
  exact Measurable.ite (measurableSet_lt (continuous_norm.measurable.comp measurable_snd) measurable_const)
    hc (Measurable.ite (measurableSet_lt (continuous_norm.measurable.comp measurable_snd) measurable_const)
      (hc.max hb) hb)

lemma outwardOffset_deterministicBound {Ω : Type*} (good : Ω → Prop) [DecidablePred good]
    {a h : Ω → TFSpace → ℝ} (ha : DeterministicLocalBound a)
    (hh : DeterministicLocalBound h) (Z B M lam1 lam2 : ℝ) {R : ℝ} (hR : 0 < R) :
    DeterministicLocalBound (fun sample => outwardOffset (good sample) (a sample) (h sample) Z B R M lam1 lam2) :=
  cutMaximum_deterministicBound (shiftedCandidates_deterministicBound good ha hh R lam1 lam2)
    (continuous_deterministicBound (outerOffset_continuous Z B hR)) _ _

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierStepBounds_barrier_scope
open Set Filter MeasureTheory Metric
open scoped Topology
open CoulombAtom CoulombAnalysis
variable {Z B C R M lam1 lam2 : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
  (hR : 0 < R) (hM : 2 < M) (hshifts : lam2 ≤ lam1)
  (hshift : C/M^4 < lam2) (hsmall : lam1 < barrierGap B)

include hB hC hR hM hshifts hshift hsmall in
lemma outwardOffset_deterministicLip {Ω : Type*} (good : Ω → Prop) [DecidablePred good]
    {a h : Ω → TFSpace → ℝ} (ha : DeterministicLocalLipschitz a)
    (hh : DeterministicLocalLipschitz h)
    (hlo : ∀ sample x, R/2 ≤ ‖x‖ → outerBarrier B (R/2) x ≤ nuclearField Z x+a sample x)
    (hhi : ∀ sample x, R/2 ≤ ‖x‖ → nuclearField Z x+a sample x ≤ C/‖x‖^4)
    (hhcap : ∀ sample, good sample → ∀ x, M*R < ‖x‖ → ‖x‖ < 2*M*R → nuclearField Z x+h sample x ≤ C/‖x‖^4) :
    DeterministicLocalLipschitz (fun sample => outwardOffset (good sample) (a sample) (h sample) Z B R M lam1 lam2) := by
  apply cutMaximum_deterministicLip (t := (27/25)*R) (L := M*R)
    (by linarith) (by nlinarith) (by nlinarith)
  · intro sample x hx hx'
    exact outward_lower_overlap (good sample) hB hR hsmall (hlo sample) (by linarith) hx'
  · exact fun sample x hx hx' => outward_upper_overlap (good sample) hB hC hR hM hshifts hshift
      (hhi sample) (hhcap sample) hx hx'
  · exact shiftedCandidates_deterministicLip good ha hh R lam1 lam2
  · exact deterministicLip_spatial (outerOffset_locallyLipschitz Z B hR)

include hB hR hsmall in
lemma outwardOffset_lower (good : Prop) [Decidable good] {a h : TFSpace → ℝ}
    (hlo : ∀ x, R/2 ≤ ‖x‖ → outerBarrier B (R/2) x ≤ nuclearField Z x+a x)
    {x : TFSpace} (hx : R ≤ ‖x‖) :
    outerBarrier B R x ≤ nuclearField Z x+outwardOffset good a h Z B R M lam1 lam2 x := by
  rw [←nuclear_outerOffset_eq (Z := Z) hx]
  apply add_le_add_right
  unfold outwardOffset cutMaximum
  split_ifs with h1 h2
  · exact outward_lower_overlap good hB hR hsmall hlo hx (by linarith)
  · exact le_max_right _ _
  · exact le_refl _

include hB hR hM hshifts in
lemma outwardOffset_cap (good : Prop) [Decidable good] {a h : TFSpace → ℝ}
    (hBC : B ≤ C) (hl2 : 0 ≤ lam2)
    (hhi : ∀ x, R/2 ≤ ‖x‖ → nuclearField Z x+a x ≤ C/‖x‖^4)
    (hhcap : good → ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < 2*M*R → nuclearField Z x+h x ≤ C/‖x‖^4)
    {x : TFSpace} (hx : R ≤ ‖x‖) :
    nuclearField Z x+outwardOffset good a h Z B R M lam1 lam2 x ≤ C/‖x‖^4 := by
  have hb : nuclearField Z x+outerOffset Z B R x ≤ C/‖x‖^4 := by
    rw [nuclear_outerOffset_eq hx]
    exact (outerBarrier_bounds hB hR hx).2.trans
      (div_le_div_of_nonneg_right hBC (pow_nonneg (norm_nonneg _) 4))
  have hv (hx' : ‖x‖ < 2*M*R) :
      nuclearField Z x+shiftedCandidates good a h R lam1 lam2 x ≤ C/‖x‖^4 := by
    have h1 := hhi x (by linarith)
    have hl1 : 0 ≤ lam1/R^4 := div_nonneg (hl2.trans hshifts) (pow_nonneg hR.le _)
    have hl2' : 0 ≤ lam2/R^4 := div_nonneg hl2 (pow_nonneg hR.le _)
    unfold shiftedCandidates
    split_ifs with hg
    · rw [add_max]
      apply max_le
      · linarith
      · have ht := hhcap hg x (by linarith) hx'; linarith
    · linarith
  unfold outwardOffset cutMaximum
  split_ifs with h1 h2
  · exact hv (by nlinarith)
  · rw [add_max]; exact max_le (hv h2) hb
  · exact hb

include hB hC hR hM hshifts hshift in
lemma outwardOffset_tail (good : Prop) [Decidable good] {a h : TFSpace → ℝ}
    (hhi : ∀ x, R/2 ≤ ‖x‖ → nuclearField Z x+a x ≤ C/‖x‖^4)
    (hhcap : good → ∀ x, M*R < ‖x‖ → ‖x‖ < 2*M*R → nuclearField Z x+h x ≤ C/‖x‖^4)
    {x : TFSpace} (hx : M*R < ‖x‖) :
    nuclearField Z x+outwardOffset good a h Z B R M lam1 lam2 x = outerBarrier B R x := by
  have he := cutMaximum_outer (r := (26/25)*R) (t := (27/25)*R)
    (R := 2*M*R) (L := M*R) (by linarith) (by nlinarith)
    (fun y hy hy' => outward_upper_overlap good hB hC hR hM hshifts hshift hhi hhcap hy hy') hx
  unfold outwardOffset
  rw [he,nuclear_outerOffset_eq (by nlinarith : R ≤ ‖x‖)]

end Work_BarrierStepBounds_barrier_scope

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma innerSource_locallyIntegrable {μ p : TFSpace → ℝ}
    (hμ : LocallyIntegrable μ) (hp : LocallyIntegrable p) (R : ℝ) :
    LocallyIntegrable (innerSource R μ p) := by
  have hi := hμ.indicator (s := {x : TFSpace | ‖x‖ < R})
    (isOpen_lt continuous_norm continuous_const).measurableSet
  exact (hi.sub hp).smul (4*Real.pi)

lemma addedError_locallyIntegrable (good : Prop) [Decidable good]
    {μ p : TFSpace → ℝ} (hμ : LocallyIntegrable μ) (hp : LocallyIntegrable p) (R : ℝ) :
    LocallyIntegrable (addedError good R μ p) := by
  unfold addedError
  split_ifs with hg
  · simpa only [add_zero] using hp
  · have hi := hμ.indicator (s := {x : TFSpace | R/2 ≤ ‖x‖} ∩ {x : TFSpace | ‖x‖ < R})
      ((isClosed_le continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet)
    have he : (({x : TFSpace | R/2 ≤ ‖x‖} ∩ {x : TFSpace | ‖x‖ < R}).indicator μ) =
        (fun x => if R/2 ≤ ‖x‖ ∧ ‖x‖ < R then μ x else 0) := by
      funext x
      simp only [indicator_apply, mem_inter_iff, mem_ofPred_eq]
    rw [he] at hi
    exact hp.add hi

lemma old_branch_height {Z B C R hl hh : ℝ} (hB : 0 < B) (hR : 0 < R)
    (hhl : hl < B/4) (hhh : C < hh) {a : TFSpace → ℝ}
    (hlo : ∀ x, R/2 ≤ ‖x‖ → outerBarrier B (R/2) x ≤ nuclearField Z x+a x)
    (hhi : ∀ x, R/2 ≤ ‖x‖ → nuclearField Z x+a x ≤ C/‖x‖^4)
    {x : TFSpace} (hx : R/2 ≤ ‖x‖) :
    0 ≤ nuclearField Z x+a x ∧ ‖x‖^4*(nuclearField Z x+a x) ∈ Icc hl hh := by
  have hd : 0 < ‖x‖ := (by linarith : 0 < R/2).trans_le hx
  have hd4 := pow_pos hd 4
  have hlow := (outerBarrier_bounds hB.le (by linarith : 0 < R/2) hx).1.trans (hlo x hx)
  have hlow' := (div_le_iff₀ hd4).mp hlow
  have hhigh := (le_div_iff₀ hd4).mp (hhi x hx)
  refine ⟨(by positivity : 0 ≤ (7*B/8)/‖x‖^4).trans hlow,?_,?_⟩ <;> nlinarith

lemma outward_old_retained_dom (good : Prop) [Decidable good]
    {Z B C R κ lam1 lam2 e ξ Cinv hl hh : ℝ}
    (hB : 0 < B) (hR : 0 < R) (hκ : 0 ≤ κ) (hlam : 0 ≤ lam1) (hξ : 0 ≤ ξ)
    (hgap : 16*ξ+2*e < lam1-lam2) (hhl : hl < B/4) (hhh : C < hh)
    {a h μ p : TFSpace → ℝ}
    (hlo : ∀ x, R/2 ≤ ‖x‖ → outerBarrier B (R/2) x ≤ nuclearField Z x+a x)
    (hhi : ∀ x, R/2 ≤ ‖x‖ → nuclearField Z x+a x ≤ C/‖x‖^4)
    (hinv : good → ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < R →
      InverseComparisonAt ‖x‖ (nuclearField Z x+h x) (μ x) κ hl hh ξ Cinv)
    {x : TFSpace} {w : ℝ} (hcand : good → h x-lam2/R^4 ≤ w)
    (hnear : w-(a x-lam1/R^4) < 2*(e/R^4)) :
    innerSource R μ (addedError good R μ p) x+
      outerCoefficient R x*reaction κ (nuclearField Z x+(a x-lam1/R^4)) ≤
    innerSource (R/2) μ p x+outerCoefficient (R/2) x*reaction κ (nuclearField Z x+a x) := by
  have hh' := outward_old_source good hR hκ hlam hξ hgap hinv
    (u := fun y => nuclearField Z y+a y) (w := fun _ => nuclearField Z x+w)
    (H := fun y => nuclearField Z y+h y) (p := p) (x := x)
    (fun hx _ => old_branch_height hB hR hhl hhh hlo hhi hx)
    (fun hg => by linarith [hcand hg]) (by convert hnear using 1 <;> ring)
  simpa only [add_sub_assoc] using hh'

lemma outward_field_retained_dom (good : Prop) [Decidable good]
    {Z B C R M κ lam2 e ξ Cinv hl hh : ℝ}
    (hB : 0 < B) (hR : 0 < R) (he : 0 < e) (hξ : 0 ≤ ξ)
    (hshift : ξ < lam2) (hlam : 0 ≤ lam2) (hhl : hl < B/4) (hhh : C < hh)
    (hsmall : 2*e*(2*M)^4 < B/4)
    {h μ p : TFSpace → ℝ} (hp : ∀ x, 0 ≤ p x) (hμ : ∀ x, 0 ≤ μ x)
    {x : TFSpace} {w : ℝ} (hd : ‖x‖ < 2*M*R)
    (hinv : R ≤ ‖x‖ → InverseComparisonAt ‖x‖ (nuclearField Z x+h x) (μ x) κ hl hh ξ Cinv)
    (hcap : R ≤ ‖x‖ → nuclearField Z x+h x ≤ C/‖x‖^4)
    (hlo : R ≤ ‖x‖ → outerBarrier B R x ≤ nuclearField Z x+w)
    (hnear : w-(h x-lam2/R^4) < 2*(e/R^4)) :
    innerSource R μ (addedError good R μ p) x+
      outerCoefficient R x*reaction κ (nuclearField Z x+(h x-lam2/R^4)) ≤ 4*Real.pi*μ x := by
  have hh' := outward_field_source good hR hξ hshift hp hμ
    (H := fun y => nuclearField Z y+h y) (x := x) hinv (fun hx => by
    apply retained_field_height hB hR he hx hd.le hhl hhh hsmall hlam rfl
      (w := nuclearField Z x+w) (H := nuclearField Z x+h x)
    · exact (outerBarrier_bounds hB.le hR hx).1.trans (hlo hx)
    · have hd4 := pow_pos (hR.trans_le hx) 4
      have hb := (le_div_iff₀ hd4).mp (hcap hx)
      nlinarith
    · convert hnear using 1 <;> ring)
  simpa only [add_sub_assoc] using hh'

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RetainedNeighborhoodBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_RetainedNeighborhood_barrier_scope

open Set Filter
open scoped Topology

theorem retained_neighborhood {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (hs : s.Nonempty) (v : ι → X → ℝ) (x : X)
    (hv : ∀ i ∈ s, ContinuousAt (v i) x) {ε : ℝ} (hε : 0 < ε) :
    ∃ (t : Finset ι) (ht : t.Nonempty) (U : Set X), t ⊆ s ∧ IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U,
        s.sup' hs (fun i => v i y) = t.sup' ht (fun i => v i y) ∧
        ∀ i ∈ t, s.sup' hs (fun i => v i y) - v i y < 2*ε := by
  classical
  let M : X → ℝ := fun y => s.sup' hs (fun i => v i y)
  let t := s.filter (fun i => M x-v i x ≤ ε)
  obtain ⟨k,hks,hk⟩ := Finset.exists_mem_eq_sup' hs (fun i => v i x)
  have hkt : k ∈ t := by
    simp only [t,Finset.mem_filter]
    exact ⟨hks,by change s.sup' hs (fun i => v i x)-v k x ≤ ε; rw [hk]; linarith⟩
  have ht : t.Nonempty := ⟨k,hkt⟩
  have hts : t ⊆ s := Finset.filter_subset _ _
  have hM : ContinuousAt M x := by
    exact ContinuousAt.finset_sup'_apply hs hv
  have hr : ∀ᶠ y in 𝓝 x, ∀ i ∈ t, M y-v i y < 2*ε := by
    change ∀ᶠ y in 𝓝 x, ∀ i ∈ (↑t : Set ι), M y-v i y < 2*ε
    rw [t.finite_toSet.eventually_all]
    intro i hi
    have his := hts hi
    have hie : M x-v i x ≤ ε := (Finset.mem_filter.mp hi).2
    exact (hM.sub (hv i his)).eventually (gt_mem_nhds (show M x-v i x < 2*ε by linarith))
  have hd : ∀ᶠ y in 𝓝 x, ∀ i ∈ s, i ∉ t → v i y < v k y := by
    change ∀ᶠ y in 𝓝 x, ∀ i ∈ (↑s : Set ι), i ∉ t → v i y < v k y
    rw [s.finite_toSet.eventually_all]
    intro i hi
    by_cases hit : i ∈ t
    · exact Eventually.of_forall fun _ h => False.elim (h hit)
    · have hgap : ε < M x-v i x := lt_of_not_ge (by
        intro he
        exact hit (Finset.mem_filter.mpr ⟨hi,he⟩))
      have hlt : v i x < v k x := by change ε < s.sup' hs (fun i => v i x)-v i x at hgap; rw [hk] at hgap; linarith
      filter_upwards [(hv i hi).eventually_lt (hv k hks) hlt] with y hy _
      exact hy
  let U := interior {y | (∀ i ∈ t, M y-v i y < 2*ε) ∧
    (∀ i ∈ s, i ∉ t → v i y < v k y)}
  have hxU : x ∈ U := mem_interior_iff_mem_nhds.mpr (hr.and hd)
  refine ⟨t,ht,U,hts,isOpen_interior,hxU,?_⟩
  intro y hy
  have hy' := interior_subset hy
  refine ⟨le_antisymm ?_ ?_,hy'.1⟩
  · apply Finset.sup'_le hs
    intro i hi
    by_cases hit : i ∈ t
    · exact Finset.le_sup' (fun i => v i y) hit
    · exact (hy'.2 i hi hit).le.trans (Finset.le_sup' (fun i => v i y) hkt)
  · apply Finset.sup'_le ht
    intro i hi
    exact Finset.le_sup' (fun i => v i y) (hts hi)

end Work_RetainedNeighborhood_barrier_scope

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology BigOperators

open CoulombAnalysis CoulombPDE CoulombAtom

theorem retained_weak_maximum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {U : Set TFSpace} (hU : IsOpen U) (u h : ι → TFSpace → ℝ)
    (hu : ∀ i ∈ s, Continuous (u i)) (hh : ∀ i ∈ s, LocallyIntegrable (h i))
    {g χ : TFSpace → ℝ} {F : TFSpace → ℝ → ℝ}
    (hg : LocallyIntegrable g) (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hF : Continuous (fun p : TFSpace × ℝ => F p.1 p.2))
    {ε : ℝ} (hε : 0 < ε)
    (hw : ∀ i ∈ s, WeakLaplacianLowerOn U (u i) (h i))
    (hdom : ∀ᵐ x, ∀ i ∈ s, x ∈ U → s.sup' hs (fun k => u k x)-u i x < 2*ε →
      g x+χ x*F x (u i x) ≤ h i x) :
    WeakLaplacianLowerOn U (fun x => s.sup' hs (fun i => u i x))
      (fun x => g x+χ x*F x (s.sup' hs (fun i => u i x))) := by
  classical
  have hM := Continuous.finset_sup'_apply hs hu
  have hgM := spatial_source_locallyIntegrable hg hχ hbχ hF hM
  apply weak_lower_local hM.locallyIntegrable hgM
  intro x hx
  obtain ⟨t,ht,V,hts,hV,hxV,hnear⟩ := retained_neighborhood s hs u x
    (fun i hi => (hu i hi).continuousAt) hε
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have htu : ∀ i ∈ t, Continuous (u i) := fun i hi => hu i (hts hi)
  have htM := Continuous.finset_sup'_apply ht htu
  have hgw := spatial_source_locallyIntegrable hg hχ hbχ hF htM
  have htw : ∀ i ∈ t, WeakLaplacianLowerOn W (u i)
      (fun y => g y+χ y*F y (u i y)) := by
    intro i hi
    apply ((hw i (hts hi)).mono_set inter_subset_left).source_mono_ae
      (hh i (hts hi)) (spatial_source_locallyIntegrable hg hχ hbχ hF (htu i hi))
    filter_upwards [hdom] with y hy
    intro hyW
    exact hy i (hts hi) hyW.1 ((hnear y hyW.2).2 i hi)
  have htweak := weak_finset_maximum_spatial t ht hW u htu hg hχ hbχ hF htw
  have he : ∀ y ∈ W, t.sup' ht (fun i => u i y) = s.sup' hs (fun i => u i y) :=
    fun y hy => (hnear y hy.2).1.symm
  refine ⟨W,hW,⟨hx,hxV⟩,?_⟩
  apply (htweak.congr_field he).source_mono hgw hgM
  intro y hy
  rw [he y hy]

theorem nuclear_retained_weak_maximum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {U : Set TFSpace} (hU : IsOpen U) (Z : ℝ) {R κ ε : ℝ} (hR : 0 < R)
    (u h : ι → TFSpace → ℝ) (hu : ∀ i ∈ s, Continuous (u i))
    (hh : ∀ i ∈ s, LocallyIntegrable (h i))
    {g χ : TFSpace → ℝ} (hg : LocallyIntegrable g)
    (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hzero : ∀ x, ‖x‖ < R → χ x = 0) (hε : 0 < ε)
    (hw : ∀ i ∈ s, WeakNuclearLowerOn U Z
      (fun x => nuclearField Z x+u i x) (h i))
    (hdom : ∀ᵐ x, ∀ i ∈ s, x ∈ U → s.sup' hs (fun k => u k x)-u i x < 2*ε →
      g x+χ x*reaction κ (nuclearField Z x+u i x) ≤ h i x) :
    WeakNuclearLowerOn U Z (fun x => nuclearField Z x+s.sup' hs (fun i => u i x))
      (fun x => g x+χ x*reaction κ (nuclearField Z x+s.sup' hs (fun i => u i x))) := by
  rw [weakNuclearLower_add_iff Z (Continuous.finset_sup'_apply hs hu).locallyIntegrable]
  simp_rw [weighted_clipped_reaction Z R hzero]
  apply retained_weak_maximum s hs hU u h hu hh hg hχ hbχ
    (F := fun x t => reaction κ (clippedNuclearField Z R x+t))
    ((reaction_continuous κ).comp
      (((clippedNuclearField_continuous Z hR).comp continuous_fst).add continuous_snd)) hε
  · exact fun i hi => (weakNuclearLower_add_iff Z (hu i hi).locallyIntegrable).mp (hw i hi)
  · simpa only [weighted_clipped_reaction Z R hzero] using hdom

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierRetainedFiniteBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierRetainedFinite_barrier_scope

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAnalysis

lemma sup_triple_values (a b c : ℝ) :
    ({0,1,2} : Finset (Fin 3)).sup' (by simp)
      (fun i => if i = 0 then a else if i = 1 then b else c) = max (max a b) c := by
  rw [Finset.sup'_insert (by simp),Finset.sup'_insert (by simp),Finset.sup'_singleton]
  simp [max_assoc]

 theorem nuclear_retained_max_three {U : Set TFSpace} (hU : IsOpen U) (Z : ℝ)
    {R κ ε : ℝ} (hR : 0 < R) (hε : 0 < ε) {u v b h₁ h₂ h₃ g χ : TFSpace → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hb : Continuous b)
    (hh₁ : LocallyIntegrable h₁) (hh₂ : LocallyIntegrable h₂) (hh₃ : LocallyIntegrable h₃)
    (hg : LocallyIntegrable g) (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hzero : ∀ x, ‖x‖ < R → χ x = 0)
    (hw₁ : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+u x) h₁)
    (hw₂ : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+v x) h₂)
    (hw₃ : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+b x) h₃)
    (hdom₁ : ∀ᵐ x, x ∈ U → max (max (u x) (v x)) (b x)-u x < 2*ε →
      g x+χ x*reaction κ (nuclearField Z x+u x) ≤ h₁ x)
    (hdom₂ : ∀ᵐ x, x ∈ U → max (max (u x) (v x)) (b x)-v x < 2*ε →
      g x+χ x*reaction κ (nuclearField Z x+v x) ≤ h₂ x)
    (hdom₃ : ∀ᵐ x, x ∈ U → max (max (u x) (v x)) (b x)-b x < 2*ε →
      g x+χ x*reaction κ (nuclearField Z x+b x) ≤ h₃ x) :
    WeakNuclearLowerOn U Z (fun x => nuclearField Z x+max (max (u x) (v x)) (b x))
      (fun x => g x+χ x*reaction κ (nuclearField Z x+max (max (u x) (v x)) (b x))) := by
  have hw := nuclear_retained_weak_maximum ({0,1,2} : Finset (Fin 3)) (by simp) hU Z hR
    (fun i x => if i = 0 then u x else if i = 1 then v x else b x)
    (fun i x => if i = 0 then h₁ x else if i = 1 then h₂ x else h₃ x)
    (by
      intro i _
      fin_cases i
      · simpa using hu
      · simpa using hv
      · simpa using hb)
    (by
      intro i _
      fin_cases i
      · simpa using hh₁
      · simpa using hh₂
      · simpa using hh₃)
    hg hχ hbχ hzero hε
    (by
      intro i _
      fin_cases i
      · simpa using hw₁
      · simpa using hw₂
      · simpa using hw₃)
    (by
      filter_upwards [hdom₁,hdom₂,hdom₃] with x hx₁ hx₂ hx₃
      intro i _ hx hi
      rw [sup_triple_values] at hi
      fin_cases i
      · simpa using hx₁ hx (by simpa using hi)
      · simpa using hx₂ hx (by simpa using hi)
      · simpa using hx₃ hx (by simpa using hi))
  simpa only [sup_triple_values] using hw

end Work_BarrierRetainedFinite_barrier_scope

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma outwardRegionOffset_inner (good : Prop) [Decidable good]
    (a h : TFSpace → ℝ) (Z B R lam1 lam2 : ℝ) :
    outwardRegionOffset good False a h Z B R lam1 lam2 = shiftedCandidates good a h R lam1 lam2 := by
  funext x
  by_cases hg : good <;> simp [outwardRegionOffset,shiftedCandidates,hg]

lemma outwardRegionOffset_middle (good : Prop) [Decidable good]
    (a h : TFSpace → ℝ) (Z B R lam1 lam2 : ℝ) :
    outwardRegionOffset good True a h Z B R lam1 lam2 =
      fun x => max (shiftedCandidates good a h R lam1 lam2 x) (outerOffset Z B R x) := by
  funext x
  by_cases hg : good <;> simp [outwardRegionOffset,shiftedCandidates,hg]

theorem outward_region_weak (good radial : Prop) [Decidable good] [Decidable radial]
    {Z B C R M κ lam1 lam2 e ξ Cinv hl hh : ℝ}
    (cal : OutwardCalibration κ B C M lam1 lam2 e ξ hl hh) (hR : 0 < R)
    {U : Set TFSpace} (hU : IsOpen U) (hUbound : ∀ x ∈ U, ‖x‖ < 2*M*R)
    (hUrad : radial → ∀ x ∈ U, R < ‖x‖)
    {a h μ p : TFSpace → ℝ} (ha : Continuous a) (hhc : Continuous h)
    (hμ : LocallyIntegrable μ) (hp : LocallyIntegrable p)
    (hμn : ∀ x, 0 ≤ μ x) (hpn : ∀ x, 0 ≤ p x)
    (hlo : ∀ x, R/2 ≤ ‖x‖ → outerBarrier B (R/2) x ≤ nuclearField Z x+a x)
    (hhi : ∀ x, R/2 ≤ ‖x‖ → nuclearField Z x+a x ≤ C/‖x‖^4)
    (hhcap : good → ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < 2*M*R → nuclearField Z x+h x ≤ C/‖x‖^4)
    (hinv : good → ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < 2*M*R →
      InverseComparisonAt ‖x‖ (nuclearField Z x+h x) (μ x) κ hl hh ξ Cinv)
    (hwlo : ∀ x ∈ U, R ≤ ‖x‖ → outerBarrier B R x ≤
      nuclearField Z x+outwardRegionOffset good radial a h Z B R lam1 lam2 x)
    (hwa : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource (R/2) μ p x+outerCoefficient (R/2) x*reaction κ (nuclearField Z x+a x)))
    (hwh : good → WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+h x) (fun x => 4*Real.pi*μ x)) :
    WeakNuclearLowerOn U Z (fun x => nuclearField Z x+outwardRegionOffset good radial a h Z B R lam1 lam2 x)
      (fun x => innerSource R μ (addedError good R μ p) x+
        outerCoefficient R x*reaction κ (nuclearField Z x+outwardRegionOffset good radial a h Z B R lam1 lam2 x)) := by
  let v₁ := fun x => a x-lam1/R^4
  let v₂ := fun x => if good then h x-lam2/R^4 else v₁ x
  let b := outerOffset Z B R
  let v₃ := fun x => if radial then b x else v₁ x
  let s₁ := fun x => innerSource (R/2) μ p x+outerCoefficient (R/2) x*reaction κ (nuclearField Z x+a x)
  let s₂ := fun x => if good then 4*Real.pi*μ x else s₁ x
  let sb := fun x => outerCoefficient R x*reaction κ (nuclearField Z x+b x)
  let s₃ := fun x => if radial then sb x else s₁ x
  let g := innerSource R μ (addedError good R μ p)
  have hv₁ : Continuous v₁ := ha.sub continuous_const
  have hv₂ : Continuous v₂ := by
    dsimp [v₂]; split_ifs; exact hhc.sub continuous_const; exact hv₁
  have hb : Continuous b := outerOffset_continuous Z B hR
  have hv₃ : Continuous v₃ := by dsimp [v₃]; split_ifs; exact hb; exact hv₁
  have hs₁ : LocallyIntegrable s₁ := nuclear_source_locallyIntegrable Z κ (by linarith : 0 < R/2)
    (innerSource_locallyIntegrable hμ hp (R/2)) (outerCoefficient_measurable (R/2))
    (outerCoefficient_bound (R/2)) (outerCoefficient_zero (R/2)) ha
  have hs₂ : LocallyIntegrable s₂ := by
    dsimp [s₂]; split_ifs; exact hμ.smul (4*Real.pi); exact hs₁
  have hsb : LocallyIntegrable sb := by
    simpa only [zero_add] using nuclear_source_locallyIntegrable Z κ hR
      (locallyIntegrable_zero (X := TFSpace) (ε'' := ℝ)) (outerCoefficient_measurable R)
      (outerCoefficient_bound R) (outerCoefficient_zero R) hb
  have hs₃ : LocallyIntegrable s₃ := by dsimp [s₃]; split_ifs; exact hsb; exact hs₁
  have hg : LocallyIntegrable g := innerSource_locallyIntegrable hμ (addedError_locallyIntegrable good hμ hp R) R
  have hw₁ : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+v₁ x) s₁ := by
    have hw := (hwa.sub_const ((nuclearField_locallyIntegrable Z).add ha.locallyIntegrable) (lam1/R^4)).mono_set
      (subset_univ U)
    simpa only [v₁,add_sub_assoc] using hw
  have hw₂ : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+v₂ x) s₂ := by
    by_cases hgood : good
    · have hw := ((hwh hgood).sub_const ((nuclearField_locallyIntegrable Z).add hhc.locallyIntegrable)
        (lam2/R^4)).mono_set (subset_univ U)
      simpa only [v₂,s₂,ite_eq_left hgood,add_sub_assoc] using hw
    · simpa only [v₂,s₂,ite_eq_right hgood] using hw₁
  have hw₃ : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+v₃ x) s₃ := by
    by_cases hrad : radial
    · have hw := (outerOffset_weak_nuclear cal.B_pos hR cal.k_nonneg cal.subsolution Z).mono_set (hUrad hrad)
      have hw' : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+b x) sb :=
        hw.congr_source (fun x hx => by simp only [sb,outerCoefficient,ite_eq_left (hUrad hrad x hx).le,one_mul,b])
      simpa only [v₃,s₃,ite_eq_left hrad] using hw'
    · simpa only [v₃,s₃,ite_eq_right hrad] using hw₁
  have hd₁ (x : TFSpace) (_hx : x ∈ U)
      (hn : max (max (v₁ x) (v₂ x)) (v₃ x)-v₁ x < 2*(e/R^4)) :
      g x+outerCoefficient R x*reaction κ (nuclearField Z x+v₁ x) ≤ s₁ x := by
    apply outward_old_retained_dom good cal.B_pos hR cal.k_nonneg
      (cal.xi_nonneg.trans (cal.low_shift.le.trans cal.shift_order)) cal.xi_nonneg cal.gap
      cal.height_low cal.height_high hlo hhi
      (fun hgood y hy hy' => hinv hgood y hy (by nlinarith [cal.M_large]))
      (h := h) (p := p) (w := max (max (v₁ x) (v₂ x)) (v₃ x))
    · intro hgood
      have hh : v₂ x ≤ max (max (v₁ x) (v₂ x)) (v₃ x) :=
        (le_max_right _ _).trans (le_max_left _ _)
      simpa only [v₂,ite_eq_left hgood] using hh
    · exact hn
  have hd₂ (x : TFSpace) (hx : x ∈ U)
      (hn : max (max (v₁ x) (v₂ x)) (v₃ x)-v₂ x < 2*(e/R^4)) :
      g x+outerCoefficient R x*reaction κ (nuclearField Z x+v₂ x) ≤ s₂ x := by
    by_cases hgood : good
    · simp only [v₂,ite_eq_left hgood] at hn ⊢
      simp only [s₂,ite_eq_left hgood]
      exact outward_field_retained_dom good cal.B_pos hR cal.e_pos cal.xi_nonneg cal.low_shift
        (cal.xi_nonneg.trans cal.low_shift.le) cal.height_low cal.height_high cal.e_small hpn hμn
        (hUbound x hx) (fun hy => hinv hgood x (by linarith) (hUbound x hx))
        (fun hy => hhcap hgood x (by linarith) (hUbound x hx)) (hwlo x hx) (by simpa only [outwardRegionOffset,v₁,v₂,v₃,b,ite_eq_left hgood] using hn)
    · simp only [v₂,ite_eq_right hgood] at hn ⊢
      simpa only [s₂,ite_eq_right hgood] using hd₁ x hx (by simpa only [v₂,ite_eq_right hgood] using hn)
  have hd₃ (x : TFSpace) (hx : x ∈ U)
      (hn : max (max (v₁ x) (v₂ x)) (v₃ x)-v₃ x < 2*(e/R^4)) :
      g x+outerCoefficient R x*reaction κ (nuclearField Z x+v₃ x) ≤ s₃ x := by
    by_cases hrad : radial
    · have hrx := hUrad hrad x hx
      have hp' := addedError_nonneg good (R := R) hμn hpn x
      have hπ : 0 < 4*Real.pi := by positivity
      simp only [v₃,s₃,g,sb,ite_eq_left hrad,innerSource,ite_eq_right (not_lt_of_ge hrx.le),zero_sub]
      nlinarith
    · simpa only [v₃,s₃,ite_eq_right hrad] using hd₁ x hx (by simpa only [v₃,ite_eq_right hrad] using hn)
  exact nuclear_retained_max_three hU Z hR (div_pos cal.e_pos (pow_pos hR 4)) hv₁ hv₂ hv₃
    hs₁ hs₂ hs₃ hg (outerCoefficient_measurable R) (outerCoefficient_bound R) (outerCoefficient_zero R)
    hw₁ hw₂ hw₃ (ae_of_all _ hd₁) (ae_of_all _ hd₂) (ae_of_all _ hd₃)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierStepWeakBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierStepWeak_barrier_scope

open Set Filter MeasureTheory Metric
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

theorem outwardOffset_weak (good : Prop) [Decidable good]
    {Z B C R M κ lam1 lam2 e ξ Cinv hl hh : ℝ}
    (cal : OutwardCalibration κ B C M lam1 lam2 e ξ hl hh) (hR : 0 < R)
    {a h μ p : TFSpace → ℝ} (ha : Continuous a) (hhc : Continuous h)
    (hμ : LocallyIntegrable μ) (hp : LocallyIntegrable p)
    (hμn : ∀ x, 0 ≤ μ x) (hpn : ∀ x, 0 ≤ p x)
    (hlo : ∀ x, R/2 ≤ ‖x‖ → outerBarrier B (R/2) x ≤ nuclearField Z x+a x)
    (hhi : ∀ x, R/2 ≤ ‖x‖ → nuclearField Z x+a x ≤ C/‖x‖^4)
    (hhcap : good → ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < 2*M*R → nuclearField Z x+h x ≤ C/‖x‖^4)
    (hinv : good → ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < 2*M*R →
      InverseComparisonAt ‖x‖ (nuclearField Z x+h x) (μ x) κ hl hh ξ Cinv)
    (hwa : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource (R/2) μ p x+outerCoefficient (R/2) x*reaction κ (nuclearField Z x+a x)))
    (hwh : good → WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+h x) (fun x => 4*Real.pi*μ x)) :
    WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+outwardOffset good a h Z B R M lam1 lam2 x)
      (fun x => innerSource R μ (addedError good R μ p) x+
        outerCoefficient R x*reaction κ (nuclearField Z x+outwardOffset good a h Z B R M lam1 lam2 x)) := by
  have hM := cal.M_large
  have hlow (x : TFSpace) (hx : (26/25)*R ≤ ‖x‖) (hx' : ‖x‖ < (27/25)*R) :
      outerOffset Z B R x ≤ shiftedCandidates good a h R lam1 lam2 x :=
    outward_lower_overlap good cal.B_pos.le hR cal.shift_small hlo (by linarith) hx'
  have hhigh (x : TFSpace) (hx : M*R < ‖x‖) (hx' : ‖x‖ < 2*M*R) :
      shiftedCandidates good a h R lam1 lam2 x ≤ outerOffset Z B R x :=
    outward_upper_overlap good cal.B_pos.le cal.C_nonneg hR hM cal.shift_order cal.cap_shift hhi
      (fun hg y hy hy' => hhcap hg y (by nlinarith) hy') hx hx'
  have hg := innerSource_locallyIntegrable hμ (addedError_locallyIntegrable good hμ hp R) R
  unfold outwardOffset
  apply cutMaximum_weak_nuclear_of_cover (t := (27/25)*R) (L := M*R)
    (by linarith) (by nlinarith) (by nlinarith) hlow hhigh Z κ hR
    (shiftedCandidates_continuous good ha hhc R lam1 lam2) (outerOffset_continuous Z B hR)
    hg (outerCoefficient_measurable R) (outerCoefficient_bound R) (outerCoefficient_zero R)
  · have hw := outward_region_weak good False cal hR (U := {x : TFSpace | ‖x‖ < (27/25)*R})
      (isOpen_lt continuous_norm continuous_const) (fun x hx => by dsimp at hx; nlinarith)
      (fun h => False.elim h) ha hhc hμ hp hμn hpn hlo hhi hhcap hinv
      (fun x hx hxR => by
        rw [outwardRegionOffset_inner,←nuclear_outerOffset_eq (Z := Z) hxR]
        exact add_le_add_right (outward_lower_overlap good cal.B_pos.le hR cal.shift_small hlo hxR hx) _)
      hwa hwh
    simpa only [outwardRegionOffset_inner] using hw
  · have hopen : IsOpen {x : TFSpace | (26/25)*R < ‖x‖ ∧ ‖x‖ < 2*M*R} :=
      (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
    have hw := outward_region_weak good True cal hR hopen (fun _ hx => hx.2)
      (fun _ x hx => by dsimp at hx; linarith [hx.1]) ha hhc hμ hp hμn hpn hlo hhi hhcap hinv
      (fun x _ hxR => by
        rw [outwardRegionOffset_middle,←nuclear_outerOffset_eq (Z := Z) hxR]
        exact add_le_add_right (le_max_right _ _) _) hwa hwh
    simpa only [outwardRegionOffset_middle] using hw
  · let b := outerOffset Z B R
    let sb := fun x => outerCoefficient R x*reaction κ (nuclearField Z x+b x)
    have hb := outerOffset_continuous Z B hR
    have hsb : LocallyIntegrable sb := by
      simpa only [zero_add] using nuclear_source_locallyIntegrable Z κ hR
        (locallyIntegrable_zero (X := TFSpace) (ε'' := ℝ)) (outerCoefficient_measurable R)
        (outerCoefficient_bound R) (outerCoefficient_zero R) hb
    have hw := (outerOffset_weak_nuclear cal.B_pos hR cal.k_nonneg cal.subsolution Z).mono_set
      (show {x : TFSpace | M*R < ‖x‖} ⊆ {x : TFSpace | R < ‖x‖} from fun x hx => by dsimp at *; nlinarith)
    have hw' : WeakNuclearLowerOn {x : TFSpace | M*R < ‖x‖} Z (fun x => nuclearField Z x+b x) sb :=
      hw.congr_source (fun x hx => by
        have hxR : R ≤ ‖x‖ := by dsimp at hx; nlinarith
        simp only [sb,b,outerCoefficient,ite_eq_left hxR,one_mul])
    apply hw'.source_mono hsb (hg.add hsb)
    intro x hx
    have hxR : R ≤ ‖x‖ := by dsimp at hx; nlinarith
    have hn := addedError_nonneg good (R := R) hμn hpn x
    have hπ := Real.pi_pos
    change innerSource R μ (addedError good R μ p) x+sb x ≤ sb x
    simp only [innerSource,ite_eq_right (not_lt_of_ge hxR),zero_sub]
    nlinarith

end CoulombBarrier

end Work_BarrierStepWeak_barrier_scope

open Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierInitialInvariantBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierInitialInvariant_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma IsNuclearBarrier.locallyLipschitz_offset {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {μ a p : Ω → TFSpace → ℝ} {Z k B C r T η : ℝ}
    (h : IsNuclearBarrier P μ Z k B C r T η a p) (sample : Ω) :
    LocallyLipschitz (a sample) := h.uniform_lipschitz_offset.locallyLipschitz sample

end Work_BarrierInitialInvariant_barrier_scope

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma nonneg_bounded_deterministicBound {Ω : Type*} {p : Ω → TFSpace → ℝ}
    (hn : ∀ sample x, 0 ≤ p sample x) {L : ℝ} (hb : ∀ sample x, p sample x ≤ L) :
    DeterministicLocalBound p := fun _ _ => ⟨L,fun sample x _ => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hn sample x)] using hb sample x⟩

lemma nonneg_bounded_locallyIntegrable {p : TFSpace → ℝ} (hm : Measurable p)
    (hn : ∀ x, 0 ≤ p x) {L : ℝ} (hb : ∀ x, p x ≤ L) : LocallyIntegrable p :=
  deterministicBound_locallyIntegrable hm (nonneg_bounded_deterministicBound (fun _ : Unit => hn) (fun _ => hb))

lemma expected_mass_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {p q : Ω → TFSpace → ℝ} (hpm : Measurable (Function.uncurry p))
    (hqm : Measurable (Function.uncurry q)) (hpb : DeterministicLocalBound p) (hqb : DeterministicLocalBound q)
    {R S : ℝ} (hps : ∀ sample x, R < ‖x‖ → p sample x = 0) (hqs : ∀ sample x, S < ‖x‖ → q sample x = 0) :
    (∫ sample, (∫ x, p sample x+q sample x) ∂P) = (∫ sample, (∫ x, p sample x) ∂P)+(∫ sample, (∫ x, q sample x) ∂P) := by
  have hpi := compactBound_integrable_prod (P := P) hpm hpb hps
  have hqi := compactBound_integrable_prod (P := P) hqm hqb hqs
  calc
    _ = ∫ z, p z.1 z.2+q z.1 z.2 ∂P.prod volume :=
      (integral_prod (fun z => p z.1 z.2+q z.1 z.2) (hpi.add hqi)).symm
    _ = (∫ z, p z.1 z.2 ∂P.prod volume)+(∫ z, q z.1 z.2 ∂P.prod volume) := integral_add hpi hqi
    _ = _ := congrArg₂ (·+·) (integral_prod (fun z => p z.1 z.2) hpi) (integral_prod (fun z => q z.1 z.2) hqi)

theorem outward_barrier_invariant {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (good : Ω → Prop) [DecidablePred good] (hgood : MeasurableSet {sample | good sample})
    {Z B C R M κ lam1 lam2 e ξ Cinv hl hh T η : ℝ}
    (cal : OutwardCalibration κ B C M lam1 lam2 e ξ hl hh) (hR : 0 < R)
    {a h μ p : Ω → TFSpace → ℝ}
    (old : IsNuclearBarrier P μ Z κ B C (R/2) T η a p)
    (hm : Measurable (Function.uncurry h)) (hhl : DeterministicLocalLipschitz h)
    (hhb : DeterministicLocalBound h)
    (hμm : Measurable (Function.uncurry μ)) (hμn : ∀ sample x, 0 ≤ μ sample x)
    {D : ℝ} (hD : 0 ≤ D) (hμb : ∀ sample x, μ sample x ≤ D)
    (hhcap : ∀ sample, good sample → ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < 2*M*R → nuclearField Z x+h sample x ≤ C/‖x‖^4)
    (hinv : ∀ sample, good sample → ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < 2*M*R →
      InverseComparisonAt ‖x‖ (nuclearField Z x+h sample x) (μ sample x) κ hl hh ξ Cinv)
    (hwh : ∀ᵐ sample ∂P, good sample → WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+h sample x) (fun x => 4*Real.pi*μ sample x)) :
    IsNuclearBarrier P μ Z κ B C R M
      (η+∫ sample, (∫ x, addedError (good sample) R (μ sample) (fun _ => 0) x) ∂P)
      (fun sample => outwardOffset (good sample) (a sample) (h sample) Z B R M lam1 lam2)
      (fun sample => addedError (good sample) R (μ sample) (p sample)) := by
  obtain ⟨L,hpL⟩ := old.bounded_error
  have hpm := old.measurable_error
  have hpb := nonneg_bounded_deterministicBound old.nonneg_error hpL
  have hps := old.support_error
  have hpn := old.nonneg_error
  have hqm := addedError_measurable good hgood (p := fun _ _ => 0) hμm measurable_const R
  have hqb := nonneg_bounded_deterministicBound
    (fun sample x => addedError_nonneg (good sample) (R := R) (hμn sample) (fun _ => le_refl 0) x)
    (fun sample x => addedError_le (good sample) (R := R) hD (hμb sample) (fun _ => le_refl 0) x)
  have hqs : ∀ sample x, R < ‖x‖ → addedError (good sample) R (μ sample) (fun _ => 0) x = 0 :=
    fun sample x hx => addedError_support (good sample) hR.le (fun _ _ => rfl) hx
  refine ⟨outwardOffset_measurable good hgood old.measurable_offset hm Z B M lam1 lam2 hR,?_,
    outwardOffset_deterministicBound good old.bound_offset hhb Z B M lam1 lam2 hR,
    addedError_measurable good hgood hμm hpm R,
    (fun sample x => addedError_nonneg (good sample) (hμn sample) (hpn sample) x),
    ⟨L+D,fun sample x => addedError_le (good sample) hD (hμb sample) (hpL sample) x⟩,?_,?_,?_,?_,?_,?_⟩
  · exact outwardOffset_deterministicLip cal.B_pos.le cal.C_nonneg hR cal.M_large cal.shift_order cal.cap_shift
      cal.shift_small good old.uniform_lipschitz_offset hhl old.lower old.upper
      (fun sample hg x hx hx' => hhcap sample hg x (by nlinarith [cal.M_large]) hx')
  · exact fun sample x hx => addedError_support (good sample) hR.le (hps sample) hx
  · filter_upwards [old.weak,hwh] with sample hwa hwh
    have hmω := hμm.comp ((measurable_const (a := sample)).prodMk measurable_id)
    have hpω := hpm.comp ((measurable_const (a := sample)).prodMk measurable_id)
    exact outwardOffset_weak (good sample) cal hR (old.locallyLipschitz_offset sample).continuous
      (hhl.locallyLipschitz sample).continuous (nonneg_bounded_locallyIntegrable hmω (hμn sample) (hμb sample))
      (nonneg_bounded_locallyIntegrable hpω (hpn sample) (hpL sample))
      (hμn sample) (hpn sample) (old.lower sample) (old.upper sample) (hhcap sample) (hinv sample) hwa hwh
  · exact fun sample x hx => outwardOffset_lower cal.B_pos.le hR cal.shift_small (good sample) (old.lower sample) hx
  · exact fun sample x hx => outwardOffset_cap cal.B_pos.le hR cal.M_large cal.shift_order (good sample)
      cal.B_le_C (cal.xi_nonneg.trans cal.low_shift.le) (old.upper sample) (hhcap sample) hx
  · exact fun sample x hx => outwardOffset_tail cal.B_pos.le cal.C_nonneg hR cal.M_large cal.shift_order cal.cap_shift
      (good sample) (old.upper sample) (fun hg y hy hy' => hhcap sample hg y (by nlinarith [cal.M_large]) hy') hx
  · have hmass := expected_mass_add (P := P)
      (q := fun sample => addedError (good sample) R (μ sample) (fun _ => 0)) hpm hqm hpb hqb hps hqs
    simp only [addedError,zero_add] at hmass ⊢
    rw [hmass]
    linarith [old.mass]

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_Conditional3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open Set Filter MeasureTheory Metric ProbabilityTheory
open scoped Topology
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis
section Conditional
variable {Ω D : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
variable [MeasurableSpace D] (P : Measure Ω) [IsProbabilityMeasure P]
variable (X : Ω → D) (hX : Measurable X)

lemma conditionalField_plus_const {u : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u)
    (c : ℝ) (d : D) (x : TFSpace) :
    c+conditionalField P X u d x = ∫ sample, c+u sample x ∂condDistrib id X P d := by
  rw [integral_add (integrable_const c) (deterministicBound_integrable_section hm hb x)]
  simp [conditionalField]

lemma conditionalField_le {u : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u)
    (c b : ℝ) (d : D) (x : TFSpace) (h : ∀ sample, c+u sample x ≤ b) :
    c+conditionalField P X u d x ≤ b := by
  rw [conditionalField_plus_const P X hm hb c d x]
  calc
    _ ≤ ∫ _ : Ω, b ∂condDistrib id X P d := integral_mono
      ((integrable_const c).add (deterministicBound_integrable_section hm hb x)) (integrable_const b) h
    _ = b := by simp

lemma le_conditionalField {u : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u)
    (c b : ℝ) (d : D) (x : TFSpace) (h : ∀ sample, b ≤ c+u sample x) :
    b ≤ c+conditionalField P X u d x := by
  rw [conditionalField_plus_const P X hm hb c d x]
  calc
    b = ∫ _ : Ω, b ∂condDistrib id X P d := by simp
    _ ≤ _ := integral_mono (integrable_const b)
      ((integrable_const c).add (deterministicBound_integrable_section hm hb x)) h

include hX

theorem IsNuclearBarrier.forget {μ a p : Ω → TFSpace → ℝ} {Z κ B C R T η : ℝ}
    (old : IsNuclearBarrier P μ Z κ B C R T η a p) (hR : 0 < R) (hκ : 0 ≤ κ)
    (hμm : Measurable (Function.uncurry μ)) (hμb : DeterministicLocalBound μ) :
    IsNuclearBarrier P (fun sample => conditionalField P X μ (X sample)) Z κ B C R T η
      (fun sample => conditionalField P X a (X sample)) (fun sample => conditionalField P X p (X sample)) := by
  obtain ⟨L,hpL⟩ := old.bounded_error
  have hpb := nonneg_bounded_deterministicBound old.nonneg_error hpL
  have hpm := old.measurable_error
  have ham := old.measurable_offset
  have hab := old.bound_offset
  refine ⟨(conditionalField_measurable P X ham).comp ((hX.comp measurable_fst).prodMk measurable_snd),
    (conditionalField_deterministicLip P X ham hab old.uniform_lipschitz_offset).comp X,
    (conditionalField_bound P X hab).comp X,
    (conditionalField_measurable P X hpm).comp ((hX.comp measurable_fst).prodMk measurable_snd),
    (fun sample x => conditionalField_nonneg P X old.nonneg_error (X sample) x),⟨L,?_⟩,
    (fun sample x hx => conditionalField_support P X old.support_error (X sample) x hx),?_,?_,?_,?_,?_⟩
  · intro sample x
    simpa only [zero_add] using conditionalField_le P X hpm hpb 0 L (X sample) x (fun t => by simpa using hpL t x)
  · have hw := weak_nuclear_conditional P X hX Z (g := fun sample => innerSource R (μ sample) (p sample)) ham hab
      (ae_of_all _ (fun sample => (old.locallyLipschitz_offset sample).continuous))
      (innerSource_measurable hμm hpm R) (innerSource_bound hμb hpb R)
      (outerCoefficient_measurable R) (outerCoefficient_bound R) (outerCoefficient_nonneg R)
      hR hκ (outerCoefficient_zero R) old.weak
    filter_upwards [ae_of_ae_map hX.aemeasurable hw] with sample hω
    apply hω.congr_source
    intro x _
    rw [conditionalField_innerSource P X hμm hμb hpm hpb R]
  · intro sample x hx
    exact le_conditionalField P X ham hab _ _ (X sample) x (fun t => old.lower t x hx)
  · intro sample x hx
    exact conditionalField_le P X ham hab _ _ (X sample) x (fun t => old.upper t x hx)
  · intro sample x hx
    apply le_antisymm
    · exact conditionalField_le P X ham hab _ _ (X sample) x (fun t => (old.tail t x hx).le)
    · exact le_conditionalField P X ham hab _ _ (X sample) x (fun t => (old.tail t x hx).ge)
  · rw [conditionalField_totalMass P X hX hpm hpb old.support_error]
    exact old.mass

end Conditional

lemma IsNuclearBarrier.congr_density {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ ν a p : Ω → TFSpace → ℝ} {Z κ B C R T η : ℝ}
    (old : IsNuclearBarrier P μ Z κ B C R T η a p) (he : ∀ᵐ sample ∂P, ∀ x, μ sample x = ν sample x) :
    IsNuclearBarrier P ν Z κ B C R T η a p := by
  refine ⟨old.measurable_offset,old.uniform_lipschitz_offset,old.bound_offset,
    old.measurable_error,old.nonneg_error,old.bounded_error,old.support_error,?_,
    old.lower,old.upper,old.tail,old.mass⟩
  filter_upwards [old.weak,he] with sample hw he
  apply hw.congr_source
  intro x _
  simp only [innerSource,he x]

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_BarrierActualMeanFieldBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter Metric
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability

lemma meanFieldOffset_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Ω → TFSpace → ℝ} (hm : Measurable (Function.uncurry ρ)) (lam : ℝ) :
    Measurable (Function.uncurry (fun sample => meanFieldOffset lam (ρ sample))) :=
  (potential_joint_measurable hm).neg.sub measurable_const

lemma meanFieldOffset_deterministicBound {Ω : Type*} {ρ : Ω → TFSpace → ℝ}
    (hm : ∀ sample, Measurable (ρ sample)) (hi : ∀ sample, Integrable (ρ sample)) {M n : ℝ}
    (hM : 0 ≤ M) (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ M)
    (hmass : ∀ sample, (∫ x, ρ sample x) = n) (lam : ℝ) :
    DeterministicLocalBound (fun sample => meanFieldOffset lam (ρ sample)) := by
  refine fun _ _ => ⟨2*Real.pi*M+n+|lam|,fun sample x _ => ?_⟩
  have hp := bounded_L1_potential_le (hm sample) (hi sample) hM (hn sample) (hb sample) x
  rw [hmass sample] at hp
  calc
    _ ≤ ‖-tfPotential (ρ sample) x‖+‖lam‖ := norm_sub_le _ _
    _ = tfPotential (ρ sample) x+|lam| := by
      rw [norm_neg,Real.norm_of_nonneg (tfPotential_nonneg (ae_of_all _ (hn sample)) x),Real.norm_eq_abs]
    _ ≤ _ := by linarith only [hp]

lemma meanFieldOffset_deterministicLip {Ω : Type*} {ρ : Ω → TFSpace → ℝ}
    (hm : ∀ sample, Measurable (ρ sample)) (hi : ∀ sample, Integrable (ρ sample)) {M n : ℝ}
    (hM : 0 ≤ M) (hn0 : 0 ≤ n) (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ M)
    (hmass : ∀ sample, (∫ x, ρ sample x) = n) (lam : ℝ) :
    DeterministicLocalLipschitz (fun sample => meanFieldOffset lam (ρ sample)) := by
  intro x
  refine ⟨⟨4*Real.pi*M+n,by positivity⟩,univ,Filter.univ_mem,fun sample => ?_⟩
  have hL := bounded_L1_potential_lipschitz (hm sample) (hi sample) hM (hn sample) (hb sample)
  have hh : LipschitzWith ⟨4*Real.pi*M+n,by positivity⟩ (tfPotential (ρ sample)) := by
    simpa only [hmass sample] using hL
  apply LipschitzWith.lipschitzOnWith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hhxy := hh.dist_le_mul x y
  change ‖(-tfPotential (ρ sample) x-lam)-(-tfPotential (ρ sample) y-lam)‖ ≤ _
  rw [show (-tfPotential (ρ sample) x-lam)-(-tfPotential (ρ sample) y-lam) = -(tfPotential (ρ sample) x-tfPotential (ρ sample) y) by ring,norm_neg]
  exact hhxy

theorem original_meanField_admissible {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (Z lam : ℝ) :
    let ρ := originalMasterField μ ell j c₁ r₀ s g
    let h := fun sample => meanFieldOffset lam (ρ sample)
    Measurable (Function.uncurry h) ∧ DeterministicLocalLipschitz h ∧
    DeterministicLocalBound h ∧ Measurable (Function.uncurry ρ) ∧
    (∀ sample x, 0 ≤ ρ sample x) ∧
    (∃ D : ℝ, 0 ≤ D ∧ ∀ sample x, ρ sample x ≤ D) ∧
    (∀ sample, WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+h sample x)
      (fun x => 4*Real.pi*ρ sample x)) := by
  dsimp only
  let ρ := originalMasterField μ ell j c₁ r₀ s g
  have hm := originalMasterField_measurable μ ell j hc hr hs hg
  have hmω (sample) : Measurable (ρ sample) := hm.comp ((measurable_const (a := sample)).prodMk measurable_id)
  have hi (sample) : Integrable (ρ sample) :=
    jointMasterPosterior_integrable μ ell j hc hr hs hg hgn (originalDatum ell j sample)
  have hn (sample x) : 0 ≤ ρ sample x :=
    jointMasterPosterior_nonneg μ ell j c₁ r₀ s g (originalDatum ell j sample) x
  have hmass (sample) : (∫ x, ρ sample x) = (N:ℝ) :=
    jointMasterPosterior_mass μ ell j hc hr hs hg hgn (originalDatum ell j sample)
  obtain ⟨D,hD,hb⟩ := jointMasterPosterior_global_bound μ ell j hc hr hs hrs hg hcg
  have hb' (sample x) : ρ sample x ≤ D :=
    (le_abs_self _).trans (by
      change |jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j sample) x| ≤ D
      simpa only [Real.norm_eq_abs] using hb (originalDatum ell j sample) x)
  exact ⟨meanFieldOffset_joint_measurable hm lam,
    meanFieldOffset_deterministicLip hmω hi hD (by positivity) hn hb' hmass lam,
    meanFieldOffset_deterministicBound hmω hi hD hn hb' hmass lam,
    hm,hn,⟨D,hD,hb'⟩,fun sample => meanFieldOffset_weak_nuclear (hmω sample) (hi sample) hD (hn sample) (hb' sample) Z lam⟩

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierOriginalForgettingBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierOriginalForgetting_barrier_scope

open Set Filter MeasureTheory Metric ProbabilityTheory
open scoped Topology

open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability

theorem IsNuclearBarrier.forget_original {N K : ℕ} (ρ : Measure (Configuration N))
    [IsProbabilityMeasure ρ] (ell : Fin K → ℝ) {j k : ℕ} (hjk : j ≤ k)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    {Z κ B C R T η : ℝ} (hR : 0 < R) (hκ : 0 ≤ κ)
    {a p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → TFSpace → ℝ}
    (old : IsNuclearBarrier (physicalObservationLaw ρ K)
      (originalMasterField ρ ell j c₁ r₀ s g) Z κ B C R T η a p) :
    IsNuclearBarrier (physicalObservationLaw ρ K) (originalMasterField ρ ell k c₁ r₀ s g)
      Z κ B C R T η
      (fun sample => conditionalField (physicalObservationLaw ρ K) (originalDatum ell k) a (originalDatum ell k sample))
      (fun sample => conditionalField (physicalObservationLaw ρ K) (originalDatum ell k) p (originalDatum ell k sample)) := by
  exact (old.forget (physicalObservationLaw ρ K) (originalDatum ell k)
    (originalDatum_measurable ell k) hR hκ
    (originalMasterField_measurable ρ ell j hc hr hs hg)
    (originalMasterField_deterministicBound ρ ell j hc hr hs hrs hg hcg)).congr_density
      (originalMasterField_tower ρ ell hjk hc hr hs hrs hg hcg)

end Work_BarrierOriginalForgetting_barrier_scope

section Work_BarrierBadMass_barrier_scope

open MeasureTheory Set Filter Metric
open scoped Topology

open CoulombAtom CoulombAnalysis CoulombObservation

lemma event_integral_le_of_square_bounds {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {f : Ω → ℝ}
    (hf : Integrable f P) (hf2 : Integrable (fun sample => (f sample)^2) P)
    (A : Set Ω) {p L : ℝ} (hp : 0 ≤ p) (hL : 0 ≤ L)
    (hprob : P.real A ≤ p^2) (hmoment : (∫ sample, (f sample)^2 ∂P) ≤ L^2) :
    (∫ sample in A, f sample ∂P) ≤ p*L := by
  by_cases hzero : P.real A = 0
  · have hz : P A = 0 := (measureReal_eq_zero_iff).mp hzero
    rw [Measure.restrict_eq_zero.mpr hz,integral_zero_measure]
    positivity
  have hpos : 0 < P.real A := lt_of_le_of_ne (measureReal_nonneg) (Ne.symm hzero)
  have hsq := event_even_moment_le f (k := 1) (by norm_num) hf (by simpa using hf2) A hpos
  norm_num only [mul_one,pow_one] at hsq
  have hbound : P.real A*(∫ sample, (f sample)^2 ∂P) ≤ p^2*L^2 :=
    mul_le_mul hprob hmoment (integral_nonneg fun sample => sq_nonneg (f sample)) (sq_nonneg p)
  have hnon : 0 ≤ p*L := mul_nonneg hp hL
  nlinarith only [hsq,hbound,hnon]

lemma bounded_density_square_data_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {ρ : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry ρ)) {D : ℝ}
    (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ D) (x : TFSpace) :
    Integrable (fun sample => (ρ sample x)^2) P := by
  apply Integrable.of_bound ((hm.comp (measurable_id.prodMk measurable_const)).pow_const 2).aestronglyMeasurable (D^2)
  exact ae_of_all _ fun sample => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hn sample x) (hb sample x) 2

theorem addedError_expected_mass_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (good : Ω → Prop) [DecidablePred good] (hg : MeasurableSet {sample | good sample})
    {ρ : Ω → TFSpace → ℝ} (hm : Measurable (Function.uncurry ρ))
    {D R p L : ℝ} (hD : 0 ≤ D) (hR : 0 < R) (hp : 0 ≤ p) (hL : 0 ≤ L)
    (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ D)
    (hprob : P.real {sample | ¬ good sample} ≤ p^2)
    (hmoment : ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < R → (∫ sample, (ρ sample x)^2 ∂P) ≤ L^2) :
    (∫ sample, (∫ x, addedError (good sample) R (ρ sample) (fun _ => 0) x) ∂P) ≤
      (4*Real.pi/3)*R^3*p*L := by
  let q (sample : Ω) (x : TFSpace) := addedError (good sample) R (ρ sample) (fun _ => 0) x
  have hqm : Measurable (Function.uncurry q) := addedError_measurable good hg (p := fun _ _ => 0) hm measurable_const R
  have hqb : DeterministicLocalBound q := nonneg_bounded_deterministicBound
    (fun sample x => addedError_nonneg (good sample) (R := R) (hn sample) (fun _ => le_refl 0) x)
    (fun sample x => by simpa only [zero_add] using addedError_le (good sample) (R := R) hD (hb sample) (fun _ => le_refl 0) x)
  have hqs : ∀ sample x, R < ‖x‖ → q sample x = 0 :=
    fun sample x hx => addedError_support (good sample) hR.le (fun _ _ => rfl) hx
  have hqi := compactBound_integrable_prod (P := P) hqm hqb hqs
  have hpi : Integrable ((ball (0 : TFSpace) R).indicator (fun _ => p*L)) volume :=
    (integrableOn_const (C := p*L) (measure_ball_lt_top.ne)).integrable_indicator measurableSet_ball
  change (∫ sample, (∫ x, q sample x) ∂P) ≤ _
  rw [integral_integral_swap hqi]
  calc
    _ ≤ ∫ x, (ball (0 : TFSpace) R).indicator (fun _ => p*L) x := by
      apply integral_mono hqi.integral_prod_right hpi
      intro x
      change (∫ sample, q sample x ∂P) ≤ (ball (0 : TFSpace) R).indicator (fun _ => p*L) x
      by_cases hx : ‖x‖ < R
      · rw [indicator_of_mem (mem_ball_zero_iff.mpr hx)]
        by_cases hx' : R/2 ≤ ‖x‖
        · have he : (fun sample => q sample x) = {sample | ¬ good sample}.indicator (fun sample => ρ sample x) := by
            funext sample
            simp only [q,addedError,ite_eq_left (show R/2 ≤ ‖x‖ ∧ ‖x‖ < R from ⟨hx',hx⟩),zero_add]
            by_cases hh : good sample <;> simp [hh]
          rw [he]
          change (∫ sample, {sample | ¬ good sample}.indicator (fun sample => ρ sample x) sample ∂P) ≤ p*L
          rw [integral_indicator (show MeasurableSet {sample | ¬ good sample} from hg.compl)]
          exact event_integral_le_of_square_bounds
            (deterministicBound_integrable_section hm (nonneg_bounded_deterministicBound hn hb) x)
            (bounded_density_square_data_integrable hm hn hb x) _ hp hL hprob (hmoment x hx' hx)
        · have he : (fun sample => q sample x) = 0 := by
            funext sample
            simp [q,addedError,hx']
          rw [he]
          change (∫ sample : Ω, (0 : ℝ) ∂P) ≤ p*L
          rw [integral_zero]
          positivity
      · rw [indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hx)]
        have he : (fun sample => q sample x) = 0 := by
          funext sample
          simp [q,addedError,hx]
        rw [he]
        change (∫ sample : Ω, (0 : ℝ) ∂P) ≤ 0
        rw [integral_zero]
    _ = _ := by
      rw [integral_indicator measurableSet_ball,setIntegral_const,smul_eq_mul]
      have hv : volume.real (ball (0 : TFSpace) R) = R^3*(Real.pi*4/3) := by
        rw [measureReal_def,EuclideanSpace.volume_ball_fin_three,ENNReal.toReal_mul,ENNReal.toReal_pow,
          ENNReal.toReal_ofReal hR.le,ENNReal.toReal_ofReal (by positivity)]
      rw [hv]
      ring

end Work_BarrierBadMass_barrier_scope

open Set Filter MeasureTheory
open scoped Topology BigOperators

open CoulombAtom CoulombAnalysis

lemma addedError_expected_mass_power {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (good : Ω → Prop) [DecidablePred good] (hg : MeasurableSet {sample | good sample})
    {ρ : Ω → TFSpace → ℝ} (hm : Measurable (Function.uncurry ρ))
    {D r A B : ℝ} (hD : 0 ≤ D) (hr : 0 < r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ D)
    (hprob : P.real {sample | ¬ good sample} ≤ A*r^(25:ℕ))
    (hmoment : ∀ x, r ≤ ‖x‖ → ‖x‖ < 2*r →
      (∫ sample, (ρ sample x)^2 ∂P) ≤ B*r^(-12-6*masterExponent)) :
    (∫ sample, (∫ x, addedError (good sample) (2*r) (ρ sample) (fun _ => 0) x) ∂P) ≤
      (32*Real.pi/3*Real.sqrt A*Real.sqrt B)*r^barrierErrorExponent := by
  have he1 : (Real.sqrt A*r^(25/2:ℝ))^2 = A*r^(25:ℕ) := by
    rw [mul_pow,Real.sq_sqrt hA,←Real.rpow_mul_natCast hr.le]
    norm_num
  have he2 : (Real.sqrt B*r^(-6-3*masterExponent))^2 = B*r^(-12-6*masterExponent) := by
    rw [mul_pow,Real.sq_sqrt hB,←Real.rpow_mul_natCast hr.le]
    congr 2
    ring
  apply (addedError_expected_mass_le good hg hm hD (by positivity)
    (p := Real.sqrt A*r^(25/2:ℝ)) (L := Real.sqrt B*r^(-6-3*masterExponent))
    (by positivity) (by positivity) hn hb (by rwa [he1])
    (fun x hx hx' => by rw [he2]; exact hmoment x (by linarith) hx')).trans_eq
  calc
    (4*Real.pi/3)*(2*r)^3*(Real.sqrt A*r^(25/2:ℝ))*(Real.sqrt B*r^(-6-3*masterExponent)) =
        (32*Real.pi/3*Real.sqrt A*Real.sqrt B)*((r^(3:ℝ)*r^(25/2:ℝ))*r^(-6-3*masterExponent)) := by
          rw [show r^(3:ℝ) = r^(3:ℕ) by exact_mod_cast Real.rpow_natCast r 3]
          ring
    _ = _ := by
      rw [←Real.rpow_add hr,←Real.rpow_add hr]
      congr 2
      dsimp only [barrierErrorExponent]
      ring

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierQuantitativeStepBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierQuantitativeStep_barrier_scope

open Set Filter MeasureTheory Metric ProbabilityTheory
open scoped Topology

open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability

lemma IsNuclearBarrier.mono_budget {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {μ a p : Ω → TFSpace → ℝ} {Z k B C r T η η' : ℝ}
    (old : IsNuclearBarrier P μ Z k B C r T η a p) (hη : η ≤ η') :
    IsNuclearBarrier P μ Z k B C r T η' a p :=
  { old with mass := old.mass.trans hη }

lemma IsNuclearBarrier.mono_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {μ a p : Ω → TFSpace → ℝ} {Z k B C r T T' η : ℝ}
    (old : IsNuclearBarrier P μ Z k B C r T η a p) (hr : 0 ≤ r) (hT : T ≤ T') :
    IsNuclearBarrier P μ Z k B C r T' η a p := by
  refine { old with tail := fun sample x hx => old.tail sample x ?_ }
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hT hr) hx

theorem original_quantitative_barrier_step {N K : ℕ} (μ : Measure (Configuration N))
    [IsProbabilityMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1)
    {Z κ B C r M lam1 lam2 e ξ Cinv hl hh T η A Q lam : ℝ}
    (cal : OutwardCalibration κ B C M lam1 lam2 e ξ hl hh) (hr : 0 < r)
    (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (good : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → Prop)
    [DecidablePred good] (hgood : MeasurableSet {sample | good sample})
    {a p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → TFSpace → ℝ}
    (old : IsNuclearBarrier (physicalObservationLaw μ K)
      (originalMasterField μ ell j c₁ r₀ s g) Z κ B C r T η a p)
    (hcap : ∀ sample, good sample → ∀ x, r ≤ ‖x‖ → ‖x‖ < 4*M*r →
      nuclearField Z x+meanFieldOffset lam (originalMasterField μ ell j c₁ r₀ s g sample) x ≤ C/‖x‖^4)
    (hinv : ∀ sample, good sample → ∀ x, r ≤ ‖x‖ → ‖x‖ < 4*M*r →
      InverseComparisonAt ‖x‖
        (nuclearField Z x+meanFieldOffset lam (originalMasterField μ ell j c₁ r₀ s g sample) x)
        (originalMasterField μ ell j c₁ r₀ s g sample x) κ hl hh ξ Cinv)
    (hprob : (physicalObservationLaw μ K).real {sample | ¬good sample} ≤ A*r^25)
    (hmoment : ∀ x, r ≤ ‖x‖ → ‖x‖ < 2*r →
      (∫ sample, (originalMasterField μ ell j c₁ r₀ s g sample x)^2 ∂physicalObservationLaw μ K) ≤
        Q*r^(-12-6*masterExponent)) :
    ∃ a' p', IsNuclearBarrier (physicalObservationLaw μ K)
      (originalMasterField μ ell (j+1) c₁ r₀ s g) Z κ B C (2*r) M
      (η+(32*Real.pi/3*Real.sqrt A*Real.sqrt Q)*r^barrierErrorExponent) a' p' := by
  obtain ⟨hm,hlip,hbound,hρm,hρn,⟨D,hD,hρb⟩,hweak⟩ :=
    original_meanField_admissible μ ell j hc hr₀ hs hrs hg hcg hgn Z lam
  have hstep := outward_barrier_invariant good hgood cal (by positivity : 0 < 2*r)
    (by simpa only [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)] using old)
    hm hlip hbound hρm hρn hD hρb
    (fun sample hg x hx hx' => hcap sample hg x (by linarith) (by nlinarith))
    (fun sample hg x hx hx' => hinv sample hg x (by linarith) (by nlinarith))
    (ae_of_all _ fun sample _ => hweak sample)
  have hmass := addedError_expected_mass_power good hgood hρm hD hr hA hQ hρn hρb hprob hmoment
  have hstep' := hstep.mono_budget
    (η' := η+(32*Real.pi/3*Real.sqrt A*Real.sqrt Q)*r^barrierErrorExponent)
    (by linarith only [hmass])
  have hnew := hstep'.forget_original
    μ ell (Nat.le_succ j) hc hr₀ hs hrs hg hcg (by positivity) cal.k_nonneg
  exact ⟨_,_,hnew⟩

end Work_BarrierQuantitativeStep_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom CoulombAnalysis

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierActualInitializationBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability

theorem original_finite_barrier_iteration_oai {N K J : ℕ} (μ : Measure (Configuration N))
    [IsProbabilityMeasure μ] (ell : Fin K → ℝ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1)
    {Z κ B C M lam1 lam2 e ξ Cinv hl hh T η A Q lam : ℝ}
    (cal : OutwardCalibration κ B C M lam1 lam2 e ξ hl hh)
    (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (good : ℕ → (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → Prop)
    [∀ j, DecidablePred (good j)] (hgood : ∀ j < J, MeasurableSet {sample | good j sample})
    {a p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → TFSpace → ℝ}
    (initial : IsNuclearBarrier (physicalObservationLaw μ K)
      (originalMasterField μ ell 0 c₁ r₀ s g) Z κ B C r₀ T η a p)
    (hcap : ∀ j < J, ∀ sample, good j sample → ∀ x, (2:ℝ)^j*r₀ ≤ ‖x‖ → ‖x‖ < 4*M*((2:ℝ)^j*r₀) →
      nuclearField Z x+meanFieldOffset lam (originalMasterField μ ell j c₁ r₀ s g sample) x ≤ C/‖x‖^4)
    (hinv : ∀ j < J, ∀ sample, good j sample → ∀ x, (2:ℝ)^j*r₀ ≤ ‖x‖ → ‖x‖ < 4*M*((2:ℝ)^j*r₀) →
      InverseComparisonAt ‖x‖
        (nuclearField Z x+meanFieldOffset lam (originalMasterField μ ell j c₁ r₀ s g sample) x)
        (originalMasterField μ ell j c₁ r₀ s g sample x) κ hl hh ξ Cinv)
    (hprob : ∀ j < J, (physicalObservationLaw μ K).real {sample | ¬good j sample} ≤ A*((2:ℝ)^j*r₀)^25)
    (hmoment : ∀ j < J, ∀ x, (2:ℝ)^j*r₀ ≤ ‖x‖ → ‖x‖ < 2*((2:ℝ)^j*r₀) →
      (∫ sample, (originalMasterField μ ell j c₁ r₀ s g sample x)^2 ∂physicalObservationLaw μ K) ≤
        Q*((2:ℝ)^j*r₀)^(-12-6*masterExponent)) :
    ∃ a' p', IsNuclearBarrier (physicalObservationLaw μ K)
      (originalMasterField μ ell J c₁ r₀ s g) Z κ B C ((2:ℝ)^J*r₀) (max T M)
      (η+∑ j ∈ Finset.range J, (32*Real.pi/3*Real.sqrt A*Real.sqrt Q)*
        ((2:ℝ)^j*r₀)^barrierErrorExponent) a' p' := by
  have hall : ∀ j ≤ J, ∃ a' p', IsNuclearBarrier (physicalObservationLaw μ K)
      (originalMasterField μ ell j c₁ r₀ s g) Z κ B C ((2:ℝ)^j*r₀) (max T M)
      (η+∑ i ∈ Finset.range j, (32*Real.pi/3*Real.sqrt A*Real.sqrt Q)*
        ((2:ℝ)^i*r₀)^barrierErrorExponent) a' p' := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨a,p,by simpa only [pow_zero,one_mul,Finset.sum_range_zero,add_zero] using
        initial.mono_tail hr₀.le (le_max_left T M)⟩
    | succ j ih =>
      intro hj
      have hjJ : j < J := Nat.lt_of_succ_le hj
      obtain ⟨aj,pj,hjbar⟩ := ih (Nat.le_of_lt hjJ)
      obtain ⟨a',p',hnew⟩ := original_quantitative_barrier_step μ ell j hc hr₀ hs hrs hg hcg hgn
        cal (by positivity : 0 < (2:ℝ)^j*r₀) hA hQ (good j) (hgood j hjJ) hjbar
        (hcap j hjJ) (hinv j hjJ) (hprob j hjJ) (hmoment j hjJ)
      refine ⟨a',p',?_⟩
      have hnew' := hnew.mono_tail (by positivity : 0 ≤ 2*((2:ℝ)^j*r₀)) (le_max_right T M)
      convert hnew' using 1 <;> simp only [Finset.sum_range_succ,pow_succ] <;> ring
  exact hall J le_rfl

end CoulombBarrier

end

end OAI
end

theorem solution : type_of% @OAI.CoulombBarrier.original_finite_barrier_iteration_oai := @OAI.CoulombBarrier.original_finite_barrier_iteration_oai
