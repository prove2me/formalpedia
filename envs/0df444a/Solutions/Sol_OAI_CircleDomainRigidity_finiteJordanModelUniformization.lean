-- Prove2me | solution 1 for OAI.CircleDomainRigidity.finiteJordanModelUniformization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T06:10:18.529784+00:00
-- url     : https://prove2.me/submissions/5d4ed357-cff1-499c-9253-e981feb0c024

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C011
import Theorems.Thm_OAI_CircleDomainRigidity_exists_round_invariant_principal_approximation_with_coefficient

section
-- module Solutions.Q146_CD.Cannon_Beltrami_MultiplyLp
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section
section
section
section
section
section
section
section
section
section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace CannonBeltrami

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma multiplier_ae (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) (f : Lp ℂ 2 ν) :
    multiplier m hm hk hb f =ᵐ[ν] fun x => m x*f x := multiplyLp_ae m hm hb f

open FourierTransform

lemma translateL2_ae (a : ℂ) (f : PlaneL2) :
    translateL2 a f =ᵐ[volume] fun z => f (z+a) :=
  Lp.coeFn_compMeasurePreserving _ _

lemma translate_schwartz (a : ℂ) (f : SchwartzMap ℂ ℂ) :
    translateL2 a (f.toLp 2)=(f.compSubConstCLM ℂ (-a)).toLp 2 := by
  change Lp.compMeasurePreserving _ _ ((f.memLp 2 volume).toLp f)=_
  rw [Lp.toLp_compMeasurePreserving]
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp ((f.memLp 2 volume).comp_measurePreserving
    (measurePreserving_add_right volume a)),(f.compSubConstCLM ℂ (-a)).coeFn_toLp 2 volume] with z h1 h2
  rw [h1,h2]
  simp

lemma fourier_translate_schwartz (a : ℂ) (f : SchwartzMap ℂ ℂ) :
    planeFourier (translateL2 a (f.toLp 2))=phaseMultiplier a (planeFourier (f.toLp 2)) := by
  rw [translate_schwartz]
  change 𝓕 ((f.compSubConstCLM ℂ (-a)).toLp 2)=phaseMultiplier a (𝓕 (f.toLp 2))
  rw [SchwartzMap.toLp_fourier_eq,SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (f.compSubConstCLM ℂ (-a))).coeFn_toLp 2 volume,
    multiplier_ae (translationPhase a) (continuous_translationPhase a).aestronglyMeasurable
      zero_le_one (.of_forall fun z => (norm_translationPhase a z).le) ((𝓕 f).toLp 2),
    (𝓕 f).coeFn_toLp 2 volume] with z h1 h2 h3
  dsimp only [phaseMultiplier]
  rw [h1,h2,h3]
  have he := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ ℂ) (f : ℂ → ℂ) a) z
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℂ)
    (fun z => f (z- -a)) z = translationPhase a z*
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℂ) (f : ℂ → ℂ) z
  simpa only [Function.comp_def,translationPhase,innerₗ_apply_apply,
    sub_neg_eq_add,Circle.smul_def,smul_eq_mul] using he

lemma fourier_translateL2 (a : ℂ) (f : PlaneL2) :
    planeFourier (translateL2 a f)=phaseMultiplier a (planeFourier f) := by
  have he := (SchwartzMap.denseRange_toLpCLM (E:=ℂ) (F:=ℂ) (μ:=volume)
    (p:=2) (by norm_num)).equalizer
      (planeFourier.continuous.comp (translateL2 a).continuous)
      ((phaseMultiplier a).continuous.comp planeFourier.continuous)
      (funext (fun s => fourier_translate_schwartz a s))
  exact congrFun he f

lemma multipliers_commute (m n : ℂ → ℂ)
    (hm : AEStronglyMeasurable m volume) (hn : AEStronglyMeasurable n volume)
    {k l : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l)
    (hb : ∀ᵐ z ∂volume, ‖m z‖ ≤ k) (hc : ∀ᵐ z ∂volume, ‖n z‖ ≤ l) (f : PlaneL2) :
    multiplier m hm hk hb (multiplier n hn hl hc f)=
      multiplier n hn hl hc (multiplier m hm hk hb f) := by
  apply Lp.ext
  filter_upwards [multiplier_ae m hm hk hb (multiplier n hn hl hc f),
    multiplier_ae n hn hl hc (multiplier m hm hk hb f),
    multiplier_ae m hm hk hb f,multiplier_ae n hn hl hc f] with z h1 h2 h3 h4
  rw [h1,h2,h3,h4,mul_left_comm]

lemma translate_beurling (a : ℂ) (f : PlaneL2) :
    translateL2 a (beurling f)=beurling (translateL2 a f) := by
  apply planeFourier.injective
  have hf (g : PlaneL2) : planeFourier (beurling g)=symbolMultiplier (planeFourier g) :=
    planeFourier.apply_symm_apply _
  rw [fourier_translateL2,hf,hf,fourier_translateL2]
  exact multipliers_commute _ _ _ _ _ _ _ _ _

lemma continuous_directionSymbol (v : ℂ) : Continuous (directionSymbol v) := by
  unfold directionSymbol
  fun_prop

lemma translationPhase_derivative (v z : ℂ) :
    HasDerivAt (fun t : ℝ => translationPhase (t • v) z) (directionSymbol v z) 0 := by
  have h := (Real.hasDerivAt_fourierChar (0*(inner ℝ v z))).scomp 0
    ((hasDerivAt_id (0:ℝ)).mul_const (inner ℝ v z))
  simpa [translationPhase,directionSymbol,inner_smul_left,Complex.real_smul,
    Function.comp_def,mul_comm,mul_left_comm,mul_assoc,mul_add] using h

lemma translationPhase_slope (v z : ℂ) :
    Tendsto (fun t : ℝ => t⁻¹ • (translationPhase (t • v) z-1))
      (𝓝[≠] 0) (𝓝 (directionSymbol v z)) := by
  simpa [translationPhase] using (translationPhase_derivative v z).tendsto_slope_zero

theorem memLp_directionSymbol_of_translation_bound (f : PlaneL2)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ a : ℂ, ‖translateL2 a f-f‖ ≤ C*‖a‖) (v : ℂ) :
    MemLp (fun z => directionSymbol v z*planeFourier f z) 2 volume ∧
      eLpNorm (fun z => directionSymbol v z*planeFourier f z) 2 volume ≤
        ENNReal.ofReal (C*‖v‖) := by
  let q (t : ℝ) : PlaneL2 := t⁻¹ • (planeFourier (translateL2 (t • v) f)-planeFourier f)
  let F (t : ℝ) (z : ℂ) := (t⁻¹ • (translationPhase (t • v) z-1))*planeFourier f z
  have hnorm (t : ℝ) : ‖q t‖ ≤ C*‖v‖ := by
    by_cases ht : t=0
    · simp [q,ht,mul_nonneg hC (norm_nonneg v)]
    · calc
        ‖q t‖ = |t|⁻¹*‖translateL2 (t • v) f-f‖ := by
          simp only [q,norm_smul,Real.norm_eq_abs,abs_inv,← map_sub,planeFourier.norm_map]
        _ ≤ |t|⁻¹*(C*‖t • v‖) :=
          mul_le_mul_of_nonneg_left (hb (t • v)) (inv_nonneg.mpr (abs_nonneg _))
        _ = C*‖v‖ := by
          rw [norm_smul,Real.norm_eq_abs]
          field_simp
  have hae (t : ℝ) : q t =ᵐ[volume] F t := by
    have ht := fourier_translateL2 (t • v) f
    filter_upwards [Lp.coeFn_smul (t⁻¹) (planeFourier (translateL2 (t • v) f)-planeFourier f),
      Lp.coeFn_sub (planeFourier (translateL2 (t • v) f)) (planeFourier f),
      multiplier_ae (translationPhase (t • v)) _ zero_le_one
        (.of_forall fun z => (norm_translationPhase (t • v) z).le) (planeFourier f)] with z h1 h2 h3
    dsimp only [q,F]
    simp only [Pi.smul_apply,Pi.sub_apply] at h1 h2
    rw [h1,h2,ht]
    change t⁻¹ • (phaseMultiplier (t • v) (planeFourier f) z-planeFourier f z)=_
    dsimp only [phaseMultiplier]
    rw [h3]
    simp only [smul_mul_assoc,sub_mul,one_mul]
  have hFm (t : ℝ) : AEStronglyMeasurable (F t) volume :=
    ((Lp.memLp (q t)).aestronglyMeasurable.congr (hae t))
  have hbound : ∀ t, eLpNorm (F t) 2 volume ≤ ENNReal.ofReal (C*‖v‖) := by
    intro t
    rw [← eLpNorm_congr_ae (hae t),← Lp.enorm_def,← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hnorm t)
  have hlim : ∀ᵐ z ∂volume, Tendsto (fun t : ℝ => F t z) (𝓝[≠] 0)
      (𝓝 (directionSymbol v z*planeFourier f z)) := by
    exact .of_forall fun z => (translationPhase_slope v z).mul_const (planeFourier f z)
  have hmeas := (continuous_directionSymbol v).aestronglyMeasurable.mul
    (Lp.memLp (planeFourier f)).aestronglyMeasurable
  have he := Lp.eLpNorm_le_of_ae_tendsto (.of_forall hbound) hFm hlim
  exact ⟨⟨hmeas, he.trans_lt ENNReal.ofReal_lt_top⟩,he⟩

open scoped ENNReal

lemma dominated_toLp_zero_filter {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → X → ℂ} (hf : ∀ n, MemLp (f n) 2 ν)
    {g : X → ℂ} (hg : MemLp g 2 ν)
    (hb : ∀ n, ∀ᵐ x ∂ν, ‖f n x‖ ≤ ‖g x‖)
    (hl : ∀ᵐ x ∂ν, Tendsto (fun n => f n x) l (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) l (𝓝 0) := by
  have hb' : ∀ n, (fun x => ‖f n x‖ₑ ^ (2:ℝ)) ≤ᵐ[ν] (fun x => ‖g x‖ₑ ^ (2:ℝ)) := by
    intro n
    filter_upwards [hb n] with x hx
    exact ENNReal.rpow_le_rpow (ENNReal.coe_le_coe.mpr hx) (by norm_num)
  have hfin : (∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂ν) ≠ ⊤ := by
    exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num) hg.2).ne
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun n => ‖f n x‖ₑ ^ (2:ℝ)) l (𝓝 (0:ℝ≥0∞)) := by
    filter_upwards [hl] with x hx
    have hc : Continuous (fun t : ℝ≥0∞ => t^(2:ℝ)) := ENNReal.continuous_rpow_const
    simpa only [Function.comp_def,enorm, nnnorm_zero, ENNReal.coe_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ)<2)] using
      hc.continuousAt.tendsto.comp (ENNReal.tendsto_coe.mpr hx.nnnorm)
  have hi := tendsto_lintegral_filter_of_dominated_convergence' _
    (.of_forall fun n => (hf n).aestronglyMeasurable.enorm.pow_const (2:ℝ))
    (.of_forall hb') hfin hlim
  have heLp : Tendsto (fun n => eLpNorm (f n) 2 ν) l (𝓝 0) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num : (2:ℝ≥0∞) ≠ ⊤)]
    have hc : Continuous (fun t : ℝ≥0∞ => t^(1/2:ℝ)) := ENNReal.continuous_rpow_const
    simpa [Function.comp_def] using hc.continuousAt.tendsto.comp hi
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf (0 : X → ℂ) (MemLp.zero : MemLp (0 : X → ℂ) 2 ν)).mpr
    (by simpa using heLp)
  simpa using h

lemma phase_slope_norm_le (v z : ℂ) (t : ℝ) :
    ‖t⁻¹ • (translationPhase (t • v) z-1)‖ ≤ ‖directionSymbol v z‖ := by
  by_cases ht : t=0
  · simp [ht]
  have he : translationPhase (t • v) z=
      Complex.exp (Complex.I*((2*Real.pi*(t*(inner ℝ v z)):ℝ):ℂ)) := by
    simp [translationPhase,Real.fourierChar_apply,
      mul_comm,mul_left_comm,mul_assoc,mul_add,add_mul]
  have hh := Real.norm_exp_I_mul_ofReal_sub_one_le (x:=2*Real.pi*(t*(inner ℝ v z)))
  rw [← he] at hh
  rw [norm_smul,Real.norm_eq_abs,abs_inv]
  calc
    |t|⁻¹*‖translationPhase (t • v) z-1‖ ≤
        |t|⁻¹*‖2*Real.pi*(t*(inner ℝ v z))‖ :=
      mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (abs_nonneg _))
    _ = ‖directionSymbol v z‖ := by
      simp only [directionSymbol,norm_mul,Complex.norm_I,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0:ℝ)<2),mul_one]
      norm_num
      field_simp

lemma fourier_difference_quotient_ae (f : PlaneL2) (v : ℂ) (t : ℝ) :
    (t⁻¹ • (planeFourier (translateL2 (t • v) f)-planeFourier f) : PlaneL2) =ᵐ[volume]
      fun z => (t⁻¹ • (translationPhase (t • v) z-1))*planeFourier f z := by
  have ht := fourier_translateL2 (t • v) f
  filter_upwards [Lp.coeFn_smul (t⁻¹) (planeFourier (translateL2 (t • v) f)-planeFourier f),
    Lp.coeFn_sub (planeFourier (translateL2 (t • v) f)) (planeFourier f),
    multiplier_ae (translationPhase (t • v)) _ zero_le_one
      (.of_forall fun z => (norm_translationPhase (t • v) z).le) (planeFourier f)] with z h1 h2 h3
  simp only [Pi.smul_apply,Pi.sub_apply] at h1 h2
  rw [h1,h2,ht]
  dsimp only [phaseMultiplier]
  rw [h3]
  simp only [smul_mul_assoc,sub_mul,one_mul]

lemma translateL2_zero (f : PlaneL2) : translateL2 0 f=f := by
  apply Lp.ext
  simpa using translateL2_ae 0 f

theorem hasDerivAt_translateL2 (f : PlaneL2) (v : ℂ)
    (hd : MemLp (fun z => directionSymbol v z*planeFourier f z) 2 volume) :
    HasDerivAt (fun t : ℝ => translateL2 (t • v) f)
      (planeFourier.symm (hd.toLp (fun z => directionSymbol v z*planeFourier f z))) 0 := by
  let g (z : ℂ) := directionSymbol v z*planeFourier f z
  let F (t : ℝ) (z : ℂ) := (t⁻¹ • (translationPhase (t • v) z-1))*planeFourier f z
  let q (t : ℝ) : PlaneL2 := t⁻¹ • (planeFourier (translateL2 (t • v) f)-planeFourier f)
  have hae (t : ℝ) : q t =ᵐ[volume] F t := fourier_difference_quotient_ae f v t
  have hF (t : ℝ) : MemLp (F t) 2 volume := MemLp.ae_eq (hae t) (Lp.memLp (q t))
  have hE (t : ℝ) : (hF t).toLp (F t)=q t := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp (hF t)).trans (hae t).symm
  have hdom (t : ℝ) : ∀ᵐ z ∂volume, ‖(F t-g) z‖ ≤ ‖(2:ℂ)*g z‖ := by
    apply Filter.Eventually.of_forall
    intro z
    change ‖F t z-g z‖ ≤ ‖(2:ℂ)*g z‖
    calc
      ‖F t z-g z‖ ≤ ‖F t z‖+‖g z‖ := norm_sub_le _ _
      _ ≤ ‖directionSymbol v z‖*‖planeFourier f z‖+‖g z‖ := by
        gcongr
        exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_right
          (phase_slope_norm_le v z t) (norm_nonneg _))
      _ = ‖(2:ℂ)*g z‖ := by simp [g] <;> ring
  have hlim : ∀ᵐ z ∂volume, Tendsto (fun t : ℝ => (F t-g) z) (𝓝[≠] 0) (𝓝 0) := by
    exact .of_forall fun z => by
      simpa only [F,g,Pi.sub_apply,sub_self] using
        ((translationPhase_slope v z).mul_const (planeFourier f z)).sub_const (g z)
  have hzero := dominated_toLp_zero_filter (fun t => (hF t).sub hd)
    (hd.const_mul (2:ℂ)) hdom hlim
  change Tendsto (fun t => (hF t).toLp (F t)-hd.toLp g) (𝓝[≠] 0) (𝓝 0) at hzero
  simp only [hE] at hzero
  have ht : Tendsto q (𝓝[≠] 0) (𝓝 (hd.toLp g)) := by
    simpa using hzero.add_const (hd.toLp g)
  have hi := planeFourier.symm.continuous.continuousAt.tendsto.comp ht
  have hsmul (t : ℝ) (x : PlaneL2) : planeFourier.symm (t • x)=t • planeFourier.symm x :=
    planeFourier.symm.toLinearEquiv.toLinearMap.map_smul_of_tower t x
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [Function.comp_def,q,zero_add,zero_smul,translateL2_zero,
    hsmul,map_sub,planeFourier.symm_apply_apply] using hi

end CannonBeltrami

end
end
end
end
end
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
-- module Solutions.Q146_CD.Cannon_Conformal_Sphere
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonSphereReflection
open Set Metric Topology
open scoped OnePoint

lemma onePoint_image (h : ℂ≃ₜℂ) (A : Set ℂ) :
    h.onePointCongr '' ((↑) '' A : Set S)=((↑) '' (h '' A) : Set S) := by
  rw [image_image,image_image]
  rfl

end CannonSphereReflection

end
end
end
end

end OAI
end

section
-- module Solutions.Q146_CD.Cannon_Beltrami_Axis
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace CannonBeltrami

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

open FourierTransform
open scoped ENNReal

lemma multiplier_strong_convergence_filter {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (μ : ι → ℂ → ℂ) (ν : ℂ → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (μ n) volume) (hn : AEStronglyMeasurable ν volume)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ n, ∀ᵐ z ∂volume, ‖μ n z‖ ≤ k)
    (hc : ∀ᵐ z ∂volume, ‖ν z‖ ≤ k)
    (ht : ∀ᵐ z ∂volume, Tendsto (fun n => μ n z) l (𝓝 (ν z))) (f : PlaneL2) :
    Tendsto (fun n => multiplier (μ n) (hm n) hk (hb n) f) l
      (𝓝 (multiplier ν hn hk hc f)) := by
  let Q (n : ι) := multiplier (μ n) (hm n) hk (hb n) f-multiplier ν hn hk hc f
  let F (n : ι) (z : ℂ) := (μ n z-ν z)*f z
  have he (n : ι) : Q n =ᵐ[volume] F n := by
    filter_upwards [Lp.coeFn_sub (multiplier (μ n) (hm n) hk (hb n) f)
      (multiplier ν hn hk hc f),multiplier_ae (μ n) (hm n) hk (hb n) f,
      multiplier_ae ν hn hk hc f] with z h1 h2 h3
    dsimp only [Q,F]
    simp only [Pi.sub_apply] at h1
    rw [h1,h2,h3,sub_mul]
  have hF (n : ι) : MemLp (F n) 2 volume := MemLp.ae_eq (he n) (Lp.memLp (Q n))
  have hdom (n : ι) : ∀ᵐ z ∂volume, ‖F n z‖ ≤ ‖((2*k:ℝ):ℂ)*f z‖ := by
    filter_upwards [hb n,hc] with z h2 h3
    dsimp only [F]
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by norm_num) hk)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by linarith)
  have hlim : ∀ᵐ z ∂volume, Tendsto (fun n => F n z) l (𝓝 0) := by
    filter_upwards [ht] with z h2
    simpa only [F,sub_self,zero_mul] using (h2.sub_const (ν z)).mul_const (f z)
  have H := dominated_toLp_zero_filter hF
    ((Lp.memLp f).const_mul ((2*k:ℝ):ℂ)) hdom hlim
  have hE (n : ι) : (hF n).toLp (F n)=Q n := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp (hF n)).trans (he n).symm
  simp only [hE] at H
  exact (tendsto_sub_nhds_zero_iff).mp H

lemma multiplier_variable_convergence {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (μ : ι → ℂ → ℂ) (ν : ℂ → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (μ n) volume) (hn : AEStronglyMeasurable ν volume)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ n, ∀ᵐ z ∂volume, ‖μ n z‖ ≤ k)
    (hc : ∀ᵐ z ∂volume, ‖ν z‖ ≤ k)
    (ht : ∀ᵐ z ∂volume, Tendsto (fun n => μ n z) l (𝓝 (ν z)))
    (f : ι → PlaneL2) (g : PlaneL2) (hf : Tendsto f l (𝓝 g)) :
    Tendsto (fun n => multiplier (μ n) (hm n) hk (hb n) (f n)) l
      (𝓝 (multiplier ν hn hk hc g)) := by
  have hzero : Tendsto (fun n => multiplier (μ n) (hm n) hk (hb n) (f n-g)) l (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => norm_multiplyLp_le (μ n) (hm n) hk (hb n) (f n-g))
    simpa using (hf.sub_const g).norm.const_mul k
  have hconst := multiplier_strong_convergence_filter μ ν hm hn hk hb hc ht g
  simpa only [map_sub,sub_add_cancel,zero_add] using hzero.add hconst

lemma translateL2_comp (a b : ℂ) (f : PlaneL2) :
    translateL2 a (translateL2 b f)=translateL2 (a+b) f := by
  apply Lp.ext
  filter_upwards [translateL2_ae a (translateL2 b f),
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp (translateL2_ae b f),
    translateL2_ae (a+b) f] with z h1 h2 h3
  simp only [Function.comp_def] at h2
  rw [h1,h2,h3,add_assoc]

lemma hasDerivAt_translateL2_at (f f' : PlaneL2) (v : ℂ)
    (hf : HasDerivAt (fun t : ℝ => translateL2 (t • v) f) f' 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => translateL2 (s • v) f) (translateL2 (t • v) f') t := by
  have ht : Tendsto (fun s : ℝ => s⁻¹ • (translateL2 (s • v) f-f))
      (𝓝[≠] 0) (𝓝 f') := by
    simpa only [zero_add,zero_smul,translateL2_zero] using hf.tendsto_slope_zero
  have hmap := (translateL2 (t • v)).continuous.continuousAt.tendsto.comp ht
  have he (s : ℝ) : translateL2 (t • v) (s⁻¹ • (translateL2 (s • v) f-f))=
      s⁻¹ • (translateL2 ((t+s) • v) f-translateL2 (t • v) f) := by
    have hsmul : translateL2 (t • v) (s⁻¹ • (translateL2 (s • v) f-f))=
        s⁻¹ • translateL2 (t • v) (translateL2 (s • v) f-f) :=
      (translateL2 (t • v)).toLinearMap.map_smul_of_tower _ _
    rw [hsmul,map_sub,translateL2_comp,← add_smul]
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [Function.comp_def,he] using hmap

lemma translation_line_bound (f f' : PlaneL2) (v : ℂ)
    (hf : HasDerivAt (fun t : ℝ => translateL2 (t • v) f) f' 0) (t : ℝ) :
    ‖translateL2 (t • v) f-f‖ ≤ ‖f'‖*|t| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s (_ : s ∈ (Set.univ : Set ℝ)) => (hasDerivAt_translateL2_at f f' v hf s).hasDerivWithinAt)
    (fun s (_ : s ∈ (Set.univ : Set ℝ)) => (translateL2 (s • v)).norm_map f' |>.le)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ (0:ℝ)) (Set.mem_univ t)
  simpa only [zero_smul,translateL2_zero,sub_zero,Real.norm_eq_abs] using hh

theorem translation_bound_of_coordinate_derivatives (f fx fy : PlaneL2)
    (hx : HasDerivAt (fun t : ℝ => translateL2 (t • (1:ℂ)) f) fx 0)
    (hy : HasDerivAt (fun t : ℝ => translateL2 (t • Complex.I) f) fy 0) (a : ℂ) :
    ‖translateL2 a f-f‖ ≤ (‖fx‖+‖fy‖)*‖a‖ := by
  have ha : a=(a.re : ℝ) • (1:ℂ)+(a.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  have he : ‖translateL2 a f-translateL2 (a.re • (1:ℂ)) f‖=
      ‖translateL2 (a.im • Complex.I) f-f‖ := by
    rw [show translateL2 a f = translateL2 (a.re • 1) (translateL2 (a.im • Complex.I) f) by
      rw [translateL2_comp, ← ha], ← map_sub]
    exact (translateL2 (a.re • (1:ℂ))).norm_map _
  calc
    ‖translateL2 a f-f‖ ≤ ‖translateL2 a f-translateL2 (a.re • (1:ℂ)) f‖+
        ‖translateL2 (a.re • (1:ℂ)) f-f‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖translateL2 (a.im • Complex.I) f-f‖+‖translateL2 (a.re • (1:ℂ)) f-f‖ := by rw [he]
    _ ≤ ‖fy‖*|a.im|+‖fx‖*|a.re| :=
      add_le_add (translation_line_bound f fy Complex.I hy a.im)
        (translation_line_bound f fx 1 hx a.re)
    _ ≤ (‖fx‖+‖fy‖)*‖a‖ := by
      nlinarith [mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm a) (norm_nonneg fy),
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm a) (norm_nonneg fx)]

lemma Sobolev.add {n : ℕ} {f g : PlaneL2} (hf : Sobolev n f) (hg : Sobolev n g) :
    Sobolev n (f+g) := by
  induction n generalizing f g with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih hf.1 hg.1, fun b => ?_⟩
    obtain ⟨df, hdf, hrf⟩ := hf.2 b
    obtain ⟨dg, hdg, hrg⟩ := hg.2 b
    refine ⟨df+dg, ?_, ih hrf hrg⟩
    convert hdf.add hdg using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
    funext t
    exact map_add (translateL2 (t • axis b)) f g

lemma hasDerivAt_translate_beurling {f df : PlaneL2} {v : ℂ}
    (hf : HasDerivAt (fun t : ℝ => translateL2 (t • v) f) df 0) :
    HasDerivAt (fun t : ℝ => translateL2 (t • v) (beurling f)) (beurling df) 0 := by
  have ht := (beurling.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hf
  change HasDerivAt (fun t : ℝ => beurling (translateL2 (t • v) f)) (beurling df) 0 at ht
  simpa only [translate_beurling] using ht

lemma Sobolev.beurling {n : ℕ} {f : PlaneL2} (hf : Sobolev n f) :
    Sobolev n (beurling f) := by
  induction n generalizing f with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih hf.1, fun b => ?_⟩
    obtain ⟨df, hdf, hrf⟩ := hf.2 b
    exact ⟨CannonBeltrami.beurling df, hasDerivAt_translate_beurling hdf, ih hrf⟩

lemma Sobolev.translation_bound {n : ℕ} {f : PlaneL2} (hf : Sobolev (n+1) f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : ℂ, ‖translateL2 a f-f‖ ≤ B*‖a‖ := by
  obtain ⟨fx,hx,_⟩ := hf.2 false
  obtain ⟨fy,hy,_⟩ := hf.2 true
  refine ⟨‖fx‖+‖fy‖, add_nonneg (norm_nonneg _) (norm_nonneg _), ?_⟩
  exact translation_bound_of_coordinate_derivatives f fx fy hx hy

open scoped SchwartzMap LineDeriv FourierTransform

lemma fourier_schwartz_derivative_ae (f : SchwartzMap ℂ ℂ) (v : ℂ) :
    planeFourier ((∂_{v} f).toLp 2) =ᵐ[volume]
      fun z => directionSymbol v z*planeFourier (f.toLp 2) z := by
  have hd : planeFourier ((∂_{v} f).toLp 2)=(𝓕 (∂_{v} f)).toLp 2 :=
    SchwartzMap.toLp_fourier_eq _
  have hf : planeFourier (f.toLp 2)=(𝓕 f).toLp 2 := SchwartzMap.toLp_fourier_eq _
  rw [hd,hf]
  filter_upwards [(𝓕 (∂_{v} f)).coeFn_toLp 2 volume,(𝓕 f).coeFn_toLp 2 volume] with z h1 h2
  rw [h1,h2,SchwartzMap.fourier_lineDerivOp_eq]
  have htemp : (inner ℝ · v).HasTemperateGrowth := ((innerSL ℝ).flip v).hasTemperateGrowth
  simp only [smul_apply,SchwartzMap.smulLeftCLM_apply_apply htemp]
  simp [directionSymbol,real_inner_comm,smul_eq_mul,mul_assoc]

lemma hasDerivAt_translateL2_of_fourier (f df : PlaneL2) (v : ℂ)
    (hae : planeFourier df =ᵐ[volume] fun z => directionSymbol v z*planeFourier f z) :
    HasDerivAt (fun t : ℝ => translateL2 (t • v) f) df 0 := by
  have hd : MemLp (fun z => directionSymbol v z*planeFourier f z) 2 volume :=
    MemLp.ae_eq hae (Lp.memLp (planeFourier df))
  have he : hd.toLp (fun z => directionSymbol v z*planeFourier f z)=planeFourier df := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp hd).trans hae.symm
  have hh := hasDerivAt_translateL2 f v hd
  have hi : planeFourier.symm (hd.toLp (fun z => directionSymbol v z*planeFourier f z))=df := by
    rw [he,planeFourier.symm_apply_apply]
  rw [hi] at hh
  exact hh

lemma schwartz_translation_derivative (f : SchwartzMap ℂ ℂ) (v : ℂ) :
    HasDerivAt (fun t : ℝ => translateL2 (t • v) (f.toLp 2)) ((∂_{v} f).toLp 2) 0 :=
  hasDerivAt_translateL2_of_fourier (f.toLp 2) ((∂_{v} f).toLp 2) v
    (fourier_schwartz_derivative_ae f v)

lemma schwartz_sobolev (n : ℕ) (f : SchwartzMap ℂ ℂ) : Sobolev n (f.toLp 2) := by
  induction n generalizing f with
  | zero => trivial
  | succ n ih =>
    exact ⟨ih f, fun b => ⟨(∂_{axis b} f).toLp 2,
      schwartz_translation_derivative f (axis b), ih _⟩⟩

lemma Sobolev.smul {n : ℕ} {f : PlaneL2} (hf : Sobolev n f) (c : ℂ) :
    Sobolev n (c • f) := by
  induction n generalizing f with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih hf.1, fun b => ?_⟩
    obtain ⟨df, hdf, hrf⟩ := hf.2 b
    refine ⟨c • df, ?_, ih hrf⟩
    convert hdf.const_smul c using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
    funext t
    exact map_smul (translateL2 (t • axis b)) c f

lemma Sobolev.sub {n : ℕ} {f g : PlaneL2} (hf : Sobolev n f) (hg : Sobolev n g) :
    Sobolev n (f-g) := by
  simpa only [neg_one_smul,sub_eq_add_neg] using hf.add (hg.smul (-1))

lemma SmoothL2.derivative {f : PlaneL2} (hf : SmoothL2 f) (j : Bool) :
    ∃ df : PlaneL2, SmoothL2 df ∧
      planeFourier df =ᵐ[volume] fun z => directionSymbol (axis j) z*planeFourier f z := by
  obtain ⟨C,hC,hCt⟩ := (hf 1).translation_bound
  let hd := (memLp_directionSymbol_of_translation_bound f hC hCt (axis j)).1
  let df := planeFourier.symm (hd.toLp (fun z => directionSymbol (axis j) z*planeFourier f z))
  have hdf : HasDerivAt (fun t : ℝ => translateL2 (t • axis j) f) df 0 :=
    hasDerivAt_translateL2 f (axis j) hd
  refine ⟨df,?_,?_⟩
  · intro n
    obtain ⟨g,hg,hrg⟩ := (hf (n+1)).2 j
    rwa [hdf.unique hg]
  · change planeFourier (planeFourier.symm _) =ᵐ[volume] _
    rw [planeFourier.apply_symm_apply]
    exact MemLp.coeFn_toLp hd

lemma directionSymbol_square_sum (z : ℂ) :
    directionSymbol 1 z ^ 2 + directionSymbol Complex.I z ^ 2 =
      -(4*Real.pi^2:ℂ)*(‖z‖^2:ℝ) := by
  have hx : inner ℝ (1:ℂ) z=z.re := by
    simp [real_inner_eq_re_inner,RCLike.inner_apply]
  have hy : inner ℝ Complex.I z=z.im := by
    simp [real_inner_eq_re_inner,RCLike.inner_apply]
  rw [directionSymbol,directionSymbol,hx,hy,Complex.sq_norm,Complex.normSq_apply]
  push_cast
  calc
    (2*↑Real.pi*Complex.I*↑z.re)^2+(2*↑Real.pi*Complex.I*↑z.im)^2 =
      4*↑Real.pi^2*Complex.I^2*((z.re:ℂ)^2+(z.im:ℂ)^2) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

lemma bessel_pointwise (z w : ℂ) :
    w-(4*Real.pi^2:ℂ)⁻¹*
      (directionSymbol 1 z*(directionSymbol 1 z*w)+
       directionSymbol Complex.I z*(directionSymbol Complex.I z*w)) =
      (1+(‖z‖^2:ℝ):ℂ)*w := by
  have hpi : (4*Real.pi^2:ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0:ℝ)<4*Real.pi^2))
  calc
    _ = w-(4*Real.pi^2:ℂ)⁻¹*
      ((directionSymbol 1 z^2+directionSymbol Complex.I z^2)*w) := by ring
    _ = _ := by rw [directionSymbol_square_sum]; field_simp <;> ring

lemma fourier_bessel_ae (f dxx dyy : PlaneL2) :
    planeFourier (f-(4*Real.pi^2:ℂ)⁻¹ • (dxx+dyy)) =ᵐ[volume]
      fun z => planeFourier f z-(4*Real.pi^2:ℂ)⁻¹*
        (planeFourier dxx z+planeFourier dyy z) := by
  let c : ℂ := (4*Real.pi^2:ℂ)⁻¹
  rw [map_sub,map_smul,map_add]
  filter_upwards [Lp.coeFn_sub (planeFourier f) (c • (planeFourier dxx+planeFourier dyy)),
    Lp.coeFn_smul c (planeFourier dxx+planeFourier dyy),
    Lp.coeFn_add (planeFourier dxx) (planeFourier dyy)] with z h1 h2 h3
  simp only [Pi.sub_apply,Pi.smul_apply,Pi.add_apply] at h1 h2 h3
  rw [h1,h2,h3]
  rfl

lemma SmoothL2.bessel_step {f : PlaneL2} (hf : SmoothL2 f) :
    ∃ g : PlaneL2, SmoothL2 g ∧
      planeFourier g =ᵐ[volume] fun z => (1+(‖z‖^2:ℝ):ℂ)*planeFourier f z := by
  obtain ⟨dx,hrx,hx⟩ := hf.derivative false
  obtain ⟨dy,hry,hy⟩ := hf.derivative true
  obtain ⟨dxx,hrxx,hxx⟩ := hrx.derivative false
  obtain ⟨dyy,hryy,hyy⟩ := hry.derivative true
  let c : ℂ := (4*Real.pi^2:ℂ)⁻¹
  refine ⟨f-c • (dxx+dyy),fun n => (hf n).sub (((hrxx n).add (hryy n)).smul c),?_⟩
  filter_upwards [hx,hy,hxx,hyy,fourier_bessel_ae f dxx dyy] with z hx hy hxx hyy hz
  rw [hz,hxx,hyy,hx,hy]
  exact bessel_pointwise z (planeFourier f z)

lemma SmoothL2.fourier_weighted_memLp {f : PlaneL2} (hf : SmoothL2 f) (n : ℕ) :
    MemLp (fun z => ((1+‖z‖^2)^n:ℝ)*planeFourier f z) 2 volume := by
  induction n generalizing f with
  | zero => simpa using Lp.memLp (planeFourier f)
  | succ n ih =>
    obtain ⟨g,hrg,hg⟩ := hf.bessel_step
    apply MemLp.ae_eq (hf_Lp:=ih hrg)
    filter_upwards [hg] with z hz
    rw [hz]
    push_cast
    ring

open scoped ContDiff

lemma inverse_weight_memLp : MemLp (fun z : ℂ => (1+‖z‖^2)⁻¹) 2 volume := by
  have hc : Continuous (fun z : ℂ => (1+‖z‖^2)⁻¹) :=
    (continuous_const.add (continuous_norm.pow 2)).inv₀ (fun z : ℂ => show 1+‖z‖^2 ≠ 0 from ne_of_gt (by positivity))
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  have hdim : (Module.finrank ℝ ℂ:ℝ)<4 := by norm_num
  have hi : Integrable (fun z : ℂ => Real.rpow (1+‖z‖^2) (-4/2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (E:=ℂ) hdim
  apply hi.congr
  filter_upwards with z
  norm_num [Real.rpow_neg (by positivity : (0:ℝ)≤1+‖z‖^2),Real.rpow_two,inv_pow]

lemma SmoothL2.fourier_weighted_integrable {f : PlaneL2} (hf : SmoothL2 f) (n : ℕ) :
    Integrable (fun z => (1+‖z‖^2)^n*‖planeFourier f z‖) volume := by
  have hi := inverse_weight_memLp.integrable_mul (hf.fourier_weighted_memLp (n+1)).norm
  apply hi.congr
  filter_upwards with z
  change (1+‖z‖^2)⁻¹*‖((1+‖z‖^2)^(n+1):ℝ)*planeFourier f z‖=_
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : 0 ≤ (1+‖z‖^2)^(n+1)),pow_succ]
  have hn : (1+‖z‖^2) ≠ 0 := ne_of_gt (by positivity)
  field_simp
  rw [pow_succ]
  ring

lemma SmoothL2.fourier_moments {f : PlaneL2} (hf : SmoothL2 f) (n : ℕ) :
    Integrable (fun z => ‖z‖^n*‖planeFourier f z‖) volume := by
  apply (hf.fourier_weighted_integrable n).mono'
    (((continuous_norm.pow n).aestronglyMeasurable).mul
      (Lp.memLp (planeFourier f)).aestronglyMeasurable.norm)
  apply Filter.Eventually.of_forall
  intro z
  change ‖‖z‖^n*‖planeFourier f z‖‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply pow_le_pow_left₀ (norm_nonneg _)
  nlinarith [sq_nonneg (‖z‖-1)]

lemma SmoothL2.fourier_integrable {f : PlaneL2} (hf : SmoothL2 f) :
    Integrable (planeFourier f : ℂ → ℂ) volume := by
  apply integrable_norm_iff (Lp.memLp (planeFourier f)).aestronglyMeasurable |>.mp
  simpa using hf.fourier_moments 0

end CannonBeltrami

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
-- module Solutions.Q146_CD.Cannon_Beltrami_CauchySymbol
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

namespace CannonBeltrami

lemma integral_inverse_fourier_mul {f g : ℂ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ z, (𝓕⁻ f) z*g z = ∫ z, f z*(𝓕⁻ g) z := by
  have hL : Continuous (fun p : ℂ × ℂ => (-(innerₗ ℂ)) p.1 p.2) :=
    continuous_inner.neg
  have he : (-(innerₗ ℂ)).flip= -(innerₗ ℂ) := by
    ext x y
    exact congrArg Neg.neg (real_inner_comm x y)
  have ht := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := -(innerₗ ℂ)) Real.continuous_fourierChar hL hf hg
  rw [he] at ht
  exact ht

lemma inverse_fourier_l2_test (f : Lp ℂ 2 (volume : Measure ℂ))
    (hf : Integrable (f : ℂ → ℂ)) (g : SchwartzMap ℂ ℂ) :
    ∫ z, g z*(𝓕⁻ f : Lp ℂ 2 (volume : Measure ℂ)) z =
      ∫ z, g z*(𝓕⁻ (f : ℂ → ℂ)) z := by
  have ht := congrArg (fun u : TemperedDistribution ℂ ℂ => u g)
    (Lp.fourierInv_toTemperedDistribution_eq f)
  simp only [TemperedDistribution.fourierInv_apply,Lp.toTemperedDistribution_apply,
    smul_eq_mul] at ht
  have hp := integral_inverse_fourier_mul hf g.integrable
  calc
    _ = ∫ z, (𝓕⁻ g) z*f z := ht.symm
    _ = ∫ z, f z*(𝓕⁻ (g : ℂ → ℂ)) z := by
      congr 1; funext z; rw [mul_comm,SchwartzMap.fourierInv_coe]
    _ = ∫ z, (𝓕⁻ (f : ℂ → ℂ)) z*g z := hp.symm
    _ = _ := by congr 1; funext z; exact mul_comm _ _

lemma inverse_fourier_l2_real_test (f : Lp ℂ 2 (volume : Measure ℂ))
    (hf : Integrable (f : ℂ → ℂ)) (g : ℂ → ℝ)
    (hgd : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) :
    ∫ z, g z • (𝓕⁻ f : Lp ℂ 2 (volume : Measure ℂ)) z =
      ∫ z, g z • (𝓕⁻ (f : ℂ → ℂ)) z := by
  have hgs' : HasCompactSupport (fun z => (g z:ℂ)) := HasCompactSupport.comp_left (g := Complex.ofReal) hgs Complex.ofReal_zero
  have hgd' : ContDiff ℝ ∞ (fun z => (g z:ℂ)) := Complex.ofRealCLM.contDiff.comp hgd
  let sg : SchwartzMap ℂ ℂ := hgs'.toSchwartzMap hgd'
  have ht := inverse_fourier_l2_test f hf sg
  change (∫ z, (g z : ℂ)*(𝓕⁻ f : Lp ℂ 2 (volume : Measure ℂ)) z) =
    (∫ z, (g z:ℂ)*(𝓕⁻ (f:ℂ → ℂ)) z) at ht
  simpa only [Complex.real_smul] using ht

lemma continuous_inverse_fourier {f : ℂ → ℂ} (hf : Integrable f) :
    Continuous (𝓕⁻ f) :=
  VectorFourier.fourierIntegral_continuous (L := -(innerₗ ℂ))
    Real.continuous_fourierChar continuous_inner.neg hf

theorem inverse_fourier_l2_ae (f : Lp ℂ 2 (volume : Measure ℂ))
    (hf : Integrable (f : ℂ → ℂ)) :
    (𝓕⁻ f : Lp ℂ 2 (volume : Measure ℂ)) =ᵐ[volume] 𝓕⁻ (f : ℂ → ℂ) := by
  have hloc : LocallyIntegrable (𝓕⁻ f : Lp ℂ 2 (volume : Measure ℂ)) volume :=
    (Lp.memLp (𝓕⁻ f)).locallyIntegrable (by norm_num)
  exact ae_eq_of_integral_contDiff_smul_eq hloc
    (continuous_inverse_fourier hf).locallyIntegrable (inverse_fourier_l2_real_test f hf)

end CannonBeltrami

namespace CannonBeltrami
open FourierTransform
open scoped RealInnerProductSpace

lemma SmoothL2.representative_ae {f : PlaneL2} (hf : SmoothL2 f) :
    f =ᵐ[volume] smoothRepresentative f := by
  have h := inverse_fourier_l2_ae (planeFourier f) hf.fourier_integrable
  have he : (𝓕⁻ (planeFourier f) : PlaneL2)=f := planeFourier.symm_apply_apply f
  rw [he] at h
  exact h

lemma SmoothL2.beurling {f : PlaneL2} (hf : SmoothL2 f) : SmoothL2 (beurling f) :=
  fun n => (hf n).beurling

end CannonBeltrami

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

namespace CannonBeltrami
open scoped RealInnerProductSpace

lemma schwartz_smoothL2 (f : SchwartzMap ℂ ℂ) : SmoothL2 (f.toLp 2) :=
  fun n => schwartz_sobolev n f

end CannonBeltrami

namespace CannonBeltrami
lemma realCLM_apply (D : ℂ →L[ℝ] ℂ) (v : ℂ) :
    D v = (v.re:ℂ)*D 1+(v.im:ℂ)*D Complex.I := by
  have hv : v = v.re • (1:ℂ)+v.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hv,map_add,map_smul,map_smul]
  simp only [Complex.real_smul]

lemma fderiv_wirtinger (f : ℂ → ℂ) (z v : ℂ) :
    fderiv ℝ f z v=partialZ f z*v+partialBar f z*star v := by
  rw [realCLM_apply]
  unfold partialZ partialBar
  have hv := Complex.re_add_im v
  conv_rhs => rw [← hv]
  simp only [map_add,map_mul,Complex.star_def,Complex.conj_ofReal,Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]

lemma partialBar_zero_of_differentiableAt {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : partialBar f z=0 := by
  unfold partialBar
  rw [hf.fderiv_restrictScalars ℝ]
  change (fderiv ℂ f z 1+Complex.I*fderiv ℂ f z Complex.I)/2=0
  have he : fderiv ℂ f z Complex.I=Complex.I*fderiv ℂ f z 1 := by
    simpa only [smul_eq_mul,mul_one] using (fderiv ℂ f z).map_smul Complex.I (1:ℂ)
  rw [he]
  calc
    (fderiv ℂ f z 1+Complex.I*(Complex.I*fderiv ℂ f z 1))/2 =
      ((1+Complex.I^2)*fderiv ℂ f z 1)/2 := by ring
    _ = 0 := by simp [Complex.I_sq]

lemma partials_id (z : ℂ) : partialZ (fun w : ℂ => w) z=1 ∧
    partialBar (fun w : ℂ => w) z=0 := by
  simp [partialZ,partialBar]

end CannonBeltrami

end
end
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
-- module Solutions.Q146_CD.Cannon_Beltrami_TwoPointNormalize
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

namespace CannonBeltrami
lemma partials_comp {F G : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ F (G z)) (hg : DifferentiableAt ℝ G z) :
    partialZ (F ∘ G) z=partialZ F (G z)*partialZ G z+partialBar F (G z)*star (partialBar G z) ∧
    partialBar (F ∘ G) z=partialZ F (G z)*partialBar G z+partialBar F (G z)*star (partialZ G z) := by
  have hd := (hf.hasFDerivAt.comp z hg.hasFDerivAt).fderiv
  constructor
  · change (fderiv ℝ (F ∘ G) z 1-Complex.I*fderiv ℝ (F ∘ G) z Complex.I)/2= _
    rw [hd]
    simp only [ContinuousLinearMap.comp_apply]
    rw [fderiv_wirtinger F (G z),fderiv_wirtinger F (G z)]
    simp only [partialZ,partialBar,map_div₀,map_add,map_mul,Complex.star_def,
      Complex.conj_I,map_ofNat]
    ring_nf
  · change (fderiv ℝ (F ∘ G) z 1+Complex.I*fderiv ℝ (F ∘ G) z Complex.I)/2= _
    rw [hd]
    simp only [ContinuousLinearMap.comp_apply]
    rw [fderiv_wirtinger F (G z),fderiv_wirtinger F (G z)]
    simp only [partialZ,partialBar,map_div₀,map_sub,map_mul,Complex.star_def,
      Complex.conj_I,map_ofNat]
    ring_nf

lemma inverse_partialBar (F : ℂ ≃ₜ ℂ) (hf : Differentiable ℝ (F : ℂ → ℂ))
    (hg : Differentiable ℝ (F.symm : ℂ → ℂ)) (μ : ℂ → ℂ)
    (he : ∀ z, partialBar F z=μ z*partialZ F z)
    (hn : ∀ z, partialZ F z ≠ 0) (z : ℂ) :
    partialBar F.symm z= -μ (F.symm z)*star (partialZ F.symm z) := by
  have hp := (partials_comp (hf (F.symm z)) (hg z)).2
  have hid : (F : ℂ → ℂ) ∘ F.symm=id := funext F.apply_symm_apply
  rw [hid] at hp
  change partialBar (fun w : ℂ => w) z = _ at hp
  rw [(partials_id z).2,he] at hp
  apply mul_left_cancel₀ (hn (F.symm z))
  linear_combination -hp

end CannonBeltrami

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace CannonBeltrami

lemma realCLM_det_wirtinger (D : ℂ →L[ℝ] ℂ) (a b : ℂ)
    (hD : ∀ v, D v=a*v+b*star v) :
    D.det = ‖a‖^2-‖b‖^2 := by
  change LinearMap.det (D : ℂ →ₗ[ℝ] ℂ) = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI]
  rw [Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply,ContinuousLinearMap.coe_coe,
    Complex.coe_basisOneI,Matrix.cons_val_zero,Matrix.cons_val_one,
    Complex.coe_basisOneI_repr,hD,
    star_one,mul_one,Complex.star_def,Complex.conj_I]
  simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.neg_re,Complex.neg_im]
  rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply]
  ring

lemma realCLM_opNorm_wirtinger (D : ℂ →L[ℝ] ℂ) (a b : ℂ)
    (hD : ∀ v, D v=a*v+b*star v) : ‖D‖ ≤ ‖a‖+‖b‖ := by
  apply D.opNorm_le_bound (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro v
  rw [hD]
  calc
    _ ≤ ‖a*v‖+‖b*star v‖ := norm_add_le _ _
    _ = (‖a‖+‖b‖)*‖v‖ := by simp only [norm_mul,norm_star] <;> ring

theorem wirtinger_energy_distortion (D : ℂ →L[ℝ] ℂ) (a b : ℂ)
    (hD : ∀ v, D v=a*v+b*star v) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hba : ‖b‖ ≤ k*‖a‖) :
    0 ≤ D.det ∧ ‖D‖^2 ≤ ((1+k)/(1-k))*|D.det| := by
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hnorm_sq : ‖b‖^2 ≤ k^2*‖a‖^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ hb (mul_nonneg hk ha)).mpr hba
  have hk_sq : k^2 ≤ 1 := by nlinarith
  have hd := realCLM_det_wirtinger D a b hD
  have hdet : 0 ≤ D.det := by
    rw [hd]
    exact sub_nonneg.mpr (hnorm_sq.trans
      ((mul_le_mul_of_nonneg_right hk_sq (sq_nonneg ‖a‖)).trans_eq (one_mul _)))
  refine ⟨hdet,?_⟩
  rw [abs_of_nonneg hdet,hd]
  have hn := realCLM_opNorm_wirtinger D a b hD
  have hns : ‖D‖^2 ≤ (‖a‖+‖b‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg ha hb)).mpr hn
  have hprod : 0 ≤ (k*‖a‖-‖b‖)*(‖a‖+‖b‖) :=
    mul_nonneg (sub_nonneg.mpr hba) (add_nonneg ha hb)
  apply hns.trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hk1)).mpr
  nlinarith

end CannonBeltrami

end
end
end
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
-- module Solutions.Q146_CD.Cannon_Beltrami_ContinuousMemLpRestrict
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Topology

noncomputable section
open Set Metric Filter Topology

noncomputable section
open Set Filter Topology Metric

namespace CannonBeltrami
open MeasureTheory Set Metric

lemma partialZ_norm_le (F : ℂ → ℂ) (z : ℂ) : ‖partialZ F z‖ ≤ ‖fderiv ℝ F z‖ := by
  unfold partialZ
  rw [norm_div]
  have hx := (fderiv ℝ F z).le_opNorm (1:ℂ)
  have hy := (fderiv ℝ F z).le_opNorm Complex.I
  have hh := norm_sub_le (fderiv ℝ F z 1) (Complex.I*fderiv ℝ F z Complex.I)
  simp only [norm_one,mul_one,Complex.norm_I,norm_mul,one_mul] at hx hy hh
  norm_num
  linarith

end CannonBeltrami

end
end
end
end
end
end
end
end
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
-- module Solutions.Q146_CD.CircleDomains_Reflection_SmoothBeltramiDistortion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth principal maps and their inverses satisfy the same
uniform quasiconformal distortion bound. -/
open MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma smooth_homeomorph_partialZ_ne_zero (F : ℂ ≃ₜ ℂ)
    (hF : Differentiable ℝ (F : ℂ → ℂ))
    (hFi : Differentiable ℝ (F.symm : ℂ → ℂ)) (μ : ℂ → ℂ)
    (he : ∀ z, partialBar F z=μ z*partialZ F z) (z : ℂ) : partialZ F z ≠ 0 := by
  intro hz
  have hz' : partialBar F z=0 := by rw [he z, hz, mul_zero]
  have hzero : fderiv ℝ (F : ℂ → ℂ) z 1=0 := by
    rw [fderiv_wirtinger F z, hz, hz']
    simp
  have hc := ((hFi (F z)).hasFDerivAt.comp z (hF z).hasFDerivAt).fderiv
  have hid : (F.symm : ℂ → ℂ) ∘ F=id := funext F.symm_apply_apply
  rw [hid, fderiv_id] at hc
  have hh := congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) hc
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    hzero, map_zero] at hh
  exact one_ne_zero hh

lemma smooth_beltrami_two_sided_distortion (F : ℂ ≃ₜ ℂ)
    (hF : ContDiff ℝ ∞ (F : ℂ → ℂ))
    (hFi : ContDiff ℝ ∞ (F.symm : ℂ → ℂ)) (μ : ℂ → ℂ)
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (hb : ∀ z, ‖μ z‖ ≤ k)
    (he : ∀ z, partialBar F z=μ z*partialZ F z) :
    (∀ z, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2 ≤
      ((1+k)/(1-k))*|(fderiv ℝ (F : ℂ → ℂ) z).det|) ∧
    ∀ z, ‖fderiv ℝ (F.symm : ℂ → ℂ) z‖^2 ≤
      ((1+k)/(1-k))*|(fderiv ℝ (F.symm : ℂ → ℂ) z).det| := by
  have hd := hF.differentiable (by simp)
  have hdi := hFi.differentiable (by simp)
  have hn := smooth_homeomorph_partialZ_ne_zero F hd hdi μ he
  constructor
  · intro z
    exact (wirtinger_energy_distortion _ _ _ (fderiv_wirtinger F z) hk hk1 (by
      rw [he, norm_mul]
      exact mul_le_mul_of_nonneg_right (hb z) (norm_nonneg _))).2
  · intro z
    have hi := inverse_partialBar F hd hdi μ he hn z
    exact (wirtinger_energy_distortion _ _ _ (fderiv_wirtinger F.symm z) hk hk1 (by
      rw [hi, norm_mul, norm_neg, norm_star]
      exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))).2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_SmoothBeltramiCancellation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact cancellation of the Beltrami coefficient when a smooth function
is pulled back by the inverse of the smooth comparison map. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma smooth_beltrami_pullback_cancellation (P : ℂ ≃ₜ ℂ)
    (hP : ContDiff ℝ ∞ (P : ℂ → ℂ)) (hPi : ContDiff ℝ ∞ (P.symm : ℂ → ℂ))
    (μ : ℂ → ℂ) (he : ∀z,partialBar P.symm z=μ z*partialZ P.symm z)
    {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f (P z)) :
    partialBar (f ∘ P) z=
      (partialBar f (P z)-μ (P z)*partialZ f (P z))*star (partialZ P z) := by
  have hd := hP.differentiable (by simp)
  have hdi := hPi.differentiable (by simp)
  have hn := smooth_homeomorph_partialZ_ne_zero P.symm hdi hd μ he
  have hi := inverse_partialBar P.symm hdi hd μ he hn z
  change partialBar P z= -μ (P z)*star (partialZ P z) at hi
  rw [(partials_comp hf (hd z)).2,hi]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothWeightedL2Pullback
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted L2 pullback used by Beltrami cancellation. The Jacobian
change of variables absorbs the derivative of the smooth comparison. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma differentiable_homeomorph_quasiMeasurePreserving (P : ℂ ≃ₜ ℂ)
    (hPi : Differentiable ℝ (P.symm : ℂ → ℂ)) :
    Measure.QuasiMeasurePreserving P volume volume := by
  refine ⟨P.continuous.measurable,Measure.AbsolutelyContinuous.mk ?_⟩
  intro s hs hs0
  rw [Measure.map_apply P.continuous.measurable hs]
  have heq : P.symm '' s=P ⁻¹' s := by simpa using P.symm.image_eq_preimage_symm s
  rw [←heq]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    hPi.differentiableOn hs0

lemma smooth_weighted_L2_pullback (P : ℂ ≃ₜ ℂ)
    (hP : ContDiff ℝ ∞ (P : ℂ → ℂ)) (hPi : ContDiff ℝ ∞ (P.symm : ℂ → ℂ))
    {K : ℝ} (_hK : 0≤K)
    (hD : ∀z,‖fderiv ℝ (P : ℂ → ℂ) z‖^2≤K*|(fderiv ℝ (P : ℂ → ℂ) z).det|)
    {e : ℂ → ℂ} (he : MemLp e 2 volume) {A : Set ℂ} (hA : MeasurableSet A) :
    MemLp (fun z => e (P z)*star (partialZ P z)) 2 (volume.restrict A) ∧
      (∫z in A,‖e (P z)*star (partialZ P z)‖^2)≤K*(∫z in P '' A,‖e z‖^2) := by
  let q := fun z => e (P z)*star (partialZ P z)
  have hm : AEStronglyMeasurable q volume :=
    (he.aestronglyMeasurable.comp_quasiMeasurePreserving
      (differentiable_homeomorph_quasiMeasurePreserving P (hPi.differentiable (by simp)))).mul
      ((Complex.continuous_conj.comp (contDiff_partials hP).1.continuous).aestronglyMeasurable)
  have hf (z : ℂ) (_hz : z∈A) : HasFDerivWithinAt (P : ℂ → ℂ)
      (fderiv ℝ (P : ℂ → ℂ) z) A z :=
    (hP.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z).hasFDerivAt.hasFDerivWithinAt
  have hei : IntegrableOn (fun z => ‖e z‖^2) (P '' A) :=
    (he.integrable_norm_pow (p := 2) (by norm_num)).integrableOn
  have hw : IntegrableOn (fun z => |(fderiv ℝ (P : ℂ → ℂ) z).det| *‖e (P z)‖^2) A := by
    simpa only [smul_eq_mul] using
      (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hA hf
        P.injective.injOn (fun z => ‖e z‖^2)).mp hei
  have hb (z : ℂ) : ‖q z‖^2≤K*(|(fderiv ℝ (P : ℂ → ℂ) z).det| *‖e (P z)‖^2) := by
    have hz : ‖partialZ P z‖^2≤K*|(fderiv ℝ (P : ℂ → ℂ) z).det| :=
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (partialZ_norm_le P z)).trans (hD z)
    dsimp [q]
    rw [norm_mul,Complex.norm_conj,mul_pow]
    calc
      _ ≤ ‖e (P z)‖^2*(K*|(fderiv ℝ (P : ℂ → ℂ) z).det|) :=
        mul_le_mul_of_nonneg_left hz (sq_nonneg _)
      _ = _ := by ring
  have hqi : IntegrableOn (fun z => ‖q z‖^2) A := by
    apply (hw.const_mul K).mono' (hm.restrict.norm.pow 2)
    filter_upwards [] with z
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hb z
  refine ⟨(memLp_two_iff_integrable_sq_norm hm.restrict).mpr hqi,?_⟩
  calc
    _ ≤ ∫z in A,K*(|(fderiv ℝ (P : ℂ → ℂ) z).det| *‖e (P z)‖^2) :=
      integral_mono_ae hqi (hw.const_mul K) (.of_forall hb)
    _ = K*(∫z in P '' A,‖e z‖^2) := by
      rw [integral_const_mul]
      congr 1
      symm
      simpa only [smul_eq_mul] using
        integral_image_eq_integral_abs_det_fderiv_smul volume hA hf P.injective.injOn (fun z => ‖e z‖^2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_StrongWeightedPullback
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong L2 convergence survives the weighted smooth pullback occurring
in the exact Beltrami cancellation formula. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma exists_strong_weighted_pullback (P : ℂ ≃ₜ ℂ)
    (hP : ContDiff ℝ ∞ (P : ℂ → ℂ)) (hPi : ContDiff ℝ ∞ (P.symm : ℂ → ℂ))
    {K : ℝ} (hK : 0≤K)
    (hD : ∀z,‖fderiv ℝ (P : ℂ → ℂ) z‖^2≤K*|(fderiv ℝ (P : ℂ → ℂ) z).det|)
    (e : ℕ → PlaneL2) (he : Tendsto e atTop (𝓝 0)) :
    ∃q : ℕ → PlaneL2,Tendsto q atTop (𝓝 0) ∧
      ∀n,∀ᵐz ∂volume,q n z=e n (P z)*star (partialZ P z) := by
  let f (n : ℕ) (z : ℂ) := e n (P z)*star (partialZ P z)
  have hh (n : ℕ) := smooth_weighted_L2_pullback P hP hPi hK hD (Lp.memLp (e n)) MeasurableSet.univ
  have hf (n : ℕ) : MemLp (f n) 2 volume := by simpa only [Measure.restrict_univ] using (hh n).1
  let q (n : ℕ) := (hf n).toLp (f n)
  have hb (n : ℕ) : ‖q n‖≤(K+1)*‖e n‖ := by
    have hi := (hh n).2
    have hq : (∫z,‖f n z‖^2)=‖q n‖^2 := by
      rw [←real_inner_self_eq_norm_sq,L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hf n).coeFn_toLp] with z hz
      rw [hz,real_inner_self_eq_norm_sq]
    have heq : (∫z,‖e n z‖^2)=‖e n‖^2 := by
      rw [←real_inner_self_eq_norm_sq,L2.inner_def]
      exact integral_congr_ae (.of_forall fun z => (real_inner_self_eq_norm_sq (e n z)).symm)
    have his : ‖q n‖^2≤K*‖e n‖^2 := by
      change (∫z in Set.univ,‖f n z‖^2)≤K*(∫z in P '' Set.univ,‖e n z‖^2) at hi
      simpa only [image_univ,P.surjective.range_eq,Measure.restrict_univ,hq,heq] using hi
    have hk : K≤(K+1)^2 := by nlinarith [sq_nonneg K]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))).mp
    rw [mul_pow]
    exact his.trans (mul_le_mul_of_nonneg_right hk (sq_nonneg _))
  refine ⟨q,?_,fun n => (hf n).coeFn_toLp⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) hb
  simpa only [norm_zero,mul_zero] using (he.norm.const_mul (K+1))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_VariableWeightedPullback
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform distortion suffices for strong L2 convergence under a varying
sequence of smooth weighted pullbacks. This applies to the actual inverse
principal approximants in the reflection-conjugacy calculation. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma exists_strong_variable_weighted_pullback (P : ℕ → ℂ ≃ₜ ℂ)
    (hP : ∀n,ContDiff ℝ ∞ (P n : ℂ → ℂ))
    (hPi : ∀n,ContDiff ℝ ∞ ((P n).symm : ℂ → ℂ))
    {K : ℝ} (hK : 0≤K)
    (hD : ∀n z,‖fderiv ℝ (P n : ℂ → ℂ) z‖^2≤K*|(fderiv ℝ (P n : ℂ → ℂ) z).det|)
    (e : ℕ → PlaneL2) (he : Tendsto e atTop (𝓝 0)) :
    ∃q : ℕ → PlaneL2,Tendsto q atTop (𝓝 0) ∧
      ∀n,∀ᵐz ∂volume,q n z=e n (P n z)*star (partialZ (P n) z) := by
  let f (n : ℕ) (z : ℂ) := e n (P n z)*star (partialZ (P n) z)
  have hh (n : ℕ) := smooth_weighted_L2_pullback (P n) (hP n) (hPi n) hK (hD n) (Lp.memLp (e n)) MeasurableSet.univ
  have hf (n : ℕ) : MemLp (f n) 2 volume := by simpa only [Measure.restrict_univ] using (hh n).1
  let q (n : ℕ) := (hf n).toLp (f n)
  have hb (n : ℕ) : ‖q n‖≤(K+1)*‖e n‖ := by
    have hi := (hh n).2
    have hq : (∫z,‖f n z‖^2)=‖q n‖^2 := by
      rw [←real_inner_self_eq_norm_sq,L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hf n).coeFn_toLp] with z hz
      rw [hz,real_inner_self_eq_norm_sq]
    have heq : (∫z,‖e n z‖^2)=‖e n‖^2 := by
      rw [←real_inner_self_eq_norm_sq,L2.inner_def]
      exact integral_congr_ae (.of_forall fun z => (real_inner_self_eq_norm_sq (e n z)).symm)
    have his : ‖q n‖^2≤K*‖e n‖^2 := by
      change (∫z in Set.univ,‖f n z‖^2)≤K*(∫z in P n '' Set.univ,‖e n z‖^2) at hi
      simpa only [image_univ,(P n).surjective.range_eq,Measure.restrict_univ,hq,heq] using hi
    have hk : K≤(K+1)^2 := by nlinarith [sq_nonneg K]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))).mp
    rw [mul_pow]
    exact his.trans (mul_le_mul_of_nonneg_right hk (sq_nonneg _))
  refine ⟨q,?_,fun n => (hf n).coeFn_toLp⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) hb
  simpa only [norm_zero,mul_zero] using (he.norm.const_mul (K+1))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_Conformal
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sphere conformality and circle-domain statements

The concrete Riemann-sphere charts define conformal equivalences,
round disks, and conformal removability. The two circle-domain statements
express unrestricted uniformization and rigidity under removability.
-/

noncomputable section

open Set
open scoped OnePoint

namespace CircleDomainRigidity

/-- The whole-sphere case of Koebe uniformization. -/
theorem circleDomainModel_univ :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f univ V :=
  ⟨univ, id, isCircleDomain_univ, isConformalEquivalence_id univ⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published finite circle-uniformization input

Conway, *Functions of One Complex Variable II*, GTM 159 (1995),
Theorem 15.7.9, p. 106, gives circle uniformization of nondegenerate
finitely connected regions. `FiniteCircleUniformization` records only
its existence conclusion on the sphere, omitting normalization and
uniqueness. It is an explicit proposition parameter, not an axiom.

The complement components of a finite family of disjoint closed
connected sets are identified below. This checks the finiteness and
nondegeneracy hypotheses for completed surfaces, also after an arbitrary
sphere homeomorphism such as compact metric uniformization.
-/

open Set Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

theorem connectedComponentIn_finite_disjoint_closed
    {X I : Type*} [TopologicalSpace X] [Finite I]
    (C : I → Set X) (hC : ∀ i, IsClosed (C i))
    (hconn : ∀ i, IsPreconnected (C i)) (hdisj : Pairwise (Disjoint on C))
    {i : I} {p : X} (hp : p ∈ C i) :
    connectedComponentIn (⋃ j, C j) p = C i := by
  classical
  let R : Set X := ⋃ j : {j : I // j ≠ i}, C j
  have hR : IsClosed R := isClosed_iUnion_of_finite (fun j => hC j)
  have hCR : Disjoint (C i) R := by
    apply Set.disjoint_left.mpr
    intro x hx hxR
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxR
    exact Set.disjoint_left.mp (hdisj j.property.symm) hx hj
  have hcover : (⋃ j, C j) ⊆ C i ∪ R := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  have hsub : connectedComponentIn (⋃ j, C j) p ⊆ C i := by
    have hs := isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_connectedComponentIn (F := ⋃ j, C j) (x := p))
      (C i) R (hC i) hR ((connectedComponentIn_subset _ _).trans hcover)
      (by rw [hCR.inter_eq, inter_empty])
    rcases hs with h | h
    · exact h
    · exact fun x hx => (Set.disjoint_left.mp hCR hp
        (h (mem_connectedComponentIn (mem_iUnion.mpr ⟨i, hp⟩)))).elim
  exact hsub.antisymm ((hconn i).subset_connectedComponentIn hp (subset_iUnion C i))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteCompletionUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite uniformization of the actual terminal-disk complement

The complementary components are exactly the closed physical terminal
caps. In particular they are finite and nondegenerate. The published
finite circle theorem therefore applies after compact metric
uniformization; the resulting map is conformal on the retained core.
-/

open Set Function Filter
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem isConnected_openCompletedRegion {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    IsConnected (openCompletedRegion H) := by
  let S : Set ℂ := (⋃ i, closure (jordanInterior (H i)))ᶜ
  have hS : IsPreconnected S := isPreconnected_exterior_finite_jordanInteriors H hdisj
  have hinf : (∞ : Sphere) ∈ closure (((↑) : ℂ → Sphere) '' S) := by
    have hmem : ∀ᶠ z : ℂ in coclosedCompact ℂ, z ∈ S := by
      rw [coclosedCompact_eq_cocompact]
      exact (isCompact_iUnion fun i => isCompact_closure_jordanInterior (H i)).compl_mem_cocompact
    exact mem_closure_of_tendsto OnePoint.tendsto_coe_infty
      (hmem.mono fun z hz => ⟨z, hz, rfl⟩)
  have hsub : ((↑) : ℂ → Sphere) '' S ⊆ openCompletedRegion H := by
    rintro _ ⟨z, hz, rfl⟩ hb
    obtain ⟨i, x, hx, heq⟩ := mem_iUnion.mp hb
    have hxz : x = z := OnePoint.coe_injective heq
    exact hz (mem_iUnion.mpr ⟨i, hxz ▸ hx⟩)
  have hupper : openCompletedRegion H ⊆ closure (((↑) : ℂ → Sphere) '' S) := by
    intro p hp
    cases p using OnePoint.rec with
    | infty => exact hinf
    | coe z =>
      apply subset_closure
      refine ⟨z, ?_, rfl⟩
      intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact hp (mem_iUnion.mpr ⟨i, z, hi, rfl⟩)
  refine ⟨⟨∞, ?_⟩, (hS.image _ OnePoint.continuous_coe.continuousOn).subset_closure hsub hupper⟩
  intro hb
  obtain ⟨i, z, _, heq⟩ := mem_iUnion.mp hb
  exact OnePoint.coe_ne_infty z heq

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HolomorphicHomeomorph
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A holomorphic plane homeomorphism has a holomorphic inverse on the
image domain. Isolated critical points are removed from the continuous
inverse; the chain rule then excludes them altogether. -/
open Set Filter Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem holomorphicHomeomorph_deriv_not_locally_zero
    (φ : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    {z : ℂ} (hz : z ∈ U) : ¬ ∀ᶠ w in 𝓝 z, deriv φ w = 0 := by
  intro hzero
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp ((show ∀ᶠ w in 𝓝 z, w ∈ U from hU.mem_nhds hz).and hzero)
  have hsub : ball z r ⊆ U := fun w hw => (hball (by simpa only [mem_ball] using hw)).1
  obtain ⟨c, hc⟩ := isOpen_ball.exists_is_const_of_deriv_eq_zero
    (convex_ball z r).isPreconnected (hφ.mono hsub)
    (fun w hw => (hball (by simpa only [mem_ball] using hw)).2)
  let w : ℂ := z + (r/2 : ℝ)
  have hw : w ∈ ball z r := by
    rw [mem_ball, dist_eq_norm]
    dsimp only [w]
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have heq : w = z := φ.injective ((hc w hw).trans (hc z (mem_ball_self hr)).symm)
  have hr0 : (r/2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  exact hr0 (Complex.ofReal_injective (add_left_cancel (show z + (r/2 : ℝ) = z+0 by
    simpa only [add_zero] using heq)))

 theorem holomorphicHomeomorph_inverse_differentiableAt
    (φ : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    {z : ℂ} (hz : z ∈ U) : DifferentiableAt ℂ φ.symm (φ z) := by
  have ha := hφ.analyticAt (hU.mem_nhds hz)
  have hn : ∀ᶠ w in 𝓝[≠] z, deriv φ w ≠ 0 :=
    ha.deriv.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (holomorphicHomeomorph_deriv_not_locally_zero φ hU hφ hz)
  have ht : Tendsto φ.symm (𝓝[≠] (φ z)) (𝓝[≠] z) := by
    change map φ.symm (𝓝[≠] (φ z)) ≤ 𝓝[≠] z
    rw [φ.symm.map_punctured_nhds_eq, φ.symm_apply_apply]
  apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    ?_ φ.symm.continuous.continuousAt).differentiableAt
  have hu : ∀ᶠ y in 𝓝 (φ z), φ.symm y ∈ U := by
    have ht₀ : Tendsto φ.symm (𝓝 (φ z)) (𝓝 z) := by
      simpa only [φ.symm_apply_apply] using φ.symm.continuous.tendsto (φ z)
    exact ht₀.eventually (hU.mem_nhds hz)
  filter_upwards [ht.eventually hn, hu.filter_mono nhdsWithin_le_nhds] with y hy hyU
  have hcont : ContDiffAt ℂ 1 φ (φ.symm y) :=
    (hφ.analyticAt (hU.mem_nhds hyU)).contDiffAt
  have hs := hcont.hasStrictDerivAt'
    ((hφ _ hyU).differentiableAt (hU.mem_nhds hyU)).hasDerivAt (by norm_num)
  have hi := hs.to_local_left_inverse hy (Eventually.of_forall φ.symm_apply_apply)
  simpa only [φ.apply_symm_apply] using hi.hasDerivAt.differentiableAt

 theorem holomorphicHomeomorph_deriv_ne_zero
    (φ : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    {z : ℂ} (hz : z ∈ U) : deriv φ z ≠ 0 := by
  have hf := ((hφ z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hi := (holomorphicHomeomorph_inverse_differentiableAt φ hU hφ hz).hasDerivAt
  have hh := (hi.comp z hf).deriv
  have hid : ((φ.symm : ℂ → ℂ) ∘ (φ : ℂ → ℂ)) = id := funext φ.symm_apply_apply
  have hidder : deriv (id : ℂ → ℂ) z = 1 := (hasDerivAt_id z).deriv
  rw [hid, hidder] at hh
  intro hzero
  rw [hzero, mul_zero] at hh
  exact one_ne_zero hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanDiskImages
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact Jordan disks contained in the domain of an open embedding have their actual Jordan
interiors as images. This identifies the anchor disks in finite models. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

/-- An open bounded region with the boundary of a Jordan disk is that disk. -/
theorem open_eq_jordanInterior_of_frontier
    (H : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    (hne : U.Nonempty) (hf : frontier U = frontier (jordanInterior H)) :
    U = jordanInterior H := open_eq_jordan_of_frontier H hU hb hne hf

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_JordanCircularizationSequence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual sequence of finite Jordan configurations and normalized
conformal maps obtained by successive one-hole circularizations. -/
open Set Function Metric Filter Asymptotics Bornology
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

namespace FiniteJordanConfiguration
variable {I : Type*} [Finite I]

lemma region_open (C : FiniteJordanConfiguration I) : IsOpen C.region :=
  isOpen_openCompletedRegion C.hole

lemma region_connected (C : FiniteJordanConfiguration I) : IsConnected C.region :=
  isConnected_openCompletedRegion C.hole C.disjoint

lemma stageMap_conformal (C : FiniteJordanConfiguration I) (schedule : ℕ → I) (n : ℕ) :
    IsConformalEquivalence (stageMap C schedule n) (iterate C schedule n).region
      (iterate C schedule (n+1)).region :=
  (chosenStep (iterate C schedule n) (schedule n)).conformal

lemma cumulativeMap_conformal (C : FiniteJordanConfiguration I) (schedule : ℕ → I) (n : ℕ) :
    IsConformalEquivalence (cumulativeMap C schedule n) C.region
      (iterate C schedule n).region := by
  induction n with
  | zero => exact isConformalEquivalence_id C.region
  | succ n ih => exact ih.trans (stageMap_conformal C schedule n)

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_AnalyticJordanCap
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic circle parametrizations of the actual compact Jordan holes.
The neighborhood and injectivity are retained so that a later
circularization has the proved local continuation. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma isAnalyticJordanCap_of_round {H : ℂ ≃ₜ ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (he : jordanInterior H=ball c r) : IsAnalyticJordanCap H := by
  refine ⟨univ,id,c,r,isOpen_univ,hr,subset_univ _,differentiableOn_id,injective_id.injOn,?_⟩
  rw [image_id,he,closure_ball _ hr.ne']

lemma IsAnalyticJordanCap.conformal_image {H K : ℂ ≃ₜ ℂ} (hH : IsAnalyticJordanCap H)
    {f : Sphere → Sphere} {U V : Set Sphere}
    (hf : IsConformalEquivalence f U V) (hU : IsOpen U)
    (hinf : ∞∈U) (hfix : f ∞=∞) (hHU : closedTerminalCap H⊆U)
    (himage : f '' closedTerminalCap H=closedTerminalCap K) : IsAnalyticJordanCap K := by
  obtain ⟨S,α,c,r,hS,hr,hDS,hα,hi,hαeq⟩ := hH
  let g : ℂ → ℂ := fun z => finiteCoord (f (z : Sphere))
  let P := ((↑) : ℂ → Sphere) ⁻¹' U
  have hP : IsOpen P := hU.preimage OnePoint.continuous_coe
  obtain ⟨hgd,_,hgi⟩ := hf.1.finite_open_embedding hU hf.bijOn.injOn hinf hfix
  let W := S ∩ α ⁻¹' P
  have hW : IsOpen W := hα.continuousOn.isOpen_inter_preimage hS hP
  have hDW : closedBall c r⊆W := by
    intro z hz
    refine ⟨hDS hz,?_⟩
    apply hHU
    refine ⟨α z,?_,rfl⟩
    rw [←hαeq]
    exact mem_image_of_mem α hz
  have hfin : ∀z∈closure (jordanInterior H),f (z : Sphere)≠∞ :=
    fun z hz => finite_image_of_fixes_infty hf.bijOn.injOn hinf hfix (hHU ⟨z,hz,rfl⟩)
  have hgimage : g '' closure (jordanInterior H)=closure (jordanInterior K) := by
    apply OnePoint.coe_injective.image_injective
    rw [finite_part_sphere_image hfin]
    exact himage
  refine ⟨W,g ∘ α,c,r,hW,hr,hDW,?_,?_,?_⟩
  · exact hgd.comp (hα.mono inter_subset_left) (fun _ hz => hz.2)
  · exact hgi.comp (hi.mono inter_subset_left) (fun _ hz => hz.2)
  · rw [image_comp,hαeq,hgimage]

namespace FiniteJordanConfiguration
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I} {j : I}

omit [Finite I] in
lemma Step.analytic_selected (q : Step C j) : IsAnalyticJordanCap (q.target.hole j) :=
  isAnalyticJordanCap_of_round q.radius_pos q.selected

omit [Finite I] in
lemma Step.analytic_other (q : Step C j) {i : I} (hij : i≠j)
    (ha : IsAnalyticJordanCap (C.hole i)) : IsAnalyticJordanCap (q.target.hole i) := by
  let U := (closedTerminalCap (C.hole j))ᶜ
  have hU : IsOpen U := (isCompact_closedTerminalCap (C.hole j)).isClosed.isOpen_compl
  have hinf : ∞∈U := by
    rintro ⟨z,_,he⟩
    exact OnePoint.coe_ne_infty z he
  have hHU : closedTerminalCap (C.hole i)⊆U := by
    intro x hx hxj
    exact Set.disjoint_left.mp (disjoint_closedTerminalCaps C.hole C.disjoint hij) hx hxj
  exact ha.conformal_image q.exterior_conformal hU hinf q.principal.1 hHU (q.others i hij)

lemma iterate_analytic_of_visited (C : FiniteJordanConfiguration I) (schedule : ℕ → I)
    (n : ℕ) (i : I) (hv : ∃k<n,schedule k=i) :
    IsAnalyticJordanCap ((iterate C schedule n).hole i) := by
  induction n with
  | zero => obtain ⟨k,hk,_⟩ := hv;omega
  | succ n ih =>
    by_cases hi : i=schedule n
    · subst i
      exact (chosenStep (iterate C schedule n) (schedule n)).analytic_selected
    · apply (chosenStep (iterate C schedule n) (schedule n)).analytic_other hi
      apply ih
      obtain ⟨k,hk,hki⟩ := hv
      have hkn : k≠n := by
        intro he
        subst k
        exact hi hki.symm
      exact ⟨k,by omega,hki⟩

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_AnalyticCircularization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! After one complete cycle every actual hole has an analytic circle
parametrization. The next one-hole map therefore has the constructed
holomorphic continuation in each source boundary chart. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration

lemma cyclic_iterate_analytic {m : ℕ} (C : FiniteJordanConfiguration (Fin (m+1)))
    {n : ℕ} (hn : m+1≤n) (i : Fin (m+1)) :
    IsAnalyticJordanCap ((iterate C (cyclicSchedule m) n).hole i) := by
  apply iterate_analytic_of_visited
  refine ⟨i.val,lt_of_lt_of_le i.isLt hn,?_⟩
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_AnalyticJordanParametrization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The analytic disk parametrizations retained by the iteration also
parametrize the entire actual Jordan boundary. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_analytic_jordan_parametrization {H : ℂ ≃ₜ ℂ} (hH : IsAnalyticJordanCap H) :
    ∃ (S : Set ℂ) (α : ℂ → ℂ) (c : ℂ) (r : ℝ), IsOpen S ∧ 0 < r ∧
      closedBall c r⊆S ∧ DifferentiableOn ℂ α S ∧ InjOn α S ∧
      α '' closedBall c r=closure (jordanInterior H) ∧
      α '' sphere c r=frontier (jordanInterior H) := by
  obtain ⟨S,α,c,r,hS,hr,hDS,hα,hi,he⟩ := hH
  let J := roundJordanAt c r hr
  have hJcl : closure (jordanInterior J)=closedBall c r := roundJordanAt_closure c r hr
  have hJS : closure (jordanInterior J)⊆S := by rwa [hJcl]
  obtain ⟨K,_,hKcl,hKf⟩ := exists_jordan_image_disk planarSchoenflies hS hα.continuousOn
    (fun _ hT hTS => holomorphic_injOn_isOpen_image hS hα hi hT hTS) hi J hJS
  rw [hJcl,he] at hKcl
  have hKI : jordanInterior K=jordanInterior H := by
    calc
      jordanInterior K = interior (closure (jordanInterior K)) :=
        (interior_closure_jordanInterior K).symm
      _ = interior (closure (jordanInterior H)) := congrArg interior hKcl.symm
      _ = jordanInterior H := interior_closure_jordanInterior H
  have hJfront : frontier (jordanInterior J)=sphere c r := by
    rw [roundJordanAt_interior,frontier_ball _ hr.ne']
  refine ⟨S,α,c,r,hS,hr,hDS,hα,hi,he,?_⟩
  rw [←hJfront,←hKf,hKI]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_RoundDiskReflection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact spherical reflections in the assigned finite round disks. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity

lemma roundDiskReflection_coe (c : ℂ) {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z≠c) :
    roundDiskReflection c r hr (z : Sphere)=
      ((c+(r:ℂ)^2/(starRingEnd ℂ (z-c)) : ℂ) : Sphere) := by
  have hrC : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
  have hn : (z-c)/(r:ℂ)≠0 := div_ne_zero (sub_ne_zero.mpr hz) hrC
  change affineSphere (r:ℂ) c hrC
    (CannonSphereReflection.reflection ((((z-c)/(r:ℂ) : ℂ) : Sphere)))=_
  rw [CannonSphereReflection.reflection_coe hn,affineSphere_coe]
  congr 1
  simp only [map_div₀,Complex.conj_ofReal]
  field_simp
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereCoefficient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel complex coefficient fields on the concrete sphere, with an explicit
value at infinity. -/
open Set Function MeasureTheory
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

lemma circleReflectionPhase_norm (c z : ℂ) : ‖circleReflectionPhase c z‖=1 := by
  classical
  by_cases hz : z=c
  · simp [circleReflectionPhase,hz]
  · simp only [circleReflectionPhase,ite_eq_right hz,norm_pow,norm_div,Complex.norm_conj,
      div_self (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)),one_pow]

lemma circleReflectionPhase_measurable (c : ℂ) : Measurable (circleReflectionPhase c) := by
  classical
  apply Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
  exact ((measurable_id.sub_const c).div (Complex.continuous_conj.measurable.comp (measurable_id.sub_const c))).pow_const 2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalSmoothApproximation
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth principal maps whose actual densities converge strongly to a
specified compact-coefficient L2 solution. The common coefficient support
will give uniform exterior estimates for the maps. -/
open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma density_operator_equation {μ : ℂ → ℂ} (hm : MemLp μ 2 volume)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k)
    (g : PlaneL2) (he : ∀ᵐ z ∂volume, g z=μ z*(1+beurling g z)) :
    g-multiplier μ hm.aestronglyMeasurable hk hb (beurling g)=hm.toLp μ := by
  apply Lp.ext
  filter_upwards [he, Lp.coeFn_sub g (multiplier μ hm.aestronglyMeasurable hk hb (beurling g)),
    multiplier_ae μ hm.aestronglyMeasurable hk hb (beurling g),
    MemLp.coeFn_toLp hm] with z hz hsub hmul hμ
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hmul, hμ, hz]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_CompactDiffeomorphismBeltrami
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth plane diffeomorphism fixed near infinity has an actual smooth,
compactly supported complex dilatation, uniformly bounded strictly below one. -/
open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma smooth_homeomorph_fderiv_injective (P : ℂ ≃ₜ ℂ)
    (hs : ContDiff ℝ ∞ (P : ℂ → ℂ)) (hi : ContDiff ℝ ∞ (P.symm : ℂ → ℂ))
    (z : ℂ) : Injective (fderiv ℝ (P : ℂ → ℂ) z) := by
  have he := ((hi.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (P z)).hasFDerivAt.comp z
    (hs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z).hasFDerivAt).fderiv
  have hid : (P.symm : ℂ → ℂ) ∘ P=id := funext P.symm_apply_apply
  rw [hid,fderiv_id] at he
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hh := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) he
  simpa only [ContinuousLinearMap.comp_apply,hv,map_zero,ContinuousLinearMap.id_apply] using hh

lemma smooth_homeomorph_wirtinger_gap_ne_zero (P : ℂ ≃ₜ ℂ)
    (hs : ContDiff ℝ ∞ (P : ℂ → ℂ)) (hi : ContDiff ℝ ∞ (P.symm : ℂ → ℂ))
    (z : ℂ) : ‖partialZ P z‖^2-‖partialBar P z‖^2≠0 := by
  have hinj := smooth_homeomorph_fderiv_injective P hs hi z
  let E : ℂ ≃ₗ[ℝ] ℂ := LinearEquiv.ofBijective (fderiv ℝ (P : ℂ → ℂ) z).toLinearMap
    ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩
  have hn : (fderiv ℝ (P : ℂ → ℂ) z).det≠0 := E.isUnit_det'.ne_zero
  rwa [realCLM_det_wirtinger _ _ _ (fderiv_wirtinger P z)] at hn

lemma homeomorph_partials_eq_id_off (P : ℂ ≃ₜ ℂ) {R : ℝ}
    (hfix : ∀z,R≤‖z‖ → P z=z) {z : ℂ} (hz : R<‖z‖) :
    partialZ P z=1 ∧ partialBar P z=0 := by
  have he : (P : ℂ → ℂ)=ᶠ[𝓝 z] id := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    exact hfix w hw.le
  have hid : id=(fun w : ℂ => w) := rfl
  simpa only [partialZ,partialBar,he.fderiv_eq,hid] using partials_id z

lemma compact_diffeomorphism_wirtinger_gap_pos (P : ℂ ≃ₜ ℂ)
    (hs : ContDiff ℝ ∞ (P : ℂ → ℂ)) (hi : ContDiff ℝ ∞ (P.symm : ℂ → ℂ))
    {R : ℝ} (hfix : ∀z,R≤‖z‖ → P z=z) (z : ℂ) :
    0<‖partialZ P z‖^2-‖partialBar P z‖^2 := by
  let q := fun w => ‖partialZ P w‖^2-‖partialBar P w‖^2
  have hq : Continuous q := (contDiff_partials hs).1.continuous.norm.pow 2 |>.sub
    ((contDiff_partials hs).2.continuous.norm.pow 2)
  let a : ℂ := ((max R 0+1 : ℝ) : ℂ)
  have ha : R<‖a‖ := by
    dsimp [a]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
    linarith [le_max_left R 0]
  have hqa : q a=1 := by
    obtain ⟨hZ,hB⟩ := homeomorph_partials_eq_id_off P hfix ha
    simp only [q,hZ,hB,norm_one,norm_zero,one_pow,zero_pow (by decide : 2≠0),sub_zero]
  by_contra hn
  have hz : q z≤0 := le_of_not_gt hn
  obtain ⟨w,hw⟩ := intermediate_value_univ z a hq ⟨hz,by rw [hqa];norm_num⟩
  exact smooth_homeomorph_wirtinger_gap_ne_zero P hs hi w hw

lemma compact_diffeomorphism_beltrami (P : ℂ ≃ₜ ℂ)
    (hs : ContDiff ℝ ∞ (P : ℂ → ℂ)) (hi : ContDiff ℝ ∞ (P.symm : ℂ → ℂ))
    {R : ℝ} (hfix : ∀z,R≤‖z‖ → P z=z) :
    ∃ (μ : ℂ → ℂ) (k S : ℝ),ContDiff ℝ ∞ μ ∧ 0≤k ∧ k<1 ∧ 0<S ∧
      (∀z,‖μ z‖≤k) ∧ (∀z,S≤‖z‖ → μ z=0) ∧
      ∀z,partialBar P z=μ z*partialZ P z := by
  have hgap := compact_diffeomorphism_wirtinger_gap_pos P hs hi hfix
  have hZ (z : ℂ) : partialZ P z≠0 := by
    intro hz
    have hh := hgap z
    rw [hz,norm_zero,zero_pow (by decide : 2≠0),zero_sub] at hh
    nlinarith [sq_nonneg ‖partialBar P z‖]
  let μ := fun z => partialBar P z/partialZ P z
  have hμs : ContDiff ℝ ∞ μ := by
    convert (contDiff_partials hs).2.mul ((contDiff_partials hs).1.inv hZ) using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have hμlt (z : ℂ) : ‖μ z‖<1 := by
    change ‖partialBar P z/partialZ P z‖<1
    rw [norm_div,div_lt_one (norm_pos_iff.mpr (hZ z))]
    nlinarith [hgap z,norm_nonneg (partialZ P z),norm_nonneg (partialBar P z)]
  let S := max R 0+1
  have hS : 0<S := by dsimp [S] <;> linarith [le_max_right R 0]
  have hzero (z : ℂ) (hz : S≤‖z‖) : μ z=0 := by
    have hz' : R<‖z‖ := by dsimp [S] at hz <;> linarith [le_max_left R 0]
    change partialBar P z/partialZ P z=0
    rw [(homeomorph_partials_eq_id_off P hfix hz').2,zero_div]
  obtain ⟨a,ha,hm⟩ := (isCompact_closedBall (0:ℂ) S).exists_isMaxOn
    ⟨0,mem_closedBall_self hS.le⟩ hμs.continuous.norm.continuousOn
  let k := (‖μ a‖+1)/2
  have hk : 0≤k := by dsimp [k] <;> positivity
  have hk1 : k<1 := by dsimp [k] <;> linarith [hμlt a]
  refine ⟨μ,k,S,hμs,hk,hk1,hS,?_,hzero,?_⟩
  · intro z
    by_cases hz : z∈closedBall (0:ℂ) S
    · have hb : ‖μ z‖≤‖μ a‖ := hm hz
      dsimp [k]
      linarith [hμlt a]
    · rw [hzero z (le_of_lt (by simpa only [mem_closedBall,dist_zero_right,not_le] using hz)),norm_zero]
      exact hk
  · intro z
    exact (div_mul_cancel₀ (partialBar P z) (hZ z)).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DisjointClosedNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite disjoint closed sets have disjoint closed neighborhoods
subordinate to individually prescribed open sets. -/
open Set Topology
noncomputable section
namespace CircleDomainRigidity

lemma finite_disjoint_closed_neighborhoods
    {X I : Type*} [TopologicalSpace X] [NormalSpace X] [Finite I]
    (A O : I → Set X) (hA : ∀ i, IsClosed (A i))
    (hO : ∀ i, IsOpen (O i)) (hAO : ∀ i, A i ⊆ O i)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ∃ U : I → Set X, (∀ i, IsOpen (U i)) ∧ (∀ i, A i ⊆ U i) ∧
      (∀ i, closure (U i) ⊆ O i) ∧
      Pairwise (fun i j => Disjoint (closure (U i)) (closure (U j))) := by
  classical
  let B (i : I) := ⋃ j : {j : I // j≠i}, A j.val
  have hB (i : I) : IsClosed (B i) := isClosed_iUnion_of_finite (fun j => hA j.val)
  have hAB (i : I) : A i ⊆ O i \ B i := by
    intro x hx
    refine ⟨hAO i hx,?_⟩
    intro hb
    obtain ⟨j,hj⟩ := mem_iUnion.mp hb
    exact Set.disjoint_left.mp (hd j.property.symm) hx hj
  choose Z hZo hAZ hZsub using fun i =>
    normal_exists_closure_subset (hA i) ((hO i).sdiff (hB i)) (hAB i)
  let V (i : I) := Z i \ ⋃ j : {j : I // j≠i}, closure (Z j.val)
  have hVo (i : I) : IsOpen (V i) :=
    (hZo i).sdiff (isClosed_iUnion_of_finite fun _ => isClosed_closure)
  have hAV (i : I) : A i ⊆ V i := by
    intro x hx
    refine ⟨hAZ i hx,?_⟩
    intro hb
    obtain ⟨j,hj⟩ := mem_iUnion.mp hb
    exact (hZsub j.val hj).2 (mem_iUnion.mpr ⟨⟨i,j.property.symm⟩,hx⟩)
  have hVd : Pairwise (fun i j => Disjoint (V i) (V j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hxi.2 (mem_iUnion.mpr ⟨⟨j,hij.symm⟩,subset_closure hxj.1⟩)
  choose U hUo hAU hUV using fun i =>
    normal_exists_closure_subset (hA i) (hVo i) (hAV i)
  refine ⟨U,hUo,hAU,?_,?_⟩
  · intro i x hx
    exact (hZsub i (subset_closure (hUV i hx).1)).1
  · intro i j hij
    exact (hVd hij).mono (hUV i) (hUV j)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DisjointSupportedHomeomorphs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite composition of smooth plane deformations supported in disjoint
open neighborhoods preserves the exact image assigned to each cap. -/
open Set Function
open scoped ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma homeomorph_maps_set_of_fixed_compl (T : ℂ ≃ₜ ℂ) {U : Set ℂ}
    (hfix : ∀z∉U,T z=z) {x : ℂ} (hx : x∈U) : T x∈U := by
  by_contra hn
  have he : T x=x := T.injective (hfix _ hn)
  rw [he] at hn
  exact hn hx

lemma exists_disjoint_supported_composition {I : Type*} [Fintype I]
    (A U : I → Set ℂ) (hA : ∀i,A i⊆U i)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    (T : I → ℂ ≃ₜ ℂ) (hs : ∀i,ContDiff ℝ ∞ (T i : ℂ → ℂ))
    (hsi : ∀i,ContDiff ℝ ∞ ((T i).symm : ℂ → ℂ))
    (hfix : ∀i z,z∉U i → T i z=z) :
    ∃P : ℂ ≃ₜ ℂ, ContDiff ℝ ∞ (P : ℂ → ℂ) ∧
      ContDiff ℝ ∞ (P.symm : ℂ → ℂ) ∧
      (∀z,(∀i,z∉U i) → P z=z) ∧ ∀i,P '' A i=T i '' A i := by
  classical
  have hfixed (i j : I) (hij : i≠j) {B : Set ℂ} (hB : B⊆U j) : T i '' B=B := by
    calc
      T i '' B = id '' B := image_congr (fun z hz => hfix i z
        (fun hi => Set.disjoint_left.mp (hU hij) hi (hB hz)))
      _ = B := image_id B
  have hfamily (s : Finset I) :
      ∃P : ℂ ≃ₜ ℂ,ContDiff ℝ ∞ (P : ℂ → ℂ) ∧
        ContDiff ℝ ∞ (P.symm : ℂ → ℂ) ∧
        (∀z,(∀i,z∉U i) → P z=z) ∧ ∀i,P '' A i=if i∈s then T i '' A i else A i := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨Homeomorph.refl ℂ,contDiff_id,contDiff_id,fun _ _ => rfl,?_⟩
      intro i
      simp
    | @insert i s hi ih =>
      obtain ⟨P,hPs,hPis,hPf,hP⟩ := ih
      refine ⟨P.trans (T i),(hs i).comp hPs,hPis.comp (hsi i),?_,?_⟩
      · intro z hz
        change T i (P z)=z
        rw [hPf z hz,hfix i z (hz i)]
      intro j
      change (T i ∘ P) '' A j=_
      rw [image_comp,hP]
      by_cases hji : j=i
      · subst j
        simp [hi]
      · by_cases hjs : j∈s
        · simp only [ite_eq_left hjs,Finset.mem_insert,hji,false_or]
          exact hfixed i j (Ne.symm hji) (by
            rintro _ ⟨x,hx,rfl⟩
            exact homeomorph_maps_set_of_fixed_compl (T j) (hfix j) (hA j hx))
        · simp only [ite_eq_right hjs,Finset.mem_insert,hji,false_or]
          exact hfixed i j (Ne.symm hji) (hA j)
  obtain ⟨P,hPs,hPis,hPf,hP⟩ := hfamily Finset.univ
  refine ⟨P,hPs,hPis,hPf,?_⟩
  intro i
  simpa only [Finset.mem_univ,ite_eq_left] using hP i

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RescaledPlaneBump
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed smooth plane cutoff with quantitative rescaling. -/
open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma planeScaledBump_smooth (r : ℝ) : ContDiff ℝ ∞ (planeScaledBump r) := by
  change ContDiff ℝ ∞ (fun z : ℂ => planeUnitBump (r⁻¹ • z))
  exact planeUnitBump.contDiff.comp
    ((contDiff_const (c := r⁻¹)).smul (contDiff_id : ContDiff ℝ ∞ (fun z : ℂ => z)))

lemma planeScaledBump_unit (r : ℝ) (z : ℂ) : planeScaledBump r z∈Icc 0 1 :=
  ⟨planeUnitBump.nonneg,planeUnitBump.le_one⟩

lemma planeScaledBump_one {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≤ r) :
    planeScaledBump r z=1 := by
  apply planeUnitBump.one_of_mem_closedBall
  change r⁻¹ • z∈closedBall (0:ℂ) 1
  apply mem_closedBall_zero_iff.mpr
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  exact (inv_mul_le_iff₀ hr).mpr (by simpa using hz)

lemma planeScaledBump_zero {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : 2*r≤‖z‖) :
    planeScaledBump r z=0 := by
  apply planeUnitBump.zero_of_le_dist
  change 2≤dist (r⁻¹ • z) 0
  rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  exact (le_inv_mul_iff₀ hr).mpr (by nlinarith)

lemma planeScaledBump_eventually_zero {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : 2*r<‖z‖) :
    planeScaledBump r =ᶠ[𝓝 z] 0 := by
  filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hz] with y hy
  exact planeScaledBump_zero hr hy.le

lemma exists_planeUnitBump_derivative_bound : ∃B:ℝ,0≤B ∧ ∀z,‖fderiv ℝ planeUnitBump z‖≤B := by
  obtain ⟨B,hB⟩ := ((planeUnitBump.contDiff : ContDiff ℝ 1 (planeUnitBump : ℂ → ℝ)).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (planeUnitBump.hasCompactSupport.fderiv ℝ)
  exact ⟨max 0 B,le_max_left _ _,fun z => (hB z).trans (le_max_right _ _)⟩

lemma planeScaledBump_derivative_bound {B r : ℝ} (hB : ∀z,‖fderiv ℝ planeUnitBump z‖≤B)
    (hr : 0 < r) (z : ℂ) : ‖fderiv ℝ (planeScaledBump r) z‖≤B/r := by
  have hd := ((planeUnitBump.contDiff : ContDiff ℝ 1 (planeUnitBump : ℂ → ℝ)).differentiable one_ne_zero (r⁻¹ • z)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).const_smul r⁻¹)
  change HasFDerivAt (planeScaledBump r) _ z at hd
  rw [hd.fderiv]
  calc
    ‖(fderiv ℝ planeUnitBump (r⁻¹ • z)).comp (r⁻¹ • ContinuousLinearMap.id ℝ ℂ)‖ ≤
        ‖fderiv ℝ planeUnitBump (r⁻¹ • z)‖*‖r⁻¹ • ContinuousLinearMap.id ℝ ℂ‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ B*r⁻¹ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),ContinuousLinearMap.norm_id,mul_one]
      exact mul_le_mul_of_nonneg_right (hB _) (inv_nonneg.mpr hr.le)
    _ = B/r := by rw [div_eq_mul_inv]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SmallPerturbationHomeomorph
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small globally Lipschitz perturbations of the identity give actual
ambient homeomorphisms. These are the deformation maps for regular collars. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

lemma smallPerturbationHomeomorph_smooth {V : ℂ → ℂ} {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L < 1) (hs : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (smallPerturbationHomeomorph V hV hL) :=
  contDiff_id.add hs

lemma id_add_fderiv_injective {V : ℂ → ℂ} {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L < 1) {z : ℂ}
    (hd : DifferentiableAt ℝ V z) :
    Injective (fderiv ℝ (fun w => w + V w) z) := by
  have hb := norm_fderiv_le_of_lipschitz ℝ hV (x₀ := z)
  change Injective (fderiv ℝ (id + V) z)
  rw [fderiv_add differentiableAt_id hd, fderiv_id]
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have he : (fderiv ℝ V z) v = -v := by
    change v + (fderiv ℝ V z) v = 0 at hv
    exact eq_neg_of_add_eq_zero_right hv
  have hh : ‖v‖ ≤ (L : ℝ) * ‖v‖ := by
    calc
      ‖v‖ = ‖(fderiv ℝ V z) v‖ := by rw [he, norm_neg]
      _ ≤ ‖fderiv ℝ V z‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L : ℝ) * ‖v‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have hL' : (L : ℝ) < 1 := hL
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])

lemma smallPerturbationHomeomorph_inverse_smooth {V : ℂ → ℂ} {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L<1) (hs : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ ((smallPerturbationHomeomorph V hV hL).symm : ℂ → ℂ) := by
  let H := smallPerturbationHomeomorph V hV hL
  have hinj (z : ℂ) := id_add_fderiv_injective hV hL (hs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z)
  let A (z : ℂ) : ℂ ≃L[ℝ] ℂ :=
    (LinearEquiv.ofBijective (fderiv ℝ (fun w => w+V w) z).toLinearMap
      ⟨hinj z,(LinearMap.injective_iff_surjective).mp (hinj z)⟩).toContinuousLinearEquiv
  have hd (z : ℂ) : HasFDerivAt (H : ℂ → ℂ) (A z : ℂ →L[ℝ] ℂ) z :=
    ((contDiff_id.add hs).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z).hasFDerivAt
  exact H.contDiff_symm hd (contDiff_id.add hs)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LocalizedSmallPerturbation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A local error with small differential gives an actual smooth ambient
perturbation, with exact values on the inner disk and compact support. -/
open Set Function Filter Metric
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

lemma localizedPlaneError_eventually_zero {r : ℝ} (hr : 0 < r) (f : ℂ → ℂ)
    {z : ℂ} (hz : 2*r<‖z‖) : localizedPlaneError r f =ᶠ[𝓝 z] 0 := by
  filter_upwards [planeScaledBump_eventually_zero hr hz] with w hw
  simp only [localizedPlaneError,hw,zero_smul,Pi.zero_apply]

lemma localizedPlaneError_smooth {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hsub : closedBall 0 (2*r)⊆U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (localizedPlaneError r f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z∈U
  · exact (planeScaledBump_smooth r).contDiffAt.smul ((hf z hz).contDiffAt (hU.mem_nhds hz))
  · have hn : 2*r<‖z‖ := lt_of_not_ge (fun h => hz (hsub (mem_closedBall_zero_iff.mpr h)))
    exact contDiffAt_const.congr_of_eventuallyEq (localizedPlaneError_eventually_zero hr f hn)

lemma localizedPlaneError_derivative_bound {r B d : ℝ}
    (hr : 0 < r) (hB0 : 0≤B) (hd0 : 0≤d)
    (hB : ∀z,‖fderiv ℝ planeUnitBump z‖≤B)
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hsub : closedBall 0 (2*r)⊆U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hf' : ∀z∈closedBall 0 (2*r),‖fderiv ℝ f z‖≤d)
    (hf0 : ∀z∈closedBall 0 (2*r),‖f z‖≤2*r*d) (z : ℂ) :
    ‖fderiv ℝ (localizedPlaneError r f) z‖≤d*(1+2*B) := by
  by_cases hz : z∈closedBall 0 (2*r)
  · have hfd := ((hf z (hsub hz)).contDiffAt (hU.mem_nhds (hsub hz))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have hp := ((planeScaledBump_smooth r).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z).hasFDerivAt.smul hfd.hasFDerivAt
    change HasFDerivAt (localizedPlaneError r f) _ z at hp
    rw [hp.fderiv]
    calc
      ‖planeScaledBump r z • fderiv ℝ f z + (fderiv ℝ (planeScaledBump r) z).smulRight (f z)‖ ≤
          ‖planeScaledBump r z • fderiv ℝ f z‖+‖(fderiv ℝ (planeScaledBump r) z).smulRight (f z)‖ := norm_add_le _ _
      _ = |planeScaledBump r z| *‖fderiv ℝ f z‖ + ‖fderiv ℝ (planeScaledBump r) z‖*‖f z‖ := by
        rw [norm_smul,Real.norm_eq_abs,ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ d+(B/r)*(2*r*d) := by
        have hu := planeScaledBump_unit r z
        apply add_le_add
        · rw [abs_of_nonneg hu.1]
          exact (mul_le_mul_of_nonneg_right hu.2 (norm_nonneg _)).trans (by simpa using hf' z hz)
        · exact mul_le_mul (planeScaledBump_derivative_bound hB hr z) (hf0 z hz)
            (norm_nonneg _) (div_nonneg hB0 hr.le)
      _ = d*(1+2*B) := by field_simp
  · have he := localizedPlaneError_eventually_zero hr f
      (lt_of_not_ge (fun h => hz (mem_closedBall_zero_iff.mpr h)))
    rw [he.fderiv_eq]
    rw [fderiv_zero]
    simp only [Pi.zero_apply,norm_zero]
    positivity

lemma exists_localized_smooth_perturbation {r B d : ℝ}
    (hr : 0 < r) (hB0 : 0≤B) (hd0 : 0≤d) (hsmall : d*(1+2*B)<1)
    (hB : ∀z,‖fderiv ℝ planeUnitBump z‖≤B)
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hsub : closedBall 0 (2*r)⊆U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hf' : ∀z∈closedBall 0 (2*r),‖fderiv ℝ f z‖≤d)
    (hf0 : ∀z∈closedBall 0 (2*r),‖f z‖≤2*r*d) :
    ∃H : ℂ ≃ₜ ℂ, ContDiff ℝ ∞ (H : ℂ → ℂ) ∧ ContDiff ℝ ∞ (H.symm : ℂ → ℂ) ∧
      (∀z∈closedBall 0 r,H z=z+f z) ∧ (∀z,2*r≤‖z‖ → H z=z) := by
  let L : ℝ≥0 := ⟨d*(1+2*B),by positivity⟩
  have hs := localizedPlaneError_smooth hr hU hsub hf
  have hl : LipschitzWith L (localizedPlaneError r f) :=
    lipschitzWith_of_nnnorm_fderiv_le (hs.differentiable (by simp))
      (fun z => localizedPlaneError_derivative_bound hr hB0 hd0 hB hU hsub hf hf' hf0 z)
  have hL : L<1 := hsmall
  refine ⟨smallPerturbationHomeomorph _ hl hL,smallPerturbationHomeomorph_smooth hl hL hs,
    smallPerturbationHomeomorph_inverse_smooth hl hL hs,?_,?_⟩
  · intro z hz
    simp only [smallPerturbationHomeomorph_apply,localizedPlaneError,
      planeScaledBump_one hr (mem_closedBall_zero_iff.mp hz),one_smul]
  · intro z hz
    simp only [smallPerturbationHomeomorph_apply,localizedPlaneError,
      planeScaledBump_zero hr hz,zero_smul,add_zero]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSmoothExtension
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth map whose value and differential vanish at the origin has
a compactly supported small ambient extension on a sufficiently small disk. -/
open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma exists_smooth_local_error_extension {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (h0 : (0:ℂ)∈U) (hf : ContDiffOn ℝ ∞ f U)
    (hf0 : f 0=0) (hdf0 : fderiv ℝ f 0=0) {ε : ℝ} (hε : 0<ε) :
    ∃r:ℝ,0 < r ∧ 2*r<ε ∧ ∃H : ℂ ≃ₜ ℂ,
      ContDiff ℝ ∞ (H : ℂ → ℂ) ∧ ContDiff ℝ ∞ (H.symm : ℂ → ℂ) ∧
      (∀z∈closedBall 0 r,H z=z+f z) ∧ (∀z,2*r≤‖z‖ → H z=z) := by
  obtain ⟨B,hB0,hB⟩ := exists_planeUnitBump_derivative_bound
  let d := 1/(2*(1+2*B))
  have hd : 0<d := by dsimp [d] <;> positivity
  have hsmall : d*(1+2*B)<1 := by
    have hpos : 0<1+2*B := by positivity
    dsimp [d]
    field_simp
    nlinarith
  have hc : ContinuousAt (fun z => ‖fderiv ℝ f z‖) 0 :=
    ((hf 0 h0).contDiffAt (hU.mem_nhds h0)).continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.norm
  have hevent : ∀ᶠ z in 𝓝 (0:ℂ), z∈U ∧ ‖fderiv ℝ f z‖<d := by
    have hn : ‖fderiv ℝ f 0‖<d := by rw [hdf0,norm_zero];exact hd
    have hmem : ∀ᶠ z in 𝓝 (0:ℂ), z∈U := hU.mem_nhds h0
    exact hmem.and (hc.eventually (gt_mem_nhds hn))
  obtain ⟨R,hR,hsubR⟩ := Metric.eventually_nhds_iff.mp hevent
  let r := min R ε/4
  have hr : 0 < r := by dsimp [r] <;> positivity
  have hrR : 2*r<R := by dsimp [r] <;> linarith [min_le_left R ε]
  have hrε : 2*r<ε := by dsimp [r] <;> linarith [min_le_right R ε]
  have hball (z : ℂ) (hz : z∈closedBall 0 (2*r)) : z∈U ∧ ‖fderiv ℝ f z‖<d := by
    apply hsubR
    rw [dist_zero_right]
    exact (mem_closedBall_zero_iff.mp hz).trans_lt hrR
  have hsub : closedBall (0:ℂ) (2*r)⊆U := fun z hz => (hball z hz).1
  have hval : ∀z∈closedBall (0:ℂ) (2*r),‖f z‖≤2*r*d := by
    intro z hz
    have hn := (convex_closedBall (0:ℂ) (2*r)).norm_image_sub_le_of_norm_fderiv_le
      (fun w hw => ((hf w (hsub hw)).contDiffAt (hU.mem_nhds (hsub hw))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (fun w hw => (hball w hw).2.le)
      (mem_closedBall_self (by positivity)) hz
    rw [hf0,sub_zero,sub_zero] at hn
    exact hn.trans (by nlinarith [mem_closedBall_zero_iff.mp hz])
  obtain ⟨H,hHs,hHi,hHin,hHout⟩ := exists_localized_smooth_perturbation hr hB0 hd.le hsmall hB
    hU hsub hf (fun z hz => (hball z hz).2.le) hval
  exact ⟨r,hr,hrε,H,hHs,hHi,hHin,hHout⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_UnitAnalyticJordanParametrization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual analytic cap can be parametrized by the unit disk, so a
fixed symmetric annulus supplies its source boundary collar. -/
open Set Function Filter Metric Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_unit_analytic_jordan_parametrization {H:ℂ≃ₜℂ} (hH:IsAnalyticJordanCap H) :
    ∃S:Set ℂ, ∃β:ℂ→ℂ, IsOpen S ∧ closedBall 0 1⊆S ∧
      DifferentiableOn ℂ β S ∧ InjOn β S ∧
      β '' closedBall 0 1=closure (jordanInterior H) ∧
      β '' sphere 0 1=frontier (jordanInterior H) := by
  obtain ⟨W,α,c,r,hW,hr,hDW,hα,hi,hclosed,hboundary⟩ := exists_analytic_jordan_parametrization hH
  have hrc : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
  let A : ℂ≃ₜℂ := (Homeomorph.mulLeft₀ (r:ℂ) hrc).trans (Homeomorph.addRight c)
  have hAnorm (z:ℂ) : ‖A z-c‖=r*‖z‖ := by
    change ‖(r:ℂ)*z+c-c‖=r*‖z‖
    rw [add_sub_cancel_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  have hAc : A '' closedBall 0 1=closedBall c r := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      rw [mem_closedBall_iff_norm,hAnorm]
      have hz' := mem_closedBall_zero_iff.mp hz
      nlinarith
    · intro z hz
      obtain ⟨w,rfl⟩ := A.surjective z
      refine ⟨w,mem_closedBall_zero_iff.mpr ?_,rfl⟩
      rw [mem_closedBall_iff_norm,hAnorm] at hz
      nlinarith
  have hAs : A '' sphere 0 1=sphere c r := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      rw [mem_sphere_iff_norm,hAnorm,mem_sphere_zero_iff_norm.mp hz,mul_one]
    · intro z hz
      obtain ⟨w,rfl⟩ := A.surjective z
      refine ⟨w,mem_sphere_zero_iff_norm.mpr ?_,rfl⟩
      rw [mem_sphere_iff_norm,hAnorm] at hz
      nlinarith
  let S := A ⁻¹' W
  have hS : IsOpen S := hW.preimage A.continuous
  have hDS : closedBall (0:ℂ) 1⊆S := by
    intro z hz
    exact hDW (hAc ▸ mem_image_of_mem A hz)
  have hAd : DifferentiableOn ℂ A S := by
    intro z _
    exact (((differentiableAt_const (r:ℂ)).mul differentiableAt_id).add_const c).differentiableWithinAt
  refine ⟨S,α ∘ A,hS,hDS,hα.comp hAd (fun _ hz => hz),hi.comp A.injective.injOn (fun _ hz => hz),?_,?_⟩
  · rw [image_comp,hAc,hclosed]
  · rw [image_comp,hAs,hboundary]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactChartConjugation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend a compactly supported deformation in an actual plane chart by
identity outside the chart. The support and smoothness are retained. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma chartConjugate_contDiff (e : OpenPartialHomeomorph ℂ ℂ) (T : ℂ ≃ₜ ℂ)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K⊆e.source) (hfix : ∀x∉K,T x=x)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hT : ContDiff ℝ ∞ (T : ℂ → ℂ)) : ContDiff ℝ ∞ (chartConjugate e T) := by
  have himage : IsCompact (e '' K) := hKc.image_of_continuousOn (e.continuousOn.mono hK)
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x∈e.target
  · have hs := compactChart_maps_source e T hK hfix (e.map_target hx)
    have he' := (he _ hs).contDiffAt (e.open_source.mem_nhds hs)
    have hi' := (hi _ hx).contDiffAt (e.open_target.mem_nhds hx)
    apply (he'.comp x (hT.contDiffAt.comp x hi')).congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hx] with y hy
    simp only [chartConjugate,ite_eq_left hy,comp_apply]
  · have ho : x∈(e '' K)ᶜ := by
      rintro ⟨z,hz,rfl⟩
      exact hx (e.map_source (hK hz))
    apply contDiffAt_id.congr_of_eventuallyEq
    filter_upwards [himage.isClosed.isOpen_compl.mem_nhds ho] with y hy
    exact chartConjugate_eq_off e T hfix hy

lemma compactChartHomeomorph_image (e : OpenPartialHomeomorph ℂ ℂ) (T : ℂ ≃ₜ ℂ)
    {K A : Set ℂ} (hKc : IsCompact K) (hK : K⊆e.source) (hfix : ∀x∉K,T x=x)
    (hA : A⊆e.source) :
    compactChartHomeomorph e T hKc hK hfix '' (e '' A)=e '' (T '' A) := by
  rw [image_image,image_image]
  apply image_congr
  intro z hz
  change chartConjugate e T (e z)=e (T z)
  rw [chartConjugate,ite_eq_left (e.map_source (hA hz)),e.left_inv (hA hz)]

lemma compactChartHomeomorph_inverse_smooth (e : OpenPartialHomeomorph ℂ ℂ) (T : ℂ ≃ₜ ℂ)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K⊆e.source) (hfix : ∀x∉K,T x=x)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hT : ContDiff ℝ ∞ (T.symm : ℂ → ℂ)) :
    ContDiff ℝ ∞ ((compactChartHomeomorph e T hKc hK hfix).symm : ℂ → ℂ) :=
  chartConjugate_contDiff e T.symm hKc hK
    (fun x hx => homeomorph_symm_eq_of_fixed (hfix x hx)) he hi hT

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HolomorphicPlaneChart
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth plane chart and inverse supplied by a holomorphic
injection on an open set. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma holomorphicPlaneChart_smooth {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) :
    ContDiffOn ℝ ∞ (holomorphicPlaneChart hU hf hi) U := by
  intro x hx
  exact ((hf.analyticAt (hU.mem_nhds hx)).contDiffAt.restrict_scalars ℝ).contDiffWithinAt

lemma holomorphicPlaneChart_inverse_smooth {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) :
    ContDiffOn ℝ ∞ (holomorphicPlaneChart hU hf hi).symm (f '' U) := by
  intro y hy
  let e := holomorphicPlaneChart hU hf hi
  have hx : e.symm y∈U := e.map_target hy
  have hd : HasDerivAt (e : ℂ → ℂ) (deriv f (e.symm y)) (e.symm y) :=
    ((hf _ hx).differentiableAt (hU.mem_nhds hx)).hasDerivAt
  have hs : ContDiffAt ℂ ∞ (e : ℂ → ℂ) (e.symm y) :=
    (hf.analyticAt (hU.mem_nhds hx)).contDiffAt
  exact ((e.contDiffAt_symm_deriv (holomorphicInjOn_deriv_ne_zero hU hf hi hx)
    hy hd hs).restrict_scalars ℝ).contDiffWithinAt

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothRadialShrink
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth ambient radial contraction, fixed outside the larger disk.
It supplies the local shrinking step for analytic Jordan caps. -/
open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma radialShrink_inner {t a b : ℝ} (ha : 0<a) (hab : a<b) {z : ℂ} (hz : ‖z‖≤a) :
    radialShrink t a b z=t • z := by
  have hden : 0<b^2-a^2 := by nlinarith
  have harg : (‖z‖^2-a^2)/(b^2-a^2)≤0 := div_nonpos_of_nonpos_of_nonneg
    (by nlinarith [norm_nonneg z]) hden.le
  simp only [radialShrink,radialShrinkFactor,Real.smoothTransition.zero_of_nonpos harg,
    mul_zero,add_zero]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothRadialShrinkInverse
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.smoothRadialShrinkHomeomorph_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial contraction has an everywhere invertible differential,
so its actual global inverse is smooth. -/
open Set Function Filter Metric
open scoped Topology ContDiff RealInnerProductSpace
noncomputable section
namespace CircleDomainRigidity

lemma radialShrink_fderiv_injective {t a b : ℝ} (ht : 0<t) (ht1 : t≤1)
    (ha : 0<a) (hab : a<b) (z : ℂ) :
    Injective (fderiv ℝ (radialShrink t a b) z) := by
  let q : ℝ → ℝ := fun s => t+(1-t)*Real.smoothTransition ((s-a^2)/(b^2-a^2))
  have hden : 0<b^2-a^2 := by nlinarith
  have hq : ContDiff ℝ ∞ q := by dsimp [q];fun_prop
  have hmono : Monotone q := by
    intro r s hrs
    dsimp [q]
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr ht1)
    exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_right hrs _) hden.le)
  have hqp : 0<q (‖z‖^2) := radialShrinkFactor_pos ht ht1
  have hdq : 0≤deriv q (‖z‖^2) := hmono.deriv_nonneg
  have hcomp := (hq.differentiable (by simp) (‖z‖^2)).hasDerivAt.comp_hasFDerivAt z
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hf := hcomp.smul (hasFDerivAt_id z)
  have heq : (fun x : ℂ => q (‖x‖^2) • x)=radialShrink t a b := rfl
  change HasFDerivAt (fun x : ℂ => q (‖x‖^2) • x) _ z at hf
  rw [heq] at hf
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  rw [hf.fderiv] at hv
  have he : q (‖z‖^2) • v + (deriv q (‖z‖^2) * (2*(inner ℝ z v))) • z=0 := by
    simp only [add_apply,smul_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,comp_apply,id_eq] at hv
    have hscalar : deriv q (‖z‖^2) • (2 • (inner ℝ z v)) =
        deriv q (‖z‖^2) * (2 * (inner ℝ z v)) := by
      simp only [two_smul,smul_eq_mul]
      ring
    rwa [hscalar] at hv

  have hi := congrArg (fun w : ℂ => (inner ℝ v w)) he
  have hvv : (inner ℝ v v)=‖v‖^2 := real_inner_self_eq_norm_sq v
  have hzv : (inner ℝ v z)=(inner ℝ z v) := (real_inner_comm v z).symm
  simp only [inner_add_right,inner_smul_right,inner_zero_right,hvv,hzv] at hi
  have hsum : q (‖z‖^2)*‖v‖^2 + 2*deriv q (‖z‖^2)*(inner ℝ z v)^2=0 := by
    linear_combination hi
  have hnon : 0≤2*deriv q (‖z‖^2)*(inner ℝ z v)^2 :=
    mul_nonneg (mul_nonneg (by norm_num) hdq) (sq_nonneg _)
  have hz : q (‖z‖^2)*‖v‖^2=0 :=
    le_antisymm (by linarith) (mul_nonneg hqp.le (sq_nonneg _))
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left hqp.ne'))

lemma smoothRadialShrinkHomeomorph_inverse_contDiff {t a b : ℝ}
    (ht : 0<t) (ht1 : t≤1) (ha : 0<a) (hab : a<b) :
    ContDiff ℝ ∞ ((smoothRadialShrinkHomeomorph ht ht1 ha hab).symm : ℂ → ℂ) := by
  let H := smoothRadialShrinkHomeomorph ht ht1 ha hab
  let A (z : ℂ) : ℂ ≃L[ℝ] ℂ :=
    (LinearEquiv.ofBijective (fderiv ℝ (radialShrink t a b) z).toLinearMap
      ⟨radialShrink_fderiv_injective ht ht1 ha hab z,
        (LinearMap.injective_iff_surjective).mp (radialShrink_fderiv_injective ht ht1 ha hab z)⟩).toContinuousLinearEquiv
  have hd (z : ℂ) : HasFDerivAt (H : ℂ → ℂ) (A z : ℂ →L[ℝ] ℂ) z :=
    ((radialShrink_contDiff t a b).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z).hasFDerivAt
  exact H.contDiff_symm hd (radialShrink_contDiff t a b)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RadialShrinkImages
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact disk images of the ambient radial shrinker. -/
open Set Function Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma radialShrink_image_inner {t a b : ℝ} (ht : 0<t) (ha : 0<a) (hab : a<b) :
    radialShrink t a b '' closedBall 0 a=closedBall 0 (t*a) := by
  apply Subset.antisymm
  · rintro _ ⟨z,hz,rfl⟩
    have hn : ‖z‖≤a := mem_closedBall_zero_iff.mp hz
    rw [radialShrink_inner ha hab hn]
    apply mem_closedBall_zero_iff.mpr
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left hn ht.le
  · intro y hy
    have hn : ‖y‖≤t*a := mem_closedBall_zero_iff.mp hy
    have hz : ‖t⁻¹ • y‖≤a := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
      calc
        t⁻¹*‖y‖ ≤ t⁻¹*(t*a) := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr ht.le)
        _ = a := by field_simp
    refine ⟨t⁻¹ • y,mem_closedBall_zero_iff.mpr hz,?_⟩
    rw [radialShrink_inner ha hab hz,smul_smul,mul_inv_cancel₀ ht.ne',one_smul]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_AnalyticCapShrink
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shrink one actual analytic Jordan cap within any prescribed open
neighborhood. The ambient map and its inverse are smooth and fix every
point outside one compact subset of that neighborhood. -/
open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_analytic_cap_shrinker {H : ℂ ≃ₜ ℂ} (ha : IsAnalyticJordanCap H)
    {O : Set ℂ} (hO : IsOpen O) (hHO : closure (jordanInterior H)⊆O) :
    ∃ (β : ℂ → ℂ) (S K : Set ℂ), IsOpen S ∧ closedBall 0 1⊆S ∧
      DifferentiableOn ℂ β S ∧ InjOn β S ∧ IsCompact K ∧ K⊆O ∧
      β '' closedBall 0 1=closure (jordanInterior H) ∧
      (∀t:ℝ,0<t → t≤1 → ∃G : ℂ ≃ₜ ℂ,
        ContDiff ℝ ∞ (G : ℂ → ℂ) ∧ ContDiff ℝ ∞ (G.symm : ℂ → ℂ) ∧
        (∀z∉K,G z=z) ∧ G '' closure (jordanInterior H)=β '' closedBall 0 t) := by
  obtain ⟨S,β,hS,hDS,hβ,hi,hclosed,_⟩ := exists_unit_analytic_jordan_parametrization ha
  let U := S∩β ⁻¹' O
  have hU : IsOpen U := hβ.continuousOn.isOpen_inter_preimage hS hO
  have hDU : closedBall (0:ℂ) 1⊆U := by
    intro z hz
    exact ⟨hDS hz,hHO (hclosed ▸ mem_image_of_mem β hz)⟩
  obtain ⟨δ,hδ,hthick⟩ := (isCompact_closedBall (0:ℂ) 1).exists_cthickening_subset_open hU hDU
  rw [cthickening_closedBall hδ.le zero_le_one] at hthick
  let b := δ+1
  have hb : 1<b := by dsimp [b] <;> linarith
  have hBU : closedBall (0:ℂ) b⊆U := hthick
  let e := holomorphicPlaneChart hU (hβ.mono inter_subset_left) (hi.mono inter_subset_left)
  let K := β '' closedBall 0 b
  have hK : IsCompact K := (isCompact_closedBall (0:ℂ) b).image_of_continuousOn
    (hβ.continuousOn.mono (hBU.trans inter_subset_left))
  have hKO : K⊆O := by rintro _ ⟨z,hz,rfl⟩;exact (hBU hz).2
  refine ⟨β,S,K,hS,hDS,hβ,hi,hK,hKO,hclosed,?_⟩
  intro t ht ht1
  let T := smoothRadialShrinkHomeomorph ht ht1 zero_lt_one hb
  have hfix : ∀z∉closedBall (0:ℂ) b,T z=z := by
    intro z hz
    apply radialShrink_outer zero_lt_one hb
    exact (lt_of_not_ge (by simpa only [mem_closedBall,dist_zero_right] using hz)).le
  let G := compactChartHomeomorph e T (isCompact_closedBall 0 b) hBU hfix
  have hes := holomorphicPlaneChart_smooth hU (hβ.mono inter_subset_left) (hi.mono inter_subset_left)
  have his := holomorphicPlaneChart_inverse_smooth hU (hβ.mono inter_subset_left) (hi.mono inter_subset_left)
  refine ⟨G,?_,?_,?_,?_⟩
  · exact chartConjugate_contDiff e T (isCompact_closedBall 0 b) hBU hfix hes his
      (radialShrink_contDiff t 1 b)
  · exact compactChartHomeomorph_inverse_smooth e T (isCompact_closedBall 0 b) hBU hfix hes his
      (smoothRadialShrinkHomeomorph_inverse_contDiff ht ht1 zero_lt_one hb)
  · intro z hz
    exact chartConjugate_eq_off e T hfix hz
  · rw [←hclosed]
    change G '' (e '' closedBall 0 1)=e '' closedBall 0 t
    rw [compactChartHomeomorph_image e T (isCompact_closedBall 0 b) hBU hfix hDU]
    change e '' (radialShrink t 1 b '' closedBall 0 1)=_
    rw [radialShrink_image_inner ht zero_lt_one hb,mul_one]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_AnalyticCapRounding
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Round one analytic Jordan cap by an actual compactly supported smooth
plane diffeomorphism inside any prescribed open neighborhood. -/
open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_smooth_analytic_cap_rounding {H : ℂ ≃ₜ ℂ} (ha : IsAnalyticJordanCap H)
    {O : Set ℂ} (hO : IsOpen O) (hHO : closure (jordanInterior H)⊆O) :
    ∃ (G : ℂ ≃ₜ ℂ) (c : ℂ) (r : ℝ),0 < r ∧
      ContDiff ℝ ∞ (G : ℂ → ℂ) ∧ ContDiff ℝ ∞ (G.symm : ℂ → ℂ) ∧
      (∀z∉O,G z=z) ∧ G '' closure (jordanInterior H)=closedBall c r := by
  obtain ⟨β,S,K,hS,hDS,hβ,hi,hK,hKO,hclosed,hshrink⟩ := exists_analytic_cap_shrinker ha hO hHO
  have hzero : (0:ℂ)∈S := hDS (mem_closedBall_self zero_le_one)
  let d := deriv β 0
  have hd : d≠0 := holomorphicInjOn_deriv_ne_zero hS hβ hi hzero
  have hdn : 0<‖d‖ := norm_pos_iff.mpr hd
  let L : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ d hd).trans (Homeomorph.addRight (β 0))
  have hL (z : ℂ) : L z=d*z+β 0 := rfl
  have hLi (z : ℂ) : L.symm z=(z-β 0)/d := by
    apply L.injective
    rw [L.apply_symm_apply,hL,mul_div_cancel₀ _ hd,sub_add_cancel]
  have hLs : ContDiff ℝ ∞ (L : ℂ → ℂ) := contDiff_const.mul contDiff_id |>.add contDiff_const
  have hLis : ContDiff ℝ ∞ (L.symm : ℂ → ℂ) := by
    have he : (L.symm : ℂ → ℂ)=(fun z => (z-β 0)/d) := funext hLi
    rw [he]
    exact (contDiff_id.sub contDiff_const).div_const d
  let f : ℂ → ℂ := fun z => (β z-β 0)/d-z
  have hβs : ContDiffOn ℝ ∞ β S := holomorphicPlaneChart_smooth hS hβ hi
  have hfs : ContDiffOn ℝ ∞ f S :=
    ((hβs.sub contDiffOn_const).div_const d).sub contDiffOn_id
  have hf0 : f 0=0 := by simp [f]
  have hdf : HasDerivAt f 0 0 := by
    have hb := ((hβ 0 hzero).differentiableAt (hS.mem_nhds hzero)).hasDerivAt
    have hh := ((hb.sub_const (β 0)).div_const d).sub (hasDerivAt_id (0:ℂ))
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (simp [f,d,div_self hd])
    rfl
  have hdf0 : fderiv ℝ f 0=0 := by
    rw [(hdf.hasFDerivAt.restrictScalars ℝ).fderiv]
    ext z
    simp
  have hcO : β 0∈O := hHO (hclosed ▸ mem_image_of_mem β (mem_closedBall_self zero_le_one))
  obtain ⟨ρ,hρ,hρO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hcO)
  let ε := min 1 (ρ/‖d‖)
  have hε : 0<ε := lt_min zero_lt_one (div_pos hρ hdn)
  obtain ⟨t,ht,htε,Q,hQs,hQis,hQin,hQout⟩ :=
    exists_smooth_local_error_extension hS hzero hfs hf0 hdf0 hε
  have ht1 : t≤1 := by dsimp [ε] at htε <;> linarith [min_le_left (1:ℝ) (ρ/‖d‖)]
  obtain ⟨T,hTs,hTis,hTout,hTimage⟩ := hshrink t ht ht1
  let P := L.symm.trans (Q.trans L)
  have hPs : ContDiff ℝ ∞ (P : ℂ → ℂ) := hLs.comp (hQs.comp hLis)
  have hPis : ContDiff ℝ ∞ (P.symm : ℂ → ℂ) := hLs.comp (hQis.comp hLis)
  have hPout (z : ℂ) (hz : z∉O) : P z=z := by
    have hdist : ρ≤‖z-β 0‖ := le_of_not_gt (fun hh => hz (hρO (mem_ball_iff_norm.mpr hh)))
    have hnorm : ‖z-β 0‖=‖d‖*‖L.symm z‖ := by
      have he := hL (L.symm z)
      rw [L.apply_symm_apply] at he
      calc
        ‖z-β 0‖=‖d*L.symm z‖ := by congr 1;linear_combination he
        _=‖d‖*‖L.symm z‖ := norm_mul _ _
    have hsmall : 2*t<ρ/‖d‖ := htε.trans_le (min_le_right _ _)
    have hlarge : 2*t≤‖L.symm z‖ := by
      rw [lt_div_iff₀ hdn] at hsmall
      nlinarith
    change L (Q (L.symm z))=z
    rw [hQout _ hlarge,L.apply_symm_apply]
  have hPimage : P '' (L '' closedBall 0 t)=β '' closedBall 0 t := by
    rw [image_image]
    apply image_congr
    intro z hz
    change L (Q (L.symm (L z)))=β z
    rw [L.symm_apply_apply,hQin z hz,hL]
    dsimp [f]
    field_simp
    ring
  have hLimage : L '' closedBall 0 t=closedBall (β 0) (‖d‖*t) := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      apply mem_closedBall_iff_norm.mpr
      rw [hL,add_sub_cancel_right,norm_mul]
      exact mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hdn.le
    · intro z hz
      refine ⟨L.symm z,?_,L.apply_symm_apply z⟩
      apply mem_closedBall_zero_iff.mpr
      have hh : ‖z-β 0‖=‖d‖*‖L.symm z‖ := by
        conv_lhs => rw [←L.apply_symm_apply z,hL,add_sub_cancel_right,norm_mul]
      rw [mem_closedBall_iff_norm,hh] at hz
      nlinarith
  refine ⟨T.trans P.symm,β 0,‖d‖*t,mul_pos hdn ht,hPis.comp hTs,hTis.comp hPs,?_,?_⟩
  · intro z hz
    change P.symm (T z)=z
    rw [hTout z (fun h => hz (hKO h))]
    exact homeomorph_symm_eq_of_fixed (hPout z hz)
  · change (P.symm ∘ T) '' closure (jordanInterior H)=_
    rw [image_comp,hTimage,←hPimage,image_image]
    simpa only [P.symm_apply_apply,image_id'] using hLimage

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteAnalyticRounding
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous smooth rounding of a finite disjoint analytic Jordan family.
The actual ambient diffeomorphism fixes the complement of a bounded disk. -/
open Set Function Metric Bornology
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_finite_analytic_rounding {I : Type*} [Finite I]
    (C : FiniteJordanConfiguration I) (ha : ∀i,IsAnalyticJordanCap (C.hole i)) :
    ∃ (P : ℂ ≃ₜ ℂ) (c : I → ℂ) (r : I → ℝ) (R : ℝ),0<R ∧
      ContDiff ℝ ∞ (P : ℂ → ℂ) ∧ ContDiff ℝ ∞ (P.symm : ℂ → ℂ) ∧
      (∀z,R≤‖z‖ → P z=z) ∧ (∀i,0 < r i) ∧
      ∀i,P '' closure (jordanInterior (C.hole i))=closedBall (c i) (r i) := by
  classical
  let := Fintype.ofFinite I
  let A := fun i => closure (jordanInterior (C.hole i))
  have hA (i : I) : IsCompact (A i) := isCompact_closure_jordanInterior (C.hole i)
  obtain ⟨R,hR,hbound⟩ := (isCompact_iUnion hA).isBounded.exists_pos_norm_lt
  obtain ⟨U,hU,hAU,hUR,hUd⟩ := finite_disjoint_closed_neighborhoods A
    (fun _ => ball (0:ℂ) R) (fun i => (hA i).isClosed) (fun _ => isOpen_ball)
    (fun i z hz => mem_ball_zero_iff.mpr (hbound _ (mem_iUnion.mpr ⟨i,hz⟩))) C.disjoint
  choose T c r hr hTs hTis hfix himage using fun i =>
    exists_smooth_analytic_cap_rounding (ha i) (hU i) (hAU i)
  have hUd' : Pairwise (fun i j => Disjoint (U i) (U j)) := by
    intro i j hij
    exact (hUd hij).mono subset_closure subset_closure
  obtain ⟨P,hPs,hPis,hPf,hP⟩ := exists_disjoint_supported_composition A U hAU hUd'
    T hTs hTis hfix
  refine ⟨P,c,r,R,hR,hPs,hPis,?_,hr,?_⟩
  · intro z hz
    apply hPf
    intro i hi
    exact (not_lt_of_ge hz) (mem_ball_zero_iff.mp (hUR i (subset_closure hi)))
  · intro i
    exact (hP i).trans (himage i)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_FiniteAnalyticBeltrami
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth comparison with a finite circular domain, together with
the compactly supported strict Beltrami coefficient of its inverse. -/
open Set Function Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer CannonBeltrami

lemma exists_finite_analytic_rounding_coefficient {I : Type*} [Finite I]
    (C : FiniteJordanConfiguration I) (ha : ∀i,IsAnalyticJordanCap (C.hole i)) :
    ∃ (P : ℂ ≃ₜ ℂ) (c : I → ℂ) (r : I → ℝ) (μ : ℂ → ℂ) (k S : ℝ),
      ContDiff ℝ ∞ (P : ℂ → ℂ) ∧ ContDiff ℝ ∞ (P.symm : ℂ → ℂ) ∧
      (∀i,0 < r i) ∧
      (∀i,P '' closure (jordanInterior (C.hole i))=closedBall (c i) (r i)) ∧
      ContDiff ℝ ∞ μ ∧ 0≤k ∧ k<1 ∧ 0<S ∧
      (∀z,‖μ z‖≤k) ∧ (∀z,S≤‖z‖ → μ z=0) ∧
      ∀z,partialBar P.symm z=μ z*partialZ P.symm z := by
  obtain ⟨P,c,r,R,hR,hPs,hPis,hPf,hr,hP⟩ := exists_finite_analytic_rounding C ha
  have hPif : ∀z,R≤‖z‖ → P.symm z=z := by
    intro z hz
    apply P.injective
    rw [P.apply_symm_apply,hPf z hz]
  obtain ⟨μ,k,S,hμ,hk,hk1,hS,hb,hz,he⟩ := compact_diffeomorphism_beltrami P.symm hPis hPs hPif
  exact ⟨P,c,r,μ,k,S,hPs,hPis,hr,hP,hμ,hk,hk1,hS,hb,hz,he⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteRoundComparison
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact labeled spherical exterior correspondence for the constructed
smooth finite rounding. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma rounding_round_disks_disjoint {I : Type*} (C : FiniteJordanConfiguration I)
    (P : ℂ ≃ₜ ℂ) (c : I → ℂ) (r : I → ℝ)
    (hp : ∀i,P '' closure (jordanInterior (C.hole i))=closedBall (c i) (r i)) :
    Pairwise (fun i j => Disjoint (((↑) : ℂ → Sphere) '' closedBall (c i) (r i))
      (((↑) : ℂ → Sphere) '' closedBall (c j) (r j))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro p ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
  have hyx : y=x := OnePoint.coe_injective he
  subst y
  rw [←hp i] at hx
  rw [←hp j] at hy
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,he⟩ := hy
  have hba : b=a := P.injective he
  exact Set.disjoint_left.mp (C.disjoint hij) ha (hba ▸ hb)

lemma rounding_spherical_cap_image {I : Type*} (C : FiniteJordanConfiguration I)
    (P : ℂ ≃ₜ ℂ) (c : I → ℂ) (r : I → ℝ)
    (hp : ∀i,P '' closure (jordanInterior (C.hole i))=closedBall (c i) (r i)) (i : I) :
    P.onePointCongr '' closedTerminalCap (C.hole i)=
      ((↑) : ℂ → Sphere) '' closedBall (c i) (r i) := by
  rw [closedTerminalCap,CannonSphereReflection.onePoint_image,hp]

lemma rounding_spherical_exterior_image {I : Type*} [Finite I] (C : FiniteJordanConfiguration I)
    (P : ℂ ≃ₜ ℂ) (c : I → ℂ) (r : I → ℝ)
    (hp : ∀i,P '' closure (jordanInterior (C.hole i))=closedBall (c i) (r i)) :
    P.onePointCongr '' C.region=(⋃i,((↑) : ℂ → Sphere) '' closedBall (c i) (r i))ᶜ := by
  change P.onePointCongr '' (⋃i,closedTerminalCap (C.hole i))ᶜ=_
  rw [P.onePointCongr.image_compl,image_iUnion]
  simp_rw [rounding_spherical_cap_image C P c r hp]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_AnalyticReflectionData
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual data for finite analytic uniformization by invariant Beltrami
coefficients. Conformality of the straightened comparison and roundness of
its boundary images are not fields and remain to be proved. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer CannonBeltrami
attribute [local instance] sphereMetric sphereBorel

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_12
lemma exists_analytic_reflection_data {I : Type*} [Finite I]
    (C : FiniteJordanConfiguration I) (ha : ∀i,IsAnalyticJordanCap (C.hole i)) :
    Nonempty (AnalyticReflectionData C) := by
  obtain ⟨P,c,r,μ,k,S,hPs,hPis,hr,hcap,hμs,hk,hk1,hS,hb,hz,he⟩ :=
    exists_finite_analytic_rounding_coefficient C ha
  have hd := rounding_round_disks_disjoint C P c r hcap
  obtain ⟨E,T,g,S,L,hEm,hEz,hEb,hEf,hEinv,hg,hc⟩ := exists_round_invariant_principal_approximation_with_coefficient
    c r hr hd μ hμs.continuous.measurable hk hk1 hb hz
  refine ⟨{
    comparison := P
    center := c
    radius := r
    radius_pos := hr
    comparison_smooth := hPs
    comparison_inverse_smooth := hPis
    cap_image := hcap
    baseCoefficient := μ
    bound := k
    bound_nonneg := hk
    bound_lt_one := hk1
    base_bound := hb
    base_equation := he
    extension := E
    extension_measurable := hEm
    extension_bound := hEb
    extension_base := ?_
    extension_invariant := hEinv
    density := g
    supportRadius := T
    extension_zero := hEz
    approximation := S
    limitData := L
    density_equation := hg
    coefficient_tendsto := hc }⟩
  rwa [rounding_spherical_exterior_image C P c r hcap]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_SmoothReflectionConjugacy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact antiholomorphic error of a smooth conjugated reflection. The
error is the failure of the smooth coefficient to obey reflection
invariance; no regularity of the limiting coefficient is assumed. -/
open Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma partials_conjugate {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    partialZ (fun w => star (f w)) z=star (partialBar f z) ∧
    partialBar (fun w => star (f w)) z=star (partialZ f z) := by
  have hd := ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt.comp z hf.hasFDerivAt).fderiv
  change fderiv ℝ (fun w => star (f w)) z=_ at hd
  simp only [partialZ,partialBar,hd,ContinuousLinearMap.comp_apply]
  change (star (fderiv ℝ f z 1)-Complex.I*star (fderiv ℝ f z Complex.I))/2=_ ∧
    (star (fderiv ℝ f z 1)+Complex.I*star (fderiv ℝ f z Complex.I))/2=_
  simp only [map_div₀,map_add,map_sub,map_mul,Complex.star_def,Complex.conj_I,map_ofNat]
  constructor <;> ring

lemma smooth_reflection_conjugate_error (F : ℂ ≃ₜ ℂ)
    (hF : Differentiable ℝ (F : ℂ → ℂ)) (hFi : Differentiable ℝ (F.symm : ℂ → ℂ))
    (μ : ℂ → ℂ) (he : ∀w,partialBar F w=μ w*partialZ F w)
    {R : ℂ → ℂ} {z : ℂ} (hR : DifferentiableAt ℝ R z) (hRz : partialZ R z=0) :
    partialBar (fun w => star (F (R (F.symm w)))) (F z)=
      star (partialZ F (R z)) *
        (partialBar R z*star (μ (R z))-μ z*star (partialBar R z)) *
        star (partialZ F.symm (F z)) := by
  have hn := smooth_homeomorph_partialZ_ne_zero F hF hFi μ he
  have hi := inverse_partialBar F hF hFi μ he hn (F z)
  have hFR := (hF (R z)).comp z hR
  have hH := (Complex.conjCLE.differentiableAt.comp z hFR)
  have hH' : DifferentiableAt ℝ (fun w => star (F (R w))) (F.symm (F z)) := by
    rw [F.symm_apply_apply]
    convert hH using 1 <;> rfl
  have hc := (partials_comp hH' (hFi (F z))).2
  change partialBar ((fun w => star (F (R w))) ∘ F.symm) (F z)=_ at hc
  simp only [F.symm_apply_apply] at hi hc
  have hstar := partials_conjugate hFR
  have hcomp := partials_comp (hF (R z)) hR
  simp only [Function.comp_def] at hstar hcomp hc
  rw [hstar.1,hstar.2,hcomp.1,hcomp.2] at hc
  simp only [hRz,mul_zero,star_zero,zero_add,add_zero,he,hi] at hc
  rw [hc]
  simp only [star_mul,star_star]
  ring

lemma smooth_reflection_conjugate_phase_error (F : ℂ ≃ₜ ℂ)
    (hF : Differentiable ℝ (F : ℂ → ℂ)) (hFi : Differentiable ℝ (F.symm : ℂ → ℂ))
    (μ : ℂ → ℂ) (he : ∀w,partialBar F w=μ w*partialZ F w)
    {R : ℂ → ℂ} {z : ℂ} (hR : DifferentiableAt ℝ R z) (hRz : partialZ R z=0)
    (s : ℂ) (hs : partialBar R z=s*star (partialBar R z)) :
    partialBar (fun w => star (F (R (F.symm w)))) (F z)=
      star (partialZ F (R z))*star (partialBar R z)*
        (s*star (μ (R z))-μ z)*star (partialZ F.symm (F z)) := by
  rw [smooth_reflection_conjugate_error F hF hFi μ he hR hRz]
  conv_lhs => enter [1,2,1,1]; rw [hs]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_RoundReflectionDifferential
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Plane formula and differential of a circular reflection off its pole. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma roundReflectionPlane_ne_center (c : ℂ) {r : ℝ} (hr : r≠0) {z : ℂ} (hz : z≠c) :
    roundReflectionPlane c r z≠c := by
  have hr' : (r:ℂ)≠0 := by exact_mod_cast hr
  intro hh
  have hh' : (r:ℂ)^2/star (z-c)=0 := by
    exact add_left_cancel (hh.trans (add_zero c).symm)
  exact (div_ne_zero (pow_ne_zero 2 hr') (star_ne_zero.mpr (sub_ne_zero.mpr hz))) hh'

lemma roundReflectionPlane_involutive (c : ℂ) {r : ℝ} (hr : r≠0) :
    Involutive (roundReflectionPlane c r) := by
  intro z
  by_cases hz : z=c
  · simp [roundReflectionPlane,hz]
  · have hr' : (r:ℂ)≠0 := by exact_mod_cast hr
    simp only [roundReflectionPlane,add_sub_cancel_left,map_div₀,map_pow,
      Complex.star_def,Complex.conj_ofReal,Complex.conj_conj]
    field_simp [sub_ne_zero.mpr hz,hr']
    ring

lemma roundReflectionPlane_differentiable {c z : ℂ} {r : ℝ} (hz : z≠c) :
    DifferentiableAt ℝ (roundReflectionPlane c r) z := by
  unfold roundReflectionPlane
  apply DifferentiableAt.const_add
  convert ((Complex.conjCLE.differentiableAt.comp z (differentiableAt_id.sub_const c)).inv
      (star_ne_zero.mpr (sub_ne_zero.mpr hz))).const_mul ((r:ℂ)^2) using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma partialZ_eq_deriv_of_complex {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    partialZ f z=deriv f z := by
  have hh := fderiv_wirtinger f z 1
  rw [partialBar_zero_of_differentiableAt hf,mul_one,zero_mul,add_zero] at hh
  rw [hf.fderiv_restrictScalars ℝ] at hh
  exact hh.symm

lemma roundReflectionPlane_partials {c z : ℂ} {r : ℝ} (hz : z≠c) :
    partialZ (roundReflectionPlane c r) z=0 ∧
      partialBar (roundReflectionPlane c r) z= -(r:ℂ)^2/(star (z-c))^2 := by
  let f : ℂ → ℂ := fun w => star c+(r:ℂ)^2/(w-c)
  have hd : HasDerivAt f (-(r:ℂ)^2/(z-c)^2) z := by
    convert (((hasDerivAt_id z).sub_const c).inv (sub_ne_zero.mpr hz)).const_mul ((r:ℂ)^2)
      |>.const_add (star c) using 1
    all_goals try with_reducible_and_instances rfl
    · funext w; dsimp [f] <;> ring
    · dsimp <;> ring
  have he : roundReflectionPlane c r=fun w => star (f w) := by
    funext w
    simp [roundReflectionPlane,f]
  rw [he]
  have hh := partials_conjugate (hd.differentiableAt.restrictScalars ℝ)
  rw [partialBar_zero_of_differentiableAt hd.differentiableAt,
    partialZ_eq_deriv_of_complex hd.differentiableAt,hd.deriv] at hh
  simpa only [star_zero,map_neg,map_div₀,map_pow,Complex.star_def,Complex.conj_ofReal] using hh

lemma roundReflectionPlane_phase {c z : ℂ} {r : ℝ} (hz : z≠c) :
    partialBar (roundReflectionPlane c r) z=
      circleReflectionPhase c z*star (partialBar (roundReflectionPlane c r) z) := by
  rw [(roundReflectionPlane_partials hz).2]
  simp only [circleReflectionPhase,ite_eq_right hz,map_neg,map_div₀,map_pow,
    Complex.star_def,Complex.conj_ofReal,Complex.conj_conj]
  field_simp [sub_ne_zero.mpr hz]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_RoundReflectionMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circular reflection preserves planar null sets, including the harmless
chosen value at its single pole. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma roundReflectionPlane_measurable (c : ℂ) (r : ℝ) :
    Measurable (roundReflectionPlane c r) :=
  measurable_const.add (measurable_const.div
    (Complex.continuous_conj.measurable.comp (measurable_id.sub_const c)))

lemma roundReflectionPlane_quasiMeasurePreserving (c : ℂ) {r : ℝ} (hr : r≠0) :
    Measure.QuasiMeasurePreserving (roundReflectionPlane c r) volume volume := by
  let R := roundReflectionPlane c r
  have hR := roundReflectionPlane_involutive c hr
  refine ⟨roundReflectionPlane_measurable c r,Measure.AbsolutelyContinuous.mk ?_⟩
  intro s hs hs0
  rw [Measure.map_apply (roundReflectionPlane_measurable c r) hs]
  have heq : R ⁻¹' s=R '' s := by
    ext z
    constructor
    · intro hz
      exact ⟨R z,hz,hR z⟩
    · rintro ⟨w,hw,rfl⟩
      change roundReflectionPlane c r (roundReflectionPlane c r w)∈s
      rw [hR w]
      exact hw
  change volume (R ⁻¹' s)=0
  rw [heq]
  have hz : volume (s \ {c})=0 := measure_mono_null sdiff_subset hs0
  have hi : volume (R '' (s \ {c}))=0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun z hz => (roundReflectionPlane_differentiable
        (show z≠c from fun h => hz.2 (by simp [h]))).differentiableWithinAt) hz
  apply measure_mono_null (show R '' s⊆R '' (s \ {c}) ∪ {c} from ?_)
    (measure_union_null hi (measure_singleton c))
  rintro z ⟨w,hw,rfl⟩
  by_cases hwc : w=c
  · right
    simp [R,roundReflectionPlane,hwc]
  · exact Or.inl ⟨w,⟨hw,by simpa using hwc⟩,rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_PrincipalReflectionDefect
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mollified coefficients' reflection defects are uniformly
bounded and tend almost everywhere to zero. The smooth conjugate's exact
antiholomorphic derivative is expressed using this defect. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma reflectionDefect_measurable (D : AnalyticReflectionData C) (i : I) (n : ℕ) :
    Measurable (D.reflectionDefect i n) :=
  ((circleReflectionPhase_measurable (D.center i)).mul
    (Complex.continuous_conj.measurable.comp
      ((D.approximation.coefficient _).continuous.measurable.comp
        (roundReflectionPlane_measurable _ _)))).sub
    (D.approximation.coefficient _).continuous.measurable

lemma reflectionDefect_bound (D : AnalyticReflectionData C) (i : I) (n : ℕ) (z : ℂ) :
    ‖D.reflectionDefect i n z‖≤2*D.bound := by
  apply (norm_sub_le _ _).trans
  rw [norm_mul,norm_star,circleReflectionPhase_norm,one_mul]
  linarith [D.approximation.coefficient_bound (D.limitData.index n) z,
    D.approximation.coefficient_bound (D.limitData.index n)
      (roundReflectionPlane (D.center i) (D.radius i) z)]

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_13
lemma reflectionDefect_tendsto (D : AnalyticReflectionData C) (i : I) :
    ∀ᵐz ∂volume,Tendsto (fun n => D.reflectionDefect i n z) atTop (𝓝 0) := by
  have hR := roundReflectionPlane_quasiMeasurePreserving (D.center i) (D.radius_pos i).ne'
  filter_upwards [D.coefficient_tendsto,hR.ae D.coefficient_tendsto,volume.ae_ne (D.center i)]
    with z hz hRz hzc
  have he := D.extension_invariant i (z : Sphere)
  rw [roundDiskReflection_coe (D.center i) (D.radius_pos i) hzc] at he
  change D.extension (z : Sphere)=circleReflectionPhase (D.center i) z*
    star (D.extension (roundReflectionPlane (D.center i) (D.radius i) z : Sphere)) at he
  have ht := ((hRz.comp D.limitData.index_strict.tendsto_atTop).star.const_mul
    (circleReflectionPhase (D.center i) z)).sub
    (hz.comp D.limitData.index_strict.tendsto_atTop)
  simpa only [reflectionDefect,Function.comp_def,←he,sub_self] using ht

lemma reflectedApproximation_error (D : AnalyticReflectionData C) (i : I) (n : ℕ)
    {z : ℂ} (hz : z≠D.center i) :
    partialBar (D.reflectedApproximation i n) (D.approximation.map (D.limitData.index n) z)=
      star (partialZ (D.approximation.map (D.limitData.index n))
        (roundReflectionPlane (D.center i) (D.radius i) z))*
      star (partialBar (roundReflectionPlane (D.center i) (D.radius i)) z)*
      D.reflectionDefect i n z*
      star (partialZ (D.approximation.map (D.limitData.index n)).symm
        (D.approximation.map (D.limitData.index n) z)) := by
  exact smooth_reflection_conjugate_phase_error _
    ((D.approximation.smooth _).differentiable (by simp))
    ((D.approximation.inverse_smooth _).differentiable (by simp))
    _ (D.approximation.equation _) (roundReflectionPlane_differentiable hz)
    (roundReflectionPlane_partials hz).1 _ (roundReflectionPlane_phase hz)

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_ReflectedApproximationLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual conjugated smooth reflections converge locally uniformly off
the limiting pole. This follows from both retained principal-map limits. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer

lemma locallyUniform_joint_tendsto {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hl : TendstoLocallyUniformly f g atTop) (hg : Continuous g) (z : ℂ) :
    Tendsto (fun p : ℕ × ℂ => f p.1 p.2) (atTop ×ˢ 𝓝 z) (𝓝 (g z)) :=
  (hg.continuousAt.tendsto.comp tendsto_snd).congr_uniformity
    (tendstoLocallyUniformly_iff_forall_tendsto.mp hl z)

namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma reflectedLimit_continuousAt (D : AnalyticReflectionData C) (i : I) {z : ℂ}
    (hz : z≠D.principal (D.center i)) : ContinuousAt (D.reflectedLimit i) z := by
  have hi : D.principal.symm z≠D.center i := by
    intro h
    apply hz
    rw [←h,D.principal.apply_symm_apply]
  exact Complex.continuous_conj.continuousAt.comp (D.principal.continuous.continuousAt.comp
    ((roundReflectionPlane_differentiable hi).continuousAt.comp D.principal.symm.continuous.continuousAt))

lemma reflectedApproximation_tendsto (D : AnalyticReflectionData C) (i : I) :
    TendstoLocallyUniformlyOn (D.reflectedApproximation i) (D.reflectedLimit i) atTop
      ({D.principal (D.center i)}ᶜ) := by
  have hf := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp D.limitData.forward
  have hi := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp D.limitData.inverse
  apply (isOpen_compl_singleton.tendstoLocallyUniformlyOn_iff_forall_tendsto).mpr
  intro z hz
  have hz' : z≠D.principal (D.center i) := hz
  have hzi : D.principal.symm z≠D.center i := by
    intro h
    apply hz'
    rw [←h,D.principal.apply_symm_apply]
  have h₁ := locallyUniform_joint_tendsto hi D.principal.symm.continuous z
  have h₂ := (roundReflectionPlane_differentiable (r:=D.radius i) hzi).continuousAt.tendsto.comp h₁
  have h₃ := (locallyUniform_joint_tendsto hf D.principal.continuous
    (roundReflectionPlane (D.center i) (D.radius i) (D.principal.symm z))).comp
      (tendsto_fst.prodMk h₂)
  have h₄ := Complex.continuous_conj.continuousAt.tendsto.comp h₃
  have h₀ : Tendsto (fun p : ℕ × ℂ => D.reflectedLimit i p.2) (atTop ×ˢ 𝓝 z)
      (𝓝 (D.reflectedLimit i z)) := (D.reflectedLimit_continuousAt i hz').tendsto.comp tendsto_snd
  exact (h₀.prodMk_nhds h₄).mono_right (nhds_le_uniformity _)

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_ReflectionWeightedL2
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The antiholomorphic Jacobian of circular reflection gives an exact
L2 isometry for its weighted pullback. The one pole is a null set. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma roundReflectionWeight_measurable (c : ℂ) (r : ℝ) :
    Measurable (roundReflectionWeight c r) :=
  measurable_const.div ((Complex.continuous_conj.measurable.comp (measurable_id.sub_const c)).pow_const 2)

lemma roundReflection_abs_det {c z : ℂ} {r : ℝ} (hz : z≠c) :
    |(fderiv ℝ (roundReflectionPlane c r) z).det|=‖roundReflectionWeight c r z‖^2 := by
  rw [realCLM_det_wirtinger _ _ _ (fderiv_wirtinger _ z),
    (roundReflectionPlane_partials hz).1,(roundReflectionPlane_partials hz).2]
  simp [roundReflectionWeight]

lemma roundReflectionWeighted_memLp (c : ℂ) {r : ℝ} (hr : r≠0)
    {e : ℂ → ℂ} (he : MemLp e 2 volume) :
    MemLp (fun z => e (roundReflectionPlane c r z)*star (roundReflectionWeight c r z)) 2 volume ∧
      (∫z,‖e (roundReflectionPlane c r z)*star (roundReflectionWeight c r z)‖^2)=∫z,‖e z‖^2 := by
  let R := roundReflectionPlane c r
  let A := ({c} : Set ℂ)ᶜ
  have ha : MeasurableSet A := (measurableSet_singleton c).compl
  have ha0 : volume.restrict A=volume :=
    Measure.restrict_eq_self_of_ae_mem (by simpa [A] using volume.ae_ne c)
  have hR := roundReflectionPlane_involutive c hr
  have himage : R '' A=A := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact roundReflectionPlane_ne_center c hr hw
    · intro hz
      exact ⟨R z,roundReflectionPlane_ne_center c hr hz,hR z⟩
  have hd (z : ℂ) (hz : z∈A) : HasFDerivWithinAt R (fderiv ℝ R z) A z :=
    (roundReflectionPlane_differentiable hz).hasFDerivAt.hasFDerivWithinAt
  have hi : IntegrableOn (fun z => ‖e z‖^2) (R '' A) :=
    (he.integrable_norm_pow (p:=2) (by norm_num)).integrableOn
  have hj := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume ha hd
    hR.injective.injOn (fun z => ‖e z‖^2)).mp hi
  let q := fun z => e (R z)*star (roundReflectionWeight c r z)
  have heq : (fun z => |(fderiv ℝ R z).det| • ‖e (R z)‖^2) =ᵐ[volume.restrict A]
      fun z => ‖q z‖^2 := by
    filter_upwards [ae_restrict_mem ha] with z hz
    rw [roundReflection_abs_det hz]
    simp only [q,norm_mul,norm_star,mul_pow,smul_eq_mul,mul_comm]
  have hqi : Integrable (fun z => ‖q z‖^2) volume := by
    have hh := hj.congr heq
    rwa [ha0] at hh
  have hm : AEStronglyMeasurable q volume :=
    (he.aestronglyMeasurable.comp_quasiMeasurePreserving
      (roundReflectionPlane_quasiMeasurePreserving c hr)).mul
      (Complex.continuous_conj.measurable.comp (roundReflectionWeight_measurable c r)).aestronglyMeasurable
  refine ⟨(memLp_two_iff_integrable_sq_norm hm).mpr hqi,?_⟩
  have hh := integral_image_eq_integral_abs_det_fderiv_smul volume ha hd
    hR.injective.injOn (fun z => ‖e z‖^2)
  rw [himage,ha0] at hh
  rw [←integral_congr_ae (by simpa only [ha0] using heq)]
  exact hh.symm

lemma exists_strong_reflection_pullback (c : ℂ) {r : ℝ} (hr : r≠0)
    (e : ℕ → PlaneL2) (he : Tendsto e atTop (𝓝 0)) :
    ∃q : ℕ → PlaneL2,Tendsto q atTop (𝓝 0) ∧ ∀n,∀ᵐz ∂volume,
      q n z=e n (roundReflectionPlane c r z)*star (roundReflectionWeight c r z) := by
  let f (n : ℕ) (z : ℂ) := e n (roundReflectionPlane c r z)*star (roundReflectionWeight c r z)
  have hf (n : ℕ) := roundReflectionWeighted_memLp c hr (Lp.memLp (e n))
  let q (n : ℕ) := (hf n).1.toLp (f n)
  have hnorm (n : ℕ) : ‖q n‖=‖e n‖ := by
    have hq : (∫z,‖f n z‖^2)=‖q n‖^2 := by
      rw [←real_inner_self_eq_norm_sq,L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hf n).1.coeFn_toLp] with z hz
      rw [hz,real_inner_self_eq_norm_sq]
    have heq : (∫z,‖e n z‖^2)=‖e n‖^2 := by
      rw [←real_inner_self_eq_norm_sq,L2.inner_def]
      exact integral_congr_ae (.of_forall fun z => (real_inner_self_eq_norm_sq (e n z)).symm)
    have hh := (hf n).2
    change (∫z,‖f n z‖^2)=_ at hh
    rw [hq,heq] at hh
    nlinarith [norm_nonneg (q n),norm_nonneg (e n)]
  refine ⟨q,?_,fun n => (hf n).1.coeFn_toLp⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero,hnorm]
  simpa only [norm_zero] using he.norm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalLocalizedDerivativeError
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded multiplier tending almost everywhere to zero annihilates
both the fixed and variable parts of the principal derivative on any
finite-measure set. This is used for the reflection defect. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma PrincipalMapLimit.exists_localized_derivative_error
    {g : PlaneL2} {k R : ℝ} {S : PrincipalSmoothApproximation g k R} (L : PrincipalMapLimit S)
    {A : Set ℂ} (hA : MeasurableSet A) (hfin : volume A ≠ ∞)
    (δ : ℕ → ℂ → ℂ) (hδ : ∀n,AEStronglyMeasurable (δ n) volume)
    {B : ℝ} (hB : 0≤B) (hb : ∀n,∀ᵐz ∂volume,‖δ n z‖≤B)
    (ht : ∀ᵐz ∂volume,Tendsto (fun n => δ n z) atTop (𝓝 0)) :
    ∃q : ℕ → PlaneL2,Tendsto q atTop (𝓝 0) ∧ ∀n,∀ᵐz ∂volume,
      q n z=A.indicator (fun w => δ n w*partialZ (S.map (L.index n)) w) z := by
  let χ : ℂ → ℂ := A.indicator (fun _ => 1)
  have hχ : AEStronglyMeasurable χ volume := aestronglyMeasurable_const.indicator hA
  have hbχ : ∀ᵐz ∂volume,‖χ z‖≤(1:ℝ) := by
    filter_upwards [] with z
    by_cases hz : z∈A <;> simp [χ,hz]
  let M := multiplier χ hχ zero_le_one hbχ
  let b := indicatorConstLp 2 hA hfin (1:ℂ)
  let f (n : ℕ) := b+M (beurling ((S.density (L.index n)).toLp 2 (μ:=volume)))
  have hf : Tendsto f atTop (𝓝 (b+M (beurling g))) :=
    tendsto_const_nhds.add (M.continuous.tendsto _ |>.comp
      (beurling.continuous.tendsto _ |>.comp (S.strong_density.comp L.index_strict.tendsto_atTop)))
  let q (n : ℕ) := multiplier (δ n) (hδ n) hB (hb n) (f n)
  have hq : Tendsto q atTop (𝓝 0) := by
    have hh := multiplier_variable_convergence δ (fun _ => 0) hδ aestronglyMeasurable_zero hB hb
      (.of_forall fun _ => by simpa using hB) ht f (b+M (beurling g)) hf
    have hz : multiplier (fun _ : ℂ => (0:ℂ)) aestronglyMeasurable_zero hB
        (.of_forall fun _ => by simpa using hB) (b+M (beurling g))=0 := by
      apply Lp.ext
      filter_upwards [multiplier_ae (fun _ : ℂ => (0:ℂ)) aestronglyMeasurable_zero hB
        (.of_forall fun _ => by simpa using hB) (b+M (beurling g)),Lp.coeFn_zero ℂ 2 volume] with z hz h0
      rw [hz,h0,Pi.zero_apply,zero_mul]
    simpa only [hz] using hh
  refine ⟨q,hq,?_⟩
  intro n
  filter_upwards [multiplier_ae (δ n) (hδ n) hB (hb n) (f n),Lp.coeFn_add b (M (beurling
      ((S.density (L.index n)).toLp 2 (μ:=volume)))),
    indicatorConstLp_coeFn (p:=2) (hs:=hA) (hμs:=hfin) (c:=(1:ℂ)),
    multiplier_ae χ hχ zero_le_one hbχ (beurling ((S.density (L.index n)).toLp 2 (μ:=volume))),
    (schwartz_smoothL2 (S.density (L.index n))).beurling.representative_ae] with z hqz hfz hcz hMz hBz
  simp only [Pi.add_apply] at hfz
  change q n z=_
  rw [hqz,hfz,hcz,hMz]
  change δ n z*(A.indicator (fun _ => (1:ℂ)) z+χ z*_) = _
  by_cases hz : z∈A
  · simp only [χ,indicator_of_mem hz,one_mul]
    rw [hBz]
    exact congrArg (fun v : ℂ => δ n z*v) (S.partials (L.index n) z).2.symm
  · simp [χ,hz]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_PrincipalReflectionSourceError
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reflection invariance and strong principal-derivative convergence give
an actual globally L2-small source error, with the exact conjugacy formula
on any prescribed finite-measure reflected source set. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer

lemma planeL2_norm_star (f : PlaneL2) : ‖star f‖=‖f‖ := by
  rw [Lp.norm_def,Lp.norm_def]
  congr 1
  exact (eLpNorm_congr_ae (Lp.coeFn_star f)).trans eLpNorm_star

lemma planeL2_star_tendsto_zero {f : ℕ → PlaneL2} (h : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun n => star (f n)) atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero,planeL2_norm_star]
  simpa only [norm_zero] using h.norm

namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma reflection_source_error (D : AnalyticReflectionData C) (i : I)
    {A : Set ℂ} (hA : MeasurableSet A) (hfin : volume A≠∞) :
    ∃q : ℕ → PlaneL2,Tendsto q atTop (𝓝 0) ∧ ∀n,∀ᵐz ∂volume,
      roundReflectionPlane (D.center i) (D.radius i) z∈A →
      q n z=star (partialZ (D.approximation.map (D.limitData.index n))
        (roundReflectionPlane (D.center i) (D.radius i) z))*
        star (roundReflectionWeight (D.center i) (D.radius i) z)*D.reflectionDefect i n z := by
  let R := roundReflectionPlane (D.center i) (D.radius i)
  have hR := roundReflectionPlane_quasiMeasurePreserving (D.center i) (D.radius_pos i).ne'
  let δ (n : ℕ) (z : ℂ) := star (D.reflectionDefect i n (R z))
  have hm (n : ℕ) : AEStronglyMeasurable (δ n) volume :=
    (Complex.continuous_conj.measurable.comp ((D.reflectionDefect_measurable i n).comp
      (roundReflectionPlane_measurable _ _))).aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐz ∂volume,‖δ n z‖≤2*D.bound := by
    filter_upwards [] with z
    simpa only [δ,norm_star] using D.reflectionDefect_bound i n (R z)
  have ht : ∀ᵐz ∂volume,Tendsto (fun n => δ n z) atTop (𝓝 0) := by
    filter_upwards [hR.ae (D.reflectionDefect_tendsto i)] with z hz
    simpa only [star_zero] using hz.star
  obtain ⟨e,he,her⟩ := D.limitData.exists_localized_derivative_error hA hfin δ hm
    (mul_nonneg zero_le_two D.bound_nonneg) hb ht
  obtain ⟨q,hq,hqr⟩ := exists_strong_reflection_pullback (D.center i) (D.radius_pos i).ne'
    (fun n => star (e n)) (planeL2_star_tendsto_zero he)
  refine ⟨q,hq,?_⟩
  intro n
  filter_upwards [hqr n,hR.ae (Lp.coeFn_star (e n)),hR.ae (her n)] with z hqz hsz hez hzA
  rw [hqz,hsz]
  simp only [Pi.star_apply] at *
  rw [hez,indicator_of_mem hzA,star_mul]
  dsimp only [δ,R]
  rw [roundReflectionPlane_involutive (D.center i) (D.radius_pos i).ne' z,star_star]
  ring

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactMapContainment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact-open convergence retains containment of each fixed compact
set in an open neighborhood of its limiting image. -/
open Set Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma eventually_mapsTo_of_compact_convergence
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : ℕ → C(X, Y)} {g : C(X, Y)}
    (hf : Tendsto f atTop (𝓝 g)) {K : Set X} (hK : IsCompact K)
    {U : Set Y} (hU : IsOpen U) (h : MapsTo g K U) :
    ∀ᶠ n in atTop, MapsTo (f n) K U :=
  hf.eventually (ContinuousMap.eventually_mapsTo hK hU h)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_PrincipalReflectionTargetError
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact reflection error stays strongly small after transport by the
varying smooth principal inverses. Every compact set avoiding the limiting
pole has a common compact inverse collar avoiding the source pole. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma inverse_compact_away_pole (D : AnalyticReflectionData C) (i : I)
    {T : Set ℂ} (hT : IsCompact T) (hpole : D.principal (D.center i)∉T) :
    ∃K : Set ℂ,IsCompact K ∧ D.center i∉K ∧
      ∀ᶠn in atTop,MapsTo (D.approximation.map (D.limitData.index n)).symm T K := by
  have hsub : D.principal.symm '' T⊆({D.center i} : Set ℂ)ᶜ := by
    rintro _ ⟨z,hz,rfl⟩ heq
    apply hpole
    have hh : z=D.principal (D.center i) := by
      calc
        z=D.principal (D.principal.symm z) := (D.principal.apply_symm_apply z).symm
        _=D.principal (D.center i) := congrArg D.principal heq
    exact hh ▸ hz
  obtain ⟨V,hV,hTV,hVc,hK⟩ := exists_open_between_and_isCompact_closure
    (hT.image D.principal.symm.continuous) isOpen_compl_singleton hsub
  refine ⟨closure V,hK,fun h => hVc h rfl,?_⟩
  have ht := eventually_mapsTo_of_compact_convergence D.limitData.inverse hT hV
    (fun z hz => hTV (mem_image_of_mem _ hz))
  exact ht.mono fun n hn z hz => subset_closure (hn hz)

lemma reflection_target_error (D : AnalyticReflectionData C) (i : I)
    {T : Set ℂ} (hT : IsCompact T) (hpole : D.principal (D.center i)∉T) :
    ∃q : ℕ → PlaneL2,Tendsto q atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∀ᵐz ∂volume,z∈T → partialBar (D.reflectedApproximation i n) z=q n z := by
  obtain ⟨K,hK,hc,hretain⟩ := D.inverse_compact_away_pole i hT hpole
  let R := roundReflectionPlane (D.center i) (D.radius i)
  have hRK : IsCompact (R '' K) := hK.image_of_continuousOn
    (fun z hz => (roundReflectionPlane_differentiable (show z≠D.center i from fun h => hc (h ▸ hz))).continuousAt.continuousWithinAt)
  obtain ⟨e,he,her⟩ := D.reflection_source_error i hRK.measurableSet hRK.measure_lt_top.ne
  let P (n : ℕ) := (D.approximation.map (D.limitData.index n)).symm
  let B := (1+D.bound)/(1-D.bound)
  have hB : 0≤B := div_nonneg (by linarith [D.bound_nonneg]) (by linarith [D.bound_lt_one])
  have hdist (n : ℕ) := (smooth_beltrami_two_sided_distortion
    (D.approximation.map (D.limitData.index n)) (D.approximation.smooth _)
    (D.approximation.inverse_smooth _) (D.approximation.coefficient _)
    D.bound_nonneg D.bound_lt_one (D.approximation.coefficient_bound _)
    (D.approximation.equation _)).2
  obtain ⟨q,hq,hqr⟩ := exists_strong_variable_weighted_pullback P
    (fun n => D.approximation.inverse_smooth _) (fun n => D.approximation.smooth _) hB hdist e he
  refine ⟨q,hq,?_⟩
  filter_upwards [hretain] with n hn
  have hP := differentiable_homeomorph_quasiMeasurePreserving (P n)
    ((D.approximation.smooth _).differentiable (by simp))
  filter_upwards [hqr n,hP.ae (her n)] with z hqz hez hzT
  have hzK := hn hzT
  have hzc : P n z≠D.center i := fun h => hc (h ▸ hzK)
  have hRz : R (P n z)∈R '' K := mem_image_of_mem _ hzK
  have herr := D.reflectedApproximation_error i n hzc
  have hw := (roundReflectionPlane_partials (r:=D.radius i) hzc).2
  change partialBar (D.reflectedApproximation i n)
      (D.approximation.map (D.limitData.index n) (P n z))=_ at herr
  simp only [P,Homeomorph.apply_symm_apply] at herr
  rw [hqz,hez hRz]
  rw [herr]
  change star (partialZ (D.approximation.map (D.limitData.index n)) (R (P n z)))*
      star (partialBar R (P n z))*D.reflectionDefect i n (P n z)*star (partialZ (P n) z)=_
  change partialBar R (P n z)=roundReflectionWeight (D.center i) (D.radius i) (P n z) at hw
  rw [hw]

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_SmoothReflectedApproximation
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conjugated smooth reflections are smooth on every fixed compact
set off the limiting pole, after a finite initial segment. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer

lemma roundReflectionPlane_contDiffAt {c z : ℂ} {r : ℝ} (hz : z≠c) :
    ContDiffAt ℝ ∞ (roundReflectionPlane c r) z := by
  have hs : ContDiffAt ℝ ∞ (fun w : ℂ => w-c) z :=
    (contDiff_id.sub contDiff_const).contDiffAt
  have hi : ContDiffAt ℝ ∞ (fun w : ℂ => (star (w-c))⁻¹) z := by
    convert (Complex.conjCLE.contDiff.contDiffAt.comp z hs).inv
      (star_ne_zero.mpr (sub_ne_zero.mpr hz)) using 1 <;> rfl
  have hm : ContDiffAt ℝ ∞ (fun w : ℂ => (r:ℂ)^2*(star (w-c))⁻¹) z :=
    contDiffAt_const.mul hi
  convert contDiffAt_const.add hm using 1 <;> rfl

namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma reflectedApproximation_contDiffAt (D : AnalyticReflectionData C) (i : I) (n : ℕ) {z : ℂ}
    (hz : (D.approximation.map (D.limitData.index n)).symm z≠D.center i) :
    ContDiffAt ℝ ∞ (D.reflectedApproximation i n) z := by
  have hh := (D.approximation.smooth (D.limitData.index n)).contDiffAt.comp z
    ((roundReflectionPlane_contDiffAt (r:=D.radius i) hz).comp z
      (D.approximation.inverse_smooth (D.limitData.index n)).contDiffAt)
  convert Complex.conjCLE.contDiff.contDiffAt.comp z hh using 1 <;> rfl

lemma eventually_reflectedApproximation_contDiffOn (D : AnalyticReflectionData C) (i : I)
    {T : Set ℂ} (hT : IsCompact T) (hpole : D.principal (D.center i)∉T) :
    ∀ᶠn in atTop,ContDiffOn ℝ 1 (D.reflectedApproximation i n) T := by
  obtain ⟨K,hK,hc,ht⟩ := D.inverse_compact_away_pole i hT hpole
  filter_upwards [ht] with n hn z hz
  exact (D.reflectedApproximation_contDiffAt i n (fun h => hc (h ▸ hn hz))).of_le
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.contDiffWithinAt

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ComplexRectangleLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangular Morera passage for smooth maps with vanishing antiholomorphic
error. Uniform convergence is needed only on the four compact edges. -/
open Set Function Filter MeasureTheory Complex
open scoped Topology Interval
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma locally_uniform_curve_integral {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀n,Continuous (f n)) (hl : TendstoLocallyUniformly f g atTop)
    (γ : ℝ → ℂ) (hγ : Continuous γ) (a b : ℝ) :
    Tendsto (fun n => ∫t in a..b,f n (γ t)) atTop (𝓝 (∫t in a..b,g (γ t))) := by
  have ht := tendstoLocallyUniformly_iff_forall_isCompact.mp hl
    (γ '' uIcc a b) (isCompact_uIcc.image hγ)
  have hc : TendstoUniformlyOn (fun n t => f n (γ t)) (fun t => g (γ t)) atTop (uIcc a b) :=
    (ht.comp γ).mono (fun t ht => mem_image_of_mem γ ht)
  exact hc.tendsto_intervalIntegral_of_continuousOn (.of_forall fun n => (hf n |>.comp hγ).continuousOn)

lemma complexRectangleFlux_tendsto {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀n,Continuous (f n)) (hl : TendstoLocallyUniformly f g atTop) (z w : ℂ) :
    Tendsto (fun n => complexRectangleFlux (f n) z w) atTop (𝓝 (complexRectangleFlux g z w)) := by
  have h₁ := locally_uniform_curve_integral hf hl (fun x => x+z.im*I) (by fun_prop) z.re w.re
  have h₂ := locally_uniform_curve_integral hf hl (fun x => x+w.im*I) (by fun_prop) z.re w.re
  have h₃ := locally_uniform_curve_integral hf hl (fun y => w.re+y*I) (by fun_prop) z.im w.im
  have h₄ := locally_uniform_curve_integral hf hl (fun y => z.re+y*I) (by fun_prop) z.im w.im
  exact ((h₁.sub h₂).add (h₃.const_mul I)).sub (h₄.const_mul I)

lemma complexRectangleFlux_eq_bar_integral {f : ℂ → ℂ}
    (hf : ContDiff ℝ 1 f) (z w : ℂ) :
    complexRectangleFlux f z w=(2*I)*(∫x : ℝ in z.re..w.re,
      ∫y : ℝ in z.im..w.im,partialBar f (x+y*I)) := by
  have hi : IntegrableOn (fun p => I • fderiv ℝ f p 1-fderiv ℝ f p I)
      (uIcc z.re w.re ×ℂ uIcc z.im w.im) :=
    (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).const_smul I |>.sub
      ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)).continuousOn.integrableOn_compact
        (isCompact_uIcc.reProdIm isCompact_uIcc)
  have he := integral_boundary_rect_of_differentiableOn_real f z w
    (hf.differentiable (by norm_num)).differentiableOn hi
  have hid (p : ℂ) : I • fderiv ℝ f p 1-fderiv ℝ f p I=(2*I)*partialBar f p := by
    simp only [smul_eq_mul,partialBar]
    ring_nf
    simp [I_sq]
    ring
  change complexRectangleFlux f z w=_ at he
  rw [he]
  simp_rw [hid,intervalIntegral.integral_const_mul]

lemma differentiableOn_of_vanishing_rectangle_errors {U : Set ℂ} (hU : IsOpen U)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hf : ∀n,ContDiff ℝ 1 (f n))
    (hl : TendstoLocallyUniformly f g atTop)
    (he : ∀z w,Rectangle z w⊆U →
      Tendsto (fun n => ∫x : ℝ in z.re..w.re,
        ∫y : ℝ in z.im..w.im,partialBar (f n) (x+y*I)) atTop (𝓝 0)) :
    DifferentiableOn ℂ g U := by
  apply (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
  refine ⟨?_,(hl.continuous (.of_forall fun n => (hf n).continuous)).continuousOn⟩
  intro z w hzw
  have hz : complexRectangleFlux g z w=0 := by
    apply tendsto_nhds_unique (complexRectangleFlux_tendsto (fun n => (hf n).continuous) hl z w)
    have ht := (he z w hzw).const_mul (2*I)
    simpa only [complexRectangleFlux_eq_bar_integral (hf _),mul_zero] using ht
  rw [←add_eq_zero_iff_eq_neg,wedgeIntegral_add_wedgeIntegral_eq]
  exact hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RectangularL2
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite rectangle integration is continuous for the actual strong L2
residuals. The coordinate and almost-everywhere bridges retain the full
closed rectangle required by Morera. -/
open Set Function Filter MeasureTheory Complex
open scoped Topology Interval ENNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma tendsto_complex_setIntegral_L2 {q : ℕ → PlaneL2}
    (hq : Tendsto q atTop (𝓝 0)) {A : Set ℂ} (hA : MeasurableSet A)
    (hfin : volume A ≠ ∞) :
    Tendsto (fun n => ∫z in A,q n z) atTop (𝓝 0) := by
  have h := tendsto_const_nhds.inner (𝕜 := ℂ) hq
    (x := indicatorConstLp 2 hA hfin (1 : ℂ))
  simpa only [L2.inner_indicatorConstLp_one,inner_zero_right] using h

lemma doubleSetIntegral_eq_complex_integral {q : ℂ → ℂ} (a b c d : ℝ)
    (hq : IntegrableOn q (Ioc a b ×ℂ Ioc c d)) :
    (∫x in Ioc a b,∫y in Ioc c d,q (x+y*I))=
      ∫z in Ioc a b ×ℂ Ioc c d,q z := by
  let e := Complex.measurableEquivRealProd.symm
  have he := Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  have hpre : e ⁻¹' (Ioc a b ×ℂ Ioc c d)=Ioc a b ×ˢ Ioc c d := by
    ext p
    rfl
  have hi := (he.integrableOn_comp_preimage e.measurableEmbedding).mpr hq
  rw [hpre] at hi
  rw [←he.setIntegral_preimage_emb e.measurableEmbedding q, hpre,Measure.volume_eq_prod,←Measure.prod_restrict]
  rw [IntegrableOn,Measure.volume_eq_prod,←Measure.prod_restrict] at hi
  have hprod := integral_prod (q ∘ e) hi
  simp only [Function.comp_apply] at hprod
  rw [hprod]
  congr 1
  funext x
  congr 1
  funext y
  congr 1
  exact Complex.re_add_im (e (x,y))

lemma tendsto_doubleSetIntegral_L2 {q : ℕ → PlaneL2}
    (hq : Tendsto q atTop (𝓝 0)) (a b c d : ℝ) :
    Tendsto (fun n => ∫x in Ioc a b,∫y in Ioc c d,q n (x+y*I)) atTop (𝓝 0) := by
  have hm : MeasurableSet (Ioc a b ×ℂ Ioc c d) :=
    (measurableSet_Ioc.preimage Complex.continuous_re.measurable).inter
      (measurableSet_Ioc.preimage Complex.continuous_im.measurable)
  have hf : volume (Ioc a b ×ℂ Ioc c d) ≠ ∞ := by
    apply ne_of_lt
    exact (measure_mono (show Ioc a b ×ℂ Ioc c d⊆Icc a b ×ℂ Icc c d from
      fun z hz => ⟨⟨hz.1.1.le,hz.1.2⟩,⟨hz.2.1.le,hz.2.2⟩⟩)).trans_lt
        (isCompact_Icc.reProdIm isCompact_Icc).measure_lt_top
  have hi (n : ℕ) := integrableOn_Lp_of_measure_ne_top (q n) (by norm_num) hf
  simpa only [doubleSetIntegral_eq_complex_integral a b c d (hi _)] using
    tendsto_complex_setIntegral_L2 hq hm hf

lemma tendsto_doubleIntervalIntegral_L2 {q : ℕ → PlaneL2}
    (hq : Tendsto q atTop (𝓝 0)) (a b c d : ℝ) :
    Tendsto (fun n => ∫x in a..b,∫y in c..d,q n (x+y*I)) atTop (𝓝 0) := by
  by_cases hab : a≤b <;> by_cases hcd : c≤d
  · simpa only [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hcd] using
      tendsto_doubleSetIntegral_L2 hq a b c d
  · simpa only [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_ge (le_of_not_ge hcd),
      integral_neg,neg_zero] using (tendsto_doubleSetIntegral_L2 hq a b d c).neg
  · simpa only [intervalIntegral.integral_of_ge (le_of_not_ge hab),intervalIntegral.integral_of_le hcd,
      neg_zero] using (tendsto_doubleSetIntegral_L2 hq b a c d).neg
  · simpa only [intervalIntegral.integral_of_ge (le_of_not_ge hab),
      intervalIntegral.integral_of_ge (le_of_not_ge hcd),integral_neg,neg_neg] using
      tendsto_doubleSetIntegral_L2 hq b a d c

lemma doubleIntervalIntegral_congr_ae {f g : ℂ → ℂ} (z w : ℂ)
    (h : ∀ᵐp ∂volume,p∈Rectangle z w → f p=g p) :
    (∫x in z.re..w.re,∫y in z.im..w.im,f (x+y*I))=
      ∫x in z.re..w.re,∫y in z.im..w.im,g (x+y*I) := by
  have he := Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  have hp := MeasureTheory.Measure.ae_ae_of_ae_prod (he.quasiMeasurePreserving.ae h)
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hp] with x hx hxI
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hx] with y hy hyI
  have heq : Complex.measurableEquivRealProd.symm (x,y)=(x:ℂ)+y*I := by
    exact (Complex.re_add_im _).symm
  rw [←heq]
  apply hy
  change x∈uIcc z.re w.re ∧ y∈uIcc z.im w.im
  exact ⟨uIoc_subset_uIcc hxI,uIoc_subset_uIcc hyI⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ComplexRectangleLocalLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A local rectangular Morera passage, allowing the smooth approximants'
poles outside the fixed open set and allowing a finite initial segment. -/
open Set Function Filter MeasureTheory Complex
open scoped Topology Interval
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma locally_uniform_curve_integral_on {U : Set ℂ} (hU : IsOpen U)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hf : ∀ᶠn in atTop,ContinuousOn (f n) U)
    (hl : TendstoLocallyUniformlyOn f g atTop U) (γ : ℝ → ℂ) (hγ : Continuous γ)
    (a b : ℝ) (hsub : MapsTo γ (uIcc a b) U) :
    Tendsto (fun n => ∫t in a..b,f n (γ t)) atTop (𝓝 (∫t in a..b,g (γ t))) := by
  have ht := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hl
    (γ '' uIcc a b) (image_subset_iff.mpr hsub) (isCompact_uIcc.image hγ)
  have hc : TendstoUniformlyOn (fun n t => f n (γ t)) (fun t => g (γ t)) atTop (uIcc a b) :=
    (ht.comp γ).mono (fun t ht => mem_image_of_mem γ ht)
  exact hc.tendsto_intervalIntegral_of_continuousOn
    (hf.mono fun n hn => hn.comp hγ.continuousOn hsub)

lemma complexRectangleFlux_tendsto_on {U : Set ℂ} (hU : IsOpen U)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hf : ∀ᶠn in atTop,ContinuousOn (f n) U)
    (hl : TendstoLocallyUniformlyOn f g atTop U) (z w : ℂ) (hzw : Rectangle z w⊆U) :
    Tendsto (fun n => complexRectangleFlux (f n) z w) atTop (𝓝 (complexRectangleFlux g z w)) := by
  have h₁ := locally_uniform_curve_integral_on hU hf hl (fun x => x+z.im*I)
    (by fun_prop) z.re w.re (fun x hx => hzw (by change _ ∈ _ ∧ _ ∈ _; simpa using And.intro hx (left_mem_uIcc : z.im∈uIcc z.im w.im)))
  have h₂ := locally_uniform_curve_integral_on hU hf hl (fun x => x+w.im*I)
    (by fun_prop) z.re w.re (fun x hx => hzw (by change _ ∈ _ ∧ _ ∈ _; simpa using And.intro hx (right_mem_uIcc : w.im∈uIcc z.im w.im)))
  have h₃ := locally_uniform_curve_integral_on hU hf hl (fun y => w.re+y*I)
    (by fun_prop) z.im w.im (fun y hy => hzw (by change _ ∈ _ ∧ _ ∈ _; simpa using And.intro (right_mem_uIcc : w.re∈uIcc z.re w.re) hy))
  have h₄ := locally_uniform_curve_integral_on hU hf hl (fun y => z.re+y*I)
    (by fun_prop) z.im w.im (fun y hy => hzw (by change _ ∈ _ ∧ _ ∈ _; simpa using And.intro (left_mem_uIcc : z.re∈uIcc z.re w.re) hy))
  exact ((h₁.sub h₂).add (h₃.const_mul I)).sub (h₄.const_mul I)

lemma complexRectangleFlux_eq_bar_integral_on {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : ContDiffOn ℝ 1 f U) (z w : ℂ) (hzw : Rectangle z w⊆U) :
    complexRectangleFlux f z w=(2*I)*(∫x : ℝ in z.re..w.re,
      ∫y : ℝ in z.im..w.im,partialBar f (x+y*I)) := by
  have hd := hf.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hi : IntegrableOn (fun p => I • fderiv ℝ f p 1-fderiv ℝ f p I) (Rectangle z w) :=
    ((hd.clm_apply continuousOn_const).const_smul I |>.sub
      (hd.clm_apply continuousOn_const)).mono hzw |>.integrableOn_compact
        (isCompact_uIcc.reProdIm isCompact_uIcc)
  have he := integral_boundary_rect_of_differentiableOn_real f z w
    ((hf.differentiableOn (by norm_num)).mono hzw) hi
  have hid (p : ℂ) : I • fderiv ℝ f p 1-fderiv ℝ f p I=(2*I)*partialBar f p := by
    simp only [smul_eq_mul,partialBar]
    ring_nf
    simp [I_sq]
    ring
  change complexRectangleFlux f z w=_ at he
  rw [he]
  simp_rw [hid,intervalIntegral.integral_const_mul]

lemma differentiableOn_of_local_rectangle_errors {U : Set ℂ} (hU : IsOpen U)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀ᶠn in atTop,ContDiffOn ℝ 1 (f n) U)
    (hl : TendstoLocallyUniformlyOn f g atTop U)
    (he : ∀z w,Rectangle z w⊆U →
      Tendsto (fun n => ∫x : ℝ in z.re..w.re,
        ∫y : ℝ in z.im..w.im,partialBar (f n) (x+y*I)) atTop (𝓝 0)) :
    DifferentiableOn ℂ g U := by
  apply (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
  refine ⟨?_,hl.continuousOn (hf.frequently.mono fun n hn => hn.continuousOn)⟩
  intro z w hzw
  have hz : complexRectangleFlux g z w=0 := by
    apply tendsto_nhds_unique (complexRectangleFlux_tendsto_on hU
      (hf.mono fun n hn => hn.continuousOn) hl z w hzw)
    have ht := (he z w hzw).const_mul (2*I)
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [hf] with n hn
    exact (complexRectangleFlux_eq_bar_integral_on hU hn z w hzw).symm
  rw [←add_eq_zero_iff_eq_neg,wedgeIntegral_add_wedgeIntegral_eq]
  exact hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_ReflectedLimitHolomorphic
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual principal map conjugates every generating circular reflection
to an antiholomorphic map away from its one pole. Vanishing smooth
coefficient defects give the local Morera identity. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma reflectedLimit_holomorphic (D : AnalyticReflectionData C) (i : I) :
    DifferentiableOn ℂ (D.reflectedLimit i) ({D.principal (D.center i)}ᶜ) := by
  intro z hz
  obtain ⟨V,hV,hzV,hVU,hK⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton : IsCompact ({z} : Set ℂ)) isOpen_compl_singleton
    (singleton_subset_iff.mpr hz)
  have hpole : D.principal (D.center i)∉closure V := fun h => hVU h rfl
  obtain ⟨q,hq,he⟩ := D.reflection_target_error i hK hpole
  have hs := (D.eventually_reflectedApproximation_contDiffOn i hK hpole).mono
    (fun n hn => hn.mono subset_closure)
  have hl := (D.reflectedApproximation_tendsto i).mono (subset_closure.trans hVU)
  have hh : DifferentiableOn ℂ (D.reflectedLimit i) V := by
    apply differentiableOn_of_local_rectangle_errors hV hs hl
    intro a b hab
    apply (tendsto_doubleIntervalIntegral_L2 hq a.re b.re a.im b.im).congr'
    filter_upwards [he] with n hn
    apply (doubleIntervalIntegral_congr_ae a b ?_).symm
    filter_upwards [hn] with w hw hwR
    exact hw (subset_closure (hab hwR))
  exact (hh.differentiableAt (hV.mem_nhds (hzV (mem_singleton z)))).differentiableWithinAt

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PrincipalSphereCharts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual charts of a principally normalized plane homeomorphism.
The analytic inverse chart follows from its local inverse identity. -/
open Set Filter Function
open scoped Topology ContDiff OnePoint
noncomputable section
namespace CircleDomainRigidity

lemma sphereLocalMap_onePointCongr_infty (F : ℂ ≃ₜ ℂ) :
    sphereLocalMap F.onePointCongr OnePoint.infty = principalInversionGerm F := by
  funext w
  by_cases hw : w = 0
  · subst w
    simp [sphereLocalMap, principalInversionGerm, Homeomorph.onePointCongr_apply,
      chart, chartSymm, sphereInv, finiteCoord]
  · simp only [principalInversionGerm, Function.update_of_ne hw]
    simp only [sphereLocalMap, Homeomorph.onePointCongr_apply, OnePoint.map_infty, OnePoint.map_some, chart_infty_apply,
      chartSymm, ite_true, if_true, sphereInv, OnePoint.elim_some, hw, ite_false, if_false]
    exact finiteCoord_sphereInv_coe _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_ReflectedSphereNormalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the pole of the actual conjugated reflection to infinity.
The result is an actual plane homeomorphism. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma reflectedSphere_infty (D : AnalyticReflectionData C) (i : I) :
    D.reflectedSphere i OnePoint.infty=(star (D.principal (D.center i)) : ℂ) := by
  change Complex.conjCLE.toHomeomorph.onePointCongr (D.principal.onePointCongr
    (roundDiskReflection (D.center i) (D.radius i) (D.radius_pos i) OnePoint.infty))=_
  rw [roundDiskReflection_infty]
  rfl

lemma reflectedSphere_coe (D : AnalyticReflectionData C) (i : I) {z : ℂ}
    (hz : z≠D.principal (D.center i)) :
    D.reflectedSphere i (z : Sphere)=(D.reflectedLimit i z : Sphere) := by
  have hi : D.principal.symm z≠D.center i := by
    intro h
    exact hz ((D.principal.apply_symm_apply z).symm.trans (congrArg D.principal h))
  change Complex.conjCLE.toHomeomorph.onePointCongr (D.principal.onePointCongr
    (roundDiskReflection (D.center i) (D.radius i) (D.radius_pos i)
      (D.principal.symm z : Sphere)))=_
  rw [roundDiskReflection_coe (D.center i) (D.radius_pos i) hi]
  rfl

lemma poleParameter_zero (D : AnalyticReflectionData C) (i : I) :
    D.poleParameter i (0:ℂ)=OnePoint.infty := by
  change affineSphere 1 _ one_ne_zero (CannonMobius.inversion (0:ℂ))=_
  rw [show CannonMobius.inversion (0:ℂ)=OnePoint.infty from CannonMobius.inv_zero]
  rfl

lemma poleParameter_coe (D : AnalyticReflectionData C) (i : I) {z : ℂ} (hz : z≠0) :
    D.poleParameter i (z : Sphere)=(D.principal (D.center i)+z⁻¹ : ℂ) := by
  change affineSphere 1 _ one_ne_zero (CannonMobius.inversion (z : Sphere))=_
  rw [show CannonMobius.inversion (z : Sphere)=(z⁻¹ : ℂ) from CannonMobius.inv_coe hz,
    affineSphere_coe]
  simp [add_comm]

lemma poleNormalized_zero (D : AnalyticReflectionData C) (i : I) :
    D.poleNormalized i 0=star (D.principal (D.center i)) := by
  apply OnePoint.coe_injective
  rw [show (D.poleNormalized i 0 : Sphere)=D.reflectedSphere i (D.poleParameter i (0:ℂ)) from
    coe_spherePlaneMap _ (D.poleNormalized_fixes_infty i) 0,D.poleParameter_zero,D.reflectedSphere_infty]

lemma poleNormalized_coe (D : AnalyticReflectionData C) (i : I) {z : ℂ} (hz : z≠0) :
    D.poleNormalized i z=D.reflectedLimit i (D.principal (D.center i)+z⁻¹) := by
  apply OnePoint.coe_injective
  rw [show (D.poleNormalized i z : Sphere)=D.reflectedSphere i (D.poleParameter i (z : Sphere)) from
    coe_spherePlaneMap _ (D.poleNormalized_fixes_infty i) z,D.poleParameter_coe i hz,D.reflectedSphere_coe i]
  exact add_ne_left.mpr (inv_ne_zero hz)

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereLocalMapContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the concrete sphere-chart representative follows from
continuity of the map at the chart center. -/
open Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma continuousAt_sphereLocalMap {f : Sphere → Sphere} {p : Sphere}
    (hf : ContinuousAt f p) :
    ContinuousAt (sphereLocalMap f p) (chart p p) := by
  have hfc : ContinuousAt f (chartSymm p (chart p p)) := by
    rwa [chartSymm_chart_self]
  have hc : ContinuousAt (fun z => chartTransform (f p) (f (chartSymm p z)))
      (chart p p) :=
    (chartTransform (f p)).continuous.continuousAt.comp
      (hfc.comp (continuous_chartSymm p).continuousAt)
  have hn : chartTransform (f p) (f (chartSymm p (chart p p))) ≠ OnePoint.infty := by
    rw [chartSymm_chart_self]
    exact chartTransform_center_ne_infty _
  have hh := (CannonMobius.continuousAt_coordinate hn).comp_of_eq hc rfl
  change ContinuousAt (fun z => chart (f p) (f (chartSymm p z))) (chart p p)
  simp_rw [chart_eq_coordinate_transform]
  simpa only [Function.comp_def, chart_eq_coordinate_transform] using hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereLocalMapInjective
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An analytic local chart of a sphere homeomorphism has nonzero
complex derivative, obtained from genuine local injectivity. -/
open Set Filter Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma isOpen_sphereLocalMapRegion (e : Sphere ≃ₜ Sphere) (p : Sphere) :
    IsOpen (sphereLocalMapRegion e p) := by
  exact isOpen_compl_singleton.preimage
    ((chartTransform (e p)).continuous.comp (e.continuous.comp (continuous_chartSymm p)))

lemma center_mem_sphereLocalMapRegion (e : Sphere ≃ₜ Sphere) (p : Sphere) :
    chart p p ∈ sphereLocalMapRegion e p := by
  change chartTransform (e p) (e (chartSymm p (chart p p))) ≠ OnePoint.infty
  rw [chartSymm_chart_self]
  exact chartTransform_center_ne_infty _

lemma sphereLocalMap_injOn (e : Sphere ≃ₜ Sphere) (p : Sphere) :
    InjOn (sphereLocalMap e p) (sphereLocalMapRegion e p) := by
  intro z hz w hw heq
  have hz' := chartSymm_chart_of_ne (e p) (e (chartSymm p z)) hz
  have hw' := chartSymm_chart_of_ne (e p) (e (chartSymm p w)) hw
  have hh := congrArg (chartSymm (e p)) heq
  change chartSymm (e p) (chart (e p) (e (chartSymm p z))) =
    chartSymm (e p) (chart (e p) (e (chartSymm p w))) at hh
  rw [hz', hw'] at hh
  have hc := congrArg (chart p) (e.injective hh)
  simpa only [chart_chartSymm] using hc

lemma sphereLocalMap_deriv_ne_zero (e : Sphere ≃ₜ Sphere) (p : Sphere)
    (ha : AnalyticAt ℂ (sphereLocalMap e p) (chart p p)) :
    deriv (sphereLocalMap e p) (chart p p) ≠ 0 := by
  have hd := Complex.analyticAt_iff_eventually_differentiableAt.mp ha
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp hd
  apply holomorphicInjOn_deriv_ne_zero
    (hVo.inter (isOpen_sphereLocalMapRegion e p))
    (fun z hz => (hV hz.1).differentiableWithinAt)
    ((sphereLocalMap_injOn e p).mono inter_subset_right)
    ⟨hpV, center_mem_sphereLocalMapRegion e p⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ExteriorHomeomorphGerm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A plane homeomorphism holomorphic near infinity has an analytic
inversion germ. No principal normalization is required here. -/
open Filter Set
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exterior_homeomorph_inversion_analytic (F : ℂ ≃ₜ ℂ)
    (hF : ∀ᶠ z in Bornology.cobounded ℂ, DifferentiableAt ℂ (F : ℂ → ℂ) z) :
    AnalyticAt ℂ (principalInversionGerm F) 0 := by
  have hc := continuousAt_sphereLocalMap
    (f := (F.onePointCongr : Sphere → Sphere)) (p := OnePoint.infty)
    F.onePointCongr.continuous.continuousAt
  rw [sphereLocalMap_onePointCongr_infty, chart_infty_self] at hc
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hc
  have hn : ∀ᶠ z in Bornology.cobounded ℂ, F z ≠ 0 := by
    rw [Metric.cobounded_eq_cocompact]
    filter_upwards [(isCompact_singleton : IsCompact ({F.symm 0} : Set ℂ)).compl_mem_cocompact]
      with z hz
    intro hzero
    apply hz
    exact F.injective (hzero.trans (F.apply_symm_apply 0).symm)
  have hd := (tendsto_inv₀_nhdsNE_zero (α := ℂ)).eventually (hF.and hn)
  filter_upwards [hd, self_mem_nhdsWithin] with w hw hw0
  have hi : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) w := differentiableAt_inv hw0
  have hcomp := (hw.1.comp w hi).inv hw.2
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds hw0] with z hz
  exact Function.update_of_ne hz _ _

lemma exterior_homeomorph_conformalAt_infty (F : ℂ ≃ₜ ℂ)
    (hF : ∀ᶠ z in Bornology.cobounded ℂ, DifferentiableAt ℂ (F : ℂ → ℂ) z) :
    IsConformalAt F.onePointCongr OnePoint.infty := by
  have ha : AnalyticAt ℂ (sphereLocalMap F.onePointCongr OnePoint.infty)
      (chart OnePoint.infty OnePoint.infty) := by
    rw [sphereLocalMap_onePointCongr_infty, chart_infty_self]
    exact exterior_homeomorph_inversion_analytic F hF
  refine ⟨F.onePointCongr.continuous.continuousAt, _,
    sphereLocalMap_deriv_ne_zero F.onePointCongr OnePoint.infty ha, ?_⟩
  convert ha.differentiableAt.hasDerivAt using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma exterior_homeomorph_conformalOn (F : ℂ ≃ₜ ℂ) {K : Set ℂ}
    (hK : IsCompact K) (hF : ∀ z ∉ K, DifferentiableAt ℂ (F : ℂ → ℂ) z) :
    IsConformalOn F.onePointCongr (((↑) : ℂ → Sphere) '' K)ᶜ := by
  have hdiff : DifferentiableOn ℂ (F : ℂ → ℂ) Kᶜ :=
    fun z hz => (hF z hz).differentiableWithinAt
  intro p hp
  cases p using OnePoint.rec with
  | infty =>
    apply exterior_homeomorph_conformalAt_infty F
    rw [Metric.cobounded_eq_cocompact]
    filter_upwards [hK.compl_mem_cocompact] with z hz
    exact hF z hz
  | coe z =>
    have hz : z ∉ K := by
      intro hz
      exact hp (mem_image_of_mem _ hz)
    refine ⟨F.onePointCongr.continuous.continuousAt, deriv F z,
      holomorphicHomeomorph_deriv_ne_zero F hK.isClosed.isOpen_compl hdiff hz, ?_⟩
    have heq : sphereLocalMap F.onePointCongr (z : Sphere) = F := by
      funext w
      simp [sphereLocalMap, Homeomorph.onePointCongr_apply, chart, chartSymm, finiteCoord]
    change HasDerivAt (sphereLocalMap F.onePointCongr (z : Sphere)) (deriv F z)
      (chart (z : Sphere) (z : Sphere))
    rw [heq, chart_coe_self]
    exact (hF z hz).hasDerivAt

lemma exterior_homeomorph_principal_normalization (F : ℂ ≃ₜ ℂ)
    (hF : ∀ᶠ z in Bornology.cobounded ℂ, DifferentiableAt ℂ (F : ℂ → ℂ) z) :
    ∃ (a b : ℂ) (ha : a ≠ 0),
      IsPrincipalNormalized (affineSphere a b ha ∘ F.onePointCongr) := by
  rw [Metric.cobounded_eq_cocompact] at hF
  obtain ⟨K, hK, hKF⟩ := Filter.mem_cocompact.mp hF
  have hU : IsOpen ((((↑) : ℂ → Sphere) '' K)ᶜ) :=
    (hK.image OnePoint.continuous_coe).isClosed.isOpen_compl
  have hi : OnePoint.infty ∈ ((((↑) : ℂ → Sphere) '' K)ᶜ) := by simp
  exact principal_normalize_at_infty hU (exterior_homeomorph_conformalOn F hK hKF)
    F.onePointCongr.injective.injOn hi rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_EntireHomeomorphAffine
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An entire plane homeomorphism is affine. Its analytic infinity germ
supplies principal normalization, after which Liouville applies to the
entire remainder. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma entire_homeomorph_affine (F : ℂ ≃ₜ ℂ) (hF : Differentiable ℂ (F : ℂ → ℂ)) :
    ∃a b : ℂ,a≠0 ∧ ∀z,F z=a*z+b := by
  obtain ⟨a,b,ha,hp⟩ := exterior_homeomorph_principal_normalization F (.of_forall hF)
  have ht := principal_remainder_tendsto_zero hp.2
  have he : Tendsto (fun z => a*F z+b-z) (cocompact ℂ) (𝓝 0) := by
    rw [←Metric.cobounded_eq_cocompact]
    simpa only [comp_apply,Homeomorph.onePointCongr_apply,OnePoint.map_some,affineSphere_coe,finiteCoord_coe] using ht
  have hd : Differentiable ℂ (fun z => a*F z+b-z) := by fun_prop
  have hz (z : ℂ) := hd.apply_eq_of_tendsto_cocompact z he
  refine ⟨a⁻¹,-b/a,inv_ne_zero ha,?_⟩
  intro z
  have hh := hz z
  field_simp
  linear_combination hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_ReflectedFractionalLinear
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual reflected conjugate is fractional linear. Moving its pole
 to infinity produces an entire plane homeomorphism, so Liouville's theorem
 supplies its affine formula. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma poleNormalized_differentiableAt_ne_zero (D : AnalyticReflectionData C) (i : I)
    {z : ℂ} (hz : z≠0) : DifferentiableAt ℂ (D.poleNormalized i : ℂ → ℂ) z := by
  have hp : D.principal (D.center i)+z⁻¹ ∈ ({D.principal (D.center i)}ᶜ : Set ℂ) := by
    exact add_ne_left.mpr (inv_ne_zero hz)
  have hd := ((D.reflectedLimit_holomorphic i _ hp).differentiableAt
    (isOpen_compl_singleton.mem_nhds hp)).comp z
      ((differentiableAt_const (D.principal (D.center i))).add (differentiableAt_inv hz))
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds hz] with w hw
  exact D.poleNormalized_coe i hw

lemma poleNormalized_holomorphic (D : AnalyticReflectionData C) (i : I) :
    Differentiable ℂ (D.poleNormalized i : ℂ → ℂ) := by
  have hzero : AnalyticAt ℂ (D.poleNormalized i : ℂ → ℂ) 0 := by
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _
      (D.poleNormalized i).continuous.continuousAt
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact D.poleNormalized_differentiableAt_ne_zero i hz
  intro z
  by_cases hz : z=0
  · subst z
    exact hzero.differentiableAt
  · exact D.poleNormalized_differentiableAt_ne_zero i hz

lemma reflectedLimit_fractional_linear (D : AnalyticReflectionData C) (i : I) :
    ∃A : ℂ,A≠0 ∧ ∀z : ℂ,z≠D.principal (D.center i) →
      D.reflectedLimit i z=star (D.principal (D.center i))+A/(z-D.principal (D.center i)) := by
  obtain ⟨A,b,hA,hf⟩ := entire_homeomorph_affine (D.poleNormalized i)
    (D.poleNormalized_holomorphic i)
  have hb : b=star (D.principal (D.center i)) := by
    have h := hf 0
    simpa only [mul_zero,zero_add,D.poleNormalized_zero i] using h.symm
  refine ⟨A,hA,?_⟩
  intro z hz
  have hw : (z-D.principal (D.center i))⁻¹≠0 := inv_ne_zero (sub_ne_zero.mpr hz)
  have h := D.poleNormalized_coe i hw
  rw [inv_inv,add_sub_cancel] at h
  rw [←h,hf,hb,div_eq_mul_inv,add_comm]

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleFixedEquation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary fixed-point equations for circular reflections and their
fractional-linear conjugates. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

lemma fractional_fixed_iff {a A z : ℂ} (hz : z≠a) :
    star a+A/(z-a)=star z ↔ A=((‖z-a‖^2 : ℝ) : ℂ) := by
  have hn : z-a≠0 := sub_ne_zero.mpr hz
  have hm : star (z-a)*(z-a)=((‖z-a‖^2 : ℝ) : ℂ) := by
    convert Complex.conj_mul' (z-a) using 1
    · rfl
    · rw [Complex.ofReal_pow]
  constructor
  · intro h
    have hd : A/(z-a)=star (z-a) := by rw [star_sub]; linear_combination h
    exact ((div_eq_iff hn).mp hd).trans hm
  · intro h
    have hd : A/(z-a)=star (z-a) := (div_eq_iff hn).mpr (h.trans hm.symm)
    rw [hd,star_sub]
    ring

lemma roundReflectionPlane_fixed_iff {c z : ℂ} {r : ℝ} (hr : 0 < r) (hz : z≠c) :
    roundReflectionPlane c r z=z ↔ z∈sphere c r := by
  have hn : star (z-c)≠0 := star_ne_zero.mpr (sub_ne_zero.mpr hz)
  have hm : (z-c)*star (z-c)=((‖z-c‖^2 : ℝ) : ℂ) := by
    convert Complex.mul_conj' (z-c) using 1
    · rfl
    · rw [Complex.ofReal_pow]
  rw [roundReflectionPlane,mem_sphere,dist_eq_norm]
  constructor
  · intro h
    have hd : (r:ℂ)^2/star (z-c)=z-c := by linear_combination h
    have hs : (r:ℂ)^2=((‖z-c‖^2 : ℝ) : ℂ) := ((div_eq_iff hn).mp hd).trans hm
    have hs' : r^2=‖z-c‖^2 := by exact_mod_cast hs
    nlinarith [norm_nonneg (z-c)]
  · intro h
    have hd : (r:ℂ)^2/star (z-c)=z-c := by
      apply (div_eq_iff hn).mpr
      rw [hm,h]
      simp
    rw [hd,add_sub_cancel]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_ReflectedCircleImages
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each boundary circle has a full round-circle image under the actual
principal map. Positivity of the radius follows from injectivity, and the
reverse inclusion follows from the exact reflected fixed-point equation. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma reflectedLimit_fixed_iff (D : AnalyticReflectionData C) (i : I) {z : ℂ}
    (hz : z≠D.principal (D.center i)) :
    D.reflectedLimit i z=star z ↔ D.principal.symm z∈sphere (D.center i) (D.radius i) := by
  have hi : D.principal.symm z≠D.center i := by
    intro h
    exact hz ((D.principal.apply_symm_apply z).symm.trans (congrArg D.principal h))
  rw [←roundReflectionPlane_fixed_iff (D.radius_pos i) hi]
  constructor
  · intro h
    have hh : D.principal (roundReflectionPlane (D.center i) (D.radius i)
        (D.principal.symm z))=z := star_injective h
    exact D.principal.injective (hh.trans (D.principal.apply_symm_apply z).symm)
  · intro h
    change star (D.principal (roundReflectionPlane (D.center i) (D.radius i)
      (D.principal.symm z)))=star z
    rw [h,D.principal.apply_symm_apply]

lemma exists_round_boundary_image (D : AnalyticReflectionData C) (i : I) :
    ∃s : ℝ,0 < s ∧ D.principal '' sphere (D.center i) (D.radius i)=
      sphere (D.principal (D.center i)) s := by
  obtain ⟨A,_hA,hform⟩ := D.reflectedLimit_fractional_linear i
  let w : ℂ := D.center i+(D.radius i : ℂ)
  have hw : w∈sphere (D.center i) (D.radius i) := by
    simp only [mem_sphere,dist_eq_norm,w,add_sub_cancel_left,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (D.radius_pos i)]
  have hwc : w≠D.center i := by
    intro h
    have h0 : (D.radius i : ℂ)=0 := add_left_cancel (h.trans (add_zero (D.center i)).symm)
    exact (D.radius_pos i).ne' (Complex.ofReal_eq_zero.mp h0)
  let s : ℝ := ‖D.principal w-D.principal (D.center i)‖
  have hs : 0 < s := norm_pos_iff.mpr (sub_ne_zero.mpr
    (fun h => hwc (D.principal.injective h)))
  have he : A=((s^2 : ℝ) : ℂ) := by
    apply (fractional_fixed_iff (fun h => hwc (D.principal.injective h))).mp
    rw [←hform _ (fun h => hwc (D.principal.injective h))]
    apply (D.reflectedLimit_fixed_iff i (fun h => hwc (D.principal.injective h))).mpr
    simpa only [D.principal.symm_apply_apply] using hw
  refine ⟨s,hs,?_⟩
  ext z
  constructor
  · rintro ⟨u,hu,rfl⟩
    have huc : u≠D.center i := by
      intro h
      subst u
      have h0 : (0:ℝ)=D.radius i := by simpa only [mem_sphere,dist_self] using hu
      exact (D.radius_pos i).ne' h0.symm
    have hn : D.principal u≠D.principal (D.center i) := fun h => huc (D.principal.injective h)
    have hf := (D.reflectedLimit_fixed_iff i hn).mpr
      (by simpa only [D.principal.symm_apply_apply] using hu)
    rw [hform _ hn] at hf
    have he' := (fractional_fixed_iff hn).mp hf
    have hsq : s^2=‖D.principal u-D.principal (D.center i)‖^2 := by
      exact_mod_cast he.symm.trans he'
    rw [mem_sphere,dist_eq_norm]
    nlinarith [norm_nonneg (D.principal u-D.principal (D.center i))]
  · intro hz
    have hn : z≠D.principal (D.center i) := by
      intro h
      subst z
      have h0 : (0:ℝ)=s := by simpa only [mem_sphere,dist_self] using hz
      linarith
    have hz' : ‖z-D.principal (D.center i)‖=s := by simpa only [mem_sphere,dist_eq_norm] using hz
    have hf : D.reflectedLimit i z=star z := by
      rw [hform _ hn]
      apply (fractional_fixed_iff hn).mpr
      rw [hz',he]
    exact ⟨D.principal.symm z,(D.reflectedLimit_fixed_iff i hn).mp hf,
      D.principal.apply_symm_apply z⟩

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HomeomorphRoundDiskImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A plane homeomorphism carrying one boundary circle onto another carries
its bounded closed disk onto the corresponding bounded closed disk. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

lemma homeomorph_image_closedBall_of_sphere (F : ℂ ≃ₜ ℂ) {c a : ℂ} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hf : F '' sphere c r=sphere a s) :
    F '' closedBall c r=closedBall a s := by
  have hb : F '' ball c r=ball a s := by
    rw [←roundJordanAt_interior a s hs]
    apply open_eq_jordanInterior_of_frontier _ (F.isOpenMap _ isOpen_ball)
      (((isCompact_closedBall c r).image F.continuous).isBounded.subset
        (image_mono ball_subset_closedBall))
      ((nonempty_ball.mpr hr).image F)
    rw [←F.image_frontier,frontier_ball _ hr.ne',hf,roundJordanAt_interior,
        frontier_ball _ hs.ne']
  rw [←closure_ball c hr.ne',F.image_closure,hb,closure_ball a hs.ne']

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_AnalyticRoundCapImages
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual invariant-coefficient straightening carries every closed
analytic Jordan cap onto a positive-radius closed round disk. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma exists_round_cap_images (D : AnalyticReflectionData C) :
    ∃s : I → ℝ,(∀i,0 < s i) ∧ ∀i,
      (D.comparison.trans D.principal) '' closure (jordanInterior (C.hole i))=
        closedBall (D.principal (D.center i)) (s i) := by
  choose s hs he using D.exists_round_boundary_image
  refine ⟨s,hs,?_⟩
  intro i
  change (D.principal ∘ D.comparison) '' closure (jordanInterior (C.hole i))=_
  rw [image_comp,D.cap_image]
  exact homeomorph_image_closedBall_of_sphere D.principal (D.radius_pos i) (hs i) (he i)

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_PrincipalBeltramiResidual
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth principal approximants solve the limiting Beltrami
equation up to a strong L2 error. This retains the residual needed when
precomposing with a smooth comparison map. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma PrincipalSmoothApproximation.exists_strong_beltrami_residual
    {g : PlaneL2} {k R : ℝ} (S : PrincipalSmoothApproximation g k R)
    (μ : ℂ → ℂ) (hμ : MemLp μ 2 volume) (hk : 0≤k)
    (hb : ∀ᵐz ∂volume,‖μ z‖≤k)
    (he : ∀ᵐz ∂volume,g z=μ z*(1+beurling g z)) :
    ∃e : ℕ → PlaneL2,Tendsto e atTop (𝓝 0) ∧
      ∀n,∀ᵐz ∂volume,e n z=partialBar (S.map n) z-μ z*partialZ (S.map n) z := by
  let M := multiplier μ hμ.aestronglyMeasurable hk hb
  let a (n : ℕ) := (S.density n).toLp 2 (μ:=volume)
  let e (n : ℕ) := a n-M (beurling (a n))-hμ.toLp μ
  have ha : Tendsto a atTop (𝓝 g) := S.strong_density
  have hB : Tendsto (fun n => beurling (a n)) atTop (𝓝 (beurling g)) :=
    (beurling.continuous.tendsto g).comp ha
  have hM : Tendsto (fun n => M (beurling (a n))) atTop (𝓝 (M (beurling g))) :=
    (M.continuous.tendsto (beurling g)).comp hB
  have hzero : g-M (beurling g)-hμ.toLp μ=0 := by
    rw [density_operator_equation hμ hk hb g he,sub_self]
  refine ⟨e,?_,?_⟩
  · simpa only [hzero] using (ha.sub hM).sub_const (hμ.toLp μ)
  · intro n
    filter_upwards [Lp.coeFn_sub (a n-M (beurling (a n))) (hμ.toLp μ),
      Lp.coeFn_sub (a n) (M (beurling (a n))),
      multiplier_ae μ hμ.aestronglyMeasurable hk hb (beurling (a n)),
      (S.density n).coeFn_toLp 2 volume,hμ.coeFn_toLp,
      (schwartz_smoothL2 (S.density n)).beurling.representative_ae] with z he' hs hm hd hmu hB'
    change e n z=_
    change beurling (a n) z=smoothBeurling (S.density n) z at hB'
    change M (beurling (a n)) z=μ z*beurling (a n) z at hm
    change a n z=S.density n z at hd
    simp only [Pi.sub_apply] at he' hs
    dsimp only [e]
    rw [he',hs,hm,hd,hmu,hB',(S.partials n z).1,(S.partials n z).2]
    ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_AnalyticStraighteningResidual
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual pulled-back principal approximants have antiholomorphic
error tending strongly to zero on the original analytic domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

local instance localInst_redac8a_1 : BorelSpace Sphere := ⟨rfl⟩
lemma exists_straightening_residual (D : AnalyticReflectionData C) :
    ∃q : ℕ → PlaneL2,Tendsto q atTop (𝓝 0) ∧
      ∀n,∀ᵐ(z : ℂ) ∂volume,(z : Sphere)∈C.region →
        partialBar (D.straighteningApproximation n) z=q n z := by
  let μ := fun z : ℂ => D.extension (z : Sphere)
  have hμ : MemLp μ 2 volume := compact_coefficient_memLp
    ((D.extension_measurable.comp OnePoint.continuous_coe.measurable).aestronglyMeasurable)
    (isCompact_closedBall 0 D.supportRadius) D.bound_nonneg
    (fun z => D.extension_bound (z : Sphere)) (fun z hz => D.extension_zero z
      (le_of_lt (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz)))
  obtain ⟨e,he,her⟩ := D.approximation.exists_strong_beltrami_residual μ hμ D.bound_nonneg
    (.of_forall fun z => D.extension_bound (z : Sphere)) D.density_equation
  let P := D.comparison
  let K := (1+D.bound)/(1-D.bound)
  have hK : 0≤K := div_nonneg (by linarith [D.bound_nonneg]) (by linarith [D.bound_lt_one])
  have hdist := (smooth_beltrami_two_sided_distortion P.symm D.comparison_inverse_smooth
    D.comparison_smooth D.baseCoefficient D.bound_nonneg D.bound_lt_one D.base_bound D.base_equation).2
  obtain ⟨q,hq,hqr⟩ := exists_strong_weighted_pullback P D.comparison_smooth D.comparison_inverse_smooth
    hK hdist e he
  have hPq := differentiable_homeomorph_quasiMeasurePreserving P
    (D.comparison_inverse_smooth.differentiable (by simp))
  refine ⟨q ∘ D.limitData.index,hq.comp D.limitData.index_strict.tendsto_atTop,?_⟩
  intro n
  let j := D.limitData.index n
  filter_upwards [hqr j,hPq.ae (her j)] with z hqz hez hz
  have hbase : D.extension (P z : Sphere)=D.baseCoefficient (P z) :=
    D.extension_base (mem_image_of_mem D.comparison.onePointCongr hz)
  change partialBar (D.approximation.map j ∘ P) z=q j z
  rw [smooth_beltrami_pullback_cancellation P D.comparison_smooth D.comparison_inverse_smooth
    D.baseCoefficient D.base_equation (D.approximation.smooth j |>.differentiable (by simp) (P z))]
  rw [hqz,hez]
  change (partialBar (D.approximation.map j) (P z)-D.baseCoefficient (P z)*
      partialZ (D.approximation.map j) (P z))*star (partialZ P z)=
    (partialBar (D.approximation.map j) (P z)-D.extension (P z : Sphere)*
      partialZ (D.approximation.map j) (P z))*star (partialZ P z)
  rw [hbase]

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_AnalyticStraighteningHolomorphic
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphicity of the actual finite straightening. The smooth
approximants have an L2-small antiholomorphic derivative on every closed
source rectangle; their locally uniform limit therefore satisfies Morera. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma straighteningApproximation_tendsto (D : AnalyticReflectionData C) :
    TendstoLocallyUniformly D.straighteningApproximation (D.principal ∘ D.comparison) atTop := by
  have h := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp D.limitData.forward
  exact h.comp D.comparison D.comparison.continuous

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_14
lemma straightening_holomorphic (D : AnalyticReflectionData C) :
    DifferentiableOn ℂ (D.principal ∘ D.comparison) ((↑) ⁻¹' C.region) := by
  obtain ⟨q,hq,he⟩ := D.exists_straightening_residual
  apply differentiableOn_of_vanishing_rectangle_errors
    (C.region_open.preimage OnePoint.continuous_coe)
    (fun n => ((D.approximation.smooth _).comp D.comparison_smooth).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    D.straighteningApproximation_tendsto
  intro z w hzw
  have hi := tendsto_doubleIntervalIntegral_L2 hq z.re w.re z.im w.im
  apply hi.congr'
  apply Eventually.of_forall
  intro n
  apply (doubleIntervalIntegral_congr_ae z w ?_).symm
  filter_upwards [he n] with p hp hpR
  exact hp (hzw hpR)

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_AnalyticFiniteUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unconditional uniformization of a finite analytic Jordan configuration.
The conformal map is the actual principal solution composed with the smooth
rounding comparison; the round cap images are proved from reflection. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_analytic_finite_uniformization {I : Type*} [Finite I]
    (C : FiniteJordanConfiguration I) (ha : ∀i,IsAnalyticJordanCap (C.hole i)) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f C.region V := by
  obtain ⟨D⟩ := exists_analytic_reflection_data C ha
  obtain ⟨s,hs,hcaps⟩ := D.exists_round_cap_images
  let H : ℂ ≃ₜ ℂ := D.comparison.trans D.principal
  let V : Set Sphere := H.onePointCongr '' C.region
  let K : Set ℂ := ⋃i,closure (jordanInterior (C.hole i))
  have hK : IsCompact K := isCompact_iUnion fun i => isCompact_closure_jordanInterior (C.hole i)
  have hr : C.region=(((↑) : ℂ → Sphere) '' K)ᶜ := by
    change (⋃i,((↑) : ℂ → Sphere) '' closure (jordanInterior (C.hole i)))ᶜ=_
    rw [image_iUnion]
  have hconf : IsConformalOn H.onePointCongr C.region := by
    rw [hr]
    apply exterior_homeomorph_conformalOn H hK
    intro z hz
    have hp : (z : Sphere)∈C.region := by
      rw [hr]
      simpa only [mem_compl_iff,OnePoint.coe_injective.mem_set_image] using hz
    exact (D.straightening_holomorphic z hp).differentiableAt
      ((C.region_open.preimage OnePoint.continuous_coe).mem_nhds hp)
  have hcomp : Vᶜ=⋃i,((↑) : ℂ → Sphere) '' closedBall (D.principal (D.center i)) (s i) := by
    have hh := rounding_spherical_exterior_image C H (fun i => D.principal (D.center i)) s hcaps
    change (H.onePointCongr '' C.region)ᶜ=_
    rw [hh,compl_compl]
  have hdisj := rounding_round_disks_disjoint C H (fun i => D.principal (D.center i)) s hcaps
  have hV : IsCircleDomain V := by
    refine ⟨H.onePointCongr.isOpenMap _ C.region_open,
      C.region_connected.image _ H.onePointCongr.continuous.continuousOn,?_⟩
    intro p hp
    have hp' := hp
    rw [hcomp] at hp'
    obtain ⟨i,hi⟩ := mem_iUnion.mp hp'
    right
    rw [hcomp,connectedComponentIn_finite_disjoint_closed
      (fun i => ((↑) : ℂ → Sphere) '' closedBall (D.principal (D.center i)) (s i))
      (fun i => ((isCompact_closedBall _ _).image OnePoint.continuous_coe).isClosed)
      (fun i => (convex_closedBall (D.principal (D.center i)) (s i)).isPreconnected.image _
        OnePoint.continuous_coe.continuousOn) hdisj hi]
    exact isRoundClosedDisk_coe_closedBall _ (hs i)
  exact ⟨V,H.onePointCongr,hV,isConformalEquivalence_of_injOn hconf C.region_open
    H.onePointCongr.injective.injOn⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteJordanUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One finite cycle makes every Jordan boundary analytic. Applying the
proved invariant-coefficient construction then uniformizes the original
finite Jordan exterior. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer FiniteJordanConfiguration

lemma exists_fin_jordan_uniformization (n : ℕ) (C : FiniteJordanConfiguration (Fin n)) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f C.region V := by
  cases n with
  | zero =>
    have he : C.region=univ := by
      change (⋃i : Fin 0,closedTerminalCap (C.hole i))ᶜ=univ
      simp
    rw [he]
    exact circleDomainModel_univ
  | succ m =>
    obtain ⟨V,f,hV,hf⟩ := exists_analytic_finite_uniformization
      (iterate C (cyclicSchedule m) (m+1)) (cyclic_iterate_analytic C le_rfl)
    exact ⟨V,f ∘ cumulativeMap C (cyclicSchedule m) (m+1),hV,
      (cumulativeMap_conformal C (cyclicSchedule m) (m+1)).trans hf⟩

lemma exists_finite_jordan_uniformization {I : Type*} [Finite I]
    (C : FiniteJordanConfiguration I) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f C.region V := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let C' : FiniteJordanConfiguration (Fin (Fintype.card I)) :=
    ⟨fun i => C.hole (e.symm i),fun i j hij => C.disjoint (e.symm.injective.ne hij)⟩
  have hreg : C'.region=C.region := by
    have hu : (⋃i,closedTerminalCap (C'.hole i))=⋃i,closedTerminalCap (C.hole i) := by
      ext p
      constructor
      · intro hp
        obtain ⟨i,hi⟩ := mem_iUnion.mp hp
        exact mem_iUnion.mpr ⟨e.symm i,hi⟩
      · intro hp
        obtain ⟨i,hi⟩ := mem_iUnion.mp hp
        apply mem_iUnion.mpr
        refine ⟨e i,?_⟩
        simpa only [C',e.symm_apply_apply] using hi
    exact congrArg compl hu
  obtain ⟨V,f,hV,hf⟩ := exists_fin_jordan_uniformization (Fintype.card I) C'
  exact ⟨V,f,hV,hreg ▸ hf⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteJordanImageUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Jordan uniformization also applies after an arbitrary sphere
homeomorphism. A conformal normalization makes its image of infinity the
point at infinity, leaving an actual plane homeomorphism of all caps. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma spherePlaneHomeomorph_onePointCongr (e : Sphere ≃ₜ Sphere)
    (he : e OnePoint.infty=OnePoint.infty) :
    (spherePlaneHomeomorph e he).onePointCongr=e := by
  ext p
  cases p using OnePoint.rec with
  | infty => exact he.symm
  | coe z => exact coe_spherePlaneMap e he z

lemma trans_closed_jordan_image (H P : ℂ ≃ₜ ℂ) :
    closure (jordanInterior (H.trans P))=P '' closure (jordanInterior H) := by
  change closure ((P ∘ H) '' _) = P '' closure (H '' _)
  rw [image_comp,P.image_closure]

lemma exists_finite_jordan_image_uniformization {I : Type*} [Finite I]
    (C : FiniteJordanConfiguration I) (e : Sphere ≃ₜ Sphere) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f (e '' C.region) V := by
  let N : Sphere ≃ₜ Sphere := pointToInfinity (e OnePoint.infty)
  let E : Sphere ≃ₜ Sphere := e.trans N
  have hE : E OnePoint.infty=OnePoint.infty := by
    exact pointToInfinity_apply_self (e OnePoint.infty)
  let P : ℂ ≃ₜ ℂ := spherePlaneHomeomorph E hE
  have hP : P.onePointCongr=E := spherePlaneHomeomorph_onePointCongr E hE
  let C' : FiniteJordanConfiguration I := {
    hole := fun i => (C.hole i).trans P
    disjoint := by
      intro i j hij
      change Disjoint (closure (jordanInterior ((C.hole i).trans P)))
        (closure (jordanInterior ((C.hole j).trans P)))
      rw [trans_closed_jordan_image,trans_closed_jordan_image]
      exact (C.disjoint hij).image P.injective.injOn (subset_univ _) (subset_univ _) }
  have hcap (i : I) : E '' closedTerminalCap (C.hole i)=closedTerminalCap (C'.hole i) := by
    rw [←hP,closedTerminalCap,CannonSphereReflection.onePoint_image]
    change ((↑) : ℂ → Sphere) '' (P '' closure (jordanInterior (C.hole i)))=_
    rw [←trans_closed_jordan_image]
    rfl
  have hreg : C'.region=E '' C.region := by
    change (⋃i,closedTerminalCap (C'.hole i))ᶜ=E '' (⋃i,closedTerminalCap (C.hole i))ᶜ
    rw [E.image_compl,image_iUnion]
    simp_rw [hcap]
  have hreg' : C'.region=N '' (e '' C.region) := by
    rw [hreg,image_image]
    rfl
  obtain ⟨V,f,hV,hf⟩ := exists_finite_jordan_uniformization C'
  rw [hreg'] at hf
  exact ⟨V,f ∘ N,hV,(isConformalEquivalence_pointToInfinity (e OnePoint.infty)
    (e '' C.region)).trans hf⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ConstructedFiniteModels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite circle models from an invariant Beltrami solution and boundary
reflection, without a finite uniformization hypothesis. -/
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem finiteJordanModelUniformization_oai : FiniteJordanModelUniformization := by
  intro n H hd e
  exact exists_finite_jordan_image_uniformization ⟨H,hd⟩ e

end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.finiteJordanModelUniformization_oai := @OAI.CircleDomainRigidity.finiteJordanModelUniformization_oai
