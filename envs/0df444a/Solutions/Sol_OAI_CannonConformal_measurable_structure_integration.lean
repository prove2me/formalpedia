-- Prove2me | solution 1 for OAI.CannonConformal.measurable_structure_integration
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:52:30.237972+00:00
-- url     : https://prove2.me/submissions/8707ae02-f6dc-4d78-a191-f4d64bb2a102

import Mathlib
import Definitions.Def_OAIQ046C000
import Definitions.Def_OAIQ046C001
import Theorems.Thm_OAI_CannonBeltrami_normalized_smooth_beltrami_solution

section
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_MultiplyLp
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
  exact ⟨⟨hmeas,he.trans_lt ENNReal.ofReal_lt_top⟩,he⟩

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
      (by norm_num) hg.eLpNorm_lt_top).ne
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
      _ = ‖(2:ℂ)*g z‖ := by simp [g]; ring
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

lemma translate_toLp_ae {F : ℂ → ℂ} (hF : MemLp F 2 volume) (w : ℂ) :
    translateL2 w (hF.toLp F) =ᵐ[volume] fun x => F (x+w) := by
  exact (translateL2_ae w (hF.toLp F)).trans
    ((measurePreserving_add_right volume w).quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp hF))

theorem translation_bound_of_increment_bound {F : ℂ → ℂ} (hF : MemLp F 2 volume)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ w : ℂ, ‖w‖ ≤ 1 →
      eLpNorm (fun x => F (x+w)-F x) 2 volume ≤ ENNReal.ofReal (C*‖w‖)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ w : ℂ, ‖translateL2 w (hF.toLp F)-hF.toLp F‖ ≤ D*‖w‖ := by
  let f := hF.toLp F
  refine ⟨max C (2*‖f‖),hC.trans (le_max_left _ _),fun w => ?_⟩
  by_cases hw : ‖w‖ ≤ 1
  · have hae : translateL2 w f-f =ᵐ[volume] fun x => F (x+w)-F x :=
      (Lp.coeFn_sub _ _).trans ((translate_toLp_ae hF w).sub (MemLp.coeFn_toLp hF))
    have he : eLpNorm (fun x => (translateL2 w f-f) x) 2 volume ≤ ENNReal.ofReal (C*‖w‖) := by
      rw [eLpNorm_congr_ae hae]
      exact hb w hw
    have hn : ‖translateL2 w f-f‖ ≤ C*‖w‖ := by
      rw [Lp.norm_def]
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq
        (ENNReal.toReal_ofReal (mul_nonneg hC (norm_nonneg _)))
    exact hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · calc
      _ ≤ ‖translateL2 w f‖+‖f‖ := norm_sub_le _ _
      _ = 2*‖f‖ := by rw [(translateL2 w).norm_map]; ring
      _ ≤ (2*‖f‖)*‖w‖ := le_mul_of_one_le_right (by positivity) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

theorem translation_derivative_eq_ae {F : ℂ → ℂ} (hF : MemLp F 2 volume)
    (hFd : ∀ᵐ x ∂volume, DifferentiableAt ℝ F x) (v : ℂ) (g : PlaneL2)
    (hg : HasDerivAt (fun t : ℝ => translateL2 (t • v) (hF.toLp F)) g 0) :
    g =ᵐ[volume] fun x => fderiv ℝ F x v := by
  let q (t : ℝ) : PlaneL2 := t⁻¹ • (translateL2 (t • v) (hF.toLp F)-hF.toLp F)
  have hq : Tendsto q (𝓝[≠] 0) (𝓝 g) := by
    simpa only [q,zero_add,zero_smul,translateL2_zero] using hg.tendsto_slope_zero
  obtain ⟨t,ht,ha⟩ := (tendstoInMeasure_of_tendsto_Lp hq).exists_seq_tendsto_ae'
  have he (n : ℕ) : q (t n) =ᵐ[volume] fun x => (t n)⁻¹ • (F (x+(t n) • v)-F x) := by
    filter_upwards [Lp.coeFn_smul ((t n)⁻¹) (translateL2 ((t n) • v) (hF.toLp F)-hF.toLp F),
      Lp.coeFn_sub (translateL2 ((t n) • v) (hF.toLp F)) (hF.toLp F),
      translate_toLp_ae hF ((t n) • v),MemLp.coeFn_toLp hF] with x h1 h2 h3 h4
    dsimp only [q]
    rw [h1]
    dsimp only [Pi.smul_apply]
    rw [h2]
    dsimp only [Pi.sub_apply]
    rw [h3,h4]
  filter_upwards [hFd,ha,ae_all_iff.mpr he] with x hdx hax hex
  have hv : HasDerivAt (fun s : ℝ => x+s • v) v 0 := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hd : HasDerivAt (fun s : ℝ => F (x+s • v)) (fderiv ℝ F x v) 0 := by
    have hx' : HasFDerivAt F (fderiv ℝ F x) (x+(0:ℝ) • v) := by simpa using hdx.hasFDerivAt
    exact hx'.comp_hasDerivAt 0 hv
  have hp : Tendsto (fun s : ℝ => s⁻¹ • (F (x+s • v)-F x)) (𝓝[≠] 0)
      (𝓝 (fderiv ℝ F x v)) := by
    simpa only [zero_add,zero_smul,add_zero] using hd.tendsto_slope_zero
  apply tendsto_nhds_unique hax
  exact (hp.comp ht).congr (fun n => (hex n).symm)

end CannonBeltrami

namespace CannonBeltrami
open MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap

lemma fourier_derivative_distribution (f : PlaneL2) (v : ℂ)
    (hd : MemLp (fun z => directionSymbol v z*planeFourier f z) 2 volume) :
    ∂_{v} (f : 𝓢'(ℂ,ℂ)) =
      (planeFourier.symm (hd.toLp (fun z => directionSymbol v z*planeFourier f z)) : PlaneL2) := by
  apply (fourierCLE ℂ 𝓢'(ℂ,ℂ)).injective
  simp only [fourierCLE_apply]
  rw [TemperedDistribution.fourier_lineDerivOp_eq,Lp.fourier_toTemperedDistribution_eq,
    Lp.fourier_toTemperedDistribution_eq]
  have he : 𝓕 (planeFourier.symm (hd.toLp (fun z => directionSymbol v z*planeFourier f z)))=
      hd.toLp (fun z => directionSymbol v z*planeFourier f z) := planeFourier.apply_symm_apply _
  rw [he]
  ext φ
  have ht : (fun z : ℂ => ((inner ℝ z v):ℂ)).HasTemperateGrowth := by fun_prop
  simp only [smul_apply,TemperedDistribution.smulLeftCLM_apply_apply,
    Lp.toTemperedDistribution_apply,smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hd] with z hz
  rw [hz]
  dsimp only [directionSymbol]
  simp only [SchwartzMap.smulLeftCLM_apply ht,smul_eq_mul]
  rw [real_inner_comm v z]
  change (2*Real.pi*Complex.I)*((inner ℝ v z:ℝ)*φ z*planeFourier f z)=
    φ z*(2*Real.pi*Complex.I*(inner ℝ v z:ℝ)*planeFourier f z)
  ring

lemma fourier_derivative_weak (f : PlaneL2) (v : ℂ)
    (hd : MemLp (fun z => directionSymbol v z*planeFourier f z) 2 volume)
    (φ : SchwartzMap ℂ ℂ) :
    (∫ z, φ z*(planeFourier.symm (hd.toLp _) : PlaneL2) z)=
      -(∫ z, (fderiv ℝ (φ : ℂ → ℂ) z v)*f z) := by
  have h := congrArg (fun T : 𝓢'(ℂ,ℂ) => T φ) (fourier_derivative_distribution f v hd)
  simpa only [TemperedDistribution.lineDerivOp_apply_apply,Lp.toTemperedDistribution_apply,
    neg_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv,smul_eq_mul,neg_mul,integral_neg] using h.symm

theorem weak_fderiv_of_increment_bound {F : ℂ → ℂ} (hF : MemLp F 2 volume)
    (hFd : ∀ᵐ x ∂volume, DifferentiableAt ℝ F x)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ w : ℂ, ‖w‖ ≤ 1 →
      eLpNorm (fun x => F (x+w)-F x) 2 volume ≤ ENNReal.ofReal (C*‖w‖)) (v : ℂ) :
    MemLp (fun x => fderiv ℝ F x v) 2 volume ∧
      ∀ φ : SchwartzMap ℂ ℂ, (∫ z, φ z*fderiv ℝ F z v)=
        -(∫ z, (fderiv ℝ (φ : ℂ → ℂ) z v)*F z) := by
  obtain ⟨D,hD,hd⟩ := translation_bound_of_increment_bound hF hC hb
  have hm := (memLp_directionSymbol_of_translation_bound (hF.toLp F) hD hd v).1
  let g : PlaneL2 := planeFourier.symm (hm.toLp _)
  have hg := hasDerivAt_translateL2 (hF.toLp F) v hm
  have he : g =ᵐ[volume] fun x => fderiv ℝ F x v := translation_derivative_eq_ae hF hFd v g hg
  refine ⟨(Lp.memLp g).ae_eq he,fun φ => ?_⟩
  have hh := fourier_derivative_weak (hF.toLp F) v hm φ
  calc
    _ = ∫ z, φ z*g z := integral_congr_ae (he.symm.mono (fun z hz => by simpa only using congrArg (fun u => φ z*u) hz))
    _ = -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z v*(hF.toLp F) z) := hh
    _ = _ := by
      congr 1
      exact integral_congr_ae ((MemLp.coeFn_toLp hF).mono (fun z hz => by simpa only using congrArg (fun u => fderiv ℝ (φ : ℂ → ℂ) z v*u) hz))
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
-- module Solutions.OAIQ046_CN.Cannon_Energy_ClopenNeighborhoodComponent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators
open Set Topology

namespace CannonContinuum

lemma clopen_neighborhood_of_component {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] (x : X) {U : Set X} (hU : IsOpen U)
    (hC : connectedComponent x ⊆ U) :
    ∃ W : Set X, IsClopen W ∧ x ∈ W ∧ W ⊆ U := by
  let S := {s : Set X // IsClopen s ∧ x ∈ s}
  have hnull : Uᶜ ∩ ⋂ s : S, (s : Set X) = ∅ := by
    rw [← connectedComponent_eq_iInter_isClopen]
    exact disjoint_iff_inter_eq_empty.mp (disjoint_compl_left_iff_subset.mpr hC)
  obtain ⟨T, hT⟩ := hU.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun s : S => (s : Set X)) (fun s => s.property.1.isClosed)
    hnull
  refine ⟨⋂ s ∈ T, (s : Set X), isClopen_biInter_finset (fun s _ => s.property.1),
    mem_iInter₂.mpr (fun s _ => s.property.2), ?_⟩
  exact disjoint_compl_left_iff_subset.mp (Set.disjoint_iff_inter_eq_empty.mpr hT)

theorem component_meets_level {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [PreconnectedSpace X]
    (f : X → ℝ) (hf : Continuous f) (r : ℝ)
    (x : {z : X // r ≤ f z}) (hbelow : ∃ y : X, f y < r) :
    ∃ z ∈ connectedComponent x, f (z : X) = r := by
  let K : Set X := {z | r ≤ f z}
  have hK : IsClosed K := isClosed_le continuous_const hf
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  by_contra hn
  push Not at hn
  have hC : connectedComponent x ⊆ {z : K | r < f (z : X)} := by
    intro z hz
    exact lt_of_le_of_ne z.property (Ne.symm (hn z hz))
  obtain ⟨W, hW, hxW, hWU⟩ := clopen_neighborhood_of_component (X := K) x
    (isOpen_lt continuous_const (hf.comp continuous_subtype_val)) hC
  let V : Set X := Subtype.val '' W
  have hVc : IsClosed V := hK.isClosedMap_subtype_val W hW.isClosed
  have hVo : IsOpen V := by
    obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp hW.isOpen
    have hV : V = O ∩ {z | r < f z} := by
      ext z
      constructor
      · rintro ⟨z', hz', rfl⟩
        exact ⟨by simpa only [← hOW, mem_preimage] using hz', hWU hz'⟩
      · rintro ⟨hzO, hzr⟩
        refine ⟨⟨z, show r ≤ f z from hzr.le⟩, ?_, rfl⟩
        simpa only [← hOW, mem_preimage] using hzO
    rw [hV]
    exact hO.inter (isOpen_lt continuous_const hf)
  have hVall : V = univ := (show IsClopen V from ⟨hVc, hVo⟩).eq_univ ⟨x, x, hxW, rfl⟩
  obtain ⟨y, hy⟩ := hbelow
  have hyV : y ∈ V := by rw [hVall]; trivial
  obtain ⟨z, hz, hzy⟩ := hyV
  have := z.property
  rw [hzy] at this
  exact (not_lt_of_ge this) hy

end CannonContinuum

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
-- module Solutions.OAIQ046_CN.Cannon_Conformal_PreservesProducts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
section
section
section
noncomputable section
namespace CannonMetricQC
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem DensityOne.approximate {s : Set ℂ} (_hs : MeasurableSet s) {x : ℂ}
    (hx : x ∈ s) (hd : DensityOne s x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℂ, dist x y < δ →
      ∃ z ∈ s, dist y z ≤ ε*dist x y := by
  let e := min ε 1
  have he : 0 < e := lt_min hε (by norm_num)
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  have hlim : Tendsto (fun r : ℝ =>
      (volume (s ∩ closedBall x r)/volume (closedBall x r)).toReal)
      (𝓝[>] 0) (𝓝 (1:ℝ)) := by
    simpa only [ENNReal.toReal_one,Function.comp_def] using
      (ENNReal.tendsto_toReal (by norm_num : (1:ℝ≥0∞) ≠ ∞)).comp hd
  have hev := hlim.eventually (lt_mem_nhds (show (1:ℝ)-e^2/8 < 1 by nlinarith [sq_pos_of_pos he]))
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨δ/2,by positivity,?_⟩
  intro y hy
  by_cases hxy : x=y
  · subst y
    exact ⟨x,hx,by simp⟩
  have hp : 0 < dist x y := dist_pos.mpr hxy
  by_contra! hhole
  have hdis : Disjoint (s ∩ closedBall x (2*dist x y)) (ball y (e*dist x y)) := by
    apply Set.disjoint_left.mpr
    intro z hzs hzb
    have h₁ := hhole z hzs.1
    have h₂ : dist y z < e*dist x y := by simpa only [mem_ball,dist_comm] using hzb
    have h₃ := mul_le_mul_of_nonneg_right heε hp.le
    linarith
  have hsub : (s ∩ closedBall x (2*dist x y)) ∪ ball y (e*dist x y) ⊆ closedBall x (2*dist x y) := by
    apply union_subset inter_subset_right
    intro z hz
    have hz' : dist z y < e*dist x y := mem_ball.mp hz
    have ht := dist_triangle z y x
    have hh := mul_le_mul_of_nonneg_right he1 hp.le
    rw [dist_comm y x] at ht
    change dist z x ≤ 2*dist x y
    linarith
  have hm := measure_mono (μ:=volume) hsub
  rw [measure_union hdis isOpen_ball.measurableSet] at hm
  have hfin : volume (closedBall x (2*dist x y)) ≠ ∞ := (isCompact_closedBall _ _).measure_ne_top
  have hr := ENNReal.toReal_mono hfin hm
  have hsf : volume (s ∩ closedBall x (2*dist x y)) ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono inter_subset_right)
  have hbf : volume (ball y (e*dist x y)) ≠ ∞ := measure_ball_ne_top
  rw [ENNReal.toReal_add hsf hbf] at hr
  have hvc (r : ℝ) (hr : 0 ≤ r) : (volume (closedBall x r)).toReal=r^2*Real.pi := by
    simp only [Complex.volume_closedBall,ENNReal.toReal_mul,ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr,ENNReal.coe_toReal,NNReal.coe_real_pi]
  have hvb : (volume (ball y (e*dist x y))).toReal=(e*dist x y)^2*Real.pi := by
    simp only [Complex.volume_ball,ENNReal.toReal_mul,ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (mul_nonneg he.le hp.le),ENNReal.coe_toReal,NNReal.coe_real_pi]
  rw [hvc _ (by positivity),hvb] at hr
  have hmem : 2*dist x y ∈ ball (0:ℝ) δ ∩ Ioi 0 := by
    constructor
    · have h2p : 0 < 2*dist x y := by linarith
      simpa only [mem_ball,Real.dist_eq,sub_zero,abs_of_pos h2p] using
        (show 2*dist x y < δ by linarith)
    · change 0 < 2*dist x y
      positivity
  have hnear := hδb hmem
  change 1-e^2/8 < (volume (s ∩ closedBall x (2*dist x y))/volume (closedBall x (2*dist x y))).toReal at hnear
  rw [ENNReal.toReal_div,hvc _ (by positivity)] at hnear
  have hvp : 0 < (2*dist x y)^2*Real.pi := by positivity
  have hh := (lt_div_iff₀ hvp).mp hnear
  have hp' : 0 < e^2*(dist x y)^2*Real.pi := by positivity
  nlinarith
end CannonMetricQC

namespace CannonMetricQC
open Set Metric MeasureTheory Filter Asymptotics
open scoped Topology ENNReal NNReal

theorem derivative_of_density {f : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r)
    (hlip : ∀ z ∈ s, ∀ y, dist z y < r → dist (f z) (f y) ≤ C*dist z y)
    {x : ℂ} (hx : x ∈ s) (hd : DensityOne s x) {A : ℂ →L[ℝ] ℂ}
    (ha : HasFDerivWithinAt f A s x) : HasFDerivAt f A x := by
  apply HasFDerivAt.of_isLittleO
  apply isLittleO_iff.mpr
  intro ε hε
  let P := C+‖A‖+1
  have hP : 0 < P := by dsimp [P]; positivity
  let e := min (1/2:ℝ) (ε/(4*P))
  have he : 0 < e := lt_min (by norm_num) (div_pos hε (by positivity))
  have he1 : e ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have heP : (C+‖A‖)*e ≤ ε/4 := by
    have h := min_le_right (1/2:ℝ) (ε/(4*P))
    have hh := (le_div_iff₀ (show 0 < 4*P by positivity)).mp h
    have hsmall : (C+‖A‖)*e ≤ P*e := mul_le_mul_of_nonneg_right (by dsimp [P]; linarith) he.le
    nlinarith
  obtain ⟨d,hdp,hda⟩ := hd.approximate hs hx he
  have hev := (isLittleO_iff.mp ha.isLittleO) (show 0 < ε/4 by positivity)
  obtain ⟨b,hbp,hba⟩ := Metric.mem_nhdsWithin_iff.mp hev
  let t := min d (min (b/2) (r/2))
  have htp : 0 < t := lt_min hdp (lt_min (by positivity) (by positivity))
  filter_upwards [ball_mem_nhds x htp] with y hy
  have hxy : dist x y < t := by simpa only [mem_ball,dist_comm] using hy
  have hyd : dist x y < d := hxy.trans_le (min_le_left _ _)
  have hyb : dist x y < b/2 := hxy.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hyr : dist x y < r/2 := hxy.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨z,hzs,hz⟩ := hda y hyd
  have hyz : dist y z ≤ dist x y := hz.trans (by nlinarith [dist_nonneg (x:=x) (y:=y)])
  have hxz : dist x z ≤ 2*dist x y := (dist_triangle x y z).trans (by linarith)
  have hzb : z ∈ ball x b ∩ s := by
    refine ⟨?_,hzs⟩
    change dist z x < b
    rw [dist_comm]
    linarith
  have hrem := hba hzb
  change ‖f z-f x-A (z-x)‖ ≤ ε/4*‖z-x‖ at hrem
  have hzy : dist z y < r := by rw [dist_comm]; linarith
  have hfl := hlip z hzs y hzy
  have hid : f y-f x-A (y-x)=(f y-f z)+(f z-f x-A (z-x))-A (y-z) := by
    simp only [map_sub]
    abel
  have hnorm : ‖f y-f x-A (y-x)‖ ≤ dist (f y) (f z)+ε/4*dist x z+‖A‖*dist y z := by
    rw [hid]
    calc
      _ ≤ ‖f y-f z‖+‖f z-f x-A (z-x)‖+‖A (y-z)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := by
        rw [← dist_eq_norm z x, dist_comm z x] at hrem
        rw [← dist_eq_norm (f y) (f z)]
        exact add_le_add (add_le_add le_rfl hrem)
          (by simpa only [dist_eq_norm] using A.le_opNorm (y-z))
  have hmult := mul_le_mul_of_nonneg_right heP (dist_nonneg (x:=x) (y:=y))
  have hzlin := mul_le_mul_of_nonneg_left hz (add_nonneg hC (norm_nonneg A))
  have hxzlin := mul_le_mul_of_nonneg_left hxz (show 0 ≤ ε/4 by positivity)
  rw [dist_comm (f z) (f y),dist_comm z y] at hfl
  change ‖f y-f x-A (y-x)‖ ≤ ε*‖y-x‖
  rw [← dist_eq_norm y x,dist_comm y x]
  nlinarith [dist_nonneg (x:=x) (y:=y)]
end CannonMetricQC

namespace CannonMetricQC
open Set Metric MeasureTheory Filter
open scoped Topology NNReal ENNReal

lemma lipPiece_closed {f : ℂ → ℂ} (hf : Continuous f) (n : ℕ) : IsClosed (lipPiece f n) := by
  have hy (y : ℂ) : IsClosed {x | dist x y < 1/((n:ℝ)+1) →
      dist (f x) (f y) ≤ (n:ℝ)*dist x y} := by
    have h₁ : IsClosed {x : ℂ | 1/((n:ℝ)+1) ≤ dist x y} :=
      isClosed_le continuous_const (continuous_id.dist continuous_const)
    have h₂ : IsClosed {x : ℂ | dist (f x) (f y) ≤ (n:ℝ)*dist x y} :=
      isClosed_le (hf.dist continuous_const) (continuous_const.mul (continuous_id.dist continuous_const))
    have hh := h₁.union h₂
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [mem_ofPred_eq,mem_union,← not_lt]
    tauto
  have h₁ : IsClosed {x : ℂ | ‖x‖ ≤ (n:ℝ)+1} := isClosed_le continuous_norm continuous_const
  have hh := h₁.inter (isClosed_iInter hy)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [lipPiece,mem_ofPred_eq,mem_inter_iff,mem_iInter]

lemma lipPiece_lipschitz {f : ℂ → ℂ} (hf : Continuous f) (n : ℕ) :
    ∃ L : ℝ≥0, LipschitzOnWith L f (lipPiece f n) := by
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0:ℂ) ((n:ℝ)+1)).exists_bound_of_continuousOn hf.continuousOn
  have hMp : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0 (by simp; positivity))
  let L : ℝ≥0 := ⟨(n:ℝ)+2*M*((n:ℝ)+1),by positivity⟩
  refine ⟨L,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have hnx : ‖f x‖ ≤ M := hM x (by simpa only [mem_closedBall,dist_zero_right] using hx.1)
  have hny : ‖f y‖ ≤ M := hM y (by simpa only [mem_closedBall,dist_zero_right] using hy.1)
  change dist (f x) (f y) ≤ ((n:ℝ)+2*M*((n:ℝ)+1))*dist x y
  by_cases hd : dist x y < 1/((n:ℝ)+1)
  · exact (hx.2 y hd).trans (mul_le_mul_of_nonneg_right (by nlinarith) dist_nonneg)
  · have hd' : 1 ≤ ((n:ℝ)+1)*dist x y := by
      have hn : 0 < (n:ℝ)+1 := by positivity
      exact (div_le_iff₀ hn).mp (le_of_not_gt hd) |>.trans_eq (mul_comm _ _)
    have ht : dist (f x) (f y) ≤ 2*M := by
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith)
    have hm := mul_le_mul_of_nonneg_left hd' (show 0 ≤ 2*M by positivity)
    nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (dist_nonneg (x:=x) (y:=y))]

lemma PointwiseLip.mem_lipPiece {f : ℂ → ℂ} {x : ℂ} (hx : PointwiseLip f x) :
    ∃ n : ℕ, x ∈ lipPiece f n := by
  obtain ⟨C,r,hC,hr,h⟩ := hx
  obtain ⟨n,hn⟩ := exists_nat_gt (max C (max (1/r) ‖x‖))
  have hnC : C < (n:ℝ) := (le_max_left _ _).trans_lt hn
  have hnr : 1/r < (n:ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hn
  have hnx : ‖x‖ < (n:ℝ) := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hn
  have hn1 : 0 < (n:ℝ)+1 := by positivity
  have hrad : 1/((n:ℝ)+1) ≤ r := by
    apply (div_le_iff₀ hn1).mpr
    have hh := (div_lt_iff₀ hr).mp hnr
    nlinarith
  refine ⟨n, ?_⟩
  change ‖x‖ ≤ (n:ℝ)+1 ∧ _
  refine ⟨by linarith, ?_⟩
  intro y hy
  exact (h y (hy.trans_le hrad)).trans (mul_le_mul_of_nonneg_right hnC.le dist_nonneg)

theorem continuous_ae_differentiable_of_pointwiseLip {f : ℂ → ℂ} (hf : Continuous f)
    (hp : ∀ᵐ x ∂volume, PointwiseLip f x) : ∀ᵐ x ∂volume, DifferentiableAt ℝ f x := by
  have hpiece (n : ℕ) : ∀ᵐ x ∂volume, x ∈ lipPiece f n → DifferentiableAt ℝ f x := by
    obtain ⟨L,hL⟩ := lipPiece_lipschitz hf n
    have hm := (lipPiece_closed hf n).measurableSet
    filter_upwards [hL.ae_differentiableWithinAt_of_mem (μ:=volume),
      Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hm] with x hdx hdens hx
    have hd : DensityOne (lipPiece f n) x := by
      simpa only [DensityOne,indicator_of_mem hx,Pi.one_apply] using hdens
    exact (derivative_of_density hm (Nat.cast_nonneg n) (by positivity)
      (fun z hz y hy => hz.2 y hy) hx hd (hdx hx).hasFDerivWithinAt).differentiableAt
  filter_upwards [ae_all_iff.mpr hpiece,hp] with x hx hp
  obtain ⟨n,hn⟩ := hp.mem_lipPiece
  exact hx n hn
end CannonMetricQC

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
-- module Solutions.OAIQ046_CN.Cannon_Conformal_ImageArea
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
section
section
section
noncomputable section
namespace CannonMetricQC
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

lemma image_ball_contains (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) (x y : ℂ) :
    ball (f x) (dist (f x) (f y)/H) ⊆ f '' closedBall x (dist x y) := by
  intro z hz
  refine ⟨f.symm z,?_,f.apply_symm_apply z⟩
  by_contra hh
  have hd : dist x y < dist x (f.symm z) := by
    simpa only [mem_closedBall,dist_comm,not_le] using hh
  have h := hf x y (f.symm z) hd.le
  rw [f.apply_symm_apply] at h
  have hz' : dist (f x) z < dist (f x) (f y)/H := by simpa only [mem_ball,dist_comm] using hz
  have hh' := (lt_div_iff₀ hH).mp hz'
  nlinarith

lemma imageArea_apply (f : ℂ ≃ₜ ℂ) {s : Set ℂ} (hs : MeasurableSet s) :
    imageArea f s=volume (f '' s) := by
  rw [imageArea,Measure.map_apply f.symm.continuous.measurable hs]
  congr 1
  exact (f.toEquiv.image_eq_preimage_symm s).symm

instance imageArea_locallyFinite (f : ℂ ≃ₜ ℂ) : IsLocallyFiniteMeasure (imageArea f) where
  finiteAtNhds x := by
    refine ⟨closedBall x 1,closedBall_mem_nhds x (by norm_num),?_⟩
    rw [imageArea_apply f isClosed_closedBall.measurableSet]
    exact ((isCompact_closedBall x 1).image f.continuous).measure_lt_top

lemma area_controls_dist (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) (x y : ℂ) :
    (dist (f x) (f y)/H)^2*Real.pi ≤
      (imageArea f (closedBall x (dist x y))).toReal := by
  have h := measure_mono (μ:=volume) (image_ball_contains f hH hf x y)
  rw [← imageArea_apply f isClosed_closedBall.measurableSet] at h
  have hm : imageArea f (closedBall x (dist x y)) ≠ ∞ :=
    (isCompact_closedBall x (dist x y)).measure_ne_top
  have hr := ENNReal.toReal_mono hm h
  simpa only [Complex.volume_ball,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (div_nonneg dist_nonneg hH.le),ENNReal.coe_toReal,
    NNReal.coe_real_pi] using hr

theorem weakQS_ae_pointwiseLip (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) : ∀ᵐ x ∂volume, PointwiseLip f x := by
  have hlim := Besicovitch.ae_tendsto_rnDeriv (imageArea f) volume
  filter_upwards [hlim,Measure.rnDeriv_lt_top (imageArea f) volume] with x hx hfin
  let c : ℝ≥0∞ := (imageArea f).rnDeriv volume x
  have hc : c ≠ ∞ := hfin.ne
  have ht : Tendsto (fun r =>
      ((imageArea f (closedBall x r))/(volume (closedBall x r))).toReal)
      (𝓝[>] (0:ℝ)) (𝓝 c.toReal) := ENNReal.tendsto_toReal hc |>.comp hx
  have hev := ht.eventually (gt_mem_nhds (show c.toReal < c.toReal+1 by linarith))
  obtain ⟨r,hr,hrb⟩ := Metric.mem_nhdsWithin_iff.mp hev
  let B := c.toReal+1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨H*(B+1),r,mul_nonneg hH.le (by positivity),hr,?_⟩
  intro y hy
  by_cases heq : x=y
  · subst y
    simp
  have hd : 0 < dist x y := dist_pos.mpr heq
  have hmem : dist x y ∈ ball (0:ℝ) r := by
    simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hd] using hy
  have hbound := hrb ⟨hmem,hd⟩
  change ((imageArea f (closedBall x (dist x y)))/(volume (closedBall x (dist x y)))).toReal < B at hbound
  have harea := area_controls_dist f hH hf x y
  have hv : (volume (closedBall x (dist x y))).toReal=(dist x y)^2*Real.pi := by
    simp only [Complex.volume_closedBall,ENNReal.toReal_mul,ENNReal.toReal_pow,
      ENNReal.toReal_ofReal dist_nonneg,ENNReal.coe_toReal,NNReal.coe_real_pi]
  rw [ENNReal.toReal_div,hv] at hbound
  have hp : 0 < (dist x y)^2*Real.pi := mul_pos (sq_pos_of_pos hd) Real.pi_pos
  have hm : (imageArea f (closedBall x (dist x y))).toReal < B*((dist x y)^2*Real.pi) :=
    (div_lt_iff₀ hp).mp hbound
  have hs : (dist (f x) (f y)/H)^2 < B*(dist x y)^2 := by
    nlinarith [Real.pi_pos]
  have hb : B ≤ (B+1)^2 := by nlinarith
  have hv' : dist (f x) (f y)/H ≤ (B+1)*dist x y := by
    have hpos : 0 ≤ (B+1)*dist x y := by positivity
    have hm' := mul_le_mul_of_nonneg_right hb (sq_nonneg (dist x y))
    nlinarith [sq_nonneg (dist (f x) (f y)/H+(B+1)*dist x y)]
  have h := (div_le_iff₀ hH).mp hv'
  nlinarith
end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory

theorem weakQS_ae_differentiable (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) : ∀ᵐ x ∂volume, DifferentiableAt ℝ f x :=
  continuous_ae_differentiable_of_pointwiseLip f.continuous (weakQS_ae_pointwiseLip f hH hf)
end CannonMetricQC

noncomputable section
namespace CannonMetricQC
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology

lemma measurable_ballArea (ν : Measure ℂ) [SFinite ν] (r : ℝ) :
    Measurable (fun x : ℂ => ν (closedBall x r)) := by
  let F : ℂ × ℂ → ℝ≥0∞ := {p | dist p.1 p.2 ≤ r}.indicator 1
  have hF : Measurable F := measurable_const.indicator
    (isClosed_le (continuous_fst.dist continuous_snd) continuous_const).measurableSet
  have h := hF.lintegral_prod_right' (ν:=ν)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  have he : (fun y => F (x,y)) = (closedBall x r).indicator (fun _ => (1:ℝ≥0∞)) := by
    funext y
    by_cases h : dist x y ≤ r
    · simp [F, h, indicator_of_mem, show y ∈ closedBall x r by simpa [mem_closedBall, dist_comm] using h]
    · simp [F, h, indicator_of_notMem, show y ∉ closedBall x r by simpa [mem_closedBall, dist_comm] using h]
  rw [he,lintegral_indicator_const isClosed_closedBall.measurableSet]
  simp

theorem integrated_ballArea (ν : Measure ℂ) [SFinite ν] (c : ℂ) (R r : ℝ) :
    (∫⁻ x in closedBall c R, ν (closedBall x r)) ≤
      (volume (closedBall (0:ℂ) r))*ν (closedBall c (R+r)) := by
  let F : ℂ → ℂ → ℝ≥0∞ := fun x y => if dist x y ≤ r then 1 else 0
  have hF : Measurable (Function.uncurry F) := by
    exact measurable_const.ite (measurableSet_le
      (measurable_fst.dist measurable_snd) measurable_const) measurable_const
  have he (x : ℂ) : (∫⁻ y, F x y ∂ν)=ν (closedBall x r) := by
    have hh : F x = (closedBall x r).indicator (fun _ => (1:ℝ≥0∞)) := by
      funext y
      by_cases h : dist x y ≤ r
      · simp [F, h, show y ∈ closedBall x r by simpa [mem_closedBall, dist_comm] using h]
      · simp [F, h, show y ∉ closedBall x r by simpa [mem_closedBall, dist_comm] using h]
    rw [hh,lintegral_indicator_const isClosed_closedBall.measurableSet]
    simp
  simp_rw [← he]
  rw [lintegral_lintegral_swap hF.aemeasurable]
  calc
    _ ≤ ∫⁻ y, (closedBall c (R+r)).indicator
        (fun _ => volume (closedBall (0:ℂ) r)) y ∂ν := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ closedBall c (R+r)
      · rw [indicator_of_mem hy]
        have hh : (fun x => F x y)=(closedBall y r).indicator (fun _ => (1:ℝ≥0∞)) := by
          funext x
          by_cases h : dist x y ≤ r
          · simp [F, h, show x ∈ closedBall y r from h]
          · simp [F, h, show x ∉ closedBall y r from h]
        change (∫⁻ x in closedBall c R, F x y) ≤ _
        rw [hh,lintegral_indicator_const isClosed_closedBall.measurableSet,one_mul]
        calc
          (volume.restrict (closedBall c R)) (closedBall y r) ≤ volume (closedBall y r) :=
            Measure.restrict_apply_le _ _
          _ = volume (closedBall (0:ℂ) r) := by rw [Complex.volume_closedBall,Complex.volume_closedBall]
      · rw [indicator_of_notMem hy]
        apply le_of_eq
        apply lintegral_eq_zero_of_ae_eq_zero
        filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with x hx
        have hh : ¬ dist x y ≤ r := by
          intro hxy
          apply hy
          change dist y c ≤ R+r
          have hx' : dist x c ≤ R := hx
          calc
            dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
            _ ≤ R+r := by rw [dist_comm y x]; linarith
        simp [F,hh]
    _ = _ := lintegral_indicator_const isClosed_closedBall.measurableSet _
end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory Set Metric
open scoped ENNReal NNReal

lemma square_dist_le_area (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) (x y : ℂ) :
    ‖f y-f x‖ₑ^2 ≤ ENNReal.ofReal (H^2/Real.pi)*imageArea f (closedBall x (dist x y)) := by
  have hm : imageArea f (closedBall x (dist x y)) ≠ ∞ :=
    (isCompact_closedBall x (dist x y)).measure_ne_top
  have h := area_controls_dist f hH hf x y
  have hh : dist (f x) (f y)^2 ≤ (H^2/Real.pi)*(imageArea f (closedBall x (dist x y))).toReal := by
    have he : (dist (f x) (f y)/H)^2*H^2=dist (f x) (f y)^2 := by
      rw [←mul_pow,div_mul_cancel₀ _ hH.ne']
    have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg H)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ Real.pi_pos).mpr
    rw [mul_assoc, mul_comm Real.pi (H^2), ← mul_assoc, he] at hmul
    nlinarith
  have hr := ENNReal.ofReal_le_ofReal hh
  rw [ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) Real.pi_pos.le),ENNReal.ofReal_toReal hm] at hr
  simpa only [dist_comm (f x) (f y),dist_eq_norm,ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm] using hr

theorem weakQS_increment_energy (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) (c w : ℂ) (R : ℝ) :
    (∫⁻ x in closedBall c R, ‖f (x+w)-f x‖ₑ^2) ≤
      ENNReal.ofReal (H^2*‖w‖^2)*imageArea f (closedBall c (R+‖w‖)) := by
  have hpt (x : ℂ) := square_dist_le_area f hH hf x (x+w)
  have hd (x : ℂ) : dist x (x+w)=‖w‖ := by simp [dist_eq_norm]
  have harea := integrated_ballArea (imageArea f) c R ‖w‖
  calc
    _ ≤ ∫⁻ x in closedBall c R, ENNReal.ofReal (H^2/Real.pi)*
        imageArea f (closedBall x ‖w‖) := by
      apply lintegral_mono
      intro x
      simpa only [hd] using hpt x
    _ = ENNReal.ofReal (H^2/Real.pi)*(∫⁻ x in closedBall c R, imageArea f (closedBall x ‖w‖)) :=
      lintegral_const_mul _ (measurable_ballArea _ _)
    _ ≤ ENNReal.ofReal (H^2/Real.pi)*(volume (closedBall (0:ℂ) ‖w‖)*
        imageArea f (closedBall c (R+‖w‖))) := mul_le_mul le_rfl harea zero_le zero_le
    _ = _ := by
      rw [Complex.volume_closedBall,← mul_assoc]
      congr 1
      have hp : (NNReal.pi:ℝ≥0∞)=ENNReal.ofReal Real.pi := by rw [← NNReal.coe_real_pi]; exact ENNReal.ofReal_coe_nnreal.symm
      rw [hp,← ENNReal.ofReal_pow (norm_nonneg _),← ENNReal.ofReal_mul (sq_nonneg _),
        ← ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) Real.pi_pos.le)]
      congr 1
      field_simp
end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory Set Metric
open scoped ENNReal NNReal

lemma eLpNorm_two_sq {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (g : X → E) (μ : Measure X) :
    (eLpNorm' g (2:ℝ) μ)^2=∫⁻ x, ‖g x‖ₑ^2 ∂μ := by
  simpa only [ENNReal.rpow_two] using
    (lintegral_rpow_enorm_eq_rpow_eLpNorm' (f:=g) (μ:=μ) (by norm_num : (0:ℝ) < 2)).symm

theorem weakQS_increment_lp (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) (c : ℂ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖w‖ ≤ 1 →
      eLpNorm (fun x => f (x+w)-f x) 2 (volume.restrict (closedBall c R)) ≤
        ENNReal.ofReal (C*‖w‖) := by
  let T := imageArea f (closedBall c (R+1))
  have hT : T ≠ ∞ := (isCompact_closedBall c (R+1)).measure_ne_top
  let C := H*(Real.sqrt T.toReal)
  have hC : 0 ≤ C := mul_nonneg hH.le (Real.sqrt_nonneg _)
  refine ⟨C,hC,fun w hw => ?_⟩
  have he := weakQS_increment_energy f hH hf c w R
  have hm : imageArea f (closedBall c (R+‖w‖)) ≤ T :=
    measure_mono (closedBall_subset_closedBall (by linarith))
  have hb : (eLpNorm (fun x => f (x+w)-f x) 2 (volume.restrict (closedBall c R)))^2 ≤
      (ENNReal.ofReal (C*‖w‖))^2 := by
    have hincrement : Continuous (fun x : ℂ => f (x+w)-f x) :=
      (f.continuous.comp (continuous_id.add continuous_const)).sub f.continuous
    rw [eLpNorm_eq_eLpNorm' (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num : (2:ℝ≥0∞) ≠ ⊤),
      ENNReal.toReal_ofNat,eLpNorm_two_sq]
    apply he.trans
    calc
      _ ≤ ENNReal.ofReal (H^2*‖w‖^2)*T := mul_le_mul le_rfl hm zero_le zero_le
      _ = _ := by
        rw [← ENNReal.ofReal_toReal hT,← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
          ← ENNReal.ofReal_pow (mul_nonneg hC (norm_nonneg _))]
        congr 1
        dsimp only [C]
        rw [mul_pow,mul_pow,Real.sq_sqrt ENNReal.toReal_nonneg]
        ring
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0:ℝ) < 2)).mp (by simpa only [ENNReal.rpow_two] using hb)
end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology

theorem cutoff_increment_bound (f : ℂ → ℂ) (hf : Continuous f)
    (χ : ℂ → ℂ) {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχb : ∀ x, ‖χ x‖ ≤ 1) {R : ℝ} (_hR : 0 ≤ R)
    (hs : ∀ x, R < ‖x‖ → χ x=0)
    (hi : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖w‖ ≤ 1 →
      eLpNorm (fun x => f (x+w)-f x) 2 (volume.restrict (closedBall 0 (R+1))) ≤
        ENNReal.ofReal (C*‖w‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖w‖ ≤ 1 →
      eLpNorm (fun x => χ (x+w)*f (x+w)-χ x*f x) 2 volume ≤
        ENNReal.ofReal (C*‖w‖) := by
  obtain ⟨E,hE,hi⟩ := hi
  let S : Set ℂ := closedBall 0 (R+1)
  let μ := volume.restrict S
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (isCompact_closedBall 0 (R+1)).measure_ne_top
  obtain ⟨B,hB0,hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ S, ‖f x‖ ≤ B := by
    obtain ⟨b,hb⟩ := (isCompact_closedBall (0:ℂ) (R+1)).exists_bound_of_continuousOn hf.continuousOn
    exact ⟨max b 0,le_max_right _ _,fun x hx => (hb x hx).trans (le_max_left _ _)⟩
  let K := eLpNorm (fun _ : ℂ => (1:ℂ)) 2 μ
  have hK : K ≠ ∞ := (memLp_const (1:ℂ) (p:=2) (μ:=μ)).2.ne
  let C := E + (L:ℝ)*B*K.toReal
  have hC : 0 ≤ C := add_nonneg hE (mul_nonneg (mul_nonneg L.coe_nonneg hB0) ENNReal.toReal_nonneg)
  refine ⟨C,hC,fun w hw => ?_⟩
  let A (x : ℂ) := χ (x+w)*(f (x+w)-f x)
  let D (x : ℂ) := (χ (x+w)-χ x)*f x
  have hA : Continuous A := (hχ.continuous.comp (continuous_id.add continuous_const)).mul
    ((hf.comp (continuous_id.add continuous_const)).sub hf)
  have hD : Continuous D := ((hχ.continuous.comp (continuous_id.add continuous_const)).sub hχ.continuous).mul hf
  have hsum : (fun x => χ (x+w)*f (x+w)-χ x*f x)=A+D := by
    funext x
    dsimp [A,D]
    ring
  have hzero (x : ℂ) (hx : x ∉ S) : (A+D) x=0 := by
    have hx' : R+1 < ‖x‖ := by simpa [S,mem_closedBall,dist_zero_right,not_le] using hx
    have hxw : R < ‖x+w‖ := by
      have hn : ‖x‖ ≤ ‖x+w‖+‖w‖ := by simpa using norm_sub_le (x+w) w
      linarith
    dsimp [A,D]
    rw [hs x (by linarith), hs (x+w) hxw]
    simp
  have hind : S.indicator (A+D)=A+D := by
    funext x
    by_cases hx : x ∈ S
    · simp [hx]
    · simp [hx,hzero x hx]
  have ha : eLpNorm A 2 μ ≤ ENNReal.ofReal (E*‖w‖) := by
    have he : eLpNorm A 2 μ ≤ eLpNorm (fun x => f (x+w)-f x) 2 μ :=
      eLpNorm_mono (fun x => by
        dsimp [A]
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hχb _))
    exact he.trans (hi w hw)
  have hd : eLpNorm D 2 μ ≤ ENNReal.ofReal ((L:ℝ)*B*‖w‖)*K := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    filter_upwards [ae_restrict_mem (isClosed_closedBall.measurableSet)] with x hx
    have hl : ‖χ (x+w)-χ x‖ ≤ (L:ℝ)*‖w‖ := by
      simpa [dist_eq_norm] using hχ.dist_le_mul (x+w) x
    dsimp [D]
    simp only [norm_mul,norm_one,mul_one]
    calc
      _ ≤ ((L:ℝ)*‖w‖)*B := mul_le_mul hl (hB x hx) (norm_nonneg _) (mul_nonneg L.coe_nonneg (norm_nonneg _))
      _ = _ := by ring
  calc
    _ = eLpNorm (A+D) 2 μ := by
      rw [hsum]
      calc
        _ = eLpNorm (S.indicator (A+D)) 2 volume := congrArg (fun g => eLpNorm g 2 volume) hind.symm
        _ = _ := eLpNorm_indicator_eq_eLpNorm_restrict isClosed_closedBall.measurableSet
    _ ≤ eLpNorm A 2 μ+eLpNorm D 2 μ := eLpNorm_add_le hA.aestronglyMeasurable hD.aestronglyMeasurable (by norm_num)
    _ ≤ ENNReal.ofReal (E*‖w‖)+ENNReal.ofReal ((L:ℝ)*B*‖w‖)*K := add_le_add ha hd
    _ = ENNReal.ofReal (C*‖w‖) := by
      rw [← ENNReal.ofReal_toReal hK,← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg L.coe_nonneg hB0) (norm_nonneg _)),
        ← ENNReal.ofReal_add (mul_nonneg hE (norm_nonneg _)) (by positivity)]
      congr 1
      dsimp [C]
      ring

lemma cutoff_hasCompactSupport (χ : ℂ → ℂ) {R : ℝ}
    (hs : ∀ x, R < ‖x‖ → χ x=0) : HasCompactSupport χ := by
  apply (isCompact_closedBall (0:ℂ) R).of_isClosed_subset (isClosed_tsupport χ)
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hh
  have hz := hs x (by simpa [mem_closedBall,dist_zero_right,not_le] using hh)
  exact hx hz

theorem weakQS_cutoff_increment_bound (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) (χ : ℂ → ℂ) {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχb : ∀ x, ‖χ x‖ ≤ 1) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ x, R < ‖x‖ → χ x=0) :
    MemLp (fun x => χ x*f x) 2 volume ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖w‖ ≤ 1 →
      eLpNorm (fun x => χ (x+w)*f (x+w)-χ x*f x) 2 volume ≤
        ENNReal.ofReal (C*‖w‖) := by
  refine ⟨(hχ.continuous.mul f.continuous).memLp_of_hasCompactSupport
    ((cutoff_hasCompactSupport χ hs).mul_right),?_⟩
  exact cutoff_increment_bound f f.continuous χ hχ hχb hR hs
    (weakQS_increment_lp f hH hf 0 (R+1))
end CannonMetricQC

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
-- module Solutions.OAIQ046_CN.Cannon_Conformal_CutoffBump
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
section
section
section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace CannonMetricQC
open Set Metric Filter
open scoped Topology ContDiff NNReal

lemma smoothCutoff_smooth (R : ℝ) : ContDiff ℝ ∞ (smoothCutoff R) :=
  Complex.ofRealCLM.contDiff.comp (cutoffBump R).contDiff

lemma smoothCutoff_support (R : ℝ) : HasCompactSupport (smoothCutoff R) :=
  (cutoffBump R).hasCompactSupport.comp_left (show ((0:ℝ):ℂ)=0 from Complex.ofReal_zero)

lemma smoothCutoff_lipschitz (R : ℝ) : ∃ L, LipschitzWith L (smoothCutoff R) :=
  ContDiff.lipschitzWith_of_hasCompactSupport (smoothCutoff_support R)
    (smoothCutoff_smooth R) (by simp)

lemma smoothCutoff_bound (R : ℝ) (x : ℂ) : ‖smoothCutoff R x‖ ≤ 1 := by
  simpa only [smoothCutoff,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (cutoffBump R).nonneg] using (cutoffBump R).le_one (x:=x)

lemma smoothCutoff_zero (R : ℝ) (x : ℂ) (hx : max R 0+2 < ‖x‖) : smoothCutoff R x=0 := by
  have hz := (cutoffBump R).zero_of_le_dist (x:=x) (by simpa [cutoffBump,dist_zero_right] using hx.le)
  simp only [smoothCutoff,hz,Complex.ofReal_zero]

lemma smoothCutoff_one (R : ℝ) (x : ℂ) (hx : x ∈ closedBall (0:ℂ) R) :
    smoothCutoff R =ᶠ[𝓝 x] fun _ => (1:ℂ) := by
  have hx' : x ∈ ball (0:ℂ) (cutoffBump R).rIn := by
    have hh : ‖x‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hx
    simp only [mem_ball,dist_zero_right,cutoffBump]
    linarith [le_max_left R 0]
  filter_upwards [(cutoffBump R).eventuallyEq_one_of_mem_ball hx'] with y hy
  simpa only [smoothCutoff,Pi.one_apply,Complex.ofReal_one] using congrArg (fun t : ℝ => (t:ℂ)) hy

lemma exists_smooth_cutoff (R : ℝ) :
    ∃ (χ : ℂ → ℂ) (L : ℝ≥0) (B : ℝ), 0 ≤ B ∧
      ContDiff ℝ ∞ χ ∧ LipschitzWith L χ ∧ (∀ x, ‖χ x‖ ≤ 1) ∧
      (∀ x, B < ‖x‖ → χ x=0) ∧
      (∀ x ∈ closedBall (0:ℂ) R, χ =ᶠ[𝓝 x] fun _ => (1:ℂ)) := by
  obtain ⟨L,hL⟩ := smoothCutoff_lipschitz R
  exact ⟨smoothCutoff R,L,max R 0+2,by linarith [le_max_right R 0],
    smoothCutoff_smooth R,hL,smoothCutoff_bound R,smoothCutoff_zero R,smoothCutoff_one R⟩

lemma cutoff_fderiv_eq {f χ : ℂ → ℂ} {x : ℂ} (hχ : χ =ᶠ[𝓝 x] fun _ => (1:ℂ)) :
    fderiv ℝ (fun y => χ y*f y) x=fderiv ℝ f x := by
  apply EventuallyEq.fderiv_eq
  exact hχ.mono (fun y hy => by simp only [hy,one_mul])
end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory Set Metric Filter
open scoped Topology ENNReal NNReal ContDiff

theorem weakQS_local_weakW12 (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) (R : ℝ) (v : ℂ) :
    MemLp (fun x => fderiv ℝ (f : ℂ → ℂ) x v) 2
      (volume.restrict (closedBall (0:ℂ) R)) ∧
    ∀ φ : SchwartzMap ℂ ℂ, tsupport (φ : ℂ → ℂ) ⊆ closedBall (0:ℂ) R →
      (∫ z, φ z*fderiv ℝ (f : ℂ → ℂ) z v)=
        -(∫ z, (fderiv ℝ (φ : ℂ → ℂ) z v)*f z) := by
  obtain ⟨χ,L,B,hB,hχd,hχL,hχb,hχs,hχone⟩ := exists_smooth_cutoff R
  obtain ⟨hF,C,hC,hinc⟩ := weakQS_cutoff_increment_bound f hH hf χ hχL hχb hB hχs
  have hFd : ∀ᵐ x ∂volume, DifferentiableAt ℝ (fun y => χ y*f y) x := by
    filter_upwards [weakQS_ae_differentiable f hH hf] with x hx
    exact ((hχd.differentiable (by simp)).differentiableAt).mul hx
  obtain ⟨hm,hw⟩ := CannonBeltrami.weak_fderiv_of_increment_bound hF hFd hC hinc v
  have he (x : ℂ) (hx : x ∈ closedBall (0:ℂ) R) :
      fderiv ℝ (fun y => χ y*f y) x=fderiv ℝ (f : ℂ → ℂ) x :=
    cutoff_fderiv_eq (hχone x hx)
  refine ⟨(hm.restrict (closedBall (0:ℂ) R)).ae_eq ?_,fun φ hφ => ?_⟩
  · filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with x hx
    exact congrArg (fun D : ℂ →L[ℝ] ℂ => D v) (he x hx)
  · have hleft : (fun z => φ z*fderiv ℝ (fun y => χ y*f y) z v)=
        (fun z => φ z*fderiv ℝ (f : ℂ → ℂ) z v) := by
      funext z
      by_cases hz : z ∈ closedBall (0:ℂ) R
      · rw [he z hz]
      · have hzero : φ z=0 := Function.notMem_support.mp (fun h => hz (hφ (subset_closure h)))
        simp only [hzero,zero_mul]
    have hright : (fun z => (fderiv ℝ (φ : ℂ → ℂ) z v)*(χ z*f z))=
        (fun z => (fderiv ℝ (φ : ℂ → ℂ) z v)*f z) := by
      funext z
      by_cases hz : z ∈ closedBall (0:ℂ) R
      · rw [(hχone z hz).eq_of_nhds,one_mul]
      · have hzero : fderiv ℝ (φ : ℂ → ℂ) z=0 :=
          Function.notMem_support.mp (fun h => hz (hφ (support_fderiv_subset ℝ h)))
        simp only [hzero,zero_apply,zero_mul]
    simpa only [show (fun z => φ z*fderiv ℝ (fun y => χ y*f y) z v)=
      (fun z => φ z*fderiv ℝ (f : ℂ → ℂ) z v) from hleft,hright] using hw φ
end CannonMetricQC
noncomputable section
namespace CannonMetricQC
open MeasureTheory Set Metric Filter Function ContinuousLinearMap
open scoped Topology Convolution ENNReal NNReal

lemma norm_integral_sq_le {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] {g : X → ℂ} (hg : Integrable g ν)
    (hgs : Integrable (fun x => ‖g x‖^2) ν) :
    ‖∫ x, g x ∂ν‖^2 ≤ ∫ x, ‖g x‖^2 ∂ν := by
  exact ((convexOn_norm (E:=ℂ) convex_univ).pow (fun _ _ => norm_nonneg _) 2).map_integral_le
    (continuous_norm.pow 2).continuousOn isClosed_univ (.of_forall fun _ => mem_univ _) hg hgs

theorem kernel_energy_pointwise {κ : ℂ → ℝ} (hκ : Continuous κ)
    (hc : HasCompactSupport κ) (hp : ∀ x, 0 ≤ κ x) (hi : ∫ x, κ x=1)
    {V : ℂ → ℂ} (hV : LocallyIntegrable V volume)
    (hVs : LocallyIntegrable (fun x => ‖V x‖^2) volume) (x : ℂ) :
    ENNReal.ofReal (‖(κ ⋆[lsmul ℝ ℝ,volume] V) x‖^2) ≤
      ∫⁻ y, ENNReal.ofReal (κ y)*ENNReal.ofReal (‖V (x-y)‖^2) := by
  let ν := volume.withDensity (fun y => ENNReal.ofReal (κ y))
  have hm : Measurable (fun y => ENNReal.ofReal (κ y)) := hκ.measurable.ennreal_ofReal
  have ht : ∀ᵐ y ∂volume, ENNReal.ofReal (κ y) < ∞ := .of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hv : ν univ=1 := by
    dsimp [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hκ.integrable_of_hasCompactSupport hc) (.of_forall hp),hi]
    norm_num
  let : IsProbabilityMeasure ν := ⟨hv⟩
  have hVi : Integrable (fun y => V (x-y)) ν := by
    apply (integrable_withDensity_iff_integrable_smul' hm ht).mpr
    simpa only [ENNReal.toReal_ofReal (hp _),ConvolutionExistsAt,lsmul_apply] using
      hc.convolutionExists_left (lsmul ℝ ℝ) hκ hV x
  have hVsi : Integrable (fun y => ‖V (x-y)‖^2) ν := by
    apply (integrable_withDensity_iff_integrable_smul' hm ht).mpr
    simpa only [ENNReal.toReal_ofReal (hp _),smul_eq_mul,ConvolutionExistsAt,mul_apply'] using
      hc.convolutionExists_left (mul ℝ ℝ) hκ hVs x
  have he : (∫ y, V (x-y) ∂ν)=(κ ⋆[lsmul ℝ ℝ,volume] V) x := by
    rw [integral_withDensity_eq_integral_toReal_smul hm ht]
    simp only [ENNReal.toReal_ofReal (hp _),convolution,lsmul_apply]
  have h := norm_integral_sq_le ν hVi hVsi
  rw [he] at h
  calc
    _ ≤ ENNReal.ofReal (∫ y, ‖V (x-y)‖^2 ∂ν) := ENNReal.ofReal_le_ofReal h
    _ = ∫⁻ y, ENNReal.ofReal (‖V (x-y)‖^2) ∂ν :=
      ofReal_integral_eq_lintegral_ofReal hVsi (.of_forall fun _ => sq_nonneg _)
    _ = _ := by
      rw [lintegral_withDensity_eq_lintegral_mul₀' (μ:=volume) hm.aemeasurable hVsi.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
      rfl

lemma translated_ball_energy_le (e : ℂ → ℝ≥0∞) (c y : ℂ) {R r : ℝ}
    (hy : ‖y‖ ≤ r) :
    (∫⁻ x in closedBall c R, e (x-y)) ≤ ∫⁻ z in closedBall c (R+r), e z := by
  rw [← lintegral_indicator isClosed_closedBall.measurableSet,
    ← lintegral_indicator isClosed_closedBall.measurableSet]
  calc
    _ ≤ ∫⁻ x, (closedBall c (R+r)).indicator e (x-y) := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ closedBall c R
      · have hx' : x-y ∈ closedBall c (R+r) := by
          have he : x-y-c=(x-c)-y := by abel
          have hh : ‖x-c‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm] using hx
          simp only [mem_closedBall,dist_eq_norm,he]
          exact (norm_sub_le _ _).trans (add_le_add hh hy)
        simp only [indicator_of_mem hx,indicator_of_mem hx',le_refl]
      · simp only [indicator_of_notMem hx,zero_le]
    _ = _ := lintegral_sub_right_eq_self _ y

theorem kernel_energy_local {κ : ℂ → ℝ} (hκ : Continuous κ)
    (hc : HasCompactSupport κ) (hp : ∀ x, 0 ≤ κ x) (hi : ∫ x, κ x=1)
    {V : ℂ → ℂ} (hVm : Measurable V) (hV : LocallyIntegrable V volume)
    (hVs : LocallyIntegrable (fun x => ‖V x‖^2) volume)
    {r : ℝ} (hs : ∀ y, κ y ≠ 0 → ‖y‖ ≤ r) (c : ℂ) (R : ℝ) :
    (∫⁻ x in closedBall c R, ENNReal.ofReal (‖(κ ⋆[lsmul ℝ ℝ,volume] V) x‖^2)) ≤
      ∫⁻ z in closedBall c (R+r), ENNReal.ofReal (‖V z‖^2) := by
  let e : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖V z‖^2)
  have he : Measurable e := (hVm.norm.pow_const 2).ennreal_ofReal
  have hκm : Measurable (fun y => ENNReal.ofReal (κ y)) := hκ.measurable.ennreal_ofReal
  have hm : Measurable (fun p : ℂ × ℂ => ENNReal.ofReal (κ p.2)*e (p.1-p.2)) :=
    (hκm.comp measurable_snd).mul (he.comp (measurable_fst.sub measurable_snd))
  have hi' : (∫⁻ y, ENNReal.ofReal (κ y))=1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hκ.integrable_of_hasCompactSupport hc) (.of_forall hp),hi]
    norm_num
  calc
    _ ≤ ∫⁻ x in closedBall c R, ∫⁻ y, ENNReal.ofReal (κ y)*e (x-y) :=
      lintegral_mono (kernel_energy_pointwise hκ hc hp hi hV hVs)
    _ = ∫⁻ y, ∫⁻ x in closedBall c R, ENNReal.ofReal (κ y)*e (x-y) :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ y, ENNReal.ofReal (κ y)*(∫⁻ x in closedBall c R, e (x-y)) := by
      apply lintegral_congr
      intro y
      exact lintegral_const_mul _ (he.comp (measurable_id.sub_const y))
    _ ≤ ∫⁻ y, ENNReal.ofReal (κ y)*(∫⁻ z in closedBall c (R+r), e z) := by
      apply lintegral_mono
      intro y
      by_cases hy : κ y=0
      · simp only [hy,ENNReal.ofReal_zero,zero_mul,le_refl]
      · exact mul_le_mul_right (translated_ball_energy_le e c y (hs y hy)) _
    _ = _ := by rw [lintegral_mul_const _ hκm,hi',one_mul]
end CannonMetricQC
noncomputable section
namespace CannonMetricQC
open MeasureTheory Set Metric Filter Function ContinuousLinearMap
open scoped Topology Convolution ContDiff

lemma convolution_directional {F κ : ℂ → ℂ} (hF : LocallyIntegrable F volume)
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (x v : ℂ) :
    fderiv ℝ (F ⋆[mul ℝ ℂ,volume] κ) x v=
      ∫ z, F z*fderiv ℝ κ (x-z) v := by
  let L := mul ℝ ℂ
  let D : ℂ → (ℂ →L[ℝ] ℂ) := fun z => L.precompR ℂ (F z) (fderiv ℝ κ (x-z))
  have hD : Integrable D volume :=
    (hc.fderiv ℝ).convolutionExists_right (L.precompR ℂ) hF
      ((hκ.of_le (by simp) : ContDiff ℝ 1 κ).continuous_fderiv (by simp)) x
  have hd := hc.hasFDerivAt_convolution_right L hF (hκ.of_le (by simp)) x
  rw [hd.fderiv]
  change (∫ z, D z) v=_
  rw [ContinuousLinearMap.integral_apply hD]
  rfl

lemma fderiv_reflect {κ : ℂ → ℂ} (hκ : Differentiable ℝ κ) (x z v : ℂ) :
    fderiv ℝ (fun w => κ (x-w)) z v = - fderiv ℝ κ (x-z) v := by
  have hd := (hκ (x-z)).hasFDerivAt.comp z ((hasFDerivAt_const x z).sub (hasFDerivAt_id z))
  change fderiv ℝ (κ ∘ fun w => x-w) z v=_
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,zero_sub,neg_apply,map_neg]

theorem weak_derivative_convolution {F V κ : ℂ → ℂ} (hF : LocallyIntegrable F volume)
    (v : ℂ) (hw : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*V z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z v*F z))
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (x : ℂ) :
    fderiv ℝ (F ⋆[mul ℝ ℂ,volume] κ) x v=
      (V ⋆[mul ℝ ℂ,volume] κ) x := by
  rw [convolution_directional hF hκ hc]
  let ψ : ℂ → ℂ := fun z => κ (x-z)
  have hψ : ContDiff ℝ ∞ ψ := hκ.comp (contDiff_const.sub contDiff_id)
  have hcψ : HasCompactSupport ψ :=
    hc.comp_homeomorph ((Homeomorph.neg ℂ).trans (Homeomorph.addLeft x))
  let φ := hcψ.toSchwartzMap hψ
  have hh := hw φ hcψ
  have he (z : ℂ) : fderiv ℝ (φ : ℂ → ℂ) z v= -fderiv ℝ κ (x-z) v :=
    fderiv_reflect (hκ.differentiable (by simp)) x z v
  simp only [he,neg_mul,integral_neg,neg_neg] at hh
  change (∫ z, F z*fderiv ℝ κ (x-z) v)=∫ z, V z*κ (x-z)
  have hh' : (∫ z, κ (x-z)*V z)=∫ z, fderiv ℝ κ (x-z) v*F z := hh
  simpa only [mul_comm] using hh'.symm
end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory Set Metric Filter Function ContinuousLinearMap
open scoped Topology Convolution ENNReal NNReal

lemma mollify_smooth {μ : ℂ → ℂ} (hm : LocallyIntegrable μ volume) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollify μ n) :=
  (mollifier n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    (mollifier n).contDiff_normed hm

lemma mollify_eq_complex_convolution (F : ℂ → ℂ) (n : ℕ) :
    mollify F n = F ⋆[mul ℝ ℂ,volume] (fun z => ((mollifier n).normed volume z:ℂ)) := by
  rw [← convolution_flip]
  funext x
  unfold mollify convolution
  apply integral_congr_ae
  exact .of_forall (fun z => by simp [mul_comm,lsmul_apply])

lemma mollifier_radius_tendsto : Tendsto (fun n => (mollifier n).rOut) atTop (𝓝 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2:ℝ)
  simpa [mollifier,div_eq_mul_inv] using h

lemma mollify_locally_uniform {F : ℂ → ℂ} (hF : Continuous F) :
    TendstoLocallyUniformly (mollify F) F atTop := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro x
  have ht : Tendsto (fun p : ℕ × ℂ => mollify F p.1 p.2)
      (atTop ×ˢ 𝓝 x) (𝓝 (F x)) := by
    apply ContDiffBump.convolution_tendsto_right
    · exact mollifier_radius_tendsto.comp tendsto_fst
    · exact .of_forall (fun _ => hF.aestronglyMeasurable)
    · exact (hF.tendsto x).comp tendsto_snd
    · exact tendsto_snd
  exact ((hF.tendsto x).comp tendsto_snd).prodMk_nhds ht |>.mono_right (nhds_le_uniformity (F x))

lemma plane_opNorm_le (D : ℂ →L[ℝ] ℂ) : ‖D‖ ≤ ‖D 1‖+‖D Complex.I‖ := by
  apply D.opNorm_le_bound (by positivity)
  intro z
  have he : z=z.re • (1:ℂ)+z.im • Complex.I := by
    simpa only [Complex.real_smul,Complex.ofReal_mul,mul_one] using (Complex.re_add_im z).symm
  calc
    ‖D z‖ = ‖z.re • D 1+z.im • D Complex.I‖ := by conv_lhs => rw [he,map_add,map_smul,map_smul]
    _ ≤ ‖z.re • D 1‖+‖z.im • D Complex.I‖ := norm_add_le _ _
    _ = |z.re| * ‖D 1‖+|z.im| * ‖D Complex.I‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ ‖z‖*‖D 1‖+‖z‖*‖D Complex.I‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (norm_nonneg _))
    _ = _ := by ring

lemma plane_opNorm_sq (D : ℂ →L[ℝ] ℂ) :
    ‖D‖^2 ≤ 2*(‖D 1‖^2+‖D Complex.I‖^2) := by
  have h := (sq_le_sq₀ (norm_nonneg D) (by positivity)).mpr (plane_opNorm_le D)
  nlinarith [sq_nonneg (‖D 1‖-‖D Complex.I‖)]

lemma mollify_directional {F V : ℂ → ℂ} (hF : LocallyIntegrable F volume)
    (v : ℂ) (hw : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*V z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z v*F z)) (n : ℕ) (x : ℂ) :
    fderiv ℝ (mollify F n) x v=mollify V n x := by
  rw [mollify_eq_complex_convolution,mollify_eq_complex_convolution]
  exact weak_derivative_convolution hF v hw
    (Complex.ofRealCLM.contDiff.comp (mollifier n).contDiff_normed)
    ((mollifier n).hasCompactSupport_normed.comp_left Complex.ofReal_zero) x

lemma mollify_energy_local {V : ℂ → ℂ} (hVm : Measurable V)
    (hV : LocallyIntegrable V volume) (hVs : LocallyIntegrable (fun x => ‖V x‖^2) volume)
    (n : ℕ) (c : ℂ) (R : ℝ) :
    (∫⁻ x in closedBall c R, ENNReal.ofReal (‖mollify V n x‖^2)) ≤
      ∫⁻ z in closedBall c (R+(mollifier n).rOut), ENNReal.ofReal (‖V z‖^2) := by
  apply kernel_energy_local (mollifier n).continuous_normed
    (mollifier n).hasCompactSupport_normed (mollifier n).nonneg_normed
    (mollifier n).integral_normed hVm hV hVs
  intro y hy
  have h : y ∈ Function.support ((mollifier n).normed volume) := hy
  rw [(mollifier n).support_normed_eq] at h
  exact (show ‖y‖ < (mollifier n).rOut by simpa only [mem_ball,dist_zero_right] using h).le

theorem mollify_opNorm_energy {F V W : ℂ → ℂ} (hF : Continuous F)
    (hVm : Measurable V) (hWm : Measurable W)
    (hV : LocallyIntegrable V volume) (hW : LocallyIntegrable W volume)
    (hVs : LocallyIntegrable (fun x => ‖V x‖^2) volume)
    (hWs : LocallyIntegrable (fun x => ‖W x‖^2) volume)
    (hv : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*V z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z 1*F z))
    (hw : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*W z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z Complex.I*F z))
    (n : ℕ) (c : ℂ) (R : ℝ) :
    ENNReal.ofReal (∫ x in closedBall c R, ‖fderiv ℝ (mollify F n) x‖^2) ≤
      2*(∫⁻ z in closedBall c (R+(mollifier n).rOut),
        ENNReal.ofReal (‖V z‖^2+‖W z‖^2)) := by
  have hd := (mollify_smooth hF.locallyIntegrable n).continuous_fderiv (by simp)
  have hi : IntegrableOn (fun x => ‖fderiv ℝ (mollify F n) x‖^2) (closedBall c R) volume :=
    (hd.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall c R)
  rw [ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun _ => sq_nonneg _)]
  have hMv := (mollify_smooth hV n).continuous
  have hMw := (mollify_smooth hW n).continuous
  calc
    _ ≤ ∫⁻ x in closedBall c R, 2*(ENNReal.ofReal (‖mollify V n x‖^2)+
        ENNReal.ofReal (‖mollify W n x‖^2)) := by
      apply lintegral_mono
      intro x
      have hh := plane_opNorm_sq (fderiv ℝ (mollify F n) x)
      rw [mollify_directional hF.locallyIntegrable 1 hv,
        mollify_directional hF.locallyIntegrable Complex.I hw] at hh
      simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat,
        ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)] using ENNReal.ofReal_le_ofReal hh
    _ = 2*((∫⁻ x in closedBall c R, ENNReal.ofReal (‖mollify V n x‖^2))+
        ∫⁻ x in closedBall c R, ENNReal.ofReal (‖mollify W n x‖^2)) := by
      have hme : Measurable (fun x => ENNReal.ofReal (‖mollify V n x‖^2)+
          ENNReal.ofReal (‖mollify W n x‖^2)) :=
        (hMv.norm.pow 2).measurable.ennreal_ofReal.add (hMw.norm.pow 2).measurable.ennreal_ofReal
      have hmeV : Measurable (fun x => ENNReal.ofReal (‖mollify V n x‖^2)) :=
        (hMv.norm.pow 2).measurable.ennreal_ofReal
      rw [lintegral_const_mul _ hme,lintegral_add_left hmeV]
    _ ≤ 2*((∫⁻ z in closedBall c (R+(mollifier n).rOut), ENNReal.ofReal (‖V z‖^2))+
        ∫⁻ z in closedBall c (R+(mollifier n).rOut), ENNReal.ofReal (‖W z‖^2)) :=
      mul_le_mul_right (add_le_add (mollify_energy_local hVm hV hVs n c R)
        (mollify_energy_local hWm hW hWs n c R)) 2
    _ = _ := by
      simp only [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      rw [lintegral_add_left (hVm.norm.pow_const 2).ennreal_ofReal]
end CannonMetricQC

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
-- module Solutions.OAIQ046_CN.Cannon_Conformal_OpenMapMaxSphere
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
section
section
section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
noncomputable section
noncomputable section
noncomputable section
open Set Metric MeasureTheory Filter Complex
open scoped Topology

namespace CannonPlane

lemma openMap_exists_max_on_sphere {u : ℂ → ℝ} (hu : Continuous u)
    (ho : IsOpenMap u) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ z ∈ sphere c r, ∀ x ∈ closedBall c r, u x ≤ u z := by
  obtain ⟨z,hz,hmax⟩ := (isCompact_closedBall c r).exists_isMaxOn
    ⟨c,mem_closedBall_self hr.le⟩ hu.continuousOn
  refine ⟨z,?_,hmax⟩
  have hzle : dist z c ≤ r := hz
  apply mem_sphere.mpr
  by_contra he
  have hzlt : dist z c < r := lt_of_le_of_ne hzle he
  have hop : IsOpen (u '' ball c r) := ho _ isOpen_ball
  obtain ⟨ε,hε,hsub⟩ := Metric.isOpen_iff.mp hop (u z) ⟨z,hzlt,rfl⟩
  have hmem : u z+ε/2 ∈ ball (u z) ε := by
    rw [mem_ball,Real.dist_eq]
    have ha : |u z+ε/2-u z|=ε/2 := by rw [add_sub_cancel_left,abs_of_pos (by linarith)]
    rw [ha]; linarith
  obtain ⟨w,hw,hew⟩ := hsub hmem
  have hh : u w ≤ u z := hmax (ball_subset_closedBall hw)
  rw [hew] at hh
  linarith

lemma openMap_exists_min_on_sphere {u : ℂ → ℝ} (hu : Continuous u)
    (ho : IsOpenMap u) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ z ∈ sphere c r, ∀ x ∈ closedBall c r, u z ≤ u x := by
  obtain ⟨z,hz,hh⟩ := openMap_exists_max_on_sphere hu.neg
    ((Homeomorph.neg ℝ).isOpenMap.comp ho) c hr
  exact ⟨z,hz,fun x hx => neg_le_neg_iff.mp (hh x hx)⟩

lemma homeomorph_disk_oscillation (F : ℂ ≃ₜ ℂ) (c : ℂ) {r L : ℝ}
    (hr : 0 < r) (hb : ∀ x ∈ sphere c r, ∀ y ∈ sphere c r, dist (F x) (F y) ≤ L) :
    ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r, dist (F x) (F y) ≤ 2*L := by
  obtain ⟨a,ha,hamax⟩ := openMap_exists_max_on_sphere (continuous_re.comp F.continuous)
    (isOpenMap_re.comp F.isOpenMap) c hr
  obtain ⟨b,hb',hbmin⟩ := openMap_exists_min_on_sphere (continuous_re.comp F.continuous)
    (isOpenMap_re.comp F.isOpenMap) c hr
  obtain ⟨d,hd,hdmax⟩ := openMap_exists_max_on_sphere (continuous_im.comp F.continuous)
    (isOpenMap_im.comp F.isOpenMap) c hr
  obtain ⟨e,he,hemin⟩ := openMap_exists_min_on_sphere (continuous_im.comp F.continuous)
    (isOpenMap_im.comp F.isOpenMap) c hr
  intro x hx y hy
  have hre : |(F x-F y).re| ≤ L := by
    have hv := (abs_re_le_norm (F a-F b)).trans (show ‖F a-F b‖ ≤ L by simpa only [dist_eq_norm] using hb a ha b hb')
    rw [abs_le] at hv ⊢
    simp only [sub_re] at hv ⊢
    have h1 := hamax x hx
    have h2 := hamax y hy
    have h3 := hbmin x hx
    have h4 := hbmin y hy
    dsimp only [Function.comp_def] at h1 h2 h3 h4
    constructor <;> linarith [hv.2]
  have him : |(F x-F y).im| ≤ L := by
    have hv := (abs_im_le_norm (F d-F e)).trans (show ‖F d-F e‖ ≤ L by simpa only [dist_eq_norm] using hb d hd e he)
    rw [abs_le] at hv ⊢
    simp only [sub_im] at hv ⊢
    have h1 := hdmax x hx
    have h2 := hdmax y hy
    have h3 := hemin x hx
    have h4 := hemin y hy
    dsimp only [Function.comp_def] at h1 h2 h3 h4
    constructor <;> linarith [hv.2]
  rw [dist_eq_norm]
  linarith [norm_le_abs_re_add_abs_im (F x-F y)]

lemma integral_sq_cauchy {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b) :
    (∫ t in a..b, f t)^2 ≤ (b-a)*(∫ t in a..b, (f t)^2) := by
  let aa := ∫ t in a..b, f t
  let bb := ∫ t in a..b, (f t)^2
  let m := aa/(b-a)
  have hfi := hf.intervalIntegrable (μ := volume) a b
  have hf2 : IntervalIntegrable (fun t => (f t)^2) volume a b :=
    (hf.pow 2).intervalIntegrable a b
  have he : (∫ t in a..b, (f t-m)^2)=bb-2*m*aa+m^2*(b-a) := by
    calc
      _ = ∫ t in a..b, ((f t)^2-2*m*f t+m^2) :=
        intervalIntegral.integral_congr fun _ _ => by ring
      _ = bb-2*m*aa+m^2*(b-a) := by
        rw [intervalIntegral.integral_add (hf2.sub (hfi.const_mul _)) intervalIntegrable_const,
          intervalIntegral.integral_sub hf2 (hfi.const_mul _),intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        simp only [smul_eq_mul,aa,bb]
        ring
  have hp : 0 ≤ ∫ t in a..b, (f t-m)^2 :=
    intervalIntegral.integral_nonneg hab.le (fun _ _ => sq_nonneg _)
  rw [he] at hp
  have ht : 0 < b-a := sub_pos.mpr hab
  have hid : (b-a)*(bb-2*m*aa+m^2*(b-a))=(b-a)*bb-aa^2 := by
    dsimp only [m]
    field_simp
    ring
  have h := mul_nonneg ht.le hp
  rw [hid] at h
  dsimp only [aa,bb] at h
  linarith

lemma circle_derivative_bound {F : ℂ → ℂ} (hf : ContDiff ℝ 1 F) (c : ℂ)
    {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖deriv (fun t => F (circleMap c r t)) θ‖ ≤ r*‖fderiv ℝ F (circleMap c r θ)‖ := by
  have hd := (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt θ
    (hasDerivAt_circleMap c r θ)
  change ‖deriv (F ∘ circleMap c r) θ‖ ≤ _
  rw [hd.deriv]
  apply le_trans (ContinuousLinearMap.le_opNorm _ _)
  rw [norm_mul,norm_circleMap_zero,Complex.norm_I,abs_of_nonneg hr,mul_one,mul_comm]

lemma circle_oscillation_bound {F : ℂ → ℂ} (hf : ContDiff ℝ 1 F) (c : ℂ)
    {r : ℝ} (hr : 0 < r) :
    ∀ x ∈ sphere c r, ∀ y ∈ sphere c r,
      dist (F x) (F y) ≤ r*(∫ t in (-Real.pi)..Real.pi, ‖fderiv ℝ F (circleMap c r t)‖) := by
  let g : ℝ → ℝ := fun t => r*‖fderiv ℝ F (circleMap c r t)‖
  have hg : Continuous g := continuous_const.mul
    ((hf.continuous_fderiv (by simp)).comp (continuous_circleMap c r)).norm
  have hcircle : circleMap c r '' Ioc (-Real.pi) Real.pi=sphere c r := by
    have h := (periodic_circleMap c r).image_Ioc Real.two_pi_pos (-Real.pi)
    rw [range_circleMap,abs_of_pos hr] at h
    convert h using 2; ring_nf
  intro x hx y hy
  rw [← hcircle] at hx hy
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  have hbound (a b : ℝ) (ha : a ∈ Ioc (-Real.pi) Real.pi)
      (hb : b ∈ Ioc (-Real.pi) Real.pi) (hab : a ≤ b) :
      ‖F (circleMap c r b)-F (circleMap c r a)‖ ≤ ∫ t in (-Real.pi)..Real.pi, g t := by
    apply (norm_sub_le_integral_of_norm_deriv_le_of_le hab
      (hf.continuous.comp (continuous_circleMap c r)).continuousOn
      ((hf.differentiable (by simp)).comp (differentiable_circleMap c r)).differentiableOn
      (.of_forall fun t _ => circle_derivative_bound hf c hr.le t) (hg.intervalIntegrable a b)).trans
    exact intervalIntegral.integral_mono_interval ha.1.le hab hb.2
      (.of_forall fun t => mul_nonneg hr.le (norm_nonneg _))
      (hg.intervalIntegrable _ _)
  rw [← intervalIntegral.integral_const_mul]
  change dist (F (circleMap c r a)) (F (circleMap c r b)) ≤ ∫ t in (-Real.pi)..Real.pi, g t
  rcases le_total a b with hab | hba
  · rw [dist_eq_norm, norm_sub_rev]; exact hbound a b ha hb hab
  · rw [dist_eq_norm]; exact hbound b a hb ha hba

lemma polar_circle (p : ℝ × ℝ) : Complex.polarCoord.symm p=circleMap 0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply,circleMap_zero,Complex.exp_mul_I,Complex.ofReal_cos,Complex.ofReal_sin]

lemma continuous_polar_circle : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
  simp only [circleMap]
  fun_prop

lemma disk_polar_integral_zero {g : ℂ → ℝ} (hg : Continuous g) {R : ℝ} (hR : 0 ≤ R) :
    (∫ z in closedBall (0 : ℂ) R, g z) =
      ∫ r in (0 : ℝ)..R, r*(∫ t in (-Real.pi)..Real.pi, g (circleMap 0 r t)) := by
  let A : Set (ℝ × ℝ) := Ioc 0 R ×ˢ Ioo (-Real.pi) Real.pi
  let T : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi
  let q : ℝ × ℝ → ℝ := fun p => p.1*g (circleMap 0 p.1 p.2)
  have hA : MeasurableSet A := measurableSet_Ioc.prod measurableSet_Ioo
  have hT : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Ioo
  have hq : Continuous q := continuous_fst.mul (hg.comp continuous_polar_circle)
  have hi : IntegrableOn q A :=
    (hq.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self)
  have hid (p : ℝ × ℝ) : T.indicator
      (fun p => p.1*(closedBall (0 : ℂ) R).indicator g (Complex.polarCoord.symm p)) p =
      A.indicator q p := by
    by_cases ht : p ∈ T
    · rw [Set.indicator_of_mem ht]
      have hr : 0 < p.1 := ht.1
      have hc : Complex.polarCoord.symm p ∈ closedBall (0 : ℂ) R ↔ p.1 ≤ R := by
        simp only [mem_closedBall,dist_zero_right,Complex.norm_polarCoord_symm,abs_of_pos hr]
      by_cases hle : p.1 ≤ R
      · rw [Set.indicator_of_mem (hc.mpr hle),Set.indicator_of_mem (show p ∈ A from ⟨⟨hr,hle⟩,ht.2⟩)]
        simp only [q,polar_circle]
      · rw [Set.indicator_of_notMem (not_iff_not.mpr hc |>.mpr hle),
          Set.indicator_of_notMem (show p ∉ A from fun hp => hle hp.1.2),mul_zero]
    · rw [Set.indicator_of_notMem ht,Set.indicator_of_notMem
        (show p ∉ A from fun hp => ht ⟨hp.1.1,hp.2⟩)]
  calc
    _ = ∫ z, (closedBall (0 : ℂ) R).indicator g z := (integral_indicator measurableSet_closedBall).symm
    _ = ∫ p in T, p.1*(closedBall (0 : ℂ) R).indicator g (Complex.polarCoord.symm p) := by
      simpa only [T,smul_eq_mul,_root_.polarCoord] using
        (Complex.integral_comp_polarCoord_symm ((closedBall (0 : ℂ) R).indicator g)).symm
    _ = ∫ p, A.indicator q p := by rw [← integral_indicator hT]; exact integral_congr_ae (.of_forall hid)
    _ = ∫ p in A, q p := integral_indicator hA
    _ = ∫ r in Ioc (0 : ℝ) R, ∫ t in Ioo (-Real.pi) Real.pi, r*g (circleMap 0 r t) := by
      rw [Measure.volume_eq_prod] at hi ⊢
      exact setIntegral_prod q hi
    _ = ∫ r in (0 : ℝ)..R, r*(∫ t in (-Real.pi)..Real.pi, g (circleMap 0 r t)) := by
      rw [intervalIntegral.integral_of_le hR]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r hr
      dsimp only
      rw [integral_const_mul,← integral_Ioc_eq_integral_Ioo,
        intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le)]

lemma translated_disk_integral (g : ℂ → ℝ) (c : ℂ) (R : ℝ) :
    (∫ z in closedBall (0 : ℂ) R, g (c+z)) = ∫ z in closedBall c R, g z := by
  rw [← integral_indicator measurableSet_closedBall,← integral_indicator measurableSet_closedBall]
  calc
    _ = ∫ z, (closedBall c R).indicator g (c+z) := by
      apply integral_congr_ae
      filter_upwards [] with z
      have he : c+z ∈ closedBall c R ↔ z ∈ closedBall (0 : ℂ) R := by
        simp only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero]
      by_cases hz : z ∈ closedBall (0 : ℂ) R
      · rw [Set.indicator_of_mem hz,Set.indicator_of_mem (he.mpr hz)]
      · rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem (not_iff_not.mpr he |>.mpr hz)]
    _ = _ := integral_add_left_eq_self _ c

lemma disk_polar_integral {g : ℂ → ℝ} (hg : Continuous g) (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ z in closedBall c R, g z) =
      ∫ r in (0 : ℝ)..R, r*(∫ t in (-Real.pi)..Real.pi, g (circleMap c r t)) := by
  rw [← translated_disk_integral g c R]
  have hc : Continuous (fun z : ℂ => g (c+z)) := hg.comp (continuous_const.add continuous_id)
  simpa only [circleMap,zero_add] using disk_polar_integral_zero hc hR

lemma continuous_circle_integral {g : ℂ → ℝ} (hg : Continuous g) (c : ℂ) :
    Continuous (fun r : ℝ => ∫ t in (-Real.pi)..Real.pi, g (circleMap c r t)) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous _ continuous_const
  exact hg.comp (by simp only [circleMap]; fun_prop)

lemma approximate_circle_energy (F : ℂ ≃ₜ ℂ) {g : ℂ → ℂ}
    (hg : ContDiff ℝ 1 g) (c : ℂ) {r : ℝ} (hr : 0 < r)
    (x y : ℂ) (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r)
    (happ : ∀ z ∈ sphere c r, dist (F z) (g z) ≤ dist (F x) (F y)/8) :
    dist (F x) (F y)^2 ≤ 32*Real.pi*r^2*
      (∫ t in (-Real.pi)..Real.pi, ‖fderiv ℝ g (circleMap c r t)‖^2) := by
  let I := ∫ t in (-Real.pi)..Real.pi, ‖fderiv ℝ g (circleMap c r t)‖
  have hb : ∀ a ∈ sphere c r, ∀ b ∈ sphere c r,
      dist (F a) (F b) ≤ r*I+dist (F x) (F y)/4 := by
    intro a ha b hb
    have ho := circle_oscillation_bound hg c hr a ha b hb
    have ht := dist_triangle4 (F a) (g a) (g b) (F b)
    have ha' := happ a ha
    have hb' := happ b hb
    rw [dist_comm (g b) (F b)] at ht
    dsimp only [I] at *
    linarith
  have hosc := homeomorph_disk_oscillation F c hr hb x hx y hy
  have hc : Continuous (fun t => ‖fderiv ℝ g (circleMap c r t)‖) :=
    ((hg.continuous_fderiv (by simp)).comp (continuous_circleMap c r)).norm
  have hcs := integral_sq_cauchy hc (neg_lt_self Real.pi_pos)
  have hn : 0 ≤ I := intervalIntegral.integral_nonneg
    (neg_le_self Real.pi_pos.le) (fun _ _ => norm_nonneg _)
  have hd : dist (F x) (F y) ≤ 4*(r*I) := by linarith
  have hs : dist (F x) (F y)^2 ≤ (4*(r*I))^2 :=
    (sq_le_sq₀ dist_nonneg (by positivity)).mpr hd
  have hm := mul_le_mul_of_nonneg_left hcs (show 0 ≤ 16*r^2 by positivity)
  dsimp only [I] at hs
  nlinarith

lemma approximate_log_energy (F : ℂ ≃ₜ ℂ) {g : ℂ → ℂ}
    (hg : ContDiff ℝ 1 g) (c : ℂ) {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (x y : ℂ) (hx : x ∈ closedBall c s) (hy : y ∈ closedBall c s)
    (happ : ∀ z ∈ closedBall c R, dist (F z) (g z) ≤ dist (F x) (F y)/8) :
      dist (F x) (F y)^2*Real.log (R/s) ≤
        32*Real.pi*(∫ z in closedBall c R, ‖fderiv ℝ g z‖^2) := by
  let e : ℝ → ℝ := fun r => r*(∫ t in (-Real.pi)..Real.pi, ‖fderiv ℝ g (circleMap c r t)‖^2)
  have hg' : Continuous (fun z => ‖fderiv ℝ g z‖^2) := (hg.continuous_fderiv (by simp)).norm.pow 2
  have he : Continuous e := continuous_id.mul (continuous_circle_integral hg' c)
  have hi : IntervalIntegrable (fun r => dist (F x) (F y)^2/r) volume s R := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div continuousOn_id
    intro r hr
    rw [uIcc_of_le hsR] at hr
    exact ne_of_gt (hs.trans_le hr.1)
  have hb : (∫ r in s..R, dist (F x) (F y)^2/r) ≤ ∫ r in s..R, 32*Real.pi*e r := by
    apply intervalIntegral.integral_mono_on hsR hi (he.const_mul _ |>.intervalIntegrable s R)
    intro r hr
    have hrp := hs.trans_le hr.1
    have h := approximate_circle_energy F hg c hrp x y
      (closedBall_subset_closedBall hr.1 hx) (closedBall_subset_closedBall hr.1 hy)
      (fun z hz => happ z (closedBall_subset_closedBall hr.2 (sphere_subset_closedBall hz)))
    apply (div_le_iff₀ hrp).mpr
    dsimp only [e]
    nlinarith
  have hm : (∫ r in s..R, e r) ≤ ∫ r in (0 : ℝ)..R, e r := by
    apply intervalIntegral.integral_mono_interval hs.le hsR le_rfl _ (he.intervalIntegrable _ _)
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro r hr
    exact mul_nonneg hr.1.le (intervalIntegral.integral_nonneg (neg_le_self Real.pi_pos.le)
      (fun _ _ => sq_nonneg _))
  rw [show (∫ r in s..R, dist (F x) (F y)^2/r)=dist (F x) (F y)^2*Real.log (R/s) by
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul,integral_inv_of_pos hs (hs.trans_le hsR)]
    simp only [div_eq_mul_inv]] at hb
  rw [intervalIntegral.integral_const_mul] at hb
  apply hb.trans
  rw [disk_polar_integral hg' c (hs.le.trans hsR)]
  exact mul_le_mul_of_nonneg_left hm (by positivity)
end CannonPlane

namespace CannonMetricQC
open MeasureTheory Set Metric Filter Function ContinuousLinearMap
open scoped Topology Convolution ENNReal NNReal

theorem weak_homeomorph_log_energy (F : ℂ ≃ₜ ℂ) {V W : ℂ → ℂ}
    (hVm : Measurable V) (hWm : Measurable W)
    (hV : LocallyIntegrable V volume) (hW : LocallyIntegrable W volume)
    (hVs : LocallyIntegrable (fun x => ‖V x‖^2) volume)
    (hWs : LocallyIntegrable (fun x => ‖W x‖^2) volume)
    (hv : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*V z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z 1*F z))
    (hw : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*W z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z Complex.I*F z))
    (c : ℂ) {s R T : ℝ} (hs : 0 < s) (hsR : s ≤ R) (hRT : R < T)
    (x y : ℂ) (hx : x ∈ closedBall c s) (hy : y ∈ closedBall c s) :
    ENNReal.ofReal (dist (F x) (F y)^2*Real.log (R/s)) ≤
      ENNReal.ofReal (64*Real.pi)*(∫⁻ z in closedBall c T,
        ENNReal.ofReal (‖V z‖^2+‖W z‖^2)) := by
  by_cases he : F x=F y
  · simp [he]
  have hd : 0 < dist (F x) (F y)/8 := div_pos (dist_pos.mpr he) (by norm_num)
  have htu := tendstoLocallyUniformly_iff_forall_isCompact.mp
    (mollify_locally_uniform F.continuous) _ (isCompact_closedBall c R)
  have hu := Metric.tendstoUniformlyOn_iff.mp htu _ hd
  have hr := mollifier_radius_tendsto.eventually (gt_mem_nhds (sub_pos.mpr hRT))
  obtain ⟨n,hn,hnr⟩ := (hu.and hr).exists
  have hl := CannonPlane.approximate_log_energy F
    ((mollify_smooth F.continuous.locallyIntegrable n).of_le (by simp)) c hs hsR x y hx hy
    (fun z hz => (hn z hz).le)
  have hE := mollify_opNorm_energy F.continuous hVm hWm hV hW hVs hWs hv hw n c R
  have hm : (∫⁻ z in closedBall c (R+(mollifier n).rOut),
      ENNReal.ofReal (‖V z‖^2+‖W z‖^2)) ≤
      ∫⁻ z in closedBall c T, ENNReal.ofReal (‖V z‖^2+‖W z‖^2) :=
    lintegral_mono_set (closedBall_subset_closedBall (by linarith))
  calc
    _ ≤ ENNReal.ofReal (32*Real.pi)*
        ENNReal.ofReal (∫ z in closedBall c R, ‖fderiv ℝ (mollify F n) z‖^2) := by
      simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ 32*Real.pi)] using
        ENNReal.ofReal_le_ofReal hl
    _ ≤ ENNReal.ofReal (32*Real.pi)*(2*(∫⁻ z in closedBall c T,
        ENNReal.ofReal (‖V z‖^2+‖W z‖^2))) :=
      mul_le_mul_right (hE.trans (mul_le_mul_right hm 2)) _
    _ = _ := by
      rw [← mul_assoc,← show ENNReal.ofReal (32*Real.pi*2)=ENNReal.ofReal (32*Real.pi)*2 by
        rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_ofNat]]
      congr 2; ring
end CannonMetricQC
noncomputable section
namespace CannonMetricQC
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

lemma WeakQS.two {f : ℂ → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : WeakQS f H)
    (x y z : ℂ) (h : dist x y ≤ 2*dist x z) :
    dist (f x) (f y) ≤ H*(H+1)*dist (f x) (f z) := by
  let u := midpoint ℝ x y
  have hxu : dist x u=dist x y/2 := by simp [u,dist_left_midpoint,div_eq_mul_inv,mul_comm]
  have hux : dist u x=dist x y/2 := by rw [dist_comm,hxu]
  have huy : dist u y=dist x y/2 := by simp [u,dist_midpoint_right,div_eq_mul_inv,mul_comm]
  have h1 := hf x u z (show dist x u ≤ dist x z by rw [hxu]; linarith)
  have h2 := hf u y x (by rw [huy,hux])
  rw [dist_comm (f u) (f x)] at h2
  have h3 := dist_triangle (f x) (f u) (f y)
  have h4 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ H+1 by positivity)
  nlinarith

lemma WeakQS.four {f : ℂ → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : WeakQS f H)
    (x y z : ℂ) (h : dist x y ≤ 4*dist x z) :
    dist (f x) (f y) ≤ (H*(H+1))^2*dist (f x) (f z) := by
  let u := midpoint ℝ x y
  have hxu : dist x u=dist x y/2 := by simp [u,dist_left_midpoint,div_eq_mul_inv,mul_comm]
  have h1 := hf.two hH x y u (by rw [hxu]; linarith)
  have h2 := hf.two hH x u z (by rw [hxu]; linarith)
  exact h1.trans (by nlinarith [mul_le_mul_of_nonneg_left h2 (show 0 ≤ H*(H+1) by positivity)])

theorem imageArea_upper_four (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) (x y : ℂ) {R : ℝ} (hR : R ≤ 4*dist x y) :
    imageArea f (closedBall x R) ≤ ENNReal.ofReal (Real.pi*(H*(H+1))^4)*
      ENNReal.ofReal (dist (f x) (f y)^2) := by
  have hsub : f '' closedBall x R ⊆ closedBall (f x) ((H*(H+1))^2*dist (f x) (f y)) := by
    rintro w ⟨z,hz,rfl⟩
    rw [mem_closedBall,dist_comm]
    apply hf.four hH.le
    exact (show dist x z ≤ R by simpa only [mem_closedBall,dist_comm] using hz).trans hR
  rw [imageArea_apply f isClosed_closedBall.measurableSet]
  apply (measure_mono (μ:=volume) hsub).trans
  rw [Complex.volume_closedBall]
  have hpi : (NNReal.pi : ℝ≥0∞)=ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi,ENNReal.ofReal_coe_nnreal]
  rw [hpi,← ENNReal.ofReal_pow (by positivity),← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith
end CannonMetricQC
noncomputable section
open MeasureTheory Set Metric Filter
open scoped Topology ENNReal

namespace CannonMetricQC

theorem measure_le_of_closedBall_le (μ ν : Measure ℂ) [IsLocallyFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν]
    (h : ∀ x r, 0 < r → μ (closedBall x r) ≤ ν (closedBall x r)) : μ ≤ ν := by
  apply Measure.le_iff.mpr
  intro s _
  apply (Besicovitch.vitaliFamily μ).measure_le_of_frequently_le ν
    Measure.AbsolutelyContinuous.rfl s
  intro x _
  apply (Besicovitch.tendsto_filterAt μ x).frequently
  apply Filter.Eventually.frequently
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact h x r hr

lemma locallyIntegrable_density_locallyFinite {e : ℂ → ℝ}
    (he : LocallyIntegrable e volume) (hp : ∀ x, 0 ≤ e x) :
    IsLocallyFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (e x))) where
  finiteAtNhds x := by
    refine ⟨closedBall x 1,closedBall_mem_nhds x (by norm_num),?_⟩
    rw [withDensity_apply _ isClosed_closedBall.measurableSet,
      ← ofReal_integral_eq_lintegral_ofReal (he.integrableOn_isCompact (isCompact_closedBall x 1))
        (.of_forall hp)]
    exact ENNReal.ofReal_lt_top
end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory Set Metric Filter Function ContinuousLinearMap
open scoped Topology Convolution ENNReal NNReal

theorem weakQS_imageArea_le_energy (F : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hF : WeakQS F H) {V W : ℂ → ℂ}
    (hVm : Measurable V) (hWm : Measurable W)
    (hV : LocallyIntegrable V volume) (hW : LocallyIntegrable W volume)
    (hVs : LocallyIntegrable (fun x => ‖V x‖^2) volume)
    (hWs : LocallyIntegrable (fun x => ‖W x‖^2) volume)
    (hv : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*V z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z 1*F z))
    (hw : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*W z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z Complex.I*F z)) :
    imageArea F ≤ (Real.toNNReal (Real.pi*(H*(H+1))^4*(64*Real.pi/Real.log 2))) •
      volume.withDensity (fun z => ENNReal.ofReal (‖V z‖^2+‖W z‖^2)) := by
  let ν := volume.withDensity (fun z => ENNReal.ofReal (‖V z‖^2+‖W z‖^2))
  let : IsLocallyFiniteMeasure ν := locallyIntegrable_density_locallyFinite
    (hVs.add hWs) (fun z => add_nonneg (sq_nonneg _) (sq_nonneg _))
  apply measure_le_of_closedBall_le
  intro c R hR
  let y : ℂ := c+(R/4:ℝ)
  have hcy : dist c y=R/4 := by
    dsimp [y]
    rw [dist_eq_norm]
    have he : c-(c+(R/4:ℝ))=(-(R/4:ℝ):ℂ) := by push_cast; ring
    rw [he,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
  have hy : y ∈ closedBall c (R/4) := by rw [mem_closedBall,dist_comm,hcy]
  have hl := weak_homeomorph_log_energy F hVm hWm hV hW hVs hWs hv hw c
    (by positivity : 0 < R/4) (by linarith : R/4 ≤ R/2) (by linarith : R/2 < R)
    c y (mem_closedBall_self (by positivity)) hy
  have heq : R/2/(R/4)=(2:ℝ) := by field_simp; ring
  rw [heq,ENNReal.ofReal_mul (sq_nonneg _)] at hl
  have hp : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hp0 : ENNReal.ofReal (Real.log (2:ℝ)) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hle := (ENNReal.le_div_iff_mul_le (Or.inl hp0) (Or.inl ENNReal.ofReal_ne_top)).mpr hl
  have hbound : ENNReal.ofReal (dist (F c) (F y)^2) ≤
      ENNReal.ofReal (64*Real.pi/Real.log 2)*ν (closedBall c R) := by
    dsimp [ν]
    rw [withDensity_apply _ isClosed_closedBall.measurableSet,ENNReal.ofReal_div_of_pos hp]
    simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hle
  have ha := imageArea_upper_four F hH hF c y (show R ≤ 4*dist c y by rw [hcy]; linarith)
  change imageArea F (closedBall c R) ≤
    ENNReal.ofReal (Real.pi*(H*(H+1))^4*(64*Real.pi/Real.log 2))*ν (closedBall c R)
  calc
    _ ≤ ENNReal.ofReal (Real.pi*(H*(H+1))^4)*ENNReal.ofReal (dist (F c) (F y)^2) := ha
    _ ≤ ENNReal.ofReal (Real.pi*(H*(H+1))^4)*
        (ENNReal.ofReal (64*Real.pi/Real.log 2)*ν (closedBall c R)) :=
      mul_le_mul_right hbound _
    _ = _ := by rw [ENNReal.ofReal_mul (show 0 ≤ Real.pi*(H*(H+1))^4 by positivity),mul_assoc]

theorem weakQS_weakW12_imageArea_ac (F : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hF : WeakQS F H) {V W : ℂ → ℂ}
    (hVm : Measurable V) (hWm : Measurable W)
    (hV : LocallyIntegrable V volume) (hW : LocallyIntegrable W volume)
    (hVs : LocallyIntegrable (fun x => ‖V x‖^2) volume)
    (hWs : LocallyIntegrable (fun x => ‖W x‖^2) volume)
    (hv : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*V z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z 1*F z))
    (hw : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*W z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z Complex.I*F z)) :
    imageArea F ≪ volume := by
  exact (Measure.absolutelyContinuous_of_le
    (weakQS_imageArea_le_energy F hH hF hVm hWm hV hW hVs hWs hv hw)).trans
      (Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _))
end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory Set Metric Filter
open scoped Topology ENNReal NNReal

lemma weakQS_full_weakW12 (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H) (hf : WeakQS f H) (v : ℂ) :
    LocallyIntegrable (fun x => fderiv ℝ (f : ℂ → ℂ) x v) volume ∧
    LocallyIntegrable (fun x => ‖fderiv ℝ (f : ℂ → ℂ) x v‖^2) volume ∧
    ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*fderiv ℝ (f : ℂ → ℂ) z v)=
        -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z v*f z) := by
  have hp (K : Set ℂ) (hK : IsCompact K) :
      IntegrableOn (fun x => fderiv ℝ (f : ℂ → ℂ) x v) K volume ∧
      IntegrableOn (fun x => ‖fderiv ℝ (f : ℂ → ℂ) x v‖^2) K volume := by
    obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_closedBall (0:ℂ)).mp hK.isBounded
    have hm := (weakQS_local_weakW12 f hH hf R v).1
    let : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) R)) :=
      ⟨by simpa using (isCompact_closedBall (0 : ℂ) R).measure_lt_top (μ := volume)⟩
    have hv : IntegrableOn (fun x => fderiv ℝ (f : ℂ → ℂ) x v)
        (closedBall (0 : ℂ) R) volume := MemLp.integrable (by norm_num) hm
    have hs : IntegrableOn (fun x => ‖fderiv ℝ (f : ℂ → ℂ) x v‖^2)
        (closedBall (0 : ℂ) R) volume :=
      (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
    exact ⟨hv.mono_set hR, hs.mono_set hR⟩
  refine ⟨locallyIntegrable_iff.mpr (fun K hK => (hp K hK).1),
    locallyIntegrable_iff.mpr (fun K hK => (hp K hK).2),?_⟩
  intro φ hφ
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_closedBall (0:ℂ)).mp hφ.isBounded
  exact (weakQS_local_weakW12 f hH hf R v).2 φ hR

theorem weakQS_imageArea_ac (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H) (hf : WeakQS f H) :
    imageArea f ≪ volume := by
  obtain ⟨hV,hVs,hv⟩ := weakQS_full_weakW12 f hH hf 1
  obtain ⟨hW,hWs,hw⟩ := weakQS_full_weakW12 f hH hf Complex.I
  exact weakQS_weakW12_imageArea_ac f hH hf
    (measurable_fderiv_apply_const ℝ (f : ℂ → ℂ) 1)
    (measurable_fderiv_apply_const ℝ (f : ℂ → ℂ) Complex.I) hV hW hVs hWs hv hw

end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory Filter
open scoped Topology

theorem weakQS_quasiMeasurePreserving (f : ℂ ≃ₜ ℂ) {H : ℝ}
    (hH : 0 < H) (hf : WeakQS f.symm H) :
    Measure.QuasiMeasurePreserving (f : ℂ → ℂ) volume volume := by
  refine ⟨f.continuous.measurable,?_⟩
  simpa only [imageArea,Homeomorph.symm_symm] using weakQS_imageArea_ac f.symm hH hf

theorem weakQS_ae_bijective_fderiv (f : ℂ ≃ₜ ℂ) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hf : WeakQS f H) (hi : WeakQS f.symm J) :
    ∀ᵐ x : ℂ, Function.Bijective (fderiv ℝ (f : ℂ → ℂ) x) := by
  have hm := weakQS_quasiMeasurePreserving f hJ hi
  filter_upwards [weakQS_ae_differentiable f hH hf,
    hm.ae (weakQS_ae_differentiable f.symm hJ hi)] with x hx hy
  have hc := hy.hasFDerivAt.comp x hx.hasFDerivAt
  have hid : (f.symm : ℂ → ℂ) ∘ (f : ℂ → ℂ)=id := by funext z; simp
  rw [hid] at hc
  have hh := hc.unique (hasFDerivAt_id x)
  have hl : Function.LeftInverse (fderiv ℝ (f.symm : ℂ → ℂ) (f x))
      (fderiv ℝ (f : ℂ → ℂ) x) := by
    intro z
    exact congrArg (fun A : ℂ →L[ℝ] ℂ => A z) hh
  exact ⟨hl.injective,LinearMap.injective_iff_surjective.mp hl.injective⟩

end CannonMetricQC

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
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_SphereMeasure
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
section
section
noncomputable section

noncomputable section
namespace CannonConformal
open Set Topology Metric

lemma determinant_nonneg_of_evaluate {p : Form} (hp : ∀ x y, 0 ≤ evaluate p x y) :
    0 ≤ determinant p := by
  have ha : 0 ≤ p 0 := by simpa [evaluate] using hp 1 0
  have hc : 0 ≤ p 2 := by simpa [evaluate] using hp 0 1
  by_cases hz : p 0=0
  · have h := hp (-(p 2+1)) (p 1)
    have hb : p 1=0 := by
      simp only [evaluate,hz,zero_mul,zero_add] at h
      nlinarith [sq_nonneg (p 1),mul_nonneg hc (sq_nonneg (p 1))]
    simp [determinant,hz,hb]
  · have h := hp (p 1) (-(p 0))
    have ha' : 0 < p 0 := lt_of_le_of_ne ha (Ne.symm hz)
    have hid : evaluate p (p 1) (-p 0)=p 0*determinant p := by
      simp [evaluate,determinant]; ring
    rw [hid] at h
    exact nonneg_of_mul_nonneg_right h ha'

lemma determinant_ge_sq_lower {ε : ℝ} (hε : 0 ≤ ε) {q : Form}
    (hl : LowerBound ε q) : ε^2 ≤ determinant q := by
  let p : Form := ![q 0-ε,q 1,q 2-ε]
  have he (x y : ℝ) : evaluate p x y=evaluate q x y-ε*(x^2+y^2) := by
    simp [p,evaluate]; ring
  have hp := determinant_nonneg_of_evaluate (p:=p) (fun x y => by rw [he]; linarith [hl x y])
  have h0 : ε ≤ q 0 := by simpa [evaluate] using hl 1 0
  have h2 : ε ≤ q 2 := by simpa [evaluate] using hl 0 1
  change 0 ≤ (q 0-ε)*(q 2-ε)-(q 1)^2 at hp
  dsimp [determinant]
  nlinarith

end CannonConformal

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
-- module Solutions.OAIQ046_CN.Cannon_Conformal_WeakQSPartialsLocally
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
noncomputable section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
noncomputable section
noncomputable section
noncomputable section
open Set Metric MeasureTheory Filter Complex
open scoped Topology

noncomputable section
noncomputable section
open MeasureTheory Set Metric Filter
open scoped Topology ENNReal

namespace CannonMetricQC
open CannonBeltrami MeasureTheory Set Metric

lemma weakQS_partials_locallyIntegrable (f : ℂ ≃ₜ ℂ) {H : ℝ}
    (hH : 0 < H) (hf : WeakQS f H) :
    LocallyIntegrable (partialZ f) volume ∧ LocallyIntegrable (partialBar f) volume := by
  have h1 := (weakQS_full_weakW12 f hH hf 1).1
  have hI := (weakQS_full_weakW12 f hH hf Complex.I).1
  constructor
  · change LocallyIntegrable (fun z => (fderiv ℝ (f : ℂ → ℂ) z 1-Complex.I*fderiv ℝ (f : ℂ → ℂ) z Complex.I)/2) volume
    simpa only [Pi.smul_def,Pi.sub_def,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
      using (h1.sub (hI.smul Complex.I)).smul ((2:ℂ)⁻¹)
  · change LocallyIntegrable (fun z => (fderiv ℝ (f : ℂ → ℂ) z 1+Complex.I*fderiv ℝ (f : ℂ → ℂ) z Complex.I)/2) volume
    simpa only [Pi.smul_def,Pi.add_def,Pi.smul_apply,Pi.add_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
      using (h1.add (hI.smul Complex.I)).smul ((2:ℂ)⁻¹)

lemma weakQS_partial_integration_by_parts (F : ℂ ≃ₜ ℂ) {H : ℝ}
    (hH : 0 < H) (hF : WeakQS F H)
    (φ : SchwartzMap ℂ ℂ) (hc : HasCompactSupport (φ : ℂ → ℂ)) :
    (∫ z, F z*partialZ φ z)=-(∫ z, partialZ F z*φ z) ∧
    (∫ z, F z*partialBar φ z)=-(∫ z, partialBar F z*φ z) := by
  have hfx (v : ℂ) : Integrable (fun z => F z*fderiv ℝ (φ : ℂ → ℂ) z v) :=
    (F.continuous.mul ((φ.smooth'.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_left
  have hdx (v : ℂ) : Integrable (fun z => fderiv ℝ (F : ℂ → ℂ) z v*φ z) := by
    simpa only [smul_eq_mul] using ((weakQS_full_weakW12 F hH hF v).1).integrable_smul_right_of_hasCompactSupport φ.continuous hc
  have hid (v : ℂ) : (∫ z, F z*fderiv ℝ (φ : ℂ → ℂ) z v)=
      -(∫ z, fderiv ℝ (F : ℂ → ℂ) z v*φ z) := by
    have hh := (weakQS_full_weakW12 F hH hF v).2.2 φ hc
    simpa only [mul_comm,neg_neg] using (congrArg Neg.neg hh).symm
  have h1 := hid 1
  have hI := hid Complex.I
  have hz1 : (fun z => F z*partialZ φ z)=
      (fun z => (F z*fderiv ℝ (φ : ℂ → ℂ) z 1-Complex.I*(F z*fderiv ℝ (φ : ℂ → ℂ) z Complex.I))/2) := by
    ext z; unfold partialZ; ring
  have hz2 : (fun z => partialZ F z*φ z)=
      (fun z => (fderiv ℝ F z 1*φ z-Complex.I*(fderiv ℝ F z Complex.I*φ z))/2) := by
    ext z; unfold partialZ; ring
  have hb1 : (fun z => F z*partialBar φ z)=
      (fun z => (F z*fderiv ℝ (φ : ℂ → ℂ) z 1+Complex.I*(F z*fderiv ℝ (φ : ℂ → ℂ) z Complex.I))/2) := by
    ext z; unfold partialBar; ring
  have hb2 : (fun z => partialBar F z*φ z)=
      (fun z => (fderiv ℝ F z 1*φ z+Complex.I*(fderiv ℝ F z Complex.I*φ z))/2) := by
    ext z; unfold partialBar; ring
  rw [hz1,hz2,hb1,hb2]
  simp only [integral_div,integral_sub (hfx 1) ((hfx Complex.I).const_mul _),
    integral_sub (hdx 1) ((hdx Complex.I).const_mul _),
    integral_add (hfx 1) ((hfx Complex.I).const_mul _),
    integral_add (hdx 1) ((hdx Complex.I).const_mul _),integral_const_mul,h1,hI]
  constructor <;> ring

end CannonMetricQC

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
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_Beltrami
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
noncomputable section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
noncomputable section
noncomputable section
noncomputable section
open Set Metric MeasureTheory Filter Complex
open scoped Topology

noncomputable section
noncomputable section
open MeasureTheory Set Metric Filter
open scoped Topology ENNReal

namespace CannonBeltrami
open MeasureTheory Set Metric Filter
open scoped Topology ENNReal

lemma ae_eq_on_of_schwartz_mul {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (hh : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      tsupport (φ : ℂ → ℂ) ⊆ U → (∫ z, f z*φ z)=(∫ z, g z*φ z)) :
    ∀ᵐ z : ℂ, z ∈ U → f z=g z := by
  have hz : ∀ᵐ z : ℂ, z ∈ U → f z-g z=0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero ((hf.sub hg).locallyIntegrableOn U)
    intro φ hφ hc hs
    let ψ : ℂ → ℂ := fun z => (φ z : ℂ)
    have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := Complex.ofRealCLM.contDiff.comp hφ
    have hcψ : HasCompactSupport ψ := hc.comp_left Complex.ofReal_zero
    let t : SchwartzMap ℂ ℂ := hcψ.toSchwartzMap hψ
    have htU : tsupport (t : ℂ → ℂ) ⊆ U :=
      (tsupport_comp_subset Complex.ofReal_zero φ).trans hs
    have he := hh t hcψ htU
    have hfφ : Integrable (fun z => f z*t z) := by
      simpa only [smul_eq_mul] using hf.integrable_smul_right_of_hasCompactSupport t.continuous hcψ
    have hgφ : Integrable (fun z => g z*t z) := by
      simpa only [smul_eq_mul] using hg.integrable_smul_right_of_hasCompactSupport t.continuous hcψ
    have hid : (fun z => φ z • (f z-g z))=(fun z => f z*t z-g z*t z) := by
      funext z
      change (φ z : ℂ)*(f z-g z)=f z*(φ z : ℂ)-g z*(φ z : ℂ)
      ring
    change (∫ z, φ z • (f z-g z))=0
    rw [hid,integral_sub hfφ hgφ,he,sub_self]
  filter_upwards [hz] with z hz hzu
  exact sub_eq_zero.mp (hz hzu)

theorem metric_weak_beltrami_classical (F : ℂ ≃ₜ ℂ) {H : ℝ}
    (hH : 0 < H) (hF : CannonMetricQC.WeakQS F H)
    (μ : ℂ → ℂ) (hm : AEStronglyMeasurable μ volume) {k : ℝ} (hk : 0 ≤ k)
    (hb : ∀ z, ‖μ z‖ ≤ k)
    (hw : ∀ S : Set ℂ, IsCompact S → ∃ a : Lp ℂ 2 (volume.restrict S),
      ∀ φ : SchwartzMap ℂ ℂ, tsupport (φ : ℂ → ℂ) ⊆ S →
        (∫ z, F z*partialZ φ z)=-(∫ z in S, a z*φ z) ∧
        (∫ z, F z*partialBar φ z)=-(∫ z in S, a z*(μ z*φ z))) :
    ∀ᵐ z : ℂ, partialBar F z=μ z*partialZ F z := by
  have hl := CannonMetricQC.weakQS_partials_locallyIntegrable F hH hF
  have he (R : ℝ) : ∀ᵐ z : ℂ, z ∈ ball (0:ℂ) R →
      partialBar F z=μ z*partialZ F z := by
    let S := closedBall (0:ℂ) R
    have hS : IsCompact S := isCompact_closedBall _ _
    let : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hS.measure_lt_top (μ:=volume)⟩
    obtain ⟨a,ha⟩ := hw S hS
    let A : ℂ → ℂ := S.indicator (fun z => a z)
    have hia : Integrable A := (integrable_indicator_iff hS.measurableSet).mpr
      (MemLp.integrable (by norm_num) (Lp.memLp a))
    have him : Integrable (fun z => μ z*A z) :=
      hia.bdd_mul (c := ‖k‖) hm (.of_forall fun point => by
        simpa only [Real.norm_of_nonneg hk] using hb point)
    have hid (φ : SchwartzMap ℂ ℂ) : (∫ z, A z*φ z)=(∫ z in S, a z*φ z) := by
      have heq : (fun z => A z*φ z)=S.indicator (fun z => a z*φ z) := by
        funext z; by_cases hz : z ∈ S <;> simp [A,hz]
      rw [heq,integral_indicator hS.measurableSet]
    have hidm (φ : SchwartzMap ℂ ℂ) :
        (∫ z, (μ z*A z)*φ z)=(∫ z in S, a z*(μ z*φ z)) := by
      calc
        _ = ∫ z, A z*(μ z*φ z) := by congr 1; funext z; ring
        _ = _ := by
          have heq : (fun z => A z*(μ z*φ z))=S.indicator (fun z => a z*(μ z*φ z)) := by
            funext z; by_cases hz : z ∈ S <;> simp [A,hz]
          rw [heq,integral_indicator hS.measurableSet]
    have hza : ∀ᵐ z : ℂ, z ∈ ball (0:ℂ) R → partialZ F z=A z := by
      apply ae_eq_on_of_schwartz_mul isOpen_ball hl.1 hia.locallyIntegrable
      intro φ hc ht
      have hh := ha φ (ht.trans ball_subset_closedBall)
      rw [← hid φ] at hh
      have hparts := CannonMetricQC.weakQS_partial_integration_by_parts F hH hF φ hc
      exact neg_injective (hparts.1.symm.trans hh.1)
    have hba : ∀ᵐ z : ℂ, z ∈ ball (0:ℂ) R → partialBar F z=μ z*A z := by
      apply ae_eq_on_of_schwartz_mul isOpen_ball hl.2 him.locallyIntegrable
      intro φ hc ht
      have hh := ha φ (ht.trans ball_subset_closedBall)
      rw [← hidm φ] at hh
      have hparts := CannonMetricQC.weakQS_partial_integration_by_parts F hH hF φ hc
      exact neg_injective (hparts.2.symm.trans hh.2)
    filter_upwards [hza,hba] with z hz hbz hzR
    rw [hbz hzR,hz hzR]
  have hall : ∀ᵐ z : ℂ, ∀ n : ℕ, z ∈ ball (0:ℂ) (n+1) →
      partialBar F z=μ z*partialZ F z := ae_all_iff.mpr (fun n => he (n+1))
  filter_upwards [hall] with z hz
  obtain ⟨n,hn⟩ := exists_nat_gt ‖z‖
  exact hz n (by simpa only [mem_ball,dist_zero_right] using (show ‖z‖ < (n:ℝ)+1 by linarith))
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
section
noncomputable section
namespace CannonConformal
open Set Topology Metric

lemma measurable_beltrami : Measurable beltrami := by
  have hd : Continuous determinant := by unfold determinant; fun_prop
  have hn : Continuous (fun q : Form => (⟨q 0-q 2,2*q 1⟩ : ℂ)) := by
    have H : Continuous (fun q : Form => ((q 0-q 2 : ℝ) : ℂ)+((2*q 1 : ℝ) : ℂ)*Complex.I) := by
      fun_prop
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    ext q
    apply Complex.ext <;> simp
  have hh : Continuous (fun q : Form => ((q 0+q 2+2*Real.sqrt (determinant q) : ℝ) : ℂ)) := by
    fun_prop
  exact hn.measurable.div hh.measurable

lemma beltrami_uniform_bound {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    {q : Form} (hl : LowerBound ε q) (hu : UpperBound K q) :
    ‖beltrami q‖ ≤ Real.sqrt (1-ε/K) ∧ Real.sqrt (1-ε/K) < 1 := by
  have h0l : ε ≤ q 0 := by simpa [evaluate] using hl 1 0
  have h2l : ε ≤ q 2 := by simpa [evaluate] using hl 0 1
  have h0u : q 0 ≤ K := by simpa [evaluate] using hu 1 0
  have h2u : q 2 ≤ K := by simpa [evaluate] using hu 0 1
  have hεK : ε ≤ K := h0l.trans h0u
  have hd := determinant_ge_sq_lower hε.le hl
  have hd0 : 0 ≤ determinant q := (sq_nonneg ε).trans hd
  have hs : 0 ≤ Real.sqrt (determinant q) := Real.sqrt_nonneg _
  have hss : (Real.sqrt (determinant q))^2=determinant q := Real.sq_sqrt hd0
  have hsl : ε ≤ Real.sqrt (determinant q) := by nlinarith
  have hdu : determinant q ≤ K^2 := by
    have hm := mul_le_mul h0u h2u (hε.le.trans h2l) hK.le
    dsimp [determinant] at *
    nlinarith [sq_nonneg (q 1)]
  have hsu : Real.sqrt (determinant q) ≤ K := by nlinarith
  let d := q 0+q 2+2*Real.sqrt (determinant q)
  have hdp : 0 < d := by dsimp [d]; linarith
  have hdu' : d ≤ 4*K := by dsimp [d]; linarith
  have hnid : (q 0-q 2)^2+(2*q 1)^2=d^2-4*Real.sqrt (determinant q)*d := by
    dsimp [d]
    have hss' : (Real.sqrt (determinant q))^2=q 0*q 2-(q 1)^2 := hss
    nlinarith only [hss']
  have hnorm : ‖beltrami q‖^2=((q 0-q 2)^2+(2*q 1)^2)/d^2 := by
    rw [beltrami,norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply,d,pow_two]
  have hratio : ε/K ≤ 4*Real.sqrt (determinant q)/d := by
    apply (div_le_div_iff₀ hK hdp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hdu' hε.le]
  have hnormle : ‖beltrami q‖^2 ≤ 1-ε/K := by
    rw [hnorm,hnid]
    have he : (d^2-4*Real.sqrt (determinant q)*d)/d^2=
        1-4*Real.sqrt (determinant q)/d := by field_simp
    rw [he]
    linarith
  have hr0 : 0 ≤ 1-ε/K := by rw [sub_nonneg]; exact (div_le_one hK).mpr hεK
  constructor
  · have hh := Real.sq_sqrt hr0
    have hs' := Real.sqrt_nonneg (1-ε/K)
    nlinarith [norm_nonneg (beltrami q)]
  · have hr : 1-ε/K < 1 := by linarith [div_pos hε hK]
    have hh := Real.sq_sqrt hr0
    have hs' := Real.sqrt_nonneg (1-ε/K)
    nlinarith

lemma evaluate_coefficientForm (μ : ℂ) (x y : ℝ) :
    evaluate (coefficientForm μ) x y=
      Complex.normSq ((⟨x,y⟩ : ℂ)+μ*star (⟨x,y⟩ : ℂ)) := by
  simp [evaluate,coefficientForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring

lemma coefficient_reconstruction {q : Form} (hq : Positive q) :
    q=((q 0+q 2+2*Real.sqrt (determinant q))/4) • coefficientForm (beltrami q) := by
  have hc : 0 < q 2 := by
    have h := hq.2
    have ha := hq.1
    dsimp [determinant] at h
    nlinarith [sq_nonneg (q 1)]
  have hd : 0 < q 0+q 2+2*Real.sqrt (determinant q) := by
    linarith [Real.sqrt_nonneg (determinant q),hq.1]
  have hs : Real.sqrt (determinant q)^2=q 0*q 2-(q 1)^2 := Real.sq_sqrt hq.2.le
  have hr : (beltrami q).re=(q 0-q 2)/(q 0+q 2+2*Real.sqrt (determinant q)) := by
    simp only [beltrami,Complex.div_ofReal_re]
  have hi : (beltrami q).im=2*q 1/(q 0+q 2+2*Real.sqrt (determinant q)) := by
    simp only [beltrami,Complex.div_ofReal_im]
  ext i
  fin_cases i
  · change q 0=((q 0+q 2+2*Real.sqrt (determinant q))/4)*
      ((1+(beltrami q).re)^2+(beltrami q).im^2)
    rw [hr,hi]
    field_simp
    nlinarith only [hs]
  · change q 1=((q 0+q 2+2*Real.sqrt (determinant q))/4)*(2*(beltrami q).im)
    rw [hi]
    field_simp
    ring
  · change q 2=((q 0+q 2+2*Real.sqrt (determinant q))/4)*
      ((1-(beltrami q).re)^2+(beltrami q).im^2)
    rw [hr,hi]
    field_simp
    nlinarith only [hs]

end CannonConformal

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
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_DirichletPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

namespace CannonBeltrami
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dirichlet_pullback_le (F : ℂ ≃ₜ ℂ) (hF : ContDiff ℝ 1 (F : ℂ → ℂ))
    (u : ℂ → E) (hu : ContDiff ℝ 1 u) {S : Set ℂ} (hS : IsCompact S)
    {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F : ℂ → ℂ) z).det|) :
    (∫ z in S, ‖fderiv ℝ (u ∘ F) z‖^2) ≤
      K*(∫ w in F '' S, ‖fderiv ℝ u w‖^2) := by
  have huD : Continuous (fun z => ‖fderiv ℝ u z‖^2) :=
    (hu.continuous_fderiv (by simp)).norm.pow 2
  have hFi : ∀ z ∈ S, HasFDerivWithinAt (F : ℂ → ℂ) (fderiv ℝ (F : ℂ → ℂ) z) S z :=
    fun z _ => (hF.differentiable (by simp) z).hasFDerivAt.hasFDerivWithinAt
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul volume hS.measurableSet
    hFi F.injective.injOn (fun z => ‖fderiv ℝ u z‖^2)
  have hint : IntegrableOn (fun z => |(fderiv ℝ (F : ℂ → ℂ) z).det| *‖fderiv ℝ u (F z)‖^2) S volume := by
    apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hS.measurableSet
      hFi F.injective.injOn (fun z => ‖fderiv ℝ u z‖^2)).mp
    exact huD.continuousOn.integrableOn_compact (hS.image F.continuous)
  have hlint : IntegrableOn (fun z => ‖fderiv ℝ (u ∘ F) z‖^2) S volume :=
    ((hu.comp hF).continuous_fderiv (by simp)).norm.pow 2 |>.continuousOn.integrableOn_compact hS
  calc
    _ ≤ ∫ z in S, K*(|(fderiv ℝ (F : ℂ → ℂ) z).det| *‖fderiv ℝ u (F z)‖^2) := by
      apply setIntegral_mono_on hlint (hint.const_mul K) hS.measurableSet
      intro z _hz
      rw [fderiv_comp z (hu.differentiable (by simp) (F z)) (hF.differentiable (by simp) z)]
      have hn := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ u (F z)) (fderiv ℝ (F : ℂ → ℂ) z)
      have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
      have hdistortion := mul_le_mul (hD z) (le_refl (‖fderiv ℝ u (F z)‖^2))
        (sq_nonneg _) (mul_nonneg hK (abs_nonneg _))
      nlinarith [hdistortion]
    _ = K*(∫ z in S, |(fderiv ℝ (F : ℂ → ℂ) z).det| *‖fderiv ℝ u (F z)‖^2) := integral_const_mul _ _
    _ = _ := by rw [hchange]; rfl

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
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_ContinuousMemLpRestrict
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

lemma l2_restrict_integral_norm_sq {f : ℂ → ℂ} {S : Set ℂ}
    (hf : MemLp f 2 (volume.restrict S)) :
    (∫ z in S, ‖f z‖^2)=‖hf.toLp‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with z hz
  rw [hz,real_inner_self_eq_norm_sq]

theorem smooth_local_energy_bound (F : ℂ ≃ₜ ℂ) (hF : ContDiff ℝ 1 (F : ℂ → ℂ))
    {S : Set ℂ} (hS : IsCompact S) {K B : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F : ℂ → ℂ) z).det|)
    (hb : ∀ z ∈ S, ‖F z‖ ≤ B) :
    (∫ z in S, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2) ≤ K*volume.real (closedBall (0:ℂ) B) := by
  have hh := dirichlet_pullback_le F hF (fun z : ℂ => z) contDiff_id hS hK hD
  have hi : (∫ z in S, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2) ≤ K*volume.real (F '' S) := by
    have hid (w : ℂ) : fderiv ℝ (fun z : ℂ => z) w=ContinuousLinearMap.id ℝ ℂ :=
      fderiv_id
    simp only [Function.comp_def,hid,ContinuousLinearMap.norm_id,one_pow,
      setIntegral_const,smul_eq_mul,mul_one] at hh
    exact hh
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ hK
  apply measureReal_mono _ (isCompact_closedBall (0:ℂ) B).measure_ne_top
  rintro _ ⟨z,hz,rfl⟩
  simpa only [mem_closedBall,dist_zero_right] using hb z hz

lemma smooth_partialZ_l2_bound (F : ℂ ≃ₜ ℂ) (hF : ContDiff ℝ ∞ (F : ℂ → ℂ))
    {S : Set ℂ} (hS : IsCompact S) {K B : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F : ℂ → ℂ) z).det|)
    (hb : ∀ z ∈ S, ‖F z‖ ≤ B) :
    let h := continuous_memLp_restrict_compact (contDiff_partials hF).1.continuous hS
    ‖h.toLp‖ ≤ K*volume.real (closedBall (0:ℂ) B)+1 := by
  dsimp only
  let h := continuous_memLp_restrict_compact (contDiff_partials hF).1.continuous hS
  have hs : ‖h.toLp‖^2 ≤ K*volume.real (closedBall (0:ℂ) B) := by
    rw [← l2_restrict_integral_norm_sq h]
    apply le_trans ?_ (smooth_local_energy_bound F (hF.of_le (by simp)) hS hK hD hb)
    apply setIntegral_mono_on h.norm.integrable_sq
      (((hF.of_le (by simp) : ContDiff ℝ 1 (F : ℂ → ℂ)).continuous_fderiv (by simp)).norm.pow 2
        |>.continuousOn.integrableOn_compact hS) hS.measurableSet
    intro z _
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (partialZ_norm_le F z)
  have hp : 0 ≤ K*volume.real (closedBall (0:ℂ) B) := mul_nonneg hK measureReal_nonneg
  nlinarith [norm_nonneg h.toLp]

end CannonBeltrami

namespace CannonBeltrami
open MeasureTheory Filter Set Metric
open scoped Topology SchwartzMap ContDiff

lemma smooth_integration_by_parts (F : ℂ → ℂ) (hf : ContDiff ℝ 1 F)
    (φ : SchwartzMap ℂ ℂ) (hc : HasCompactSupport (φ : ℂ → ℂ)) (v : ℂ) :
    (∫ z, F z*fderiv ℝ (φ : ℂ → ℂ) z v) = -(∫ z, fderiv ℝ F z v*φ z) := by
  have hdf : Continuous (fun z => fderiv ℝ F z v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ : Continuous (fun z => fderiv ℝ (φ : ℂ → ℂ) z v) :=
    (φ.smooth'.continuous_fderiv (by simp)).clm_apply continuous_const
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (hdf.mul φ.continuous).integrable_of_hasCompactSupport hc.mul_left
  · exact (hf.continuous.mul hdφ).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_left
  · exact (hf.continuous.mul φ.continuous).integrable_of_hasCompactSupport hc.mul_left
  · intro z _; exact hf.differentiable (by simp) z
  · intro z _; exact φ.differentiable z

end CannonBeltrami

namespace CannonBeltrami

lemma smooth_partial_integration_by_parts (F : ℂ → ℂ) (hf : ContDiff ℝ 1 F)
    (φ : SchwartzMap ℂ ℂ) (hc : HasCompactSupport (φ : ℂ → ℂ)) :
    (∫ z, F z*partialZ φ z)=-(∫ z, partialZ F z*φ z) ∧
    (∫ z, F z*partialBar φ z)=-(∫ z, partialBar F z*φ z) := by
  have hfx (v : ℂ) : Integrable (fun z => F z*fderiv ℝ (φ : ℂ → ℂ) z v) :=
    (hf.continuous.mul ((φ.smooth'.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_left
  have hdx (v : ℂ) : Integrable (fun z => fderiv ℝ F z v*φ z) :=
    (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul φ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have h1 := smooth_integration_by_parts F hf φ hc 1
  have hI := smooth_integration_by_parts F hf φ hc Complex.I
  have hz1 : (fun z => F z*partialZ φ z)=
      (fun z => (F z*fderiv ℝ (φ : ℂ → ℂ) z 1-Complex.I*(F z*fderiv ℝ (φ : ℂ → ℂ) z Complex.I))/2) := by
    ext z; unfold partialZ; ring
  have hz2 : (fun z => partialZ F z*φ z)=
      (fun z => (fderiv ℝ F z 1*φ z-Complex.I*(fderiv ℝ F z Complex.I*φ z))/2) := by
    ext z; unfold partialZ; ring
  have hb1 : (fun z => F z*partialBar φ z)=
      (fun z => (F z*fderiv ℝ (φ : ℂ → ℂ) z 1+Complex.I*(F z*fderiv ℝ (φ : ℂ → ℂ) z Complex.I))/2) := by
    ext z; unfold partialBar; ring
  have hb2 : (fun z => partialBar F z*φ z)=
      (fun z => (fderiv ℝ F z 1*φ z+Complex.I*(fderiv ℝ F z Complex.I*φ z))/2) := by
    ext z; unfold partialBar; ring
  rw [hz1,hz2,hb1,hb2]
  simp only [integral_div,integral_sub (hfx 1) ((hfx Complex.I).const_mul _),
    integral_sub (hdx 1) ((hdx Complex.I).const_mul _),
    integral_add (hfx 1) ((hfx Complex.I).const_mul _),
    integral_add (hdx 1) ((hdx Complex.I).const_mul _),integral_const_mul,h1,hI]
  constructor <;> ring

lemma compact_test_tendsto (F : ℕ → ℂ → ℂ) (G : ℂ → ℂ)
    (hf : ∀ n, Continuous (F n))
    (hb : ∀ S : Set ℂ, IsCompact S → ∃ B : ℝ, 0 ≤ B ∧ ∀ n z, z ∈ S → ‖F n z‖ ≤ B)
    (ht : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (G z)))
    (ψ : ℂ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Tendsto (fun n => ∫ z, F n z*ψ z) atTop (𝓝 (∫ z, G z*ψ z)) := by
  obtain ⟨B,hB,hbB⟩ := hb (tsupport ψ) hc
  have hdom : Integrable (fun z => B*‖ψ z‖) :=
    (continuous_const.mul hψ.norm).integrable_of_hasCompactSupport hc.norm.mul_left
  apply tendsto_integral_of_dominated_convergence (fun z => B*‖ψ z‖)
    (fun n => ((hf n).mul hψ).aestronglyMeasurable) hdom
  · intro n
    exact .of_forall (fun z => by
      change ‖F n z*ψ z‖ ≤ _
      rw [norm_mul]
      by_cases hz : ψ z=0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_right (hbB n z (subset_tsupport _ hz)) (norm_nonneg _))
  · exact .of_forall (fun z => (ht z).mul_const (ψ z))

lemma hasCompactSupport_partials {φ : ℂ → ℂ} (hc : HasCompactSupport φ) :
    HasCompactSupport (partialZ φ) ∧ HasCompactSupport (partialBar φ) := by
  unfold partialZ partialBar
  simp only [div_eq_mul_inv]
  exact ⟨((hc.fderiv_apply ℝ 1).sub ((hc.fderiv_apply ℝ Complex.I).mul_left)).mul_right,
    ((hc.fderiv_apply ℝ 1).add ((hc.fderiv_apply ℝ Complex.I).mul_left)).mul_right⟩

end CannonBeltrami

noncomputable section
open Set Filter Topology

namespace CannonHilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma real_hilbert_biddual_surjective :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E) := by
  intro A
  let R := InnerProductSpace.toDual ℝ E
  let B : E →L[ℝ] ℝ := A.comp R.toContinuousLinearEquiv.toContinuousLinearMap
  let x := R.symm B
  refine ⟨x,?_⟩
  ext L
  obtain ⟨y,rfl⟩ := R.surjective L
  change R y x=A (R y)
  have h : R x y=A (R y) := by
    change (R (R.symm B)) y=A (R y)
    rw [R.apply_symm_apply]
    rfl
  dsimp only [R] at h ⊢
  rw [InnerProductSpace.toDual_apply_apply,real_inner_comm,← InnerProductSpace.toDual_apply_apply]
  exact h

lemma bounded_weak_closure_compact (S : Set E) (hS : Bornology.IsBounded S) :
    IsCompact (closure (toWeakSpace ℝ E '' S)) := by
  apply NormedSpace.isCompact_closure_of_isBounded
  · simpa only [Set.preimage_image_eq _ (toWeakSpace ℝ E).injective] using hS
  · have hs : Function.Surjective (NormedSpace.inclusionInDoubleDualWeak ℝ E) := by
      intro A
      obtain ⟨x,hx⟩ := real_hilbert_biddual_surjective (StrongDual.toWeakDual.symm A)
      refine ⟨toWeakSpace ℝ E x,?_⟩
      change StrongDual.toWeakDual (NormedSpace.inclusionInDoubleDual ℝ E x)=A
      rw [hx]
      exact StrongDual.toWeakDual.apply_symm_apply A
    rw [hs.range_eq]
    exact subset_univ _

theorem bounded_weak_filter_limit (f : ℕ → E) {B : ℝ} (hB : ∀ n, ‖f n‖ ≤ B) :
    ∃ a : E, ∃ l : Filter ℕ, l.NeBot ∧ l ≤ atTop ∧
      Tendsto (fun n => toWeakSpace ℝ E (f n)) l (𝓝 (toWeakSpace ℝ E a)) := by
  have hb : Bornology.IsBounded (range f) :=
    isBounded_iff_forall_norm_le.mpr ⟨B,by rintro _ ⟨n,rfl⟩; exact hB n⟩
  have hc := bounded_weak_closure_compact (range f) hb
  let g : ℕ → WeakSpace ℝ E := fun n => toWeakSpace ℝ E (f n)
  obtain ⟨a,_,ha⟩ := hc.exists_mapClusterPt (u:=g) (f:=atTop) (Filter.le_principal_iff.mpr (by
    change ∀ᶠ n : ℕ in atTop, g n ∈ closure (toWeakSpace ℝ E '' range f)
    exact .of_forall (fun n => subset_closure ⟨f n,mem_range_self n,rfl⟩)))
  refine ⟨(toWeakSpace ℝ E).symm a,atTop ⊓ Filter.comap g (𝓝 a),?_,inf_le_left,?_⟩
  · exact Filter.neBot_inf_comap_iff_map.mpr (by simpa only [MapClusterPt,ClusterPt,inf_comm] using ha)
  · simp only [(toWeakSpace ℝ E).apply_symm_apply]
    exact Filter.map_le_iff_le_comap.mpr inf_le_right

end CannonHilbert

namespace CannonHilbert
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma weak_real_eval_tendsto {ι : Type*} {l : Filter ι} {f : ι → E} {a : E}
    (ht : Tendsto (fun i => toWeakSpace ℝ E (f i)) l (𝓝 (toWeakSpace ℝ E a)))
    (A : E →L[ℝ] ℝ) : Tendsto (fun i => A (f i)) l (𝓝 (A a)) := by
  exact (WeakBilin.eval_continuous _ A).tendsto (toWeakSpace ℝ E a) |>.comp ht

lemma weak_complex_eval_tendsto {ι : Type*} {l : Filter ι} {f : ι → E} {a : E}
    (ht : Tendsto (fun i => toWeakSpace ℝ E (f i)) l (𝓝 (toWeakSpace ℝ E a)))
    (A : E →L[ℝ] ℂ) : Tendsto (fun i => A (f i)) l (𝓝 (A a)) := by
  have hre := weak_real_eval_tendsto ht (Complex.reCLM.comp A)
  have him := weak_real_eval_tendsto ht (Complex.imCLM.comp A)
  have h := ((Complex.continuous_ofReal.tendsto _).comp hre).add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul_const Complex.I)
  simpa only [ContinuousLinearMap.comp_apply,Complex.reCLM_apply,Complex.imCLM_apply,
    Function.comp_def,Complex.re_add_im] using h

variable [InnerProductSpace ℂ E]

lemma weak_inner_tendsto {ι : Type*} {l : Filter ι} {f : ι → E} {a : E}
    (ht : Tendsto (fun i => toWeakSpace ℝ E (f i)) l (𝓝 (toWeakSpace ℝ E a)))
    (v : E) : Tendsto (fun i => inner ℂ v (f i)) l (𝓝 (inner ℂ v a)) :=
  weak_complex_eval_tendsto ht ((innerSL ℂ v).restrictScalars ℝ)

theorem strong_weak_inner_tendsto {ι : Type*} {l : Filter ι} {f v : ι → E} {a b : E}
    (ht : Tendsto (fun i => toWeakSpace ℝ E (f i)) l (𝓝 (toWeakSpace ℝ E a)))
    (hv : Tendsto v l (𝓝 b)) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i, ‖f i‖ ≤ B) :
    Tendsto (fun i => inner ℂ (v i) (f i)) l (𝓝 (inner ℂ b a)) := by
  have hz : Tendsto (fun i => ‖v i-b‖*‖B‖) l (𝓝 0) := by
    simpa using ((hv.sub_const b).norm.mul_const ‖B‖)
  have he : Tendsto (fun i => inner ℂ (v i-b) (f i)) l (𝓝 0) := by
    apply squeeze_zero_norm (fun i => ?_) hz
    rw [Real.norm_of_nonneg hB]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _))
  have hh := he.add (weak_inner_tendsto ht b)
  simpa only [inner_sub_left,sub_add_cancel,zero_add] using hh
end CannonHilbert

open MeasureTheory
open scoped ENNReal

namespace CannonHilbert
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma dominated_toLp_zero {f : ℕ → X → ℂ} (hf : ∀ n, MemLp (f n) 2 ν)
    {g : X → ℂ} (hg : MemLp g 2 ν)
    (hb : ∀ n, ∀ᵐ x ∂ν, ‖f n x‖ ≤ ‖g x‖)
    (hl : ∀ᵐ x ∂ν, Tendsto (fun n => f n x) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 0) := by
  have hb' : ∀ n, (fun x => ‖f n x‖ₑ ^ (2:ℝ)) ≤ᵐ[ν] (fun x => ‖g x‖ₑ ^ (2:ℝ)) := by
    intro n
    filter_upwards [hb n] with x hx
    exact ENNReal.rpow_le_rpow (ENNReal.coe_le_coe.mpr hx) (by norm_num)
  have hfin : (∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂ν) ≠ ⊤ := by
    exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num) hg.eLpNorm_lt_top).ne
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun n => ‖f n x‖ₑ ^ (2:ℝ)) atTop (𝓝 (0:ℝ≥0∞)) := by
    filter_upwards [hl] with x hx
    have hc : Continuous (fun t : ℝ≥0∞ => t^(2:ℝ)) := ENNReal.continuous_rpow_const
    simpa only [Function.comp_def,enorm, nnnorm_zero, ENNReal.coe_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ)<2)] using
      hc.continuousAt.tendsto.comp (ENNReal.tendsto_coe.mpr hx.nnnorm)
  have hi := tendsto_lintegral_of_dominated_convergence' _
    (fun n => (hf n).aestronglyMeasurable.enorm.pow_const (2:ℝ)) hb' hfin hlim
  have heLp : Tendsto (fun n => eLpNorm (f n) 2 ν) atTop (𝓝 0) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num : (2:ℝ≥0∞) ≠ ⊤)]
    have hc : Continuous (fun t : ℝ≥0∞ => t^(1/2:ℝ)) := ENNReal.continuous_rpow_const
    simpa [Function.comp_def] using hc.continuousAt.tendsto.comp hi
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf (0 : X → ℂ) (MemLp.zero : MemLp (0 : X → ℂ) 2 ν)).mpr
    (by simpa using heLp)
  simpa using h

lemma integral_mul_eq_inner (a : Lp ℂ 2 ν) {ψ : X → ℂ} (hψ : MemLp ψ 2 ν) :
    (∫ x, a x*ψ x ∂ν)=inner ℂ hψ.star.toLp a := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hψ.star.coeFn_toLp] with x hx
  simp only [RCLike.inner_apply,hx,Pi.star_apply]
  change a x*ψ x=a x*star (star (ψ x))
  rw [star_star]

lemma weak_integral_test_tendsto {ι : Type*} {l : Filter ι}
    {f : ι → Lp ℂ 2 ν} {a : Lp ℂ 2 ν}
    (ht : Tendsto (fun i => toWeakSpace ℝ (Lp ℂ 2 ν) (f i)) l
      (𝓝 (toWeakSpace ℝ (Lp ℂ 2 ν) a))) {ψ : X → ℂ} (hψ : MemLp ψ 2 ν) :
    Tendsto (fun i => ∫ x, f i x*ψ x ∂ν) l (𝓝 (∫ x, a x*ψ x ∂ν)) := by
  simp only [integral_mul_eq_inner _ hψ]
  exact weak_inner_tendsto ht hψ.star.toLp

lemma coefficient_test_strong_tendsto (μ : ℕ → X → ℂ) (m : X → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (μ n) ν) (hm₀ : AEStronglyMeasurable m ν)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ n, ∀ᵐ x ∂ν, ‖μ n x‖ ≤ k)
    (hb₀ : ∀ᵐ x ∂ν, ‖m x‖ ≤ k)
    (ht : ∀ᵐ x ∂ν, Tendsto (fun n => μ n x) atTop (𝓝 (m x)))
    {ψ : X → ℂ} (hψ : MemLp ψ 2 ν) :
    Tendsto (fun n => (bounded_mul_memLp (hm n) (hb n) hψ).star.toLp) atTop
      (𝓝 (bounded_mul_memLp hm₀ hb₀ hψ).star.toLp) := by
  let u (n : ℕ) : Lp ℂ 2 ν := (bounded_mul_memLp (hm n) (hb n) hψ).star.toLp
  let v : Lp ℂ 2 ν := (bounded_mul_memLp hm₀ hb₀ hψ).star.toLp
  have he (n : ℕ) : (u n-v : Lp ℂ 2 ν) =ᵐ[ν] fun x => star (μ n x*ψ x)-star (m x*ψ x) := by
    filter_upwards [Lp.coeFn_sub (u n) v,
      (bounded_mul_memLp (hm n) (hb n) hψ).star.coeFn_toLp,
      (bounded_mul_memLp hm₀ hb₀ hψ).star.coeFn_toLp] with x h1 h2 h3
    change (u n : X → ℂ) x=star (μ n x*ψ x) at h2
    change (v : X → ℂ) x=star (m x*ψ x) at h3
    simpa only [Pi.sub_apply,h2,h3] using h1
  have hd (n : ℕ) : ∀ᵐ x ∂ν, ‖(u n-v : Lp ℂ 2 ν) x‖ ≤ ‖((2*k:ℝ):ℂ)*ψ x‖ := by
    filter_upwards [he n,hb n,hb₀] with x hx h1 h2
    rw [hx,← star_sub,norm_star,← sub_mul,norm_mul,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤2*k)]
    exact mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (by linarith)) (norm_nonneg _)
  have hl : ∀ᵐ x ∂ν, Tendsto (fun n => (u n-v : Lp ℂ 2 ν) x) atTop (𝓝 0) := by
    filter_upwards [ae_all_iff.mpr he,ht] with x h1 h2
    simp only [h1]
    simpa using ((h2.mul_const (ψ x)).star.sub_const (star (m x*ψ x)))
  have hh := dominated_toLp_zero (fun n => Lp.memLp (u n-v))
    (hψ.const_mul ((2*k:ℝ):ℂ)) hd hl
  simp only [Lp.toLp_coeFn] at hh
  exact tendsto_sub_nhds_zero_iff.mp hh

lemma weak_moving_integral_test_tendsto {l : Filter ℕ} (hl : l ≤ atTop)
    {f : ℕ → Lp ℂ 2 ν} {a : Lp ℂ 2 ν}
    (hw : Tendsto (fun n => toWeakSpace ℝ (Lp ℂ 2 ν) (f n)) l
      (𝓝 (toWeakSpace ℝ (Lp ℂ 2 ν) a))) {B : ℝ} (hB : 0 ≤ B) (hfB : ∀ n, ‖f n‖ ≤ B)
    (μ : ℕ → X → ℂ) (m : X → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (μ n) ν) (hm₀ : AEStronglyMeasurable m ν)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ n, ∀ᵐ x ∂ν, ‖μ n x‖ ≤ k)
    (hb₀ : ∀ᵐ x ∂ν, ‖m x‖ ≤ k)
    (ht : ∀ᵐ x ∂ν, Tendsto (fun n => μ n x) atTop (𝓝 (m x)))
    {ψ : X → ℂ} (hψ : MemLp ψ 2 ν) :
    Tendsto (fun n => ∫ x, f n x*(μ n x*ψ x) ∂ν) l
      (𝓝 (∫ x, a x*(m x*ψ x) ∂ν)) := by
  simp only [integral_mul_eq_inner _ (bounded_mul_memLp (hm _) (hb _) hψ),
    integral_mul_eq_inner _ (bounded_mul_memLp hm₀ hb₀ hψ)]
  exact strong_weak_inner_tendsto hw
    ((coefficient_test_strong_tendsto μ m hm hm₀ hk hb hb₀ ht hψ).mono_left hl) hB hfB
end CannonHilbert

namespace CannonBeltrami
open CannonHilbert

theorem local_weak_beltrami_limit (F : ℕ → ℂ ≃ₜ ℂ) (G : ℂ → ℂ)
    (hf : ∀ n, ContDiff ℝ ∞ (F n : ℂ → ℂ))
    (hlocal : ∀ S : Set ℂ, IsCompact S → ∃ B : ℝ, 0 ≤ B ∧ ∀ n z, z ∈ S → ‖F n z‖ ≤ B)
    (hlim : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (G z)))
    {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ n z, ‖fderiv ℝ (F n : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F n : ℂ → ℂ) z).det|)
    (μ : ℕ → ℂ → ℂ) (m : ℂ → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (μ n) volume) (hm₀ : AEStronglyMeasurable m volume)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ n z, ‖μ n z‖ ≤ k) (hb₀ : ∀ z, ‖m z‖ ≤ k)
    (hμ : ∀ᵐ z ∂volume, Tendsto (fun n => μ n z) atTop (𝓝 (m z)))
    (he : ∀ n z, partialBar (F n) z=μ n z*partialZ (F n) z)
    {S : Set ℂ} (hS : IsCompact S) :
    ∃ a : Lp ℂ 2 (volume.restrict S),
      ∀ φ : SchwartzMap ℂ ℂ, tsupport (φ : ℂ → ℂ) ⊆ S →
        (∫ z, G z*partialZ φ z)=-(∫ z in S, a z*φ z) ∧
        (∫ z, G z*partialBar φ z)=-(∫ z in S, a z*(m z*φ z)) := by
  let ν := volume.restrict S
  have hLp (n : ℕ) : MemLp (partialZ (F n)) 2 ν :=
    continuous_memLp_restrict_compact (contDiff_partials (hf n)).1.continuous hS
  let f (n : ℕ) : Lp ℂ 2 ν := (hLp n).toLp
  obtain ⟨B,hB,hbB⟩ := hlocal S hS
  let C := K*volume.real (closedBall (0:ℂ) B)+1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (n : ℕ) : ‖f n‖ ≤ C :=
    smooth_partialZ_l2_bound (F n) (hf n) hS hK (hD n) (hbB n)
  obtain ⟨a,l,hl,hlTop,ha⟩ := bounded_weak_filter_limit f hbound
  let : l.NeBot := hl
  refine ⟨a,?_⟩
  intro φ hφS
  have hcφ : HasCompactSupport (φ : ℂ → ℂ) := hS.of_isClosed_subset (isClosed_tsupport _) hφS
  have hφ : MemLp (φ : ℂ → ℂ) 2 ν := continuous_memLp_restrict_compact φ.continuous hS
  have hφout (z : ℂ) (hz : z ∉ S) : φ z=0 := by
    by_contra hn
    exact hz (hφS (subset_tsupport _ hn))
  have htestZ := weak_integral_test_tendsto ha hφ
  have htestBar := weak_moving_integral_test_tendsto hlTop ha hC hbound μ m
    (fun n => (hm n).restrict) hm₀.restrict hk
    (fun n => .of_forall (hb n)) (.of_forall hb₀) (ae_restrict_of_ae hμ) hφ
  have hidZ (n : ℕ) : (∫ z in S, f n z*φ z)=(∫ z, partialZ (F n) z*φ z) := by
    calc
      _ = ∫ z in S, partialZ (F n) z*φ z := by
        apply integral_congr_ae
        filter_upwards [(hLp n).coeFn_toLp] with z hz
        rw [hz]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [hφout z hz,mul_zero])
  have hidBar (n : ℕ) : (∫ z in S, f n z*(μ n z*φ z))=(∫ z, partialBar (F n) z*φ z) := by
    calc
      _ = ∫ z in S, partialBar (F n) z*φ z := by
        apply integral_congr_ae
        filter_upwards [(hLp n).coeFn_toLp] with z hz
        rw [hz,he]; ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [hφout z hz,mul_zero])
  have hp := hasCompactSupport_partials hcφ
  have hz := compact_test_tendsto (fun n z => F n z) G (fun n => (F n).continuous)
    hlocal hlim (partialZ φ) (contDiff_partials φ.smooth').1.continuous hp.1
  have hb' := compact_test_tendsto (fun n z => F n z) G (fun n => (F n).continuous)
    hlocal hlim (partialBar φ) (contDiff_partials φ.smooth').2.continuous hp.2
  have hparts (n : ℕ) := smooth_partial_integration_by_parts (F n)
    ((hf n).of_le (by simp)) φ hcφ
  constructor
  · have ht : Tendsto (fun n => ∫ z, F n z*partialZ φ z) l (𝓝 (-(∫ z in S, a z*φ z))) := by
      simpa only [ν,hidZ, (hparts _).1] using htestZ.neg
    exact tendsto_nhds_unique (hz.mono_left hlTop) ht
  · have ht : Tendsto (fun n => ∫ z, F n z*partialBar φ z) l (𝓝 (-(∫ z in S, a z*(m z*φ z)))) := by
      simpa only [ν,hidBar, (hparts _).2] using htestBar.neg
    exact tendsto_nhds_unique (hb'.mono_left hlTop) ht
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
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_StopInside
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

namespace CannonContinuum

theorem stop_inside {X : Type*} [MetricSpace X]
    {D : Set X} (hD : IsCompact D) (hconn : IsConnected D)
    {p x : X} {r : ℝ} (hx : x ∈ D) (hxr : dist x p < r)
    (hout : ∃ y ∈ D, r < dist y p) :
    ∃ C : Set X, IsCompact C ∧ IsConnected C ∧ C ⊆ D ∧ x ∈ C ∧
      (∃ z ∈ C, dist z p = r) ∧ ∀ z ∈ C, dist z p ≤ r := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let : PreconnectedSpace D := Subtype.preconnectedSpace hconn.isPreconnected
  let f : D → ℝ := fun z => -dist (z : X) p
  have hf : Continuous f := (continuous_subtype_val.dist continuous_const).neg
  let K : Set D := {z | -r ≤ f z}
  let xK : K := ⟨⟨x,hx⟩,neg_le_neg hxr.le⟩
  have hK : IsClosed K := isClosed_le continuous_const hf
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  have hbelow : ∃ y : D, f y < -r := by
    obtain ⟨y,hy,hyr⟩ := hout
    exact ⟨⟨y,hy⟩,neg_lt_neg hyr⟩
  obtain ⟨z,hz,hzr⟩ := component_meets_level f hf (-r) xK hbelow
  let g : K → X := fun z => z.val.val
  have hg : Continuous g := continuous_subtype_val.comp continuous_subtype_val
  refine ⟨g '' connectedComponent xK,isClosed_connectedComponent.isCompact.image hg,
    isConnected_connectedComponent.image g hg.continuousOn,?_,?_,?_,?_⟩
  · rintro _ ⟨y,hy,rfl⟩
    exact y.val.property
  · exact ⟨xK,mem_connectedComponent,rfl⟩
  · refine ⟨g z,⟨z,hz,rfl⟩,?_⟩
    exact neg_injective hzr
  · rintro _ ⟨y,hy,rfl⟩
    exact neg_le_neg_iff.mp y.property

end CannonContinuum

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
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_RectCrossing
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

namespace CannonRealPlane

lemma integral_sq_cauchy {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b) :
    (∫ t in a..b, f t)^2 ≤ (b-a)*(∫ t in a..b, (f t)^2) := by
  let aa := ∫ t in a..b, f t
  let bb := ∫ t in a..b, (f t)^2
  let m := aa/(b-a)
  have hfi := hf.intervalIntegrable (μ := volume) a b
  have hf2 : IntervalIntegrable (fun t => (f t)^2) volume a b :=
    (hf.pow 2).intervalIntegrable a b
  have he : (∫ t in a..b, (f t-m)^2)=bb-2*m*aa+m^2*(b-a) := by
    calc
      _ = ∫ t in a..b, ((f t)^2-2*m*f t+m^2) :=
        intervalIntegral.integral_congr fun _ _ => by ring
      _ = bb-2*m*aa+m^2*(b-a) := by
        rw [intervalIntegral.integral_add (hf2.sub (hfi.const_mul _)) intervalIntegrable_const,
          intervalIntegral.integral_sub hf2 (hfi.const_mul _),intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        simp only [smul_eq_mul,aa,bb]
        ring
  have hp : 0 ≤ ∫ t in a..b, (f t-m)^2 :=
    intervalIntegral.integral_nonneg hab.le (fun _ _ => sq_nonneg _)
  rw [he] at hp
  have ht : 0 < b-a := sub_pos.mpr hab
  have hid : (b-a)*(bb-2*m*aa+m^2*(b-a))=(b-a)*bb-aa^2 := by
    dsimp only [m]
    field_simp
    ring
  have h := mul_nonneg ht.le hp
  rw [hid] at h
  dsimp only [aa,bb] at h
  linarith

lemma line_energy_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {q : ℝ → ℝ}
    (hq : Continuous q) (hp : ∀ x, 0 ≤ q x) (hb : ∀ x, ‖deriv f x‖ ≤ q x)
    {a b x y : ℝ} (hab : a < b) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖f x-f y‖^2 ≤ (b-a)*(∫ t in a..b, (q t)^2) := by
  have hbound (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
      ‖f y-f x‖ ≤ ∫ t in a..b, q t := by
    apply (norm_sub_le_integral_of_norm_deriv_le_of_le hxy hf.continuous.continuousOn
      (hf.differentiable (by simp)).differentiableOn (.of_forall (fun t _ => hb t))
      (hq.intervalIntegrable x y)).trans
    exact intervalIntegral.integral_mono_interval hx.1 hxy hy.2 (.of_forall hp)
      (hq.intervalIntegrable a b)
  have h : ‖f x-f y‖ ≤ ∫ t in a..b, q t := by
    rcases le_total x y with hxy | hyx
    · rw [norm_sub_rev]; exact hbound x y hx hy hxy
    · exact hbound y x hy hx hyx
  have hn : 0 ≤ ∫ t in a..b, q t := intervalIntegral.integral_nonneg hab.le (fun t _ => hp t)
  exact ((sq_le_sq₀ (norm_nonneg _) hn).mpr h).trans (integral_sq_cauchy hq hab)

lemma continuous_line_integral {q : ℝ × ℝ → ℝ} (hq : Continuous q) (a b : ℝ) :
    Continuous (fun x => ∫ y in Icc a b, q (x,y)) :=
  continuous_parametric_integral_of_continuous (f:=fun x y => q (x,y)) hq isCompact_Icc

lemma exists_line_below_average {f : ℝ → ℝ} (hf : Continuous f) {a b E : ℝ}
    (hab : a < b) (hE : (∫ x in Icc a b, f x) ≤ E) :
    ∃ x ∈ Icc a b, f x ≤ E/(b-a) := by
  obtain ⟨x,hx,hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a,left_mem_Icc.mpr hab.le⟩ hf.continuousOn
  refine ⟨x,hx,(le_div_iff₀ (sub_pos.mpr hab)).mpr ?_⟩
  have hm : (b-a)*f x ≤ ∫ t in Icc a b, f t := by
    calc
      _ = ∫ _t in Icc a b, f x := by simp [Real.volume_real_Icc,hab.le,smul_eq_mul]
      _ ≤ _ := setIntegral_mono_on (integrableOn_const isCompact_Icc.measure_ne_top)
        (hf.continuousOn.integrableOn_compact isCompact_Icc) measurableSet_Icc (fun t ht => hmin ht)
  linarith

lemma rectangle_fubini {q : ℝ × ℝ → ℝ} (hq : Continuous q) (a b : ℝ) :
    (∫ p in Icc a b ×ˢ Icc a b, q p) = ∫ x in Icc a b, ∫ y in Icc a b, q (x,y) := by
  have hi : IntegrableOn q (Icc a b ×ˢ Icc a b) volume :=
    hq.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.volume_eq_prod] at hi ⊢
  exact setIntegral_prod q hi

lemma rectangle_fubini_swap {q : ℝ × ℝ → ℝ} (hq : Continuous q) (a b : ℝ) :
    (∫ p in Icc a b ×ˢ Icc a b, q p) = ∫ y in Icc a b, ∫ x in Icc a b, q (x,y) := by
  rw [rectangle_fubini hq]
  have hi : IntegrableOn q (Icc a b ×ˢ Icc a b) volume :=
    hq.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.volume_eq_prod] at hi
  change Integrable q ((volume.prod volume).restrict (Icc a b ×ˢ Icc a b)) at hi
  rw [← Measure.prod_restrict (Icc a b) (Icc a b)] at hi
  exact integral_integral_swap hi

lemma vertical_slice_energy {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    {a b x y y' : ℝ} (hab : a < b) (hy : y ∈ Icc a b) (hy' : y' ∈ Icc a b) :
    ‖u (x,y)-u (x,y')‖^2 ≤ (b-a)*(∫ t in Icc a b, ‖fderiv ℝ u (x,t)‖^2) := by
  have hf : ContDiff ℝ 1 (fun t : ℝ => u (x,t)) := hu.comp (contDiff_const.prodMk contDiff_id)
  have hq : Continuous (fun t : ℝ => ‖fderiv ℝ u (x,t)‖) :=
    ((hu.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_id)).norm
  have hd (t : ℝ) : ‖deriv (fun s : ℝ => u (x,s)) t‖ ≤ ‖fderiv ℝ u (x,t)‖ := by
    have hs : HasDerivAt (fun s : ℝ => (x,s)) (0,1) t :=
      (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
    have H := (hu.differentiable (by simp) (x,t)).hasFDerivAt.comp_hasDerivAt t hs
    simp only [Function.comp_def] at H
    rw [H.deriv]
    simpa using ContinuousLinearMap.le_opNorm (fderiv ℝ u (x,t)) (0,1)
  have H := line_energy_bound hf hq (fun t => norm_nonneg _) hd hab hy hy'
  rw [intervalIntegral.integral_of_le hab.le,← integral_Icc_eq_integral_Ioc] at H
  exact H

lemma horizontal_slice_energy {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    {a b x x' y : ℝ} (hab : a < b) (hx : x ∈ Icc a b) (hx' : x' ∈ Icc a b) :
    ‖u (x,y)-u (x',y)‖^2 ≤ (b-a)*(∫ t in Icc a b, ‖fderiv ℝ u (t,y)‖^2) := by
  have hf : ContDiff ℝ 1 (fun t : ℝ => u (t,y)) := hu.comp (contDiff_id.prodMk contDiff_const)
  have hq : Continuous (fun t : ℝ => ‖fderiv ℝ u (t,y)‖) :=
    ((hu.continuous_fderiv (by simp)).comp (continuous_id.prodMk continuous_const)).norm
  have hd (t : ℝ) : ‖deriv (fun s : ℝ => u (s,y)) t‖ ≤ ‖fderiv ℝ u (t,y)‖ := by
    have hs : HasDerivAt (fun s : ℝ => (s,y)) (1,0) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    have H := (hu.differentiable (by simp) (t,y)).hasFDerivAt.comp_hasDerivAt t hs
    simp only [Function.comp_def] at H
    rw [H.deriv]
    simpa using ContinuousLinearMap.le_opNorm (fderiv ℝ u (t,y)) (1,0)
  have H := line_energy_bound hf hq (fun t => norm_nonneg _) hd hab hx hx'
  rw [intervalIntegral.integral_of_le hab.le,← integral_Icc_eq_integral_Ioc] at H
  exact H

lemma norm_sq_triangle (a b c : ℝ) : ‖a-c‖^2 ≤ 2*‖a-b‖^2+2*‖b-c‖^2 := by
  have h := norm_sub_le_norm_sub_add_norm_sub a b c
  have hsq := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  nlinarith [sq_nonneg (‖a-b‖-‖b-c‖)]

theorem rectangle_capacity_bound {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    {A B δ : ℝ} (hAB : A < B) (hδ : 0 < δ)
    (h0 : RectCrossing u 0 A B δ) (h1 : RectCrossing u 1 A B δ) :
    1 ≤ 8*((B-A)/δ+1)*(∫ p in Icc A B ×ˢ Icc A B, ‖fderiv ℝ u p‖^2) := by
  let q (p : ℝ × ℝ) := ‖fderiv ℝ u p‖^2
  let E := ∫ p in Icc A B ×ˢ Icc A B, q p
  let V (x : ℝ) := ∫ y in Icc A B, q (x,y)
  let H (y : ℝ) := ∫ x in Icc A B, q (x,y)
  have hq : Continuous q := (hu.continuous_fderiv (by simp)).norm.pow 2
  have hV : Continuous V := continuous_line_integral hq A B
  have hH : Continuous H := continuous_line_integral (hq.comp continuous_swap) A B
  have hqp (p : ℝ × ℝ) : 0 ≤ q p := sq_nonneg _
  have hVp (x : ℝ) : 0 ≤ V x := integral_nonneg (fun y => hqp _)
  have hHp (y : ℝ) : 0 ≤ H y := integral_nonneg (fun x => hqp _)
  have hEp : 0 ≤ E := integral_nonneg hqp
  have hEV : (∫ x in Icc A B, V x)=E := (rectangle_fubini hq A B).symm
  have hEH : (∫ y in Icc A B, H y)=E := (rectangle_fubini_swap hq A B).symm
  obtain ⟨x,hx,hxE⟩ := exists_line_below_average hV hAB hEV.le
  obtain ⟨y,hy,hyE⟩ := exists_line_below_average hH hAB hEH.le
  have hcross (c : ℝ) (hc : RectCrossing u c A B δ) :
      ‖u (x,y)-c‖^2 ≤ 2*((B-A)/δ+1)*E := by
    obtain ⟨a,b,ha,hb,hspan,hcross⟩ := hc
    have hab : a < b := by linarith
    have hsub : Icc a b ⊆ Icc A B := Icc_subset_Icc ha.1 hb.2
    rcases hcross with hvertical | hhorizontal
    · have hint : (∫ t in Icc a b, V t) ≤ E := by
        rw [← hEV]
        exact setIntegral_mono_set (hV.continuousOn.integrableOn_compact isCompact_Icc)
          (.of_forall hVp) (.of_forall hsub)
      obtain ⟨t,ht,htE⟩ := exists_line_below_average hV hab hint
      have htE' : V t ≤ E/δ := htE.trans (div_le_div_of_nonneg_left hEp hδ hspan)
      obtain ⟨s,hs,heq⟩ := hvertical t ht
      have hv := vertical_slice_energy hu hAB hy hs (x:=t)
      have hh := horizontal_slice_energy hu hAB hx (hsub ht) (y:=y)
      have htri := norm_sq_triangle (u (x,y)) (u (t,y)) (u (t,s))
      rw [heq] at htri hv
      change ‖u (t,y)-c‖^2 ≤ (B-A)*V t at hv
      change ‖u (x,y)-u (t,y)‖^2 ≤ (B-A)*H y at hh
      have hv' := hv.trans (mul_le_mul_of_nonneg_left htE' (sub_pos.mpr hAB).le)
      have hh' := hh.trans (mul_le_mul_of_nonneg_left hyE (sub_pos.mpr hAB).le)
      rw [mul_div_cancel₀ _ (sub_pos.mpr hAB).ne'] at hh'
      have hid : (B-A)*(E/δ)=((B-A)/δ)*E := by ring
      rw [hid] at hv'
      nlinarith
    · have hint : (∫ t in Icc a b, H t) ≤ E := by
        rw [← hEH]
        exact setIntegral_mono_set (hH.continuousOn.integrableOn_compact isCompact_Icc)
          (.of_forall hHp) (.of_forall hsub)
      obtain ⟨t,ht,htE⟩ := exists_line_below_average hH hab hint
      have htE' : H t ≤ E/δ := htE.trans (div_le_div_of_nonneg_left hEp hδ hspan)
      obtain ⟨s,hs,heq⟩ := hhorizontal t ht
      have hv := vertical_slice_energy hu hAB hy (hsub ht) (x:=x)
      have hh := horizontal_slice_energy hu hAB hx hs (y:=t)
      have htri := norm_sq_triangle (u (x,y)) (u (x,t)) (u (s,t))
      rw [heq] at htri hh
      change ‖u (x,y)-u (x,t)‖^2 ≤ (B-A)*V x at hv
      change ‖u (x,t)-c‖^2 ≤ (B-A)*H t at hh
      have hv' := hv.trans (mul_le_mul_of_nonneg_left hxE (sub_pos.mpr hAB).le)
      have hh' := hh.trans (mul_le_mul_of_nonneg_left htE' (sub_pos.mpr hAB).le)
      rw [mul_div_cancel₀ _ (sub_pos.mpr hAB).ne'] at hv'
      have hid : (B-A)*(E/δ)=((B-A)/δ)*E := by ring
      rw [hid] at hh'
      nlinarith
  have H0 := hcross 0 h0
  have H1 := hcross 1 h1
  have ht := norm_sq_triangle (0:ℝ) (u (x,y)) 1
  simp only [zero_sub,norm_neg,norm_one,one_pow] at ht
  simp only [sub_zero] at H0
  change 1 ≤ 8*((B-A)/δ+1)*E
  nlinarith

lemma preconnected_rectCrossing {u : ℝ × ℝ → ℝ} {c : ℝ}
    {E : Set (ℝ × ℝ)} (hEc : IsPreconnected E) {A B δ : ℝ}
    (hbox : E ⊆ Icc A B ×ˢ Icc A B) (hu : ∀ p ∈ E, u p=c)
    {p q : ℝ × ℝ} (hp : p ∈ E) (hq : q ∈ E) (hd : δ ≤ dist p q) :
    RectCrossing u c A B δ := by
  have hpB := hbox hp
  have hqB := hbox hq
  have hd' : δ ≤ dist p.1 q.1 ∨ δ ≤ dist p.2 q.2 := by
    simpa only [Prod.dist_eq,le_max_iff] using hd
  have hcases (f : ℝ × ℝ → ℝ) (hf : Continuous f) (hfB : ∀ r ∈ E, f r ∈ Icc A B)
      (hh : δ ≤ dist (f p) (f q)) :
      ∃ a b : ℝ, a ∈ Icc A B ∧ b ∈ Icc A B ∧ δ ≤ b-a ∧
        (∀ t ∈ Icc a b, ∃ r ∈ E, f r=t) := by
    rw [Real.dist_eq] at hh
    rcases le_total (f p) (f q) with hle | hle
    · refine ⟨f p,f q,hfB p hp,hfB q hq,?_,?_⟩
      · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hh
        linarith
      · intro t ht
        exact hEc.intermediate_value hp hq hf.continuousOn ht
    · refine ⟨f q,f p,hfB q hq,hfB p hp,?_,?_⟩
      · simpa only [abs_of_nonneg (sub_nonneg.mpr hle)] using hh
      · intro t ht
        exact hEc.intermediate_value hq hp hf.continuousOn ht
  rcases hd' with hdx | hdy
  · obtain ⟨a,b,ha,hb,hab,hfill⟩ := hcases Prod.fst continuous_fst (fun r hr => (hbox hr).1) hdx
    refine ⟨a,b,ha,hb,hab,Or.inl ?_⟩
    intro t ht
    obtain ⟨r,hr,heq⟩ := hfill t ht
    refine ⟨r.2,(hbox hr).2,?_⟩
    rw [← heq]
    exact hu r hr
  · obtain ⟨a,b,ha,hb,hab,hfill⟩ := hcases Prod.snd continuous_snd (fun r hr => (hbox hr).2) hdy
    refine ⟨a,b,ha,hb,hab,Or.inr ?_⟩
    intro t ht
    obtain ⟨r,hr,heq⟩ := hfill t ht
    refine ⟨r.1,(hbox hr).1,?_⟩
    rw [← heq]
    exact hu r hr

theorem continuum_capacity_bound {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    {E F : Set (ℝ × ℝ)} (hEc : IsPreconnected E) (hFc : IsPreconnected F)
    {A B δ : ℝ} (hAB : A < B) (hδ : 0 < δ)
    (hEB : E ⊆ Icc A B ×ˢ Icc A B) (hFB : F ⊆ Icc A B ×ˢ Icc A B)
    (hE : ∀ p ∈ E, u p=0) (hF : ∀ p ∈ F, u p=1)
    (hdE : ∃ p ∈ E, ∃ q ∈ E, δ ≤ dist p q)
    (hdF : ∃ p ∈ F, ∃ q ∈ F, δ ≤ dist p q) :
    1 ≤ 8*((B-A)/δ+1)*(∫ p in Icc A B ×ˢ Icc A B, ‖fderiv ℝ u p‖^2) := by
  obtain ⟨p,hp,q,hq,hd⟩ := hdE
  obtain ⟨r,hr,s,hs,hd'⟩ := hdF
  exact rectangle_capacity_bound hu hAB hδ
    (preconnected_rectCrossing hEc hEB hE hp hq hd)
    (preconnected_rectCrossing hFc hFB hF hr hs hd')

end CannonRealPlane

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
-- module Solutions.OAIQ046_CN.Cannon_Topology_PlaneBox
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

namespace CannonPlane
open Set Metric MeasureTheory

lemma realProd_to_complex_norm (p : ℝ × ℝ) :
    ‖Complex.equivRealProdCLM.symm p‖ ≤ 2*‖p‖ := by
  rw [Complex.equivRealProdCLM_symm_apply]
  calc
    _ ≤ ‖(p.1:ℂ)‖+‖(p.2:ℂ)*Complex.I‖ := norm_add_le _ _
    _ = ‖p.1‖+‖p.2‖ := by simp
    _ ≤ 2*‖p‖ := by have h1 := norm_fst_le p; have h2 := norm_snd_le p; linarith

lemma realProd_to_complex_opNorm : ‖(Complex.equivRealProdCLM.symm : (ℝ × ℝ) →L[ℝ] ℂ)‖ ≤ 2 := by
  exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) realProd_to_complex_norm

lemma planeBox_compact (R : ℝ) : IsCompact (planeBox R) :=
  Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr (isCompact_Icc.prod isCompact_Icc)

lemma closedBall_subset_planeBox (R : ℝ) : closedBall (0:ℂ) R ⊆ planeBox R := by
  intro z hz
  have hz' : ‖z‖ ≤ R := by simpa using hz
  have hr := Complex.abs_re_le_norm z |>.trans hz'
  have hi := Complex.abs_im_le_norm z |>.trans hz'
  exact ⟨abs_le.mp hr,abs_le.mp hi⟩

lemma coordinate_energy_bound (u : ℂ → ℝ) (hu : ContDiff ℝ 1 u) (R : ℝ) :
    (∫ p in Icc (-R) R ×ˢ Icc (-R) R, ‖fderiv ℝ (u ∘ Complex.equivRealProdCLM.symm) p‖^2) ≤
      4*(∫ z in planeBox R, ‖fderiv ℝ u z‖^2) := by
  let e := Complex.equivRealProdCLM.symm
  let S := Icc (-R) R ×ˢ Icc (-R) R
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hcomp : ContDiff ℝ 1 (u ∘ e) := hu.comp e.contDiff
  have hq : Continuous (fun p => ‖fderiv ℝ u (e p)‖^2) :=
    ((hu.continuous_fderiv (by simp)).comp e.continuous).norm.pow 2
  have hchange : (∫ z in planeBox R, ‖fderiv ℝ u z‖^2) =
      ∫ p in S, ‖fderiv ℝ u (e p)‖^2 := by
    have H := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding (fun p => ‖fderiv ℝ u (e p)‖^2) S
    simpa only [Complex.measurableEquivRealProd,Homeomorph.toMeasurableEquiv_coe,
      ContinuousLinearEquiv.coe_toHomeomorph,ContinuousLinearEquiv.symm_apply_apply,e,planeBox] using H
  rw [hchange,← integral_const_mul]
  apply setIntegral_mono_on
    ((hcomp.continuous_fderiv (by simp)).norm.pow 2 |>.continuousOn.integrableOn_compact hS)
    ((hq.const_mul 4).continuousOn.integrableOn_compact hS) hS.measurableSet
  intro p hp
  change ‖fderiv ℝ (u ∘ e) p‖^2 ≤ 4*‖fderiv ℝ u (e p)‖^2
  rw [fderiv_comp p (hu.differentiable (by simp) (e p)) e.differentiableAt,e.fderiv]
  have hc := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ u (e p)) e.toContinuousLinearMap
  have hn := hc.trans (mul_le_mul_of_nonneg_left realProd_to_complex_opNorm (norm_nonneg _))
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖fderiv ℝ u (e p)‖*2)).mpr hn
  nlinarith

theorem plane_continuum_capacity (u : ℂ → ℝ) (hu : ContDiff ℝ 1 u)
    {E F : Set ℂ} (hEc : IsPreconnected E) (hFc : IsPreconnected F)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hEB : E ⊆ closedBall 0 R) (hFB : F ⊆ closedBall 0 R)
    (hE : ∀ z ∈ E, u z=0) (hF : ∀ z ∈ F, u z=1)
    (hdE : ∃ p ∈ E, ∃ q ∈ E, δ ≤ dist p q)
    (hdF : ∃ p ∈ F, ∃ q ∈ F, δ ≤ dist p q) :
    1 ≤ 32*(4*R/δ+1)*(∫ z in planeBox R, ‖fderiv ℝ u z‖^2) := by
  let e := Complex.equivRealProdCLM
  have hwide (T : Set ℂ) (hT : ∃ p ∈ T, ∃ q ∈ T, δ ≤ dist p q) :
      ∃ p ∈ e '' T, ∃ q ∈ e '' T, δ/2 ≤ dist p q := by
    obtain ⟨p,hp,q,hq,hd⟩ := hT
    refine ⟨e p,⟨p,hp,rfl⟩,e q,⟨q,hq,rfl⟩,?_⟩
    have hh := realProd_to_complex_norm (e p-e q)
    rw [map_sub,e.symm_apply_apply,e.symm_apply_apply] at hh
    rw [dist_eq_norm] at hd ⊢
    linarith
  have hbox (T : Set ℂ) (hT : T ⊆ closedBall 0 R) :
      e '' T ⊆ Icc (-R) R ×ˢ Icc (-R) R := by
    rintro p ⟨z,hz,rfl⟩
    exact closedBall_subset_planeBox R (hT hz)
  have H := CannonRealPlane.continuum_capacity_bound (hu.comp e.symm.contDiff)
    (hEc.image e e.continuous.continuousOn) (hFc.image e e.continuous.continuousOn)
    (by linarith : -R < R) (by positivity : 0 < δ/2) (hbox E hEB) (hbox F hFB)
    (by rintro p ⟨z,hz,rfl⟩; simpa only [Function.comp_apply,e.symm_apply_apply] using hE z hz)
    (by rintro p ⟨z,hz,rfl⟩; simpa only [Function.comp_apply,e.symm_apply_apply] using hF z hz)
    (hwide E hdE) (hwide F hdF)
  have henergy := coordinate_energy_bound u hu R
  have hC : 0 ≤ 8*((R- -R)/(δ/2)+1) := by
    have : 0 ≤ R- -R := by linarith
    positivity
  have hh := mul_le_mul_of_nonneg_left henergy hC
  have hid : 8*((R- -R)/(δ/2)+1)*4=32*(4*R/δ+1) := by ring
  rw [← mul_assoc,hid] at hh
  exact H.trans hh

end CannonPlane

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace CannonPlane

lemma smoothTransition_deriv_zero {t : ℝ} (ht : t < 0 ∨ 1 < t) :
    deriv Real.smoothTransition t=0 := by
  rcases ht with ht | ht
  · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [isOpen_Iio.mem_nhds ht] with x hx
      exact Real.smoothTransition.zero_of_nonpos hx.le
    simpa only [deriv_const] using he.deriv_eq
  · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
      exact Real.smoothTransition.one_of_one_le hx.le
    simpa only [deriv_const] using he.deriv_eq

lemma smoothTransition_deriv_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ t, |deriv Real.smoothTransition t| ≤ C := by
  have hc : Continuous (fun t => |deriv Real.smoothTransition t|) :=
    (Real.smoothTransition.contDiff (n:=1) |>.continuous_deriv (by simp)).abs
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).bddAbove_image hc.continuousOn
  refine ⟨max C 1,le_max_right _ _,?_⟩
  intro t
  by_cases ht : t ∈ Icc (0:ℝ) 1
  · exact (hC ⟨t,ht,rfl⟩).trans (le_max_left _ _)
  · have ht' : t < 0 ∨ 1 < t := by simpa only [mem_Icc,not_and_or,not_le] using ht
    rw [smoothTransition_deriv_zero ht',abs_zero]
    exact le_trans zero_le_one (le_max_right _ _)

lemma annularCutoff_inner {r R : ℝ} (hr : 0 < r) (hrR : r < R) {z : ℂ} (hz : ‖z‖ ≤ r) :
    annularCutoff r R z=0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hL : 0 < Real.log (R/r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  apply div_nonpos_of_nonpos_of_nonneg _ hL.le
  exact Real.log_nonpos (div_nonneg (norm_nonneg _) hr.le) ((div_le_one hr).mpr hz)

lemma annularCutoff_outer {r R : ℝ} (hr : 0 < r) (hrR : r < R) {z : ℂ} (hz : R ≤ ‖z‖) :
    annularCutoff r R z=1 := by
  apply Real.smoothTransition.one_of_one_le
  have hL : 0 < Real.log (R/r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  apply (one_le_div hL).mpr
  exact Real.log_le_log (div_pos (hr.trans hrR) hr) (div_le_div_of_nonneg_right hz hr.le)

lemma annularCutoff_contDiff {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ContDiff ℝ ∞ (annularCutoff r R) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z=0
  · subst z
    have he : annularCutoff r R =ᶠ[𝓝 (0:ℂ)] fun _ => (0:ℝ) := by
      filter_upwards [Metric.ball_mem_nhds (0:ℂ) hr] with z hz
      apply annularCutoff_inner hr hrR
      exact (show ‖z‖ < r by simpa only [mem_ball,dist_zero_right] using hz).le
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact Real.smoothTransition.contDiffAt.comp z
      (((contDiffAt_id.norm ℝ hz).div_const r).log (div_ne_zero (norm_ne_zero_iff.mpr hz) hr.ne') |>.div_const _)

lemma annularCutoff_fderiv_zero_inner {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {z : ℂ} (hz : ‖z‖ < r) : fderiv ℝ (annularCutoff r R) z=0 := by
  have he : annularCutoff r R =ᶠ[𝓝 z] fun _ => (0:ℝ) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
    exact annularCutoff_inner hr hrR hw.le
  simpa only [fderiv_const_apply] using he.fderiv_eq (𝕜:=ℝ)

lemma annularCutoff_fderiv_zero_outer {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {z : ℂ} (hz : R < ‖z‖) : fderiv ℝ (annularCutoff r R) z=0 := by
  have he : annularCutoff r R =ᶠ[𝓝 z] fun _ => (1:ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    exact annularCutoff_outer hr hrR hw.le
  simpa only [fderiv_const_apply] using he.fderiv_eq (𝕜:=ℝ)

lemma annularCutoff_fderiv_bound {r R C : ℝ} (hr : 0 < r) (hrR : r < R)
    (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C) {z : ℂ} (hz : z ≠ 0) :
    ‖fderiv ℝ (annularCutoff r R) z‖ ≤ C/(Real.log (R/r)*‖z‖) := by
  let L := Real.log (R/r)
  have hL : 0 < L := Real.log_pos ((one_lt_div hr).mpr hrR)
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hn : DifferentiableAt ℝ (fun w : ℂ => ‖w‖) z :=
    (contDiffAt_id.norm ℝ hz : ContDiffAt ℝ 1 (fun w : ℂ => ‖w‖) z).differentiableAt (by simp)
  have hdiv : HasFDerivAt (fun w : ℂ => ‖w‖/r) (r⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) z) z := by
    simpa only [Pi.smul_def,smul_eq_mul,div_eq_mul_inv,mul_comm] using hn.hasFDerivAt.const_smul r⁻¹
  have hlog := (Real.hasDerivAt_log (div_ne_zero hzn.ne' hr.ne')).comp_hasFDerivAt z hdiv
  have hscale : HasFDerivAt (fun w : ℂ => Real.log (‖w‖/r)/L)
      (L⁻¹ • ((‖z‖/r)⁻¹ • (r⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) z))) z := by
    simpa only [Function.comp_def,Pi.smul_def,smul_eq_mul,div_eq_mul_inv,mul_comm] using hlog.const_smul L⁻¹
  have ht := (Real.smoothTransition.contDiff (n:=1) |>.differentiable (by simp) (Real.log (‖z‖/r)/L)).hasDerivAt
  have hd := ht.comp_hasFDerivAt z hscale
  change HasFDerivAt (annularCutoff r R) _ z at hd
  rw [hd.fderiv]
  simp only [norm_smul,Real.norm_eq_abs]
  rw [norm_fderiv_norm hn]
  simp only [abs_inv,abs_of_pos hr,abs_of_pos hL,abs_of_pos (div_pos hzn hr)]
  calc
    _ = |deriv Real.smoothTransition (Real.log (‖z‖/r)/L)|/(L*‖z‖) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (hC _) (mul_pos hL hzn).le

end CannonPlane

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
-- module Solutions.OAIQ046_CN.Cannon_Modulus_AnnularCutoffEnergy
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

namespace CannonPlane
open Complex

theorem annularCutoff_energy {r R C : ℝ} (hr : 0 < r) (hrR : 2*r ≤ R)
    (hC0 : 0 ≤ C) (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C) :
    (∫ z in closedBall (0:ℂ) R, ‖fderiv ℝ (annularCutoff r R) z‖^2) ≤
      4*Real.pi*C^2/Real.log (R/r) := by
  have hrR' : r < R := by linarith
  let L := Real.log (R/r)
  have hL : 0 < L := Real.log_pos ((one_lt_div hr).mpr hrR')
  let q (z : ℂ) := ‖fderiv ℝ (annularCutoff r R) z‖^2
  have hq : Continuous q := ((annularCutoff_contDiff hr hrR').continuous_fderiv (by simp)).norm.pow 2
  let e (ρ : ℝ) := ρ*(∫ t in (-Real.pi)..Real.pi, q (circleMap 0 ρ t))
  have he : Continuous e := continuous_id.mul (continuous_circle_integral hq 0)
  have hzero (ρ : ℝ) (hρ : ρ ∈ Icc 0 (r/2)) : e ρ=0 := by
    dsimp only [e]
    have heq : (∫ t in (-Real.pi)..Real.pi, q (circleMap 0 ρ t))=0 := by
      apply (intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_).trans intervalIntegral.integral_zero
      intro _ _
      dsimp only [q]
      rw [annularCutoff_fderiv_zero_inner hr hrR']
      · simp
      · rw [norm_circleMap_zero,abs_of_nonneg hρ.1]
        linarith [hρ.2]
    rw [heq,mul_zero]
  have hsmall : (∫ ρ in (0:ℝ)..(r/2), e ρ)=0 := by
    apply (intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_).trans intervalIntegral.integral_zero
    intro ρ hρ
    rw [uIcc_of_le (by positivity)] at hρ
    exact hzero ρ hρ
  have hbound (ρ : ℝ) (hρ : 0 < ρ) :
      e ρ ≤ (2*Real.pi*C^2/L^2)*ρ⁻¹ := by
    have hang : (∫ t in (-Real.pi)..Real.pi, q (circleMap 0 ρ t)) ≤
        (2*Real.pi)*(C/(L*ρ))^2 := by
      calc
        _ ≤ ∫ _t in (-Real.pi)..Real.pi, (C/(L*ρ))^2 := by
          apply intervalIntegral.integral_mono_on (neg_le_self Real.pi_pos.le)
            ((hq.comp (continuous_circleMap 0 ρ)).intervalIntegrable _ _) intervalIntegrable_const
          intro angle _
          have hn : ‖circleMap 0 ρ angle‖=ρ := by rw [norm_circleMap_zero,abs_of_pos hρ]
          have hz : circleMap 0 ρ angle ≠ 0 := norm_pos_iff.mp (by rw [hn]; exact hρ)
          have hh := annularCutoff_fderiv_bound hr hrR' hC hz
          rw [hn] at hh
          exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg hC0 (mul_pos hL hρ).le)).mpr hh
        _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring
    have hh := mul_le_mul_of_nonneg_left hang hρ.le
    have hid : ρ*((2*Real.pi)*(C/(L*ρ))^2)=(2*Real.pi*C^2/L^2)*ρ⁻¹ := by field_simp
    exact hh.trans_eq hid
  have hInv : IntervalIntegrable (fun ρ : ℝ => ρ⁻¹) volume (r/2) R :=
    ContinuousOn.intervalIntegrable (continuousOn_id.inv₀ (by
      intro x hx
      rw [uIcc_of_le (by linarith)] at hx
      change x ≠ 0
      intro hx0
      linarith [hx.1]))
  have hi := intervalIntegral.integral_mono_on (show r/2 ≤ R by linarith)
    (he.intervalIntegrable _ _) (hInv.const_mul (2*Real.pi*C^2/L^2))
    (fun ρ hρ => hbound ρ (by linarith [hρ.1]))
  rw [intervalIntegral.integral_const_mul,integral_inv_of_pos (by positivity) (by linarith)] at hi
  have hlog : Real.log (R/(r/2)) ≤ 2*L := by
    have h2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) ((le_div_iff₀ hr).mpr hrR)
    have hid : R/(r/2)=(R/r)*2 := by ring
    rw [hid,Real.log_mul (div_ne_zero (by linarith) hr.ne') (by norm_num)]
    dsimp only [L] at h2 ⊢
    linarith
  have hi' := hi.trans (mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2*Real.pi*C^2/L^2))
  have hid : (2*Real.pi*C^2/L^2)*(2*L)=4*Real.pi*C^2/L := by field_simp; ring
  rw [hid] at hi'
  rw [disk_polar_integral hq 0 (by linarith)]
  change (∫ ρ in (0:ℝ)..R, e ρ) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (he.intervalIntegrable 0 (r/2))
    (he.intervalIntegrable (r/2) R),hsmall,zero_add]
  exact hi'

end CannonPlane

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
-- module Solutions.OAIQ046_CN.Cannon_Modulus_AnnularCutoffEnergy2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

namespace CannonPlane

lemma annularCutoff_energy_on {r R C : ℝ} (hr : 0 < r) (hrR : 2*r ≤ R)
    (hC0 : 0 ≤ C) (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C) (S : Set ℂ) :
    (∫ z in S, ‖fderiv ℝ (annularCutoff r R) z‖^2) ≤
      4*Real.pi*C^2/Real.log (R/r) := by
  let q (z : ℂ) := ‖fderiv ℝ (annularCutoff r R) z‖^2
  have hrR' : r < R := by linarith
  have hq : Continuous q := ((annularCutoff_contDiff hr hrR').continuous_fderiv (by simp)).norm.pow 2
  have hz (z : ℂ) (hz : z ∉ closedBall (0:ℂ) R) : q z=0 := by
    have hzn : R < ‖z‖ := by simpa using hz
    dsimp only [q]
    rw [annularCutoff_fderiv_zero_outer hr hrR' hzn]
    simp
  have hc : HasCompactSupport q := HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0:ℂ) R) (Function.support_subset_iff'.mpr hz)
  have hi := hq.integrable_of_hasCompactSupport hc (μ:=volume)
  have hg : (∫ z in closedBall (0:ℂ) R, q z) = ∫ z, q z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hz
  have hp : 0 ≤ᵐ[volume] q := .of_forall (fun z => sq_nonneg _)
  calc
    _ ≤ ∫ z, q z := setIntegral_le_integral hi hp
    _ = ∫ z in closedBall (0:ℂ) R, q z := hg.symm
    _ ≤ _ := annularCutoff_energy hr hrR hC0 hC

theorem annular_condenser_bound (F : ℂ ≃ₜ ℂ)
    (hF : ContDiff ℝ 1 (F.symm : ℂ → ℂ)) {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F.symm : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F.symm : ℂ → ℂ) z).det|)
    {r R C S δ : ℝ} (hr : 0 < r) (hrR : 2*r ≤ R)
    (hC0 : 0 ≤ C) (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C)
    (hS : 0 < S) (hδ : 0 < δ)
    {E G : Set ℂ} (hEc : IsPreconnected E) (hGc : IsPreconnected G)
    (hEB : E ⊆ closedBall 0 S) (hGB : G ⊆ closedBall 0 S)
    (hE : ∀ z ∈ E, ‖F.symm z‖ ≤ r) (hG : ∀ z ∈ G, R ≤ ‖F.symm z‖)
    (hdE : ∃ p ∈ E, ∃ q ∈ E, δ ≤ dist p q)
    (hdG : ∃ p ∈ G, ∃ q ∈ G, δ ≤ dist p q) :
    Real.log (R/r) ≤ 128*(4*S/δ+1)*K*Real.pi*C^2 := by
  have hrR' : r < R := by linarith
  have hL : 0 < Real.log (R/r) := Real.log_pos ((one_lt_div hr).mpr hrR')
  let u := annularCutoff r R
  have hu : ContDiff ℝ 1 u := (annularCutoff_contDiff hr hrR').of_le (by simp)
  have hcap := plane_continuum_capacity (u ∘ F.symm) (hu.comp hF) hEc hGc hS hδ hEB hGB
    (fun z hz => annularCutoff_inner hr hrR' (hE z hz))
    (fun z hz => annularCutoff_outer hr hrR' (hG z hz)) hdE hdG
  have htrans := CannonBeltrami.dirichlet_pullback_le F.symm hF u hu
    (planeBox_compact S) hK hD
  have hupper := annularCutoff_energy_on hr hrR hC0 hC (F.symm '' planeBox S)
  have hc : 0 ≤ 32*(4*S/δ+1) := by positivity
  have hh := hcap.trans (mul_le_mul_of_nonneg_left (htrans.trans
    (mul_le_mul_of_nonneg_left hupper hK)) hc)
  have hid : 32*(4*S/δ+1)*(K*(4*Real.pi*C^2/Real.log (R/r))) =
      (128*(4*S/δ+1)*K*Real.pi*C^2)/Real.log (R/r) := by ring
  rw [hid] at hh
  simpa only [one_mul] using (le_div_iff₀ hL).mp hh

end CannonPlane

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
-- module Solutions.OAIQ046_CN.Cannon_Topology_CenteredHomeomorph
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

namespace CannonPlane

lemma segment_isCompact (a b : ℂ) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

lemma segment_isConnected (a b : ℂ) : IsConnected (segment ℝ a b) := by
  rw [segment_eq_image]
  exact (isConnected_Icc (by norm_num : (0:ℝ) ≤ 1)).image _ (by fun_prop)

lemma ray_image_escapes (F : ℂ ≃ₜ ℂ) {b : ℂ} (hb : b ≠ 0) (S : ℝ) :
    ∃ t : ℝ, 1 ≤ t ∧ S < ‖F (t • b)‖ := by
  obtain ⟨M,hM,hbound⟩ := ((isCompact_closedBall (0:ℂ) S).image F.symm.continuous).isBounded.exists_pos_norm_lt
  let t : ℝ := 1+M/‖b‖
  have hb0 : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have ht : 1 ≤ t := by dsimp [t]; linarith [div_nonneg hM.le hb0.le]
  refine ⟨t,ht,?_⟩
  by_contra hn
  have hin : t • b ∈ F.symm '' closedBall (0:ℂ) S := by
    refine ⟨F (t • b),?_,F.symm_apply_apply _⟩
    simpa using le_of_not_gt hn
  have hm := hbound _ hin
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ t)] at hm
  dsimp only [t] at hm
  have hh : (1+M/‖b‖)*‖b‖=‖b‖+M := by field_simp
  rw [hh] at hm
  linarith

lemma norm_ge_of_mem_radial_segment {b z : ℂ} {t : ℝ} (ht : 1 ≤ t)
    (hz : z ∈ segment ℝ b (t • b)) : ‖b‖ ≤ ‖z‖ := by
  obtain ⟨a₁,a₂,ha₁,ha₂,ha,rfl⟩ := hz
  rw [smul_smul,← add_smul,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg ha₁ (mul_nonneg ha₂ (by linarith)))]
  have hc : 1 ≤ a₁+a₂*t := by nlinarith
  nlinarith [norm_nonneg b]

theorem annular_ratio (F : ℂ ≃ₜ ℂ) (hF0 : F 0=0)
    (hF : ContDiff ℝ 1 (F.symm : ℂ → ℂ)) {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F.symm : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F.symm : ℂ → ℂ) z).det|)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C)
    {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : 2*‖a‖ ≤ ‖b‖) :
    Real.log (‖b‖/‖a‖) ≤
      128*(16*‖F b‖/min ‖F a‖ ‖F b‖+1)*K*Real.pi*C^2 := by
  have ha0 : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hAf : F a ≠ 0 := by rw [← hF0]; exact fun h => ha (F.injective h)
  have hBf : F b ≠ 0 := by rw [← hF0]; exact fun h => hb (F.injective h)
  have hA : 0 < ‖F a‖ := norm_pos_iff.mpr hAf
  have hB : 0 < ‖F b‖ := norm_pos_iff.mpr hBf
  let d := min ‖F a‖ ‖F b‖/2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdA : d < ‖F a‖ := by have := min_le_left ‖F a‖ ‖F b‖; dsimp [d]; linarith
  have hdB : d ≤ ‖F b‖ := by have := min_le_right ‖F a‖ ‖F b‖; dsimp [d]; linarith
  let D := F '' segment ℝ (0:ℂ) a
  have hDc : IsCompact D := (segment_isCompact 0 a).image F.continuous
  have hDconn : IsConnected D := (segment_isConnected 0 a).image F F.continuous.continuousOn
  have h0D : (0:ℂ) ∈ D := ⟨0,left_mem_segment ℝ 0 a,hF0⟩
  have hfar : ∃ y ∈ D, d < dist y 0 := ⟨F a,⟨a,right_mem_segment ℝ 0 a,rfl⟩,by simpa using hdA⟩
  obtain ⟨E,hEc,hEconn,hED,h0E,⟨e,heE,he⟩,heB⟩ :=
    CannonContinuum.stop_inside hDc hDconn h0D (by simpa using hd) hfar
  obtain ⟨t,ht,htF⟩ := ray_image_escapes F hb (2*‖F b‖)
  let D' := F '' segment ℝ b (t • b)
  have hD'c : IsCompact D' := (segment_isCompact b (t • b)).image F.continuous
  have hD'conn : IsConnected D' := (segment_isConnected b (t • b)).image F F.continuous.continuousOn
  have hbD' : F b ∈ D' := ⟨b,left_mem_segment ℝ b (t • b),rfl⟩
  have hfar' : ∃ y ∈ D', 2*‖F b‖ < dist y 0 :=
    ⟨F (t • b),⟨t • b,right_mem_segment ℝ b (t • b),rfl⟩,by simpa using htF⟩
  obtain ⟨G,hGc,hGconn,hGD,hbG,⟨g,hgG,hg⟩,hgB⟩ :=
    CannonContinuum.stop_inside hD'c hD'conn hbD' (by simpa using (show ‖F b‖ < 2*‖F b‖ by linarith)) hfar'
  have hEin : ∀ z ∈ E, ‖F.symm z‖ ≤ ‖a‖ := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := hED hz
    rw [F.symm_apply_apply]
    have hh := (convex_closedBall (0:ℂ) ‖a‖).segment_subset
      (mem_closedBall.mpr (by simp)) (mem_closedBall.mpr (by simp)) hw
    simpa using hh
  have hGout : ∀ z ∈ G, ‖b‖ ≤ ‖F.symm z‖ := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := hGD hz
    rw [F.symm_apply_apply]
    exact norm_ge_of_mem_radial_segment ht hw
  have hGwide : d ≤ dist (F b) g := by
    have hh := dist_triangle g (F b) 0
    rw [hg,dist_comm g (F b),dist_zero_right] at hh
    linarith
  have hh := annular_condenser_bound F hF hK hD ha0 hab hC0 hC
    (by positivity : 0 < 2*‖F b‖) hd hEconn.isPreconnected hGconn.isPreconnected
    (fun z hz => mem_closedBall.mpr ((heB z hz).trans (by linarith)))
    (fun z hz => mem_closedBall.mpr (hgB z hz)) hEin hGout
    ⟨0,h0E,e,heE,by rw [dist_comm,he]⟩ ⟨F b,hbG,g,hgG,hGwide⟩
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [d]
  ring

end CannonPlane

namespace CannonPlane

lemma centered_symm_contDiff (F : ℂ ≃ₜ ℂ) (hF : ContDiff ℝ 1 (F.symm : ℂ → ℂ)) (x : ℂ) :
    ContDiff ℝ 1 ((centeredHomeomorph F x).symm : ℂ → ℂ) :=
  (hF.comp (contDiff_id.add contDiff_const)).sub contDiff_const

lemma centered_symm_fderiv (F : ℂ ≃ₜ ℂ) (hF : ContDiff ℝ 1 (F.symm : ℂ → ℂ)) (x z : ℂ) :
    fderiv ℝ ((centeredHomeomorph F x).symm : ℂ → ℂ) z = fderiv ℝ (F.symm : ℂ → ℂ) (z+F x) := by
  have h := ((hF.differentiable (by simp) (z+F x)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).add_const (F x))).sub_const x
  change fderiv ℝ (fun w => F.symm (w+F x)-x) z = _
  simpa only [Function.comp_def,id_eq,ContinuousLinearMap.comp_id] using h.fderiv

theorem annular_ratio_at (F : ℂ ≃ₜ ℂ)
    (hF : ContDiff ℝ 1 (F.symm : ℂ → ℂ)) {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F.symm : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F.symm : ℂ → ℂ) z).det|)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C)
    {x a b : ℂ} (ha : a ≠ x) (hb : b ≠ x) (hab : 2*dist a x ≤ dist b x) :
    Real.log (dist b x/dist a x) ≤
      128*(16*dist (F b) (F x)/min (dist (F a) (F x)) (dist (F b) (F x))+1)*K*Real.pi*C^2 := by
  have h := annular_ratio (centeredHomeomorph F x) (by simp [centeredHomeomorph])
    (centered_symm_contDiff F hF x) hK
    (by intro z; rw [centered_symm_fderiv F hF]; exact hD _)
    hC0 hC (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb)
    (by simpa only [dist_eq_norm] using hab)
  simpa only [centeredHomeomorph_apply,sub_add_cancel,dist_eq_norm] using h

theorem smooth_qc_uniform_shrink {K : ℝ} (hK : 0 ≤ K) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ F : ℂ ≃ₜ ℂ,
      ContDiff ℝ 1 (F.symm : ℂ → ℂ) →
      (∀ z, ‖fderiv ℝ (F.symm : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F.symm : ℂ → ℂ) z).det|) →
      ∀ x a b : ℂ, b ≠ x → dist a x < η*dist b x →
        dist (F a) (F x) < ε*dist (F b) (F x) := by
  intro ε hε
  obtain ⟨C,hC1,hC⟩ := smoothTransition_deriv_bound
  have hC0 : 0 ≤ C := by linarith
  let e := min ε 1
  have he : 0 < e := lt_min hε (by norm_num)
  have heε : e ≤ ε := min_le_left _ _
  have he1 : e ≤ 1 := min_le_right _ _
  let L := 128*(16/e+1)*K*Real.pi*C^2
  let η := min (1/2:ℝ) (Real.exp (-(L+1)))
  have hη : 0 < η := lt_min (by norm_num) (Real.exp_pos _)
  refine ⟨η,hη,?_⟩
  intro F hF hD x a b hb hab
  have hB : 0 < dist (F b) (F x) := dist_pos.mpr (fun hh => hb (F.injective hh))
  by_cases ha : a=x
  · subst a
    simpa only [dist_self] using mul_pos hε hB
  have hr : 0 < dist a x := dist_pos.mpr ha
  have hR : 0 < dist b x := dist_pos.mpr hb
  have h2 : 2*dist a x ≤ dist b x := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left (1/2:ℝ) (Real.exp (-(L+1)))) hR.le
    dsimp only [η] at hab
    nlinarith
  have hlog := annular_ratio_at F hF hK hD hC0 hC ha hb h2
  by_contra hn
  have hn' : ε*dist (F b) (F x) ≤ dist (F a) (F x) := le_of_not_gt hn
  have hmin : e*dist (F b) (F x) ≤ min (dist (F a) (F x)) (dist (F b) (F x)) := by
    apply le_min
    · exact (mul_le_mul_of_nonneg_right heε hB.le).trans hn'
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 hB.le
  have hminpos : 0 < min (dist (F a) (F x)) (dist (F b) (F x)) := (mul_pos he hB).trans_le hmin
  have hdiv : dist (F b) (F x)/min (dist (F a) (F x)) (dist (F b) (F x)) ≤ 1/e := by
    apply (div_le_div_iff₀ hminpos he).mpr
    simpa only [one_mul,mul_comm] using hmin
  have hupper : 128*(16*dist (F b) (F x)/min (dist (F a) (F x)) (dist (F b) (F x))+1)*K*Real.pi*C^2 ≤ L := by
    dsimp only [L]
    have hh : 16*dist (F b) (F x)/min (dist (F a) (F x)) (dist (F b) (F x)) ≤ 16/e := by
      simpa only [div_eq_mul_inv,mul_assoc,one_mul] using mul_le_mul_of_nonneg_left hdiv (by norm_num : (0:ℝ) ≤ 16)
    gcongr
  have hsource : dist a x/dist b x < Real.exp (-(L+1)) := by
    apply (div_lt_iff₀ hR).mpr
    exact hab.trans_le (mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le)
  have hlogsmall := Real.log_lt_log (div_pos hr hR) hsource
  rw [Real.log_exp] at hlogsmall
  have hlogeq : Real.log (dist b x/dist a x) = -Real.log (dist a x/dist b x) := by
    simpa only [inv_div] using Real.log_inv (dist a x/dist b x)
  rw [hlogeq] at hlog
  linarith [hlog.trans hupper]

end CannonPlane

noncomputable section
open Set Metric Filter Topology

namespace CannonPlane

theorem normalized_family_pointwise_bound {ι : Type*} (F : ι → ℂ → ℂ)
    (hF0 : ∀ i, F i 0=0) (hF1 : ∀ i, F i 1=1) (hF : UniformRelativeControl F) :
    ∀ z, ∃ B : ℝ, ∀ i, ‖F i z‖ ≤ B := by
  obtain ⟨η,hη,hηF⟩ := hF 1 (by norm_num)
  let P : Set ℂ := {z | ∃ B : ℝ, ∀ i, ‖F i z‖ ≤ B}
  have h0 : (0:ℂ) ∈ P := ⟨0,fun i => by simp [hF0]⟩
  have hnear {z w : ℂ} (hz : z ≠ 0) (hw : dist w z < η*‖z‖) (hzP : z ∈ P) : w ∈ P := by
    obtain ⟨B,hB⟩ := hzP
    refine ⟨2*B,fun i => ?_⟩
    have hs := hηF i z w 0 hz.symm (by simpa only [dist_zero_left] using hw)
    rw [one_mul,hF0,dist_zero_left] at hs
    have ht := dist_triangle (F i w) (F i z) 0
    simp only [dist_zero_right] at ht
    linarith [hB i]
  have ho : IsOpen P := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    by_cases hz0 : z=0
    · subst z
      refine ⟨η,hη,?_⟩
      intro w hw
      refine ⟨1,fun i => ?_⟩
      have hs := hηF i 0 w 1 (by norm_num) (by simpa using hw)
      simpa only [hF0,hF1,dist_zero_right,norm_one,one_mul] using hs.le
    · exact ⟨η*‖z‖,mul_pos hη (norm_pos_iff.mpr hz0),fun w hw => hnear hz0 hw hz⟩
  have hc : IsClosed P := by
    apply closure_subset_iff_isClosed.mp
    intro z hz
    by_cases hz0 : z=0
    · simpa only [hz0] using h0
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    obtain ⟨w,hwP,hw⟩ := Metric.mem_closure_iff.mp hz
      (min (‖z‖/2) (η*‖z‖/2)) (by positivity)
    have hw1 := hw.trans_le (min_le_left _ _)
    have hw2 := hw.trans_le (min_le_right _ _)
    have ht := dist_triangle z w 0
    simp only [dist_zero_right] at ht
    have hwpos : 0 < ‖w‖ := by linarith
    have hsmall : dist z w < η*‖w‖ := by nlinarith
    exact hnear (norm_pos_iff.mp hwpos) hsmall hwP
  have hall : P=univ := (show IsClopen P from ⟨hc,ho⟩).eq_univ ⟨0,h0⟩
  intro z
  exact (show z ∈ P by rw [hall]; trivial)

theorem relative_control_equicontinuous {ι : Type*} (F : ι → ℂ → ℂ)
    (hF : UniformRelativeControl F) (hb : ∀ z, ∃ B : ℝ, ∀ i, ‖F i z‖ ≤ B) :
    Equicontinuous F := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  let b := x+1
  have hbx : b ≠ x := by simp [b]
  have hdist : 0 < dist b x := dist_pos.mpr hbx
  obtain ⟨A,hA⟩ := hb x
  obtain ⟨B,hB⟩ := hb b
  let L := max (A+B) 0+1
  have hL : 0 < L := by dsimp [L]; positivity
  have hble : A+B ≤ L := by dsimp [L]; linarith [le_max_left (A+B) 0]
  obtain ⟨η,hη,hcontrol⟩ := hF (ε/L) (div_pos hε hL)
  refine ⟨η*dist b x,mul_pos hη hdist,fun y hy i => ?_⟩
  have hh := hcontrol i x y b hbx hy
  have hdf : dist (F i b) (F i x) ≤ L := by
    have ht := dist_triangle (F i b) 0 (F i x)
    simp only [dist_zero_left,dist_zero_right] at ht
    linarith [hA i,hB i]
  have hbound := mul_le_mul_of_nonneg_left hdf (div_pos hε hL).le
  rw [div_mul_cancel₀ ε hL.ne'] at hbound
  rw [dist_comm]
  exact hh.trans_le hbound

end CannonPlane

noncomputable section
open Set Filter Topology Metric

namespace CannonPlane

lemma complex_map_subsequence (f : ℕ → C(ℂ,ℂ))
    (heq : Equicontinuous (fun n z => f n z))
    (hb : ∀ z, ∃ B, ∀ n, ‖f n z‖ ≤ B) :
    ∃ F : C(ℂ,ℂ), ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (f ∘ φ) atTop (𝓝 F) := by
  classical
  have : T2Space (UniformOnFun ℂ ℂ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      apply eq_univ_of_forall
      intro x
      exact mem_sUnion_of_mem (mem_singleton x) isCompact_singleton)
  have hcompact : IsCompact (closure (range f)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun g : C(ℂ,ℂ) => (g : ℂ → ℂ)) (𝔖 := {K | IsCompact K}) (fun _ h => h)
    · exact ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K hK
      have hindex : ∀ g : range f, ∃ n, f n=g.val := fun g => g.property
      choose index hindex using hindex
      have heq' := heq.comp index
      have heq'' : Equicontinuous (fun g : range f => (g.val : ℂ → ℂ)) := by
        convert heq' using 1
        all_goals try with_reducible_and_instances rfl
        funext g x
        exact congrArg (fun h : C(ℂ,ℂ) => h x) (hindex g).symm
      exact heq''.equicontinuousOn K
    · intro K _hK z _hz
      obtain ⟨B,hB⟩ := hb z
      refine ⟨closedBall (0 : ℂ) B,isCompact_closedBall _ _,?_⟩
      rintro g ⟨n,rfl⟩
      simpa only [mem_closedBall,dist_zero_right] using hB n
  obtain ⟨F,_hF,φ,hφ,ht⟩ := hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  exact ⟨F,φ,hφ,ht⟩

theorem pointwise_bounded_homeomorph_subsequence (F : ℕ → ℂ ≃ₜ ℂ)
    (heq : Equicontinuous (fun n z => F n z))
    (heq' : Equicontinuous (fun n z => (F n).symm z))
    (hb : ∀ z, ∃ B, ∀ n, ‖F n z‖ ≤ B)
    (hb' : ∀ z, ∃ B, ∀ n, ‖(F n).symm z‖ ≤ B) :
    ∃ H : ℂ ≃ₜ ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => homeomorphMap (F (φ n))) atTop (𝓝 (homeomorphMap H)) ∧
      Tendsto (fun n => homeomorphMap (F (φ n)).symm) atTop (𝓝 (homeomorphMap H.symm)) := by
  obtain ⟨f,φ,hφ,ht⟩ := complex_map_subsequence (fun n => homeomorphMap (F n)) heq hb
  obtain ⟨g,ψ,hψ,ht'⟩ := complex_map_subsequence (fun n => homeomorphMap (F (φ n)).symm)
    (heq'.comp φ) (by
      intro z
      obtain ⟨B,hB⟩ := hb' z
      exact ⟨B,fun n => hB (φ n)⟩)
  have htF : Tendsto (fun n => homeomorphMap (F (φ (ψ n)))) atTop (𝓝 f) := ht.comp hψ.tendsto_atTop
  have htG : Tendsto (fun n => homeomorphMap (F (φ (ψ n))).symm) atTop (𝓝 g) := ht'
  have hfg (z : ℂ) : f (g z)=z := by
    have hz : Tendsto (fun n => (F (φ (ψ n))).symm z) atTop (𝓝 (g z)) :=
      (continuous_eval_const z).tendsto g |>.comp htG
    have h := continuous_eval.tendsto (f,g z) |>.comp (htF.prodMk_nhds hz)
    have h' : Tendsto (fun _ : ℕ => z) atTop (𝓝 (f (g z))) := by simpa [Function.comp_def,homeomorphMap] using h
    exact tendsto_nhds_unique h' tendsto_const_nhds
  have hgf (z : ℂ) : g (f z)=z := by
    have hz : Tendsto (fun n => F (φ (ψ n)) z) atTop (𝓝 (f z)) :=
      (continuous_eval_const z).tendsto f |>.comp htF
    have h := continuous_eval.tendsto (g,f z) |>.comp (htG.prodMk_nhds hz)
    have h' : Tendsto (fun _ : ℕ => z) atTop (𝓝 (g (f z))) := by simpa [Function.comp_def,homeomorphMap] using h
    exact tendsto_nhds_unique h' tendsto_const_nhds
  let H : ℂ ≃ₜ ℂ := {
    toFun := f
    invFun := g
    left_inv := hgf
    right_inv := hfg
    continuous_toFun := f.continuous
    continuous_invFun := g.continuous }
  exact ⟨H,φ ∘ ψ,hφ.comp hψ,htF,htG⟩

end CannonPlane

namespace CannonPlane

theorem normalized_smooth_qc_subsequence (F : ℕ → ℂ ≃ₜ ℂ)
    (hF0 : ∀ n, F n 0=0) (hF1 : ∀ n, F n 1=1)
    (hF : ∀ n, ContDiff ℝ 1 (F n : ℂ → ℂ))
    (hF' : ∀ n, ContDiff ℝ 1 ((F n).symm : ℂ → ℂ))
    {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ n z, ‖fderiv ℝ (F n : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F n : ℂ → ℂ) z).det|)
    (hD' : ∀ n z, ‖fderiv ℝ ((F n).symm : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ ((F n).symm : ℂ → ℂ) z).det|) :
    ∃ H : ℂ ≃ₜ ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      H 0=0 ∧ H 1=1 ∧
      Tendsto (fun n => homeomorphMap (F (φ n))) atTop (𝓝 (homeomorphMap H)) ∧
      Tendsto (fun n => homeomorphMap (F (φ n)).symm) atTop (𝓝 (homeomorphMap H.symm)) := by
  have hr : UniformRelativeControl (fun n z => F n z) := by
    intro ε hε
    obtain ⟨η,hη,h⟩ := smooth_qc_uniform_shrink hK ε hε
    exact ⟨η,hη,fun n => h (F n) (hF' n) (hD' n)⟩
  have hr' : UniformRelativeControl (fun n z => (F n).symm z) := by
    intro ε hε
    obtain ⟨η,hη,h⟩ := smooth_qc_uniform_shrink hK ε hε
    exact ⟨η,hη,fun n => h (F n).symm (hF n) (hD n)⟩
  have h0' (n) : (F n).symm 0=0 := by apply (F n).injective; simpa using (hF0 n).symm
  have h1' (n) : (F n).symm 1=1 := by apply (F n).injective; simpa using (hF1 n).symm
  have hb := normalized_family_pointwise_bound _ hF0 hF1 hr
  have hb' := normalized_family_pointwise_bound _ h0' h1' hr'
  obtain ⟨H,φ,hφ,ht,ht'⟩ := pointwise_bounded_homeomorph_subsequence F
    (relative_control_equicontinuous _ hr hb) (relative_control_equicontinuous _ hr' hb') hb hb'
  refine ⟨H,φ,hφ,?_,?_,ht,ht'⟩
  · have h := (continuous_eval_const (0:ℂ)).tendsto (homeomorphMap H) |>.comp ht
    have hh : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 (H 0)) := by
      simpa only [Function.comp_def,homeomorphMap,ContinuousMap.coe_mk,hF0] using h
    exact tendsto_nhds_unique hh tendsto_const_nhds
  · have h := (continuous_eval_const (1:ℂ)).tendsto (homeomorphMap H) |>.comp ht
    have hh : Tendsto (fun _ : ℕ => (1:ℂ)) atTop (𝓝 (H 1)) := by
      simpa only [Function.comp_def,homeomorphMap,ContinuousMap.coe_mk,hF1] using h
    exact tendsto_nhds_unique hh tendsto_const_nhds
end CannonPlane

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
-- module Solutions.OAIQ046_CN.Cannon_Topology_EquicontinuousCompactBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

noncomputable section
open Set Filter Topology
open MeasureTheory
open scoped ENNReal

noncomputable section
open Set Metric Filter Topology

namespace CannonPlane

lemma equicontinuous_compact_bound {ι : Type*} (F : ι → ℂ → ℂ)
    (he : Equicontinuous F) (hb : ∀ z, ∃ B : ℝ, ∀ i, ‖F i z‖ ≤ B)
    {S : Set ℂ} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i z, z ∈ S → ‖F i z‖ ≤ B := by
  classical
  have hlocal (z : ℂ) : ∃ r : ℝ, 0 < r ∧ ∀ w, dist w z < r → ∀ i, dist (F i w) (F i z) < 1 := by
    obtain ⟨r,hr,h⟩ := Metric.equicontinuousAt_iff.mp (he z) 1 (by norm_num)
    exact ⟨r,hr,fun w hw i => by simpa only [dist_comm] using h w hw i⟩
  choose r hr hh using hlocal
  choose B hB using hb
  obtain ⟨t,hts,hcover⟩ := hS.elim_nhds_subcover (fun z => ball z (r z))
    (fun z _ => ball_mem_nhds z (hr z))
  refine ⟨∑ z ∈ t, (max (B z) 0+1),Finset.sum_nonneg (fun z _ => by positivity),?_⟩
  intro i w hw
  obtain ⟨z,hzt,hwz⟩ := mem_iUnion₂.mp (hcover hw)
  have hdist := hh z w hwz i
  have htri : ‖F i w‖ ≤ dist (F i w) (F i z)+‖F i z‖ := by
    simpa only [dist_zero_right] using dist_triangle (F i w) (F i z) 0
  have hle : ‖F i w‖ ≤ max (B z) 0+1 := by linarith [hB z i,le_max_left (B z) 0]
  exact hle.trans (Finset.single_le_sum (f:=fun x => max (B x) 0+1) (fun x _ => by positivity) hzt)

end CannonPlane

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
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_Mollifier
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

noncomputable section
open Set Filter Topology
open MeasureTheory
open scoped ENNReal

noncomputable section
open Set Metric Filter Topology

noncomputable section
open MeasureTheory Filter Set Metric Function ContinuousLinearMap
open scoped Topology Convolution ContDiff Pointwise

namespace CannonBeltrami

lemma locallyIntegrable_bounded {μ : ℂ → ℂ} (hm : AEStronglyMeasurable μ volume)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ z, ‖μ z‖ ≤ k) : LocallyIntegrable μ volume := by
  apply (show LocallyIntegrable (fun _ : ℂ => k) volume from
    continuous_const.locallyIntegrable).mono hm
  exact .of_forall (fun z => by simpa only [Real.norm_eq_abs,abs_of_nonneg hk] using hb z)

lemma mollify_smooth {μ : ℂ → ℂ} (hm : LocallyIntegrable μ volume) (n : ℕ) :
    ContDiff ℝ ∞ (mollify μ n) :=
  (mollifier n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    (mollifier n).contDiff_normed hm

lemma mollify_bound {μ : ℂ → ℂ} (hm : AEStronglyMeasurable μ volume)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ z, ‖μ z‖ ≤ k) (n : ℕ) (z : ℂ) :
    ‖mollify μ n z‖ ≤ k := by
  have h := dist_convolution_le (x₀:=z) (z₀:=0) hk
    (mollifier n).support_normed_eq.subset (mollifier n).nonneg_normed
    (mollifier n).integral_normed hm (fun x _ => by simpa using hb x)
  simpa only [dist_zero_right, mollify] using h

lemma mollify_ae_tendsto {μ : ℂ → ℂ} (hm : LocallyIntegrable μ volume) :
    ∀ᵐ z ∂volume, Tendsto (fun n => mollify μ n z) atTop (𝓝 (μ z)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (K:=2) _ _ hm
  · have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2:ℝ)
    simpa [mollifier,div_eq_mul_inv] using h
  · exact .of_forall (fun n => by dsimp [mollifier]; ring_nf; exact le_refl _)

end CannonBeltrami

namespace CannonBeltrami

theorem global_smooth_coefficient_approximation {μ : ℂ → ℂ}
    (hm : AEStronglyMeasurable μ volume) {k : ℝ} (hk : 0 ≤ k)
    (hb : ∀ z, ‖μ z‖ ≤ k) :
    ∃ ν : ℕ → SchwartzMap ℂ ℂ,
      (∀ n, HasCompactSupport (ν n : ℂ → ℂ)) ∧
      (∀ n z, ‖ν n z‖ ≤ k) ∧
      (∀ᵐ z ∂volume, Tendsto (fun n => ν n z) atTop (𝓝 (μ z))) := by
  let f : ℕ → ℂ → ℂ := fun n z => (globalCutoff n z:ℂ)*mollify μ n z
  have hf (n : ℕ) : ContDiff ℝ ∞ (f n) :=
    (Complex.ofRealCLM.contDiff.comp (globalCutoff n).contDiff).mul
      (mollify_smooth (locallyIntegrable_bounded hm hk hb) n)
  have hc (n : ℕ) : HasCompactSupport (f n) :=
    ((globalCutoff n).hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  let ν (n : ℕ) := (hc n).toSchwartzMap (hf n)
  refine ⟨ν,hc,?_,?_⟩
  · intro n z
    change ‖(globalCutoff n z:ℂ)*mollify μ n z‖ ≤ k
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (globalCutoff n).nonneg]
    calc
      globalCutoff n z*‖mollify μ n z‖ ≤ 1*k :=
        mul_le_mul (globalCutoff n).le_one (mollify_bound hm hk hb n z)
          (norm_nonneg _) (by norm_num)
      _ = k := one_mul _
  · filter_upwards [mollify_ae_tendsto (locallyIntegrable_bounded hm hk hb)] with z hz
    apply hz.congr'
    have hev : ∀ᶠ n : ℕ in atTop, ‖z‖ ≤ (n:ℝ)+1 :=
      (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖z‖)).mono
        (fun n hn => by linarith)
    filter_upwards [hev] with n hn
    change mollify μ n z=(globalCutoff n z:ℂ)*mollify μ n z
    rw [(globalCutoff n).one_of_mem_closedBall (by simpa [globalCutoff] using hn)]
    simp

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
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_WeakQSInverseShrink
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

noncomputable section
open Set Filter Topology
open MeasureTheory
open scoped ENNReal

noncomputable section
open Set Metric Filter Topology

noncomputable section
open MeasureTheory Filter Set Metric Function ContinuousLinearMap
open scoped Topology Convolution ContDiff Pointwise

noncomputable section
namespace CannonMetricQC
open Metric

lemma weakQS_of_inverse_shrink (f : ℂ ≃ₜ ℂ) {η : ℝ} (hη : 0 < η)
    (hs : ∀ x a b : ℂ, b ≠ x → dist a x < η*dist b x →
      dist (f.symm a) (f.symm x) ≤ (1/2:ℝ)*dist (f.symm b) (f.symm x)) :
    WeakQS f η⁻¹ := by
  intro x a b hab
  by_cases ha : a=x
  · rw [ha,dist_self]
    positivity
  have hp : 0 < dist a x := dist_pos.mpr ha
  have hpx : f a ≠ f x := fun h => ha (f.injective h)
  have h : η*dist (f a) (f x) ≤ dist (f b) (f x) := by
    by_contra! hn
    have hh := hs (f x) (f b) (f a) hpx hn
    simp only [f.symm_apply_apply] at hh
    rw [dist_comm x a,dist_comm x b] at hab
    linarith
  have he : dist (f a) (f x) ≤ dist (f b) (f x)/η := (le_div_iff₀ hη).mpr (by nlinarith [h])
  simpa only [div_eq_mul_inv,mul_comm,dist_comm] using he
end CannonMetricQC

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
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_GlobalMetricWeakMrmt
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

noncomputable section
open Set Filter Topology
open MeasureTheory
open scoped ENNReal

noncomputable section
open Set Metric Filter Topology

noncomputable section
open MeasureTheory Filter Set Metric Function ContinuousLinearMap
open scoped Topology Convolution ContDiff Pointwise

noncomputable section
namespace CannonBeltrami
open CannonPlane

theorem global_metric_weak_mrmt (μ : ℂ → ℂ) (hm : AEStronglyMeasurable μ volume)
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (hb : ∀ z, ‖μ z‖ ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ H : ℂ ≃ₜ ℂ, H 0=0 ∧ H 1=1 ∧
      CannonMetricQC.WeakQS H C ∧ CannonMetricQC.WeakQS H.symm C ∧
      ∀ S : Set ℂ, IsCompact S → ∃ a : Lp ℂ 2 (volume.restrict S),
        ∀ φ : SchwartzMap ℂ ℂ, tsupport (φ : ℂ → ℂ) ⊆ S →
          (∫ z, H z*partialZ φ z)=-(∫ z in S, a z*φ z) ∧
          (∫ z, H z*partialBar φ z)=-(∫ z in S, a z*(μ z*φ z)) := by
  obtain ⟨ν,hνc,hνb,hνlim⟩ := global_smooth_coefficient_approximation hm hk hb
  choose F hF0 hF1 hF hF' hFe hFD hFD' using
    (fun n => normalized_smooth_beltrami_solution (ν n) (hνc n) hk hk1 (hνb n))
  let K := (1+k)/(1-k)
  have hK : 0 ≤ K := div_nonneg (by linarith) (sub_pos.mpr hk1).le
  obtain ⟨H,σ,hσ,hH0,hH1,hlim,hlim'⟩ := normalized_smooth_qc_subsequence F hF0 hF1
    (fun n => (hF n).of_le (by simp)) (fun n => (hF' n).of_le (by simp)) hK hFD hFD'
  have hr : UniformRelativeControl (fun n z => F n z) := by
    intro ε hε
    obtain ⟨η,hη,h⟩ := smooth_qc_uniform_shrink hK ε hε
    exact ⟨η,hη,fun n => h (F n) ((hF' n).of_le (by simp)) (hFD' n)⟩
  have hp := normalized_family_pointwise_bound (fun n z => F n z) hF0 hF1 hr
  have he := relative_control_equicontinuous (fun n z => F n z) hr hp
  have hlocal (S : Set ℂ) (hS : IsCompact S) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ n z, z ∈ S → ‖F (σ n) z‖ ≤ B := by
    obtain ⟨B,hB,hbB⟩ := equicontinuous_compact_bound (fun n z => F n z) he hp hS
    exact ⟨B,hB,fun n => hbB (σ n)⟩
  have hpt (z : ℂ) : Tendsto (fun n => F (σ n) z) atTop (𝓝 (H z)) :=
    (continuous_eval_const z).tendsto (homeomorphMap H) |>.comp hlim
  have hνt : ∀ᵐ z ∂volume, Tendsto (fun n => ν (σ n) z) atTop (𝓝 (μ z)) := by
    filter_upwards [hνlim] with z hz
    exact hz.comp hσ.tendsto_atTop
  have hpt' (z : ℂ) : Tendsto (fun n => (F (σ n)).symm z) atTop (𝓝 (H.symm z)) :=
    (continuous_eval_const z).tendsto (homeomorphMap H.symm) |>.comp hlim'
  obtain ⟨η,hη,hs⟩ := smooth_qc_uniform_shrink hK (1/2) (by norm_num)
  have hsh : ∀ x a b : ℂ, b ≠ x → dist a x < η*dist b x →
      dist (H a) (H x) ≤ (1/2:ℝ)*dist (H b) (H x) := by
    intro x a b hb hab
    apply le_of_tendsto_of_tendsto ((hpt a).dist (hpt x))
      (((hpt b).dist (hpt x)).const_mul (1/2))
    exact Eventually.of_forall (fun n => (hs (F (σ n))
      ((hF' (σ n)).of_le (by simp)) (hFD' (σ n)) x a b hb hab).le)
  have hshi : ∀ x a b : ℂ, b ≠ x → dist a x < η*dist b x →
      dist (H.symm a) (H.symm x) ≤ (1/2:ℝ)*dist (H.symm b) (H.symm x) := by
    intro x a b hb hab
    apply le_of_tendsto_of_tendsto ((hpt' a).dist (hpt' x))
      (((hpt' b).dist (hpt' x)).const_mul (1/2))
    exact Eventually.of_forall (fun n => (hs (F (σ n)).symm
      ((hF (σ n)).of_le (by simp)) (hFD (σ n)) x a b hb hab).le)
  refine ⟨η⁻¹,inv_pos.mpr hη,H,hH0,hH1,
    CannonMetricQC.weakQS_of_inverse_shrink H hη hshi,
    CannonMetricQC.weakQS_of_inverse_shrink H.symm hη hsh,fun S hS => ?_⟩
  exact local_weak_beltrami_limit (fun n => F (σ n)) H (fun n => hF (σ n)) hlocal hpt hK
    (fun n => hFD (σ n)) (fun n => ν (σ n)) μ
    (fun n => (ν (σ n)).continuous.aestronglyMeasurable) hm hk (fun n => hνb (σ n)) hb hνt
    (fun n => hFe (σ n)) hS

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
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Center
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
section
noncomputable section
namespace CannonConformal
open Set Topology Metric

lemma evaluate_smul (a : ℝ) (p : Form) (x y : ℝ) :
    evaluate (a • p) x y=a*evaluate p x y := by
  simp only [evaluate,Pi.smul_apply,smul_eq_mul]
  ring

end CannonConformal

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
-- module Solutions.OAIQ046_CN.Cannon_Conformal_LinearZ
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
namespace CannonConformal
open Complex

lemma linearZBar_apply (A : ℂ →L[ℝ] ℂ) (z : ℂ) :
    A z=linearZ A*z+linearBar A*star z := by
  have hz : z=z.re • (1:ℂ)+z.im • Complex.I := by
    apply Complex.ext <;> simp
  have ha : A z=z.re • A 1+z.im • A Complex.I := by
    conv_lhs => rw [hz]
    rw [map_add,map_smul,map_smul]
  rw [ha]
  apply Complex.ext <;> simp [linearZ,linearBar,Complex.mul_re,Complex.mul_im] <;> ring

lemma linearZ_ne_zero {A : ℂ →L[ℝ] ℂ} (hA : Function.Injective A) {μ : ℂ}
    (hμ : linearBar A=μ*linearZ A) : linearZ A ≠ 0 := by
  intro hz
  have hb : linearBar A=0 := by rw [hμ,hz,mul_zero]
  have ha : A 1=A 0 := by rw [linearZBar_apply,hz,hb]; simp
  exact one_ne_zero (hA ha)

lemma linear_beltrami_evaluate {A : ℂ →L[ℝ] ℂ} {μ : ℂ}
    (hμ : linearBar A=μ*linearZ A) (z : ℂ) :
    Complex.normSq (A z)=Complex.normSq (linearZ A)*evaluate (coefficientForm μ) z.re z.im := by
  rw [linearZBar_apply,hμ]
  have hh : linearZ A*z+μ*linearZ A*star z=linearZ A*(z+μ*star z) := by ring
  rw [hh,map_mul,evaluate_coefficientForm]

lemma coefficient_scale_pos {q : Form} (hq : Positive q) :
    0 < (q 0+q 2+2*Real.sqrt (determinant q))/4 := by
  have hc : 0 < q 2 := by
    have h := hq.2
    have ha := hq.1
    dsimp [determinant] at h
    nlinarith [sq_nonneg (q 1)]
  linarith [Real.sqrt_nonneg (determinant q),hq.1]

theorem beltrami_integrates_form {q : Form} (hq : Positive q)
    {A : ℂ →L[ℝ] ℂ} (hA : Function.Injective A)
    (hμ : linearBar A=beltrami q*linearZ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℂ, Complex.normSq (A z)=c*evaluate q z.re z.im := by
  let s : ℝ := (q 0+q 2+2*Real.sqrt (determinant q))/4
  have hs : 0 < s := coefficient_scale_pos hq
  have hn : 0 < Complex.normSq (linearZ A) := Complex.normSq_pos.mpr (linearZ_ne_zero hA hμ)
  refine ⟨Complex.normSq (linearZ A)/s,div_pos hn hs,?_⟩
  intro z
  have heq : evaluate q z.re z.im=s*evaluate (coefficientForm (beltrami q)) z.re z.im := by
    conv_lhs => rw [coefficient_reconstruction hq]
    exact evaluate_smul _ _ _ _
  rw [linear_beltrami_evaluate hμ,heq]
  field_simp

end CannonConformal

end
end
namespace CannonConformal
open MeasureTheory CannonBeltrami CannonMetricQC

theorem measurable_structure_integration_oai (q : ℂ → Form) (hq : Measurable q)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hl : ∀ z, LowerBound ε (q z)) (hu : ∀ z, UpperBound K (q z)) :
    ∃ C : ℝ, 0 < C ∧ ∃ F : ℂ ≃ₜ ℂ, F 0=0 ∧ F 1=1 ∧
      WeakQS F C ∧ WeakQS F.symm C ∧
      (∀ᵐ z : ℂ, DifferentiableAt ℝ (F : ℂ → ℂ) z ∧
        Function.Bijective (fderiv ℝ (F : ℂ → ℂ) z) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ v : ℂ,
          Complex.normSq (fderiv ℝ (F : ℂ → ℂ) z v)=c*evaluate (q z) v.re v.im) := by
  let μ : ℂ → ℂ := fun z => beltrami (q z)
  let k : ℝ := Real.sqrt (1-ε/K)
  have hm : AEStronglyMeasurable μ volume := (measurable_beltrami.comp hq).aestronglyMeasurable
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hk1 : k < 1 := (beltrami_uniform_bound hε hK (hl 0) (hu 0)).2
  have hb (z : ℂ) : ‖μ z‖ ≤ k := (beltrami_uniform_bound hε hK (hl z) (hu z)).1
  obtain ⟨C,hC,F,hF0,hF1,hF,hFi,hw⟩ := global_metric_weak_mrmt μ hm hk hk1 hb
  have hbc := metric_weak_beltrami_classical F hC hF μ hm hk hb hw
  have hn := weakQS_ae_bijective_fderiv F hC hC hF hFi
  have hd := weakQS_ae_differentiable F hC hF
  refine ⟨C,hC,F,hF0,hF1,hF,hFi,?_⟩
  filter_upwards [hbc,hn,hd] with z hz hzn hzd
  refine ⟨hzd,hzn,beltrami_integrates_form ?_ hzn.1 ?_⟩
  · constructor
    · have h := hl z 1 0
      simp only [evaluate,one_pow,mul_one,zero_pow (by norm_num : 2 ≠ 0),mul_zero,
        add_zero] at h
      exact hε.trans_le h
    · have h := determinant_ge_sq_lower hε.le (hl z)
      exact (sq_pos_of_pos hε).trans_le h
  · exact hz

end CannonConformal

end
end
end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.CannonConformal.measurable_structure_integration_oai := @OAI.CannonConformal.measurable_structure_integration_oai
