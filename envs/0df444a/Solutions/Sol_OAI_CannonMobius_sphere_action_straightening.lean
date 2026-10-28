-- Prove2me | solution 1 for OAI.CannonMobius.sphere_action_straightening
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:05:18.426649+00:00
-- url     : https://prove2.me/submissions/0229e510-8f5b-4771-9dad-870289804ef7

import Mathlib
import Definitions.Def_OAIQ046C002
import Theorems.Thm_OAI_CannonConformal_measurable_structure_integration

section
-- module Solutions.OAIQ046_CN.Compat
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

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
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Sphere
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set Filter Topology
open scoped OnePoint

noncomputable section
open Set Filter Topology

namespace CannonMobius
open Set Filter Topology
open scoped OnePoint

lemma restriction_extension (f : Sphere ≃ₜ Sphere) (hf : f ∞=∞) :
    (finiteRestriction f hf).onePointCongr=f := by
  apply Homeomorph.ext
  intro p
  induction p using OnePoint.rec with
  | infty => exact hf.symm
  | coe z => exact coe_coordinate (coe_map_ne_infty f hf z)

end CannonMobius

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_CauchySymbol
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

lemma differentiableAt_of_partialBar_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (h0 : partialBar f z=0) : DifferentiableAt ℂ f z := by
  let A : ℂ →L[ℂ] ℂ := (partialZ f z) • ContinuousLinearMap.id ℂ ℂ
  apply (hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt (f':=A) ?_).differentiableAt
  ext v
  change partialZ f z*v = fderiv ℝ f z v
  rw [fderiv_wirtinger,h0,zero_mul,add_zero]

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
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Round
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonMobius
open Set Metric Topology
open scoped OnePoint

lemma sphere_dist (p q : Sphere) : dist p q=dist (roundChart p) (roundChart q) := rfl
lemma roundChart_isometry : Isometry roundChart := Isometry.of_dist_eq (fun _ _ => rfl)

end CannonMobius

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Chart
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonStereo
open Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma stereo_inner {v : E} (hv : ‖v‖=1) (x y : (ℝ ∙ v)ᗮ) :
    inner ℝ (stereoInvFunAux v x) (stereoInvFunAux v y) =
      (16*inner ℝ (x:E) (y:E)+(‖x‖^2-4)*(‖y‖^2-4)) /
        ((‖x‖^2+4)*(‖y‖^2+4)) := by
  have hx := Submodule.mem_orthogonal_singleton_iff_inner_left.mp x.2
  have hy := Submodule.mem_orthogonal_singleton_iff_inner_left.mp y.2
  have hy' : inner ℝ v (y:E)=0 := by rw [real_inner_comm,hy]
  simp only [stereoInvFunAux_apply,inner_smul_left,inner_smul_right,
    inner_add_left,inner_add_right,conj_trivial,hx,hy',real_inner_self_eq_norm_sq,hv]
  simp only [div_eq_mul_inv,mul_inv_rev,Submodule.norm_coe]

  ring

lemma stereo_dist_sq {v : E} (hv : ‖v‖=1) (x y : (ℝ ∙ v)ᗮ) :
    (dist (stereoInvFun hv x) (stereoInvFun hv y))^2 =
      16*(dist x y)^2/((‖x‖^2+4)*(‖y‖^2+4)) := by
  have hx := mem_sphere_zero_iff_norm.mp (stereoInvFunAux_mem hv x.2)
  have hy := mem_sphere_zero_iff_norm.mp (stereoInvFunAux_mem hv y.2)
  change (dist (stereoInvFunAux v x) (stereoInvFunAux v y))^2=_
  rw [dist_eq_norm,norm_sub_sq_real,hx,hy,stereo_inner hv]
  rw [dist_eq_norm,norm_sub_sq_real]
  have hp : ‖x‖^2+4 ≠ 0 := by positivity
  have hq : ‖y‖^2+4 ≠ 0 := by positivity
  simp only [Submodule.coe_inner]
  field_simp [hp,hq]
  ring

lemma stereo_dist {v : E} (hv : ‖v‖=1) (x y : (ℝ ∙ v)ᗮ) :
    dist (stereoInvFun hv x) (stereoInvFun hv y) =
      4*dist x y/(Real.sqrt (‖x‖^2+4)*Real.sqrt (‖y‖^2+4)) := by
  have hx : 0 < Real.sqrt (‖x‖^2+4) := Real.sqrt_pos.mpr (by positivity)
  have hy : 0 < Real.sqrt (‖y‖^2+4) := Real.sqrt_pos.mpr (by positivity)
  have hh := stereo_dist_sq hv x y
  have he : (4*dist x y/(Real.sqrt (‖x‖^2+4)*Real.sqrt (‖y‖^2+4)))^2 =
      16*(dist x y)^2/((‖x‖^2+4)*(‖y‖^2+4)) := by
    rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
    norm_num
  nlinarith [div_nonneg (show 0 ≤ 4*dist x y by positivity) (mul_nonneg hx.le hy.le),
    dist_nonneg (x:=stereoInvFun hv x) (y:=stereoInvFun hv y)]

end CannonStereo

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Distinct
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
noncomputable section
namespace CannonQM
open Metric
open scoped NNReal

lemma Distinct.map {X Y : Type*} {f : X → Y} (hf : Function.Injective f)
    {x y z w : X} (h : Distinct x y z w) : Distinct (f x) (f y) (f z) (f w) := by
  rcases h with ⟨hxy,hxz,hxw,hyz,hyw,hzw⟩
  exact ⟨fun h => hxy (hf h),fun h => hxz (hf h),fun h => hxw (hf h),
    fun h => hyz (hf h),fun h => hyw (hf h),fun h => hzw (hf h)⟩

lemma Distinct.flip {X : Type*} {x y z w : X} (h : Distinct x y z w) : Distinct x w z y := by
  rcases h with ⟨hxy,hxz,hxw,hyz,hyw,hzw⟩
  exact ⟨hxw,hxz,hxy,hzw.symm,hyw.symm,hyz.symm⟩

lemma nndist_pos {X : Type*} [MetricSpace X] {x y : X} : 0 < nndist x y ↔ x ≠ y := by
  rw [pos_iff_ne_zero,ne_eq,nndist_eq_zero]

lemma crossRatio_pos {X : Type*} [MetricSpace X] {x y z w : X}
    (h : Distinct x y z w) : 0 < crossRatio x y z w := by
  exact div_pos (mul_pos (nndist_pos.mpr h.1) (nndist_pos.mpr h.2.2.2.2.2))
    (mul_pos (nndist_pos.mpr h.2.2.1) (nndist_pos.mpr h.2.2.2.1))

lemma crossRatio_flip {X : Type*} [MetricSpace X] (x y z w : X) :
    crossRatio x w z y = (crossRatio x y z w)⁻¹ := by
  simp only [crossRatio,inv_div,nndist_comm z y,nndist_comm w z]

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

lemma Controlled.comp {f : X → Y} {g : Y → Z} {η θ : Distortion}
    (hg : Controlled g θ) (hf : Controlled f η) (hinj : Function.Injective f) :
    Controlled (g ∘ f) (η.trans θ) := by
  intro x y z w hh
  exact (hg _ _ _ _ (hh.map hinj)).trans (θ.monotone (hf _ _ _ _ hh))

lemma Controlled.inverse (f : X ≃ₜ Y) {η : Distortion} (hf : Controlled f η) :
    Controlled f.symm (reciprocal η.symm) := by
  intro x y z w hh
  have hh' := hh.map f.symm.injective
  have H := hf _ _ _ _ hh'.flip
  simp only [f.apply_symm_apply] at H
  rw [crossRatio_flip x y z w, crossRatio_flip (f.symm x) (f.symm y) (f.symm z) (f.symm w)] at H
  have H' := η.symm.monotone H
  simp only [OrderIso.symm_apply_apply] at H'
  change crossRatio (f.symm x) (f.symm y) (f.symm z) (f.symm w) ≤ (η.symm (crossRatio x y z w)⁻¹)⁻¹
  have hpos : 0 < η.symm (crossRatio x y z w)⁻¹ := by
    simpa only [distortion_zero] using η.symm.strictMono (inv_pos.mpr (crossRatio_pos hh))
  have hi := (inv_le_inv₀ (inv_pos.mpr (crossRatio_pos hh')) hpos).mpr H'
  simpa only [inv_inv] using hi

end CannonQM

end
end
namespace CannonMetricQC
open Metric CannonQM

lemma cycle_sorted_bounds {a b c d T : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hT : 1  ≤  T)
    (hab : a  ≤  b) (hcd : c  ≤  d) (hp : a*b  ≤  T*(c*d))
    (hbt : b  ≤  a+c+d) (hdt : d  ≤  a+b+c) :
    a  ≤  (2*T+3)*c ∧ b  ≤  (2*T+3)*d := by
  have hT0 : 0 < T := by linarith
  constructor
  · by_contra hn
    have hn' : (2*T+3)*c < a := lt_of_not_ge hn
    have hhdt : d  ≤  2*b+c := by linarith
    have hm := mul_le_mul_of_nonneg_left hhdt (mul_nonneg hT0.le hc.le)
    have hTb : T*c < b := by nlinarith
    have hm1 := mul_pos (sub_pos.mpr hn') hb
    have hm2 := mul_pos (sub_pos.mpr hTb) hc
    nlinarith
  · by_contra hn
    have hn' : (2*T+3)*d < b := lt_of_not_ge hn
    have hha : T*d < a := by nlinarith
    have hhb : d < b := by nlinarith
    have hm1 := mul_pos (sub_pos.mpr hha) hb
    have hm2 := mul_nonneg (mul_nonneg hT0.le hd.le) (sub_nonneg.mpr hhb.le)
    have hm3 := mul_le_mul_of_nonneg_left hcd (mul_nonneg hT0.le hd.le)
    nlinarith

lemma crossRatio_pair_bounds {X : Type*} [MetricSpace X] (x y z w : X)
    (hh : Distinct x y z w) {T : ℝ} (hT : 1  ≤  T)
    (hp : dist x y*dist z w  ≤  T*(dist x w*dist y z)) :
    (dist x y  ≤  (2*T+3)*dist x w ∧ dist z w  ≤  (2*T+3)*dist y z) ∨
    (dist x y  ≤  (2*T+3)*dist y z ∧ dist z w  ≤  (2*T+3)*dist x w) := by
  let a := dist x y
  let b := dist z w
  let c := dist x w
  let d := dist y z
  have ha : 0 < a := dist_pos.mpr hh.1
  have hb : 0 < b := dist_pos.mpr hh.2.2.2.2.2
  have hc : 0 < c := dist_pos.mpr hh.2.2.1
  have hd : 0 < d := dist_pos.mpr hh.2.2.2.1
  have ht1 : a  ≤  b+c+d := by
    have h1 := dist_triangle x w y
    have h2 := dist_triangle w z y
    dsimp [a,b,c,d]
    rw [dist_comm w z,dist_comm z y] at h2
    linarith
  have ht2 : b  ≤  a+c+d := by
    have h1 := dist_triangle z y w
    have h2 := dist_triangle y x w
    dsimp [a,b,c,d]
    rw [dist_comm z y] at h1
    rw [dist_comm y x] at h2
    linarith
  have ht3 : c  ≤  a+b+d := by
    have h1 := dist_triangle x y w
    have h2 := dist_triangle y z w
    dsimp [a,b,c,d]
    linarith
  have ht4 : d  ≤  a+b+c := by
    have h1 := dist_triangle y x z
    have h2 := dist_triangle x w z
    dsimp [a,b,c,d]
    rw [dist_comm y x] at h1
    rw [dist_comm w z] at h2
    linarith
  change (a  ≤  (2*T+3)*c ∧ b  ≤  (2*T+3)*d) ∨
    (a  ≤  (2*T+3)*d ∧ b  ≤  (2*T+3)*c)
  rcases le_total a b with hab | hba <;> rcases le_total c d with hcd | hdc
  · exact Or.inl (cycle_sorted_bounds ha hb hc hd hT hab hcd hp ht2 ht4)
  · exact Or.inr (cycle_sorted_bounds ha hb hd hc hT hab hdc (by nlinarith [hp])
      (by linarith) ht3)
  · have hh := cycle_sorted_bounds hb ha hc hd hT hba hcd (by nlinarith [hp])
      (by linarith) (by linarith)
    exact Or.inr ⟨hh.2,hh.1⟩
  · have hh := cycle_sorted_bounds hb ha hd hc hT hba hdc (by nlinarith [hp])
      (by linarith) (by linarith)
    exact Or.inl ⟨hh.2,hh.1⟩

end CannonMetricQC

end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_PreservesProducts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace
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
section
section
noncomputable section

namespace CannonStereo
open Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma stereo_crossRatio {v : E} (hv : ‖v‖=1) (x y z w : (ℝ ∙ v)ᗮ) :
    CannonQM.crossRatio (stereoInvFun hv x) (stereoInvFun hv y)
      (stereoInvFun hv z) (stereoInvFun hv w)=CannonQM.crossRatio x y z w := by
  apply NNReal.coe_injective
  change dist (stereoInvFun hv x) (stereoInvFun hv y)*
    dist (stereoInvFun hv z) (stereoInvFun hv w) /
    (dist (stereoInvFun hv x) (stereoInvFun hv w)*
      dist (stereoInvFun hv y) (stereoInvFun hv z)) =
      dist x y*dist z w/(dist x w*dist y z)
  simp only [stereo_dist]
  have hp (u : (ℝ ∙ v)ᗮ) : Real.sqrt (‖u‖^2+4) ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity)).ne'
  by_cases hxw : x=w
  · subst w; simp
  by_cases hyz : y=z
  · subst z; simp
  have h1 : dist x w ≠ 0 := (dist_pos.mpr hxw).ne'
  have h2 : dist y z ≠ 0 := (dist_pos.mpr hyz).ne'
  field_simp

end CannonStereo

end
end
noncomputable section
namespace CannonMobius
open Metric Topology
open scoped OnePoint

lemma coe_dist (z w : ℂ) : dist (z:Sphere) (w:Sphere)=
    4*dist z w/(Real.sqrt (‖z‖^2+4)*Real.sqrt (‖w‖^2+4)) := by
  rw [sphere_dist,roundChart_coe,roundChart_coe,CannonStereo.stereo_dist]
  simp only [planeHyperplane.isometry.dist_eq,planeHyperplane.norm_map]

lemma coe_crossRatio (x y z w : ℂ) :
    CannonQM.crossRatio (x:Sphere) (y:Sphere) (z:Sphere) (w:Sphere)=
      CannonQM.crossRatio x y z w := by
  have hh := CannonStereo.stereo_crossRatio north_norm
    (planeHyperplane x) (planeHyperplane y) (planeHyperplane z) (planeHyperplane w)
  simpa only [CannonQM.crossRatio,← roundChart_coe,roundChart_isometry.nndist_eq,
    planeHyperplane.isometry.nndist_eq] using hh

end CannonMobius

namespace CannonMobius
open Set Metric Topology
open scoped OnePoint

lemma preservesProducts_dense {α : Type*} (e : α → Sphere) (he : DenseRange e)
    {f : Sphere → Sphere} (hf : Continuous f)
    (h : ∀ p : Fin 4 → α,
      dist (f (e (p 0))) (f (e (p 1)))*dist (f (e (p 2))) (f (e (p 3)))*
        (dist (e (p 0)) (e (p 3))*dist (e (p 1)) (e (p 2))) =
      dist (e (p 0)) (e (p 1))*dist (e (p 2)) (e (p 3))*
        (dist (f (e (p 0))) (f (e (p 3)))*dist (f (e (p 1))) (f (e (p 2))))) :
    PreservesProducts f := by
  have hd : DenseRange (fun p : Fin 4 → α => fun i => e (p i)) := DenseRange.piMap (fun _ => he)
  let l : (Fin 4 → Sphere) → ℝ := fun p =>
    dist (f (p 0)) (f (p 1))*dist (f (p 2)) (f (p 3))*(dist (p 0) (p 3)*dist (p 1) (p 2))
  let r : (Fin 4 → Sphere) → ℝ := fun p =>
    dist (p 0) (p 1)*dist (p 2) (p 3)*(dist (f (p 0)) (f (p 3))*dist (f (p 1)) (f (p 2)))
  have hl : Continuous l := by dsimp [l]; fun_prop
  have hr : Continuous r := by dsimp [r]; fun_prop
  exact fun p => congrFun (hd.equalizer hl hr (funext h)) p

lemma PreservesProducts.crossRatio {f : Sphere → Sphere} (hf : PreservesProducts f)
    (hi : Function.Injective f) (x y z w : Sphere) (hh : CannonQM.Distinct x y z w) :
    CannonQM.crossRatio (f x) (f y) (f z) (f w)=CannonQM.crossRatio x y z w := by
  apply NNReal.coe_injective
  change dist (f x) (f y)*dist (f z) (f w)/(dist (f x) (f w)*dist (f y) (f z))=
    dist x y*dist z w/(dist x w*dist y z)
  have h1 : dist (f x) (f w)*dist (f y) (f z) ≠ 0 := mul_ne_zero
    (dist_ne_zero.mpr (fun h => hh.2.2.1 (hi h)))
    (dist_ne_zero.mpr (fun h => hh.2.2.2.1 (hi h)))
  have h2 : dist x w*dist y z ≠ 0 := mul_ne_zero
    (dist_ne_zero.mpr hh.2.2.1) (dist_ne_zero.mpr hh.2.2.2.1)
  exact (div_eq_div_iff h1 h2).mpr (hf ![x,y,z,w])

lemma PreservesProducts.controlled {f : Sphere → Sphere} (hf : PreservesProducts f)
    (hi : Function.Injective f) : CannonQM.Controlled f (OrderIso.refl _) :=
  fun x y z w hh => (hf.crossRatio hi x y z w hh).le

lemma inversion_preservesProducts : PreservesProducts inversion := by
  let e : {z : ℂ // z ≠ 0} → Sphere := fun z => (z.val:Sphere)
  have he : DenseRange e := (OnePoint.denseRange_coe (X:=ℂ)).comp
    (denseRange_subtype_val.mpr (dense_compl_singleton (0:ℂ))) OnePoint.continuous_coe
  apply preservesProducts_dense e he inversion.continuous
  intro p
  have hinv (i : Fin 4) : inversion (e (p i))=((p i).val⁻¹:ℂ) := inv_coe (p i).2
  simp only [hinv,e,coe_dist,dist_inv_inv₀ (p _).2 (p _).2]
  have hn (i : Fin 4) : ‖(p i).val‖ ≠ 0 := norm_ne_zero_iff.mpr (p i).2
  have hp (z : ℂ) : Real.sqrt (‖z‖^2+4) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

lemma affine_preservesProducts (a b : ℂ) (ha : a ≠ 0) : PreservesProducts (affine a b ha) := by
  apply preservesProducts_dense (fun z : ℂ => (z:Sphere)) OnePoint.denseRange_coe
    (affine a b ha).continuous
  intro p
  have hdist (i j : Fin 4) : dist (a*p i+b) (a*p j+b)=‖a‖*dist (p i) (p j) := by
    rw [dist_add_right,dist_eq_norm,← mul_sub,norm_mul,← dist_eq_norm]
  have haffi (z : ℂ) : affine a b ha (z:Sphere)=((a*z+b:ℂ):Sphere) := rfl
  simp only [haffi,coe_dist,hdist]
  have hp (z : ℂ) : Real.sqrt (‖z‖^2+4) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

lemma inversion_controlled : CannonQM.Controlled inversion (OrderIso.refl _) :=
  inversion_preservesProducts.controlled inversion.injective
lemma affine_controlled (a b : ℂ) (ha : a ≠ 0) :
    CannonQM.Controlled (affine a b ha) (OrderIso.refl _) :=
  (affine_preservesProducts a b ha).controlled (affine a b ha).injective

end CannonMobius

end
end
section
noncomputable section

namespace CannonQM
open Set Metric Filter Bornology

lemma eventually_dist_large (x : ℂ) (R : ℝ) :
    ∀ᶠ w : ℂ in cobounded ℂ, R < dist w x := by
  have hh := (isBounded_closedBall (x:=x) (r:=R)).compl
  have ht : (closedBall x R)ᶜ ∈ cobounded ℂ := hh
  filter_upwards [ht] with w hw
  exact lt_of_not_ge hw

theorem Controlled.plane_weakQS (f : ℂ ≃ₜ ℂ) {η : Distortion}
    (hf : Controlled f η) : CannonMetricQC.WeakQS f (1+2*(η 2 : ℝ)) := by
  intro x y z hxyz
  have hη0 : 0 ≤ (η 2 : ℝ) := (η 2).coe_nonneg
  have hH : 1 ≤ 1+2*(η 2 : ℝ) := by linarith
  by_cases hxy : x=y
  · subst y; simp; positivity
  by_cases hxz : x=z
  · subst z
    have : x=y := dist_eq_zero.mp (le_antisymm (by simpa using hxyz) dist_nonneg)
    exact (hxy this).elim
  by_cases hyz : y=z
  · subst z
    exact le_mul_of_one_le_left dist_nonneg hH
  have ht : Tendsto f (cobounded ℂ) (cobounded ℂ) := by
    simpa only [cobounded_eq_cocompact] using f.isClosedEmbedding.tendsto_cocompact
  have hs := eventually_dist_large y (dist z y)
  have hi := ht.eventually (eventually_dist_large (f z) (dist (f y) (f z)))
  obtain ⟨w,hw,hwi,hwx⟩ := (hs.and (hi.and (eventually_ne_cobounded x))).exists
  have hwy : w ≠ y := by intro he; rw [he,dist_self] at hw; exact not_lt_of_ge dist_nonneg hw
  have hwz : w ≠ z := by intro he; rw [he] at hw; exact (lt_irrefl _ hw)
  have hquad : Distinct x y w z := ⟨hxy,hwx.symm,hxz,hwy.symm,hyz,hwz⟩
  have hsource : dist w z ≤ 2*dist y w := by
    have hh := dist_triangle w y z
    rw [dist_comm z y] at hw
    rw [dist_comm w y] at hw hh
    linarith
  have htarget : dist (f y) (f w) ≤ 2*dist (f w) (f z) := by
    have hh := dist_triangle (f y) (f z) (f w)
    rw [dist_comm (f z) (f w)] at hh
    linarith
  have hp : 0 < dist x z := dist_pos.mpr hxz
  have hpy : 0 < dist y w := dist_pos.mpr hwy.symm
  have hrat : crossRatio x y w z ≤ 2 := by
    have hh : dist x y*dist w z ≤ 2*(dist x z*dist y w) := by
      calc
        _ ≤ dist x z*(2*dist y w) := mul_le_mul hxyz hsource dist_nonneg dist_nonneg
        _ = _ := by ring
    apply NNReal.coe_le_coe.mp
    change dist x y*dist w z/(dist x z*dist y w) ≤ (2:ℝ)
    exact (div_le_iff₀ (mul_pos hp hpy)).mpr hh
  have hc := (hf x y w z hquad).trans (η.monotone hrat)
  have hfxz : 0 < dist (f x) (f z) := dist_pos.mpr (fun he => hxz (f.injective he))
  have hfyw : 0 < dist (f y) (f w) := dist_pos.mpr (fun he => hwy (f.injective he).symm)
  have hfwz : 0 < dist (f w) (f z) := dist_pos.mpr (fun he => hwz (f.injective he))
  have hcR : dist (f x) (f y)*dist (f w) (f z) ≤
      (η 2 : ℝ)*(dist (f x) (f z)*dist (f y) (f w)) := by
    have hh := NNReal.coe_le_coe.mpr hc
    change dist (f x) (f y)*dist (f w) (f z)/(dist (f x) (f z)*dist (f y) (f w)) ≤ (η 2 : ℝ) at hh
    exact (div_le_iff₀ (mul_pos hfxz hfyw)).mp hh
  have he : dist (f x) (f y) ≤ 2*(η 2 : ℝ)*dist (f x) (f z) := by
    apply (mul_le_mul_iff_left₀ hfwz).mp
    calc
      _ ≤ (η 2 : ℝ)*(dist (f x) (f z)*dist (f y) (f w)) := hcR
      _ ≤ (η 2 : ℝ)*(dist (f x) (f z)*(2*dist (f w) (f z))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htarget dist_nonneg) hη0
      _ = _ := by ring
  nlinarith [dist_nonneg (x:=f x) (y:=f z)]
end CannonQM

end
end
noncomputable section
namespace CannonMobius
open Set Filter Topology
open scoped OnePoint

lemma sendToInfty_apply (p : Sphere) : sendToInfty p p=∞ := by
  by_cases hp : p=∞
  · simp [sendToInfty,hp]
  · rw [sendToInfty,ite_eq_right hp,← coe_coordinate hp]
    change inv (((1*coordinate p + -coordinate p):ℂ):Sphere)=∞
    simp

lemma sendToInfty_controlled (p : Sphere) :
    CannonQM.Controlled (sendToInfty p) (OrderIso.refl _) := by
  by_cases hp : p=∞
  · simp only [sendToInfty,ite_eq_left hp]
    exact fun _ _ _ _ _ => le_rfl
  · rw [sendToInfty,ite_eq_right hp]
    exact inversion_controlled.comp (affine_controlled 1 (-coordinate p) one_ne_zero)
      (affine 1 (-coordinate p) one_ne_zero).injective

lemma restriction_controlled (f : Sphere ≃ₜ Sphere) (hf : f ∞=∞)
    {η : CannonQM.Distortion} (hη : CannonQM.Controlled f η) :
    CannonQM.Controlled (finiteRestriction f hf) η := by
  intro x y z w hh
  have hcoe : Function.Injective (fun z : ℂ => (z:Sphere)) := OnePoint.coe_injective
  have h := hη (x:Sphere) (y:Sphere) (z:Sphere) (w:Sphere) (hh.map hcoe)
  have he (u : ℂ) : f (u:Sphere)=((finiteRestriction f hf u:ℂ):Sphere) :=
    (coe_coordinate (coe_map_ne_infty f hf u)).symm
  simpa only [he,coe_crossRatio] using h

theorem normalized_weakQS (f : Sphere ≃ₜ Sphere) {η : CannonQM.Distortion}
    (hf : CannonQM.Controlled f η) :
    ∃ (M : Sphere ≃ₜ Sphere) (hM : (M*f) ∞=∞),
      M ∈ biholomorphic ∧
      CannonMetricQC.WeakQS (finiteRestriction (M*f) hM) (1+2*(η 2:ℝ)) := by
  let M := sendToInfty (f ∞)
  have hM : (M*f) ∞=∞ := sendToInfty_apply (f ∞)
  refine ⟨M,hM,?_,?_⟩
  · by_cases hp : f ∞=∞
    · simp [M,sendToInfty,hp]
    · exact (by
        dsimp [M,sendToInfty]
        rw [ite_eq_right hp]
        exact biholomorphic.mul_mem inversion_biholomorphic
          (affine_biholomorphic 1 (-coordinate (f ∞)) one_ne_zero))
  · apply CannonQM.Controlled.plane_weakQS
    apply restriction_controlled
    exact (sendToInfty_controlled (f ∞)).comp hf f.injective

end CannonMobius

end
end
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

theorem weakQS_image_null (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H) (hf : WeakQS f H)
    {S : Set ℂ} (hS : volume S=0) : volume (f '' S)=0 := by
  have ht := weakQS_imageArea_ac f hH hf
  have hz : imageArea f (toMeasurable volume S)=0 := ht (by simpa only [measure_toMeasurable] using hS)
  rw [imageArea_apply f (measurableSet_toMeasurable _ _)] at hz
  exact measure_mono_null (image_mono (subset_toMeasurable volume S)) hz
end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory Filter
open scoped Topology

theorem weakQS_quasiMeasurePreserving (f : ℂ ≃ₜ ℂ) {H : ℝ}
    (hH : 0 < H) (hf : WeakQS f.symm H) :
    Measure.QuasiMeasurePreserving (f : ℂ → ℂ) volume volume := by
  refine ⟨f.continuous.measurable,?_⟩
  simpa only [imageArea,Homeomorph.symm_symm] using weakQS_imageArea_ac f.symm hH hf

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
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_Increment
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
namespace CannonOrientation
open Set Topology
open scoped ComplexConjugate

private lemma simplyConnected_univ (X : Type*) [TopologicalSpace X]
    [SimplyConnectedSpace X] : IsSimplyConnected (univ : Set X) :=
  (Homeomorph.Set.univ X).toHomotopyEquiv.simplyConnectedSpace

lemma continuous_log_exists {X : Type*} [TopologicalSpace X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {g : X → ℂ} (hg : Continuous g) (h0 : ∀ x, g x ≠ 0) :
    ∃ L : X → ℂ, Continuous L ∧ ∀ x, Complex.exp (L x)=g x := by
  obtain ⟨L,hL,he⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    (simplyConnected_univ X) isOpen_univ hg.continuousOn
    (by rintro ⟨x,-,hx⟩; exact h0 x hx)
  exact ⟨L,continuousOn_univ.mp hL,fun x => he (mem_univ x)⟩

lemma exp_equal_difference_constant {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {L M : X → ℂ} (hL : Continuous L) (hM : Continuous M)
    (he : ∀ x, Complex.exp (L x)=Complex.exp (M x)) (x y : X) :
    L x-M x=L y-M y := by
  let D : X → AddSubgroup.zmultiples (2*(Real.pi:ℂ)*Complex.I) := fun x =>
    ⟨L x-M x, by
      obtain ⟨n,hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (he x)
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n,by simpa [zsmul_eq_mul] using
        (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hn.symm))⟩⟩
  have hD : Continuous D := (hL.sub hM).subtype_mk _
  exact congrArg Subtype.val (PreconnectedSpace.constant inferInstance hD (x:=x) (y:=y))

lemma HasIncrement.unique {g : ℝ → ℂ} {u v : ℂ}
    (hu : HasIncrement g u) (hv : HasIncrement g v) : u=v := by
  obtain ⟨L,hL,heL,hu⟩ := hu
  obtain ⟨M,hM,heM,hv⟩ := hv
  have h := exp_equal_difference_constant hL hM (fun t => (heL t).trans (heM t).symm) 1 0
  linear_combination -hu+hv+h

lemma HasIncrement.of_homotopy {g : ℝ × ℝ → ℂ} (hg : Continuous g)
    (h0 : ∀ p, g p ≠ 0) (hloop : ∀ s, g (s,1)=g (s,0))
    {w : ℂ} (hw : HasIncrement (fun t => g (0,t)) w) :
    HasIncrement (fun t => g (1,t)) w := by
  obtain ⟨L,hL,he⟩ := continuous_log_exists hg h0
  have hL0 : Continuous (fun s => L (s,0)) := hL.comp (continuous_id.prodMk continuous_const)
  have hL1 : Continuous (fun s => L (s,1)) := hL.comp (continuous_id.prodMk continuous_const)
  have hsame : L (1,1)-L (1,0)=L (0,1)-L (0,0) :=
    exp_equal_difference_constant hL1 hL0
      (fun s => (he (s,1)).trans ((hloop s).trans (he (s,0)).symm)) 1 0
  have hstart : HasIncrement (fun t => g (0,t)) (L (0,1)-L (0,0)) :=
    ⟨fun t => L (0,t),hL.comp (continuous_const.prodMk continuous_id),fun t => he (0,t),rfl⟩
  exact ⟨fun t => L (1,t),hL.comp (continuous_const.prodMk continuous_id),
    fun t => he (1,t),hsame.trans (hstart.unique hw)⟩

lemma norm_circle (t : ℝ) : ‖circle t‖=1 := Complex.norm_exp_ofReal_mul_I _
lemma circle_ne_zero (t : ℝ) : circle t ≠ 0 := Complex.exp_ne_zero _

lemma increment_circle_mul {a : ℂ} (ha : a ≠ 0) :
    HasIncrement (fun t => a*circle t) (2*(Real.pi:ℂ)*Complex.I) := by
  refine ⟨fun t => Complex.log a + (2*Real.pi*t:ℝ)*Complex.I,by fun_prop,?_,?_⟩
  · intro t; rw [Complex.exp_add,Complex.exp_log ha]; rfl
  · push_cast; ring

lemma increment_conj_circle_mul {a : ℂ} (ha : a ≠ 0) :
    HasIncrement (fun t => a*conj (circle t)) (-(2*(Real.pi:ℂ)*Complex.I)) := by
  refine ⟨fun t => Complex.log a - (2*Real.pi*t:ℝ)*Complex.I,by fun_prop,?_,?_⟩
  · intro t
    dsimp only
    rw [sub_eq_add_neg,Complex.exp_add,Complex.exp_log ha]
    congr 1
    simp [circle, ← Complex.exp_conj]
    rw [show (starRingEnd ℂ) (2:ℂ)=2 by apply Complex.ext <;> norm_num]
  · push_cast; ring

lemma clip_nonneg (s : ℝ) : 0 ≤ clip s := le_max_left _ _
lemma clip_le_one (s : ℝ) : clip s ≤ 1 := max_le (by norm_num) (min_le_left _ _)
end CannonOrientation

namespace CannonOrientation
open Set Topology Filter
open scoped ComplexConjugate

lemma HasIncrement.mul_const {g : ℝ → ℂ} {w a : ℂ} (hw : HasIncrement g w)
    (ha : a ≠ 0) : HasIncrement (fun t => a*g t) w := by
  obtain ⟨L,hL,he,hw⟩ := hw
  refine ⟨fun t => Complex.log a+L t,continuous_const.add hL,?_,?_⟩
  · intro t
    simpa only [Complex.exp_add,Complex.exp_log ha] using congrArg (a*·) (he t)
  · dsimp only
    linear_combination hw

lemma HasIncrement.of_close {g h : ℝ → ℂ} {w : ℂ}
    (hg : Continuous g) (hh : Continuous h) (hgl : g 1=g 0) (hhl : h 1=h 0)
    (hc : ∀ t, ‖g t-h t‖ < ‖h t‖) (hw : HasIncrement h w) : HasIncrement g w := by
  let G : ℝ × ℝ → ℂ := fun p => h p.2+(clip p.1) • (g p.2-h p.2)
  have hG : Continuous G := by
    dsimp [G]
    fun_prop
  have hn (p : ℝ × ℝ) : G p ≠ 0 := by
    intro hz
    have he : h p.2 = -((clip p.1) • (g p.2-h p.2)) := by
      dsimp [G] at hz
      exact eq_neg_of_add_eq_zero_left hz
    have hn : ‖h p.2‖ ≤ ‖g p.2-h p.2‖ := by
      calc
        _ = clip p.1*‖g p.2-h p.2‖ := by
          conv_lhs => rw [he]
          rw [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg (clip_nonneg _)]
        _ ≤ 1*‖g p.2-h p.2‖ := mul_le_mul_of_nonneg_right (clip_le_one _) (norm_nonneg _)
        _ = _ := one_mul _
    exact (not_lt_of_ge hn) (hc p.2)
  have hl (s : ℝ) : G (s,1)=G (s,0) := by simp [G,hgl,hhl]
  have hs : HasIncrement (fun t => G (0,t)) w := by simpa [G] using hw
  simpa [G] using hs.of_homotopy hG hn hl

lemma increment_move_circle {f : ℂ → ℂ} (hf : Continuous f) (hi : Function.Injective f)
    {x y : ℂ} {r R : ℝ} (hr : 0 < r) (hR : 0 < R) {w : ℂ}
    (hw : HasIncrement (fun t => f (x+r • circle t)-f x) w) :
    HasIncrement (fun t => f (y+R • circle t)-f y) w := by
  let center (s : ℝ) : ℂ := (1-clip s) • x+clip s • y
  let radius (s : ℝ) : ℝ := (1-clip s)*r+clip s*R
  have hcenter : Continuous center := by dsimp [center]; fun_prop
  have hradius : Continuous radius := by dsimp [radius]; fun_prop
  have hpos (s : ℝ) : 0 < radius s := by
    have h0 := clip_nonneg s
    have h1 := clip_le_one s
    dsimp [radius]
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) hr.le,mul_nonneg h0 hR.le]
  let G : ℝ × ℝ → ℂ := fun p =>
    f (center p.1+radius p.1 • circle p.2)-f (center p.1)
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hn (p : ℝ × ℝ) : G p ≠ 0 := by
    intro he
    have hz : radius p.1 • circle p.2=0 := add_eq_left.mp (hi (sub_eq_zero.mp he))
    exact (smul_ne_zero (ne_of_gt (hpos _)) (circle_ne_zero _)) hz
  have hl (s : ℝ) : G (s,1)=G (s,0) := by simp [G]
  have hs : HasIncrement (fun t => G (0,t)) w := by simpa [G,center,radius] using hw
  simpa [G,center,radius] using hs.of_homotopy hG hn hl

end CannonOrientation

namespace CannonOrientation
open Set Topology Filter
open scoped ComplexConjugate

lemma increment_at_derivative {f : ℂ → ℂ} (hf : Continuous f)
    {x : ℂ} {A : ℂ →L[ℝ] ℂ} (hA : HasFDerivAt f A x)
    {m : ℝ} (hm : 0 < m) (hn : ∀ t, ‖A (circle t)‖=m)
    {w : ℂ} (hw : HasIncrement (fun t => A (circle t)) w) :
    ∃ r : ℝ, 0 < r ∧ HasIncrement (fun t => f (x+r • circle t)-f x) w := by
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp (hA.isLittleO.bound (half_pos hm))
  let r : ℝ := ε/2
  have hr : 0 < r := half_pos hε
  have hd (t : ℝ) : dist (x+r • circle t) x=r := by
    simp [dist_eq_norm,Real.norm_eq_abs,abs_of_pos hr,norm_circle]
  have hs : HasIncrement (fun t => r • A (circle t)) w := by
    simpa only [Complex.real_smul] using hw.mul_const (a:=(r:ℂ)) (by exact_mod_cast hr.ne')
  refine ⟨r,hr,HasIncrement.of_close ?_ ?_ ?_ ?_ ?_ hs⟩
  · exact (hf.comp (continuous_const.add (continuous_circle.const_smul r))).sub continuous_const
  · exact (A.continuous.comp continuous_circle).const_smul r
  · simp
  · simp
  · intro t
    have hh := he (y:=x+r • circle t) (by rw [hd]; dsimp [r]; linarith)
    have hl : ‖f (x+r • circle t)-f x-r • A (circle t)‖ ≤ (m/2)*r := by
      simpa only [add_sub_cancel_left,map_smul,norm_smul,norm_circle,mul_one,
        Real.norm_eq_abs,abs_of_pos hr] using hh
    have hn' : ‖r • A (circle t)‖=r*m := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hn]
    rw [hn']
    exact hl.trans_lt (by nlinarith)

theorem no_opposite_similarities {f : ℂ → ℂ} (hf : Continuous f)
    (hi : Function.Injective f) {x y : ℂ} {A B : ℂ →L[ℝ] ℂ}
    (hA : HasFDerivAt f A x) (hB : HasFDerivAt f B y)
    {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hAz : ∀ z, A z=a*z) (hBz : ∀ z, B z=b*conj z) : False := by
  obtain ⟨r,hr,hri⟩ := increment_at_derivative hf hA (norm_pos_iff.mpr ha)
    (fun t => by rw [hAz,norm_mul,norm_circle,mul_one])
    (by simpa only [hAz] using increment_circle_mul ha)
  obtain ⟨R,hR,hRi⟩ := increment_at_derivative hf hB (norm_pos_iff.mpr hb)
    (fun t => by rw [hBz,norm_mul,Complex.norm_conj,norm_circle,mul_one])
    (by simpa only [hBz] using increment_conj_circle_mul hb)
  have he := (increment_move_circle hf hi hr hR hri).unique hRi
  have hh := congrArg Complex.im he
  norm_num [Complex.mul_im] at hh
  linarith [Real.pi_pos]
end CannonOrientation

namespace CannonOrientation
open scoped ComplexConjugate

lemma conformal_scalar_cases {A : ℂ →L[ℝ] ℂ} (hA : IsConformalMap A) :
    (∃ a : ℂ, a ≠ 0 ∧ ∀ z, A z=a*z) ∨
    (∃ a : ℂ, a ≠ 0 ∧ ∀ z, A z=a*conj z) := by
  have hn : A 1 ≠ 0 := fun he => one_ne_zero (hA.injective (he.trans (map_zero A).symm))
  rcases hA.is_complex_or_conj_linear with ⟨L,hL⟩ | ⟨L,hL⟩
  · left
    refine ⟨A 1,hn,?_⟩
    intro z
    have he : L z=z*L 1 := by simpa using L.map_smul z (1:ℂ)
    have he' : ∀ u, L u=A u := fun u => congrArg (fun T : ℂ →L[ℝ] ℂ => T u) hL
    simpa only [he',mul_comm] using he
  · right
    refine ⟨A 1,hn,?_⟩
    intro z
    have he : L (conj z)=conj z*L 1 := by simpa using L.map_smul (conj z) (1:ℂ)
    have he' : ∀ u, L u=A (conj u) := fun u => congrArg (fun T : ℂ →L[ℝ] ℂ => T u) hL
    simpa only [he',map_one,starRingEnd_self_apply,mul_comm] using he

theorem conformal_differential_orientation {f : ℂ → ℂ} (hf : Continuous f)
    (hi : Function.Injective f) :
    (∀ x, DifferentiableAt ℝ f x → IsConformalMap (fderiv ℝ f x) →
      ∃ a : ℂ, a ≠ 0 ∧ ∀ z, fderiv ℝ f x z=a*z) ∨
    (∀ x, DifferentiableAt ℝ f x → IsConformalMap (fderiv ℝ f x) →
      ∃ a : ℂ, a ≠ 0 ∧ ∀ z, fderiv ℝ f x z=a*conj z) := by
  classical
  by_cases h : ∃ x, DifferentiableAt ℝ f x ∧ IsConformalMap (fderiv ℝ f x) ∧
      ∃ a : ℂ, a ≠ 0 ∧ ∀ z, fderiv ℝ f x z=a*z
  · obtain ⟨x,hx,-,a,ha,haz⟩ := h
    left
    intro y hy hfy
    rcases conformal_scalar_cases hfy with han | ⟨b,hb,hbz⟩
    · exact han
    · exact (no_opposite_similarities hf hi hx.hasFDerivAt hy.hasFDerivAt ha hb haz hbz).elim
  · right
    intro y hy hfy
    rcases conformal_scalar_cases hfy with ⟨a,ha,haz⟩ | han
    · exact (h ⟨y,hy,hfy,a,ha,haz⟩).elim
    · exact han
end CannonOrientation

end
end
section
noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open MeasureTheory Filter Set Metric Function ContinuousLinearMap
open scoped Topology Convolution ContDiff Pointwise

namespace CannonBeltrami
open ContinuousLinearMap

lemma partialBar_reflect {κ : ℂ → ℂ} (hκ : Differentiable ℝ κ) (x z : ℂ) :
    partialBar (fun w => κ (x-w)) z = -partialBar κ (x-z) := by
  have hd := (hκ (x-z)).hasFDerivAt.comp z ((hasFDerivAt_const x z).sub (hasFDerivAt_id z))
  have hd' : fderiv ℝ (fun w => κ (x-w)) z = _ := hd.fderiv
  unfold partialBar
  rw [hd']
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,zero_sub,
    neg_apply,map_neg]
  ring

lemma barProject_apply (D : ℂ →L[ℝ] ℂ) :
    barProject D=(D 1+Complex.I*D Complex.I)/2 := by
  simp [barProject,smul_eq_mul]; ring

lemma convolution_partialBar {F κ : ℂ → ℂ} (hF : LocallyIntegrable F volume)
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (x : ℂ) :
    partialBar (F ⋆[mul ℝ ℂ,volume] κ) x=
      ∫ z, F z*partialBar κ (x-z) := by
  let L := mul ℝ ℂ
  let D : ℂ → (ℂ →L[ℝ] ℂ) := fun z => L.precompR ℂ (F z) (fderiv ℝ κ (x-z))
  have hD : Integrable D volume :=
    (hc.fderiv ℝ).convolutionExists_right (L.precompR ℂ) hF
      ((hκ.of_le (by simp) : ContDiff ℝ 1 κ).continuous_fderiv (by simp)) x
  have hd := hc.hasFDerivAt_convolution_right L hF (hκ.of_le (by simp)) x
  change (fderiv ℝ (F ⋆[L,volume] κ) x 1 +
    Complex.I * fderiv ℝ (F ⋆[L,volume] κ) x Complex.I) / 2 = _
  rw [← barProject_apply]
  rw [hd.fderiv]
  change barProject (∫ z, D z)=_
  rw [← barProject.integral_comp_comm hD]
  apply integral_congr_ae
  exact .of_forall (fun z => by
    change barProject (D z) = F z * partialBar κ (x-z)
    rw [barProject_apply]
    simp only [D,L,precompR_apply,compL_apply,ContinuousLinearMap.comp_apply,mul_apply']
    unfold partialBar
    ring)

lemma weak_partialBar_convolution {F : ℂ → ℂ} (hF : LocallyIntegrable F volume)
    (hw : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, F z*partialBar φ z)=0)
    {κ : ℂ → ℂ} (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) :
    Differentiable ℂ (F ⋆[mul ℝ ℂ,volume] κ) := by
  have hs := hc.contDiff_convolution_right (mul ℝ ℂ) hF hκ
  intro x
  apply differentiableAt_of_partialBar_zero (hs.differentiable (by simp) x)
  rw [convolution_partialBar hF hκ hc]
  let ψ : ℂ → ℂ := fun z => κ (x-z)
  have hψ : ContDiff ℝ ∞ ψ := hκ.comp (contDiff_const.sub contDiff_id)
  have hcψ : HasCompactSupport ψ := by
    exact hc.comp_homeomorph ((Homeomorph.neg ℂ).trans (Homeomorph.addLeft x))
  let φ := hcψ.toSchwartzMap hψ
  have hh := hw φ hcψ
  have he (z : ℂ) : partialBar φ z=-partialBar κ (x-z) :=
    partialBar_reflect (hκ.differentiable (by simp)) x z
  simp only [he,mul_neg,integral_neg,neg_eq_zero] at hh
  exact hh

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

theorem weak_partialBar_zero_holomorphic {F : ℂ → ℂ} (hF : Continuous F)
    (hw : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, F z*partialBar φ z)=0) : Differentiable ℂ F := by
  have hs (n : ℕ) : Differentiable ℂ (mollify F n) := by
    rw [mollify_eq_complex_convolution]
    exact weak_partialBar_convolution hF.locallyIntegrable hw
      (Complex.ofRealCLM.contDiff.comp (mollifier n).contDiff_normed)
      ((mollifier n).hasCompactSupport_normed.comp_left Complex.ofReal_zero)
  exact differentiableOn_univ.mp
    ((tendstoLocallyUniformlyOn_univ.mpr (mollify_locally_uniform hF)).differentiableOn
      (.of_forall (fun n => (hs n).differentiableOn)) isOpen_univ)
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
-- module Solutions.OAIQ046_CN.Cannon_Conformal_BoundedCrossRatios
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace
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
noncomputable section
namespace CannonMetricQC
open MeasureTheory CannonBeltrami CannonOrientation
open scoped ComplexConjugate

lemma weakQS_ae_complexLinear_holomorphic (f : ℂ ≃ₜ ℂ) {H : ℝ}
    (hH : 0 < H) (hf : WeakQS f H)
    (hl : ∀ᵐ x : ℂ, ∃ a : ℂ, ∀ z, fderiv ℝ (f : ℂ → ℂ) x z=a*z) :
    Differentiable ℂ (f : ℂ → ℂ) := by
  have hb : ∀ᵐ x : ℂ, partialBar f x=0 := by
    filter_upwards [hl] with x hx
    obtain ⟨a,ha⟩ := hx
    unfold partialBar
    rw [ha,ha,mul_one]
    have he : Complex.I*(a*Complex.I)= -a := by
      calc
        _ = a*(Complex.I*Complex.I) := by ring
        _ = -a := by simp
    rw [he]; simp
  apply weak_partialBar_zero_holomorphic f.continuous
  intro φ hφ
  rw [(weakQS_partial_integration_by_parts f hH hf φ hφ).2]
  have he : (∫ z, partialBar f z*φ z)=0 := by
    calc
      _ = ∫ z : ℂ, (0:ℂ) := integral_congr_ae (hb.mono (fun _ hh => by rw [hh,zero_mul]))
      _ = 0 := integral_zero _ _
  rw [he,neg_zero]

theorem weakQS_ae_conformal_rigidity (f : ℂ ≃ₜ ℂ) {H : ℝ}
    (hH : 0 < H) (hf : WeakQS f H)
    (hc : ∀ᵐ x : ℂ, IsConformalMap (fderiv ℝ (f : ℂ → ℂ) x)) :
    Differentiable ℂ (f : ℂ → ℂ) ∨ Differentiable ℂ (fun z => conj (f z)) := by
  have hd := weakQS_ae_differentiable f hH hf
  rcases conformal_differential_orientation f.continuous f.injective with hp | hn
  · left
    apply weakQS_ae_complexLinear_holomorphic f hH hf
    filter_upwards [hd,hc] with x hx hcx
    obtain ⟨a,-,ha⟩ := hp x hx hcx
    exact ⟨a,ha⟩
  · right
    let F : ℂ ≃ₜ ℂ := f.trans Complex.conjCLE.toHomeomorph
    have hF : WeakQS F H := by
      intro x y z hxyz
      simpa only [F,Homeomorph.trans_apply,ContinuousLinearEquiv.coe_toHomeomorph,
        Complex.conjCLE_apply,Complex.dist_conj_conj] using hf x y z hxyz
    have hl : ∀ᵐ x : ℂ, ∃ a : ℂ, ∀ z, fderiv ℝ (F : ℂ → ℂ) x z=a*z := by
      filter_upwards [hd,hc] with x hx hcx
      obtain ⟨a,-,ha⟩ := hn x hx hcx
      have he : fderiv ℝ (F : ℂ → ℂ) x=
          (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ (f : ℂ → ℂ) x) :=
        (Complex.conjCLE.hasFDerivAt.comp x hx.hasFDerivAt).fderiv
      refine ⟨conj a,fun z => ?_⟩
      rw [he]
      change conj (fderiv ℝ (f : ℂ → ℂ) x z)=conj a*z
      rw [ha,map_mul,starRingEnd_self_apply]
    exact weakQS_ae_complexLinear_holomorphic F hH hF hl
end CannonMetricQC

end
end
noncomputable section
namespace CannonMetricQC
open MeasureTheory CannonConformal
open scoped ComplexConjugate

lemma holomorphic_weakQS_inverse (f : ℂ ≃ₜ ℂ) {J : ℝ}
    (hJ : 0 < J) (hi : WeakQS f.symm J) (hf : Differentiable ℂ (f : ℂ → ℂ)) :
    Differentiable ℂ (f.symm : ℂ → ℂ) := by
  apply weakQS_ae_complexLinear_holomorphic f.symm hJ hi
  filter_upwards [weakQS_ae_differentiable f.symm hJ hi] with y hy
  let L := fderiv ℂ (f : ℂ → ℂ) (f.symm y)
  let B := fderiv ℝ (f.symm : ℂ → ℂ) y
  have hc := ((hf (f.symm y)).hasFDerivAt.restrictScalars ℝ).comp y hy.hasFDerivAt
  have hid : (f : ℂ → ℂ) ∘ (f.symm : ℂ → ℂ)=id := by funext z; simp
  rw [hid] at hc
  have he (z : ℂ) : L (B z)=z := congrArg (fun A : ℂ →L[ℝ] ℂ => A z)
    (hc.unique (hasFDerivAt_id y))
  have hl (v : ℂ) : L v=v*L 1 := by simpa using L.map_smul v (1:ℂ)
  have hp (z : ℂ) : L 1*B z=z := by
    calc
      L 1*B z = B z*L 1 := mul_comm _ _
      _ = L (B z) := (hl _).symm
      _ = z := he z
  have hn : L 1 ≠ 0 := by intro hz; have hh := hp 1; rw [hz,zero_mul] at hh; exact zero_ne_one hh
  refine ⟨(L 1)⁻¹,fun z => ?_⟩
  calc
    B z = (L 1)⁻¹*(L 1*B z) := by rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]
    _ = (L 1)⁻¹*z := by rw [hp]

lemma WeakQS.pre_conj (f : ℂ ≃ₜ ℂ) {H : ℝ} (hf : WeakQS f H) :
    WeakQS (Complex.conjCLE.toHomeomorph.trans f) H := by
  intro x y z hh
  exact hf (conj x) (conj y) (conj z) (by simpa only [Complex.dist_conj_conj] using hh)

theorem weakQS_ae_conformal_affine_or_anti (f : ℂ ≃ₜ ℂ) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hf : WeakQS f H) (hi : WeakQS f.symm J)
    (hc : ∀ᵐ x : ℂ, IsConformalMap (fderiv ℝ (f : ℂ → ℂ) x)) :
    (∃ a b : ℂ, a ≠ 0 ∧ ∀ z, f z=a*z+b) ∨
    (∃ a b : ℂ, a ≠ 0 ∧ ∀ z, f z=a*conj z+b) := by
  rcases weakQS_ae_conformal_rigidity f hH hf hc with hp | hn
  · exact Or.inl (biholomorphic_affine f hp (holomorphic_weakQS_inverse f hJ hi hp))
  · let F : ℂ ≃ₜ ℂ := f.trans Complex.conjCLE.toHomeomorph
    have hFi : WeakQS F.symm J := hi.pre_conj f.symm
    obtain ⟨a,b,ha,he⟩ := biholomorphic_affine F hn (holomorphic_weakQS_inverse F hJ hFi hn)
    right
    refine ⟨conj a,conj b,by simpa using ha,?_⟩
    intro z
    have hh := congrArg (starRingEnd ℂ) (he z)
    simpa only [F,Homeomorph.trans_apply,ContinuousLinearEquiv.coe_toHomeomorph,
      Complex.conjCLE_apply,starRingEnd_self_apply,map_add,map_mul] using hh
end CannonMetricQC

end
end
section
section
noncomputable section
namespace CannonMetricQC
open Metric CannonQM

lemma WeakQS.dyadic {f : ℂ → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : WeakQS f H)
    (n : ℕ) (x y z : ℂ) (h : dist x y ≤ 2^n*dist x z) :
    dist (f x) (f y) ≤ H*(H+1)^n*dist (f x) (f z) := by
  induction n generalizing y with
  | zero => simpa using hf x y z (by simpa using h)
  | succ n ihn =>
    let u := midpoint ℝ x y
    have hxu : dist x u=dist x y/2 := by simp [u,dist_left_midpoint,div_eq_mul_inv,mul_comm]
    have hux : dist u x=dist x y/2 := by rw [dist_comm,hxu]
    have huy : dist u y=dist x y/2 := by simp [u,dist_midpoint_right,div_eq_mul_inv,mul_comm]
    have h1 := ihn u (by rw [hxu]; rw [pow_succ] at h; linarith)
    have h2 := hf u y x (by rw [huy,hux])
    rw [dist_comm (f u) (f x)] at h2
    have h3 := dist_triangle (f x) (f u) (f y)
    have h4 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ H+1 by positivity)
    rw [pow_succ]
    nlinarith

lemma WeakQS.bounded_ratios {f : ℂ → ℂ} {H : ℝ} (hH : 0 < H) (hf : WeakQS f H)
    (R : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ x y z : ℂ, dist x y ≤ R*dist x z →
      dist (f x) (f y) ≤ C*dist (f x) (f z) := by
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt R (by norm_num : (1:ℝ) < 2)
  refine ⟨H*(H+1)^n,by positivity,fun x y z h => hf.dyadic hH.le n x y z ?_⟩
  exact h.trans (mul_le_mul_of_nonneg_right hn.le dist_nonneg)

theorem WeakQS.crossRatio_bound (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H) (hf : WeakQS f H)
    (T : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ x y z w : ℂ, Distinct x y z w →
      (crossRatio x y z w : ℝ) ≤ T →
      (crossRatio (f x) (f y) (f z) (f w) : ℝ) ≤ C := by
  obtain ⟨B,hB,hb⟩ := hf.bounded_ratios hH (2*max T 1+3)
  refine ⟨B^2,sq_pos_of_pos hB,fun x y z w hh hp => ?_⟩
  have hden : 0 < dist x w*dist y z := mul_pos (dist_pos.mpr hh.2.2.1)
    (dist_pos.mpr hh.2.2.2.1)
  have hprod : dist x y*dist z w ≤ max T 1*(dist x w*dist y z) := by
    apply (div_le_iff₀ hden).mp
    exact hp.trans (le_max_left _ _)
  have hfh := hh.map f.injective
  have hfden : 0 < dist (f x) (f w)*dist (f y) (f z) :=
    mul_pos (dist_pos.mpr hfh.2.2.1) (dist_pos.mpr hfh.2.2.2.1)
  change dist (f x) (f y)*dist (f z) (f w)/(dist (f x) (f w)*dist (f y) (f z)) ≤ B^2
  apply (div_le_iff₀ hfden).mpr
  rcases crossRatio_pair_bounds x y z w hh (le_max_right _ _) hprod with h | h
  · have h1 := hb x y w h.1
    have h2 := hb z w y (by simpa only [dist_comm] using h.2)
    rw [dist_comm (f z) (f y)] at h2
    nlinarith [mul_le_mul h1 h2 dist_nonneg (by positivity : 0 ≤ B*dist (f x) (f w))]
  · have h1 := hb y x z (by simpa only [dist_comm] using h.1)
    have h2 := hb w z x (by simpa only [dist_comm] using h.2)
    rw [dist_comm (f y) (f x)] at h1
    rw [dist_comm (f w) (f z),dist_comm (f w) (f x)] at h2
    nlinarith [mul_le_mul h1 h2 dist_nonneg (by positivity : 0 ≤ B*dist (f y) (f z))]

end CannonMetricQC

end
end
noncomputable section
namespace CannonQM
open Set Metric Filter Bornology Topology

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

lemma BoundedCrossRatios.comp {f : X → Y} {g : Y → Z}
    (hg : BoundedCrossRatios g) (hf : BoundedCrossRatios f) (hi : Function.Injective f) :
    BoundedCrossRatios (g ∘ f) := by
  intro T
  obtain ⟨B,hB,hb⟩ := hf T
  obtain ⟨C,hC,hc⟩ := hg B
  exact ⟨C,hC,fun x y z w hh hp => hc _ _ _ _ (hh.map hi) (hb _ _ _ _ hh hp)⟩

lemma Controlled.boundedCrossRatios {f : X → Y} {η : Distortion} (hf : Controlled f η) :
    BoundedCrossRatios f := by
  intro T
  refine ⟨(η T.toNNReal:ℝ)+1,by positivity,?_⟩
  intro x y z w hh hp
  have ht : crossRatio x y z w ≤ T.toNNReal := by
    exact_mod_cast hp.trans (Real.le_coe_toNNReal T)
  have hc := (hf x y z w hh).trans (η.monotone ht)
  have hc' := NNReal.coe_le_coe.mpr hc
  linarith

lemma isOpen_distinct_quad : IsOpen {p : Fin 4 → X | Distinct (p 0) (p 1) (p 2) (p 3)} := by
  exact (isOpen_ne_fun (continuous_apply 0) (continuous_apply 1)).inter
    ((isOpen_ne_fun (continuous_apply 0) (continuous_apply 2)).inter
    ((isOpen_ne_fun (continuous_apply 0) (continuous_apply 3)).inter
    ((isOpen_ne_fun (continuous_apply 1) (continuous_apply 2)).inter
    ((isOpen_ne_fun (continuous_apply 1) (continuous_apply 3)).inter
      (isOpen_ne_fun (continuous_apply 2) (continuous_apply 3))))))

lemma boundedCrossRatios_dense {α : Type*} (e : α → X) (he : DenseRange e)
    (f : X → Y) (hf : Continuous f) (hi : Function.Injective f)
    (h : ∀ T : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ p : Fin 4 → α,
      Distinct (e (p 0)) (e (p 1)) (e (p 2)) (e (p 3)) →
      (crossRatio (e (p 0)) (e (p 1)) (e (p 2)) (e (p 3)) : ℝ) ≤ T →
      (crossRatio (f (e (p 0))) (f (e (p 1))) (f (e (p 2))) (f (e (p 3))) : ℝ) ≤ C) :
    BoundedCrossRatios f := by
  intro T
  obtain ⟨C,hC,hc⟩ := h (T+1)
  refine ⟨C,hC,?_⟩
  intro x y z w hh hp
  by_contra hn
  have hn' : C < (crossRatio (f x) (f y) (f z) (f w) : ℝ) := lt_of_not_ge hn
  let p : Fin 4 → X := ![x,y,z,w]
  let a : (Fin 4 → X) → ℝ := fun q => dist (q 0) (q 1)*dist (q 2) (q 3)
  let b : (Fin 4 → X) → ℝ := fun q => dist (q 0) (q 3)*dist (q 1) (q 2)
  let c : (Fin 4 → X) → ℝ := fun q => dist (f (q 0)) (f (q 1))*dist (f (q 2)) (f (q 3))
  let d : (Fin 4 → X) → ℝ := fun q => dist (f (q 0)) (f (q 3))*dist (f (q 1)) (f (q 2))
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hb : Continuous b := by dsimp [b]; fun_prop
  have hc' : Continuous c := by dsimp [c]; fun_prop
  have hd : Continuous d := by dsimp [d]; fun_prop
  let U : Set (Fin 4 → X) := {q | Distinct (q 0) (q 1) (q 2) (q 3)} ∩
    {q | a q < (T+1)*b q} ∩ {q | C*d q < c q}
  have hU : IsOpen U := (isOpen_distinct_quad.inter (isOpen_lt ha (continuous_const.mul hb))).inter
    (isOpen_lt (continuous_const.mul hd) hc')
  have hden : 0 < dist x w*dist y z := mul_pos (dist_pos.mpr hh.2.2.1)
    (dist_pos.mpr hh.2.2.2.1)
  have hfh := hh.map hi
  have hfden : 0 < dist (f x) (f w)*dist (f y) (f z) := mul_pos
    (dist_pos.mpr hfh.2.2.1) (dist_pos.mpr hfh.2.2.2.1)
  have hpU : p ∈ U := by
    refine ⟨⟨hh,?_⟩,?_⟩
    · have hhh := (div_lt_iff₀ hden).mp (lt_of_le_of_lt hp (by linarith : T < T+1))
      exact hhh
    · exact (lt_div_iff₀ hfden).mp hn'
  have hde : DenseRange (fun q : Fin 4 → α => fun i => e (q i)) := DenseRange.piMap (fun _ => he)
  obtain ⟨q,hq⟩ := hde.exists_mem_open hU ⟨p,hpU⟩
  have hhq := hq.1.1
  have hdq : 0 < dist (e (q 0)) (e (q 3))*dist (e (q 1)) (e (q 2)) :=
    mul_pos (dist_pos.mpr hhq.2.2.1) (dist_pos.mpr hhq.2.2.2.1)
  have hFq := hhq.map hi
  have hdfq : 0 < dist (f (e (q 0))) (f (e (q 3)))*dist (f (e (q 1))) (f (e (q 2))) :=
    mul_pos (dist_pos.mpr hFq.2.2.1) (dist_pos.mpr hFq.2.2.2.1)
  have hcrq : (crossRatio (e (q 0)) (e (q 1)) (e (q 2)) (e (q 3)) : ℝ) ≤ T+1 :=
    ((div_lt_iff₀ hdq).mpr hq.1.2).le
  have hbound := hc q hhq hcrq
  have hviol : C < (crossRatio (f (e (q 0))) (f (e (q 1))) (f (e (q 2))) (f (e (q 3))) : ℝ) :=
    (lt_div_iff₀ hdfq).mpr hq.2
  exact not_lt_of_ge hbound hviol

end CannonQM

namespace CannonMobius
open CannonQM CannonMetricQC Set
open scoped OnePoint

theorem weakQS_sphere_boundedCrossRatios (F : ℂ ≃ₜ ℂ) {H : ℝ}
    (hH : 0 < H) (hF : WeakQS F H) : BoundedCrossRatios F.onePointCongr := by
  apply boundedCrossRatios_dense (fun z : ℂ => (z:Sphere)) OnePoint.denseRange_coe
    F.onePointCongr F.onePointCongr.continuous F.onePointCongr.injective
  intro T
  obtain ⟨C,hC,hc⟩ := hF.crossRatio_bound F hH T
  refine ⟨C,hC,fun p hh hp => ?_⟩
  have hhp : Distinct (p 0) (p 1) (p 2) (p 3) := by
    rcases hh with ⟨h1,h2,h3,h4,h5,h6⟩
    exact ⟨fun he => h1 (congrArg (fun z : ℂ => (z:Sphere)) he),
      fun he => h2 (congrArg (fun z : ℂ => (z:Sphere)) he),
      fun he => h3 (congrArg (fun z : ℂ => (z:Sphere)) he),
      fun he => h4 (congrArg (fun z : ℂ => (z:Sphere)) he),
      fun he => h5 (congrArg (fun z : ℂ => (z:Sphere)) he),
      fun he => h6 (congrArg (fun z : ℂ => (z:Sphere)) he)⟩
  have hpp : (crossRatio (p 0) (p 1) (p 2) (p 3) : ℝ) ≤ T := by simpa only [coe_crossRatio] using hp
  change (crossRatio ((F (p 0):ℂ):Sphere) ((F (p 1):ℂ):Sphere) ((F (p 2):ℂ):Sphere) ((F (p 3):ℂ):Sphere) : ℝ) ≤ C
  simpa only [coe_crossRatio] using hc _ _ _ _ hhp hpp

lemma boundedCrossRatios_restriction (f : Sphere ≃ₜ Sphere) (hi : f ∞=∞)
    (hf : BoundedCrossRatios f) : BoundedCrossRatios (finiteRestriction f hi) := by
  intro T
  obtain ⟨C,hC,hc⟩ := hf T
  refine ⟨C,hC,fun x y z w hh hp => ?_⟩
  have he (u : ℂ) : f (u:Sphere)=((finiteRestriction f hi u:ℂ):Sphere) :=
    (coe_coordinate (coe_map_ne_infty f hi u)).symm
  have hh' := hh.map (OnePoint.coe_injective (X:=ℂ))
  have h := hc (x:Sphere) (y:Sphere) (z:Sphere) (w:Sphere) hh' (by simpa only [coe_crossRatio] using hp)
  simpa only [he,coe_crossRatio] using h

end CannonMobius

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
namespace CannonMobius
open Set Filter Topology MeasureTheory
open scoped OnePoint

lemma sphereMeasure_apply (S : Set Sphere) :
    sphereMeasure S=volume ((fun z : ℂ => (z:Sphere)) ⁻¹' S) :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding.map_apply volume S

lemma chartDomain_ae (f : Sphere ≃ₜ Sphere) (s t : Bool) :
    ∀ᵐ z : ℂ, z ∈ chartDomain s t f := by
  rw [ae_iff]
  apply Set.Subsingleton.measure_zero
  intro x hx y hy
  have hx' : chart t (f (chart s (x:Sphere)))=∞ := by simpa only [chartDomain,mem_ofPred_eq,not_not] using hx
  have hy' : chart t (f (chart s (y:Sphere)))=∞ := by simpa only [chartDomain,mem_ofPred_eq,not_not] using hy
  exact OnePoint.coe_injective ((chart s).injective (f.injective ((chart t).injective (hx'.trans hy'.symm))))

lemma sphere_image_null_of_chart (f : Sphere ≃ₜ Sphere)
    (hN : ∀ S : Set ℂ, volume S=0 →
      volume (inChart false false f '' (S ∩ chartDomain false false f))=0)
    {T : Set Sphere} (hT : sphereMeasure T=0) : sphereMeasure (f '' T)=0 := by
  rw [sphereMeasure_apply] at hT ⊢
  let S := (fun z : ℂ => (z:Sphere)) ⁻¹' T
  have hsub : (fun z : ℂ => (z:Sphere)) ⁻¹' (f '' T) ⊆
      inChart false false f '' (S ∩ chartDomain false false f) ∪ {coordinate (f ∞)} := by
    rintro z ⟨p,hp,he⟩
    induction p using OnePoint.rec with
    | infty =>
      right
      exact (congrArg coordinate he).symm
    | coe w =>
      left
      refine ⟨w,⟨hp,?_⟩,?_⟩
      · change f (w:Sphere) ≠ ∞
        rw [he]
        exact OnePoint.coe_ne_infty z
      · change coordinate (f (w:Sphere))=z
        rw [he,coordinate_coe]
  exact measure_mono_null hsub (measure_union_null (hN S hT) (measure_singleton _))

lemma analytic_sphere_image_null {f : Sphere ≃ₜ Sphere} (hf : IsAnalytic f)
    {T : Set Sphere} (hT : sphereMeasure T=0) : sphereMeasure (f '' T)=0 := by
  apply sphere_image_null_of_chart f _ hT
  intro S hS
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (((hf false false).restrictScalars ℝ).mono inter_subset_right)
    (measure_mono_null inter_subset_left hS)

lemma onePoint_image_null (F : ℂ ≃ₜ ℂ)
    (hF : ∀ S : Set ℂ, volume S=0 → volume (F '' S)=0)
    {T : Set Sphere} (hT : sphereMeasure T=0) :
    sphereMeasure (F.onePointCongr '' T)=0 := by
  apply sphere_image_null_of_chart F.onePointCongr _ hT
  intro S hS
  have he : inChart false false F.onePointCongr=(F : ℂ → ℂ) := by
    funext z
    simp [inChart,chart,coordinate]
  rw [he]
  exact measure_mono_null (image_mono inter_subset_left) (hF S hS)

theorem controlled_sphere_image_null (f : Sphere ≃ₜ Sphere) {η : CannonQM.Distortion}
    (hf : CannonQM.Controlled f η) {T : Set Sphere} (hT : sphereMeasure T=0) :
    sphereMeasure (f '' T)=0 := by
  obtain ⟨M,hM,hMa,hF⟩ := normalized_weakQS f hf
  let F := finiteRestriction (M*f) hM
  have hN := onePoint_image_null F
    (fun S => CannonMetricQC.weakQS_image_null F (by positivity) hF (S:=S)) hT
  have hN' := analytic_sphere_image_null hMa.2 hN
  have he : (M.symm : Sphere → Sphere) ∘ (F.onePointCongr : Sphere → Sphere)=f := by
    rw [show F.onePointCongr=M*f from restriction_extension (M*f) hM]
    funext p
    exact M.symm_apply_apply (f p)
  rw [image_image] at hN'
  change sphereMeasure (((M.symm : Sphere → Sphere) ∘ (F.onePointCongr : Sphere → Sphere)) '' T)=0 at hN'
  rwa [he] at hN'

theorem controlled_sphere_quasiMeasurePreserving (f : Sphere ≃ₜ Sphere)
    {η : CannonQM.Distortion} (hf : CannonQM.Controlled f η) :
    Measure.QuasiMeasurePreserving (f : Sphere → Sphere) sphereMeasure sphereMeasure := by
  refine ⟨f.continuous.measurable,?_⟩
  intro S hS
  rw [f.measurableEmbedding.map_apply]
  rw [← show f.symm '' S=f ⁻¹' S from f.toEquiv.image_symm_eq_preimage S]
  exact controlled_sphere_image_null f.symm (hf.inverse f) hS

end CannonMobius

namespace CannonMobius
open Set Filter Topology MeasureTheory
open scoped OnePoint

lemma chart_mul_eventually (f g : Sphere ≃ₜ Sphere) {z : ℂ}
    (hz : z ∈ chartDomain false false g) :
    inChart false false (f*g) =ᶠ[𝓝 z]
      (fun w => inChart false false f (inChart false false g w)) := by
  filter_upwards [(isOpen_chartDomain false false g).mem_nhds hz] with w hw
  change coordinate (f (g (w:Sphere)))=coordinate (f (coordinate (g (w:Sphere)):Sphere))
  change g (w:Sphere) ≠ ∞ at hw
  rw [coe_coordinate hw]

lemma chart_symm_domain (f : Sphere ≃ₜ Sphere) {z : ℂ}
    (hz : z ∈ chartDomain false false f) :
    inChart false false f z ∈ chartDomain false false f.symm := by
  change f.symm (coordinate (f (z:Sphere)):Sphere) ≠ ∞
  change f (z:Sphere) ≠ ∞ at hz
  rw [coe_coordinate hz,f.symm_apply_apply]
  exact OnePoint.coe_ne_infty z

lemma chart_symm_comp_eventually (f : Sphere ≃ₜ Sphere) {z : ℂ}
    (hz : z ∈ chartDomain false false f) :
    (fun w => inChart false false f.symm (inChart false false f w)) =ᶠ[𝓝 z] id := by
  filter_upwards [(isOpen_chartDomain false false f).mem_nhds hz] with w hw
  change coordinate (f.symm (coordinate (f (w:Sphere)):Sphere))=w
  change f (w:Sphere) ≠ ∞ at hw
  rw [coe_coordinate hw,f.symm_apply_apply,coordinate_coe]

lemma analytic_chart_bijective (f : Sphere ≃ₜ Sphere) (hf : f ∈ biholomorphic)
    {z : ℂ} (hz : z ∈ chartDomain false false f) :
    Function.Bijective (fderiv ℝ (inChart false false f) z) := by
  have hd := (analytic_differentiableAt hf.1 false false hz).restrictScalars ℝ
  have hi := (analytic_differentiableAt hf.2 false false (chart_symm_domain f hz)).restrictScalars ℝ
  have he := ((hi.hasFDerivAt.comp z hd.hasFDerivAt).congr_of_eventuallyEq
    (chart_symm_comp_eventually f hz).symm).unique (hasFDerivAt_id z)
  have hl : Function.LeftInverse (fderiv ℝ (inChart false false f.symm) (inChart false false f z))
      (fderiv ℝ (inChart false false f) z) := by
    intro v
    exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) he
  exact ⟨hl.injective,LinearMap.injective_iff_surjective.mp hl.injective⟩

lemma analytic_chart_conformal (f : Sphere ≃ₜ Sphere) (hf : f ∈ biholomorphic)
    {z : ℂ} (hz : z ∈ chartDomain false false f) :
    IsConformalMap (fderiv ℝ (inChart false false f) z) := by
  have hd := analytic_differentiableAt hf.1 false false hz
  have hbij := analytic_chart_bijective f hf hz
  rw [(hd.hasFDerivAt.restrictScalars ℝ).fderiv] at hbij ⊢
  apply isConformalMap_complex_linear
  intro he
  apply (zero_ne_one : (0:ℂ) ≠ 1)
  apply hbij.1
  rw [he]
  rfl

theorem controlled_sphere_ae_differentiable (f : Sphere ≃ₜ Sphere)
    {η : CannonQM.Distortion} (hf : CannonQM.Controlled f η) :
    ∀ᵐ z : ℂ, DifferentiableAt ℝ (inChart false false f) z := by
  obtain ⟨M,hM,hMa,hF⟩ := normalized_weakQS f hf
  let F := finiteRestriction (M*f) hM
  filter_upwards [CannonMetricQC.weakQS_ae_differentiable F (by positivity) hF,
    chartDomain_ae f false false] with z hz hdom
  have he (w : ℂ) : (F w:Sphere)=M (f (w:Sphere)) :=
    coe_coordinate (coe_map_ne_infty (M*f) hM w)
  have hMd : F z ∈ chartDomain false false M.symm := by
    change M.symm (F z:Sphere) ≠ ∞
    rw [he,M.symm_apply_apply]
    exact hdom
  have hh := ((analytic_differentiableAt hMa.2 false false hMd).restrictScalars ℝ).comp z hz
  have heq : inChart false false f=inChart false false M.symm ∘ (F : ℂ → ℂ) := by
    funext w
    change coordinate (f (w:Sphere))=coordinate (M.symm (F w:Sphere))
    rw [he,M.symm_apply_apply]
  rw [heq]
  exact hh

end CannonMobius

namespace CannonMobius
open Set Filter Topology MeasureTheory
open scoped OnePoint

lemma ae_sphere_iff {P : Sphere → Prop} :
    (∀ᵐ p ∂sphereMeasure, P p) ↔ ∀ᵐ z : ℂ, P (z:Sphere) := by
  simp only [ae_iff,sphereMeasure_apply,preimage_ofPred_eq]

lemma controlled_chart_ae_pullback (f : Sphere ≃ₜ Sphere)
    {η : CannonQM.Distortion} (hf : CannonQM.Controlled f η)
    {P : ℂ → Prop} (hP : ∀ᵐ z : ℂ, P z) :
    ∀ᵐ z : ℂ, P (inChart false false f z) := by
  have hps : ∀ᵐ p ∂sphereMeasure, P (coordinate p) := by
    rw [ae_sphere_iff]
    simpa only [coordinate_coe] using hP
  simpa only [ae_sphere_iff,inChart,chart,Homeomorph.one_apply] using
    (controlled_sphere_quasiMeasurePreserving f hf).ae hps

theorem controlled_sphere_ae_bijective_fderiv (f : Sphere ≃ₜ Sphere)
    {η : CannonQM.Distortion} (hf : CannonQM.Controlled f η) :
    ∀ᵐ z : ℂ, Function.Bijective (fderiv ℝ (inChart false false f) z) := by
  filter_upwards [controlled_sphere_ae_differentiable f hf,
    controlled_chart_ae_pullback f hf
      (controlled_sphere_ae_differentiable f.symm (hf.inverse f)),
    chartDomain_ae f false false] with z hz hi hdom
  have he := ((hi.hasFDerivAt.comp z hz.hasFDerivAt).congr_of_eventuallyEq
    (chart_symm_comp_eventually f hdom).symm).unique (hasFDerivAt_id z)
  have hl : Function.LeftInverse
      (fderiv ℝ (inChart false false f.symm) (inChart false false f z))
      (fderiv ℝ (inChart false false f) z) := by
    intro v
    exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) he
  exact ⟨hl.injective,LinearMap.injective_iff_surjective.mp hl.injective⟩

end CannonMobius

end
end
section
noncomputable section

namespace CannonMetricQC
open Filter MeasureTheory
open scoped Topology

lemma WeakQS.derivative_distortion {f : ℂ → ℂ} {H : ℝ} (hf : WeakQS f H)
    {x : ℂ} {A : ℂ →L[ℝ] ℂ} (ha : HasFDerivAt f A x)
    {u v : ℂ} (huv : ‖u‖ ≤ ‖v‖) : ‖A u‖ ≤ H*‖A v‖ := by
  apply le_of_tendsto_of_tendsto (ha.lim_real u |>.norm)
    ((ha.lim_real v |>.norm).const_mul H)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with c hc
  have hdist : dist x (x+c⁻¹ • u) ≤ dist x (x+c⁻¹ • v) := by
    simpa only [dist_eq_norm,sub_add_cancel_left,norm_neg,norm_smul]
      using mul_le_mul_of_nonneg_left huv (norm_nonneg c⁻¹)
  have h := hf x (x+c⁻¹ • u) (x+c⁻¹ • v) hdist
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hc]
  rw [dist_comm x (x+c⁻¹ • u),dist_comm x (x+c⁻¹ • v)] at hdist
  rw [dist_comm (f x) (f (x+c⁻¹ • u)),dist_comm (f x) (f (x+c⁻¹ • v)),dist_eq_norm,dist_eq_norm] at h
  nlinarith
end CannonMetricQC

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

namespace CannonMetricQC
open CannonConformal
open scoped ComplexOrder

lemma derivative_apply (A : ℂ →L[ℝ] ℂ) (z : ℂ) :
    A z=z.re • A 1+z.im • A Complex.I := by
  calc
    A z = A (z.re • (1 : ℂ)+z.im • Complex.I) := by
      congr 1
      simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
    _ = _ := by rw [map_add,map_smul,map_smul]

lemma derivativeForm_evaluate (A : ℂ →L[ℝ] ℂ) (x y : ℝ) :
    evaluate (derivativeForm A) x y=‖A (⟨x,y⟩ : ℂ)‖^2 := by
  rw [derivative_apply,Complex.sq_norm]
  simp [evaluate,derivativeForm,Complex.sq_norm,Complex.normSq_apply]
  ring

lemma derivativeForm_det (A : ℂ →L[ℝ] ℂ) :
    determinant (derivativeForm A)=(derivativeDet A)^2 := by
  simp [determinant,derivativeForm,derivativeDet,Complex.sq_norm,Complex.normSq_apply]
  ring

lemma linear_distortion_scaled {A : ℂ →L[ℝ] ℂ} {H : ℝ}
    (ha : ∀ u v : ℂ, ‖u‖ ≤ ‖v‖ → ‖A u‖ ≤ H*‖A v‖) (u v : ℂ) :
    ‖A u‖*‖v‖ ≤ H*‖A v‖*‖u‖ := by
  by_cases hu : u=0
  · simp [hu]
  have hp : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hn : ‖(‖v‖/‖u‖) • u‖=‖v‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    field_simp
  have h := ha ((‖v‖/‖u‖) • u) v hn.le
  rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)] at h
  have he : (‖v‖/‖u‖)*‖A u‖=(‖A u‖*‖v‖)/‖u‖ := by ring
  rw [he] at h
  exact (div_le_iff₀ hp).mp h

theorem linear_distortion_jacobian {A : ℂ →L[ℝ] ℂ} {H : ℝ} (hH : 0 < H)
    (ha : ∀ u v : ℂ, ‖u‖ ≤ ‖v‖ → ‖A u‖ ≤ H*‖A v‖) (u : ℂ) :
    ‖A u‖^2 ≤ H^2* |derivativeDet A| * ‖u‖^2 := by
  by_cases hu : u=0
  · simp [hu]
  have hp : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let ε : ℝ := ‖A u‖^2/(H^2*‖u‖^2)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hl : LowerBound ε (derivativeForm A) := by
    intro x y
    let v : ℂ := ⟨x,y⟩
    have hh := linear_distortion_scaled ha u v
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ‖A u‖*‖v‖) hh 2
    have hv : ‖v‖^2=x^2+y^2 := by rw [Complex.sq_norm]; simp [v,Complex.normSq_apply,pow_two]
    rw [mul_pow,mul_pow,mul_pow,hv] at hs
    rw [derivativeForm_evaluate]
    change ε*(x^2+y^2) ≤ ‖A v‖^2
    dsimp [ε]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < H^2*‖u‖^2)).mpr
    nlinarith only [hs]
  have hd := determinant_ge_sq_lower hε hl
  rw [derivativeForm_det] at hd
  have he : ε ≤ |derivativeDet A| := by
    nlinarith [sq_abs (derivativeDet A),abs_nonneg (derivativeDet A)]
  dsimp [ε] at he
  have he' := (div_le_iff₀ (by positivity : 0 < H^2*‖u‖^2)).mp he
  nlinarith only [he']

lemma derivativeDet_eq_det (A : ℂ →L[ℝ] ℂ) : derivativeDet A=A.toLinearMap.det := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI,Matrix.det_fin_two]
  simp [derivativeDet,LinearMap.toMatrix_apply,Complex.coe_basisOneI,Complex.coe_basisOneI_repr]

lemma derivativeDet_ne_zero {A : ℂ →L[ℝ] ℂ} (hA : Function.Bijective A) :
    derivativeDet A ≠ 0 := by
  rw [derivativeDet_eq_det]
  exact (LinearEquiv.ofBijective A.toLinearMap hA).isUnit_det'.ne_zero
end CannonMetricQC

end
end
end
noncomputable section
namespace CannonMobius
open Set Filter Topology MeasureTheory
open scoped OnePoint

lemma chart_normalized_eq (f M : Sphere ≃ₜ Sphere) (hM : (M*f) ∞=∞) :
    inChart false false f=inChart false false M.symm ∘ finiteRestriction (M*f) hM := by
  funext w
  change coordinate (f (w:Sphere))=
    coordinate (M.symm (coordinate ((M*f) (w:Sphere)):Sphere))
  rw [coe_coordinate (coe_map_ne_infty (M*f) hM w)]
  simp only [Homeomorph.mul_apply,Homeomorph.symm_apply_apply]

theorem controlled_sphere_ae_distortion (f : Sphere ≃ₜ Sphere)
    {η : CannonQM.Distortion} (hf : CannonQM.Controlled f η) :
    ∀ᵐ z : ℂ, ∀ u v : ℂ, ‖u‖ ≤ ‖v‖ →
      ‖fderiv ℝ (inChart false false f) z u‖ ≤
        (1+2*(η 2:ℝ))*‖fderiv ℝ (inChart false false f) z v‖ := by
  obtain ⟨M,hM,hMa,hF⟩ := normalized_weakQS f hf
  let F := finiteRestriction (M*f) hM
  filter_upwards [CannonMetricQC.weakQS_ae_differentiable F (by positivity) hF,
    chartDomain_ae f false false] with z hz hdom
  have he (w : ℂ) : (F w:Sphere)=M (f (w:Sphere)) :=
    coe_coordinate (coe_map_ne_infty (M*f) hM w)
  have hMd : F z ∈ chartDomain false false M.symm := by
    change M.symm (F z:Sphere) ≠ ∞
    rw [he,M.symm_apply_apply]
    exact hdom
  have hd := (analytic_differentiableAt hMa.2 false false hMd).restrictScalars ℝ
  have hre : fderiv ℝ (inChart false false f) z=
      (fderiv ℝ (inChart false false M.symm) (F z)).comp (fderiv ℝ (F : ℂ → ℂ) z) := by
    rw [chart_normalized_eq f M hM]
    exact (hd.hasFDerivAt.comp z hz.hasFDerivAt).fderiv
  have hc := analytic_chart_conformal M.symm ⟨hMa.2,hMa.1⟩ hMd
  obtain ⟨r,hr,U,hU⟩ := hc
  intro u v huv
  have hh := hF.derivative_distortion hz.hasFDerivAt huv
  rw [hre,hU]
  simpa only [ContinuousLinearMap.comp_apply,smul_apply,
    norm_smul,LinearIsometry.coe_toContinuousLinearMap,U.norm_map,mul_assoc,mul_left_comm] using
    mul_le_mul_of_nonneg_left hh (norm_nonneg r)

theorem controlled_sphere_ae_jacobian_bound (f : Sphere ≃ₜ Sphere)
    {η : CannonQM.Distortion} (hf : CannonQM.Controlled f η) :
    ∀ᵐ z : ℂ, ∀ u : ℂ, ‖fderiv ℝ (inChart false false f) z u‖^2 ≤
      (1+2*(η 2:ℝ))^2* |CannonMetricQC.derivativeDet (fderiv ℝ (inChart false false f) z)| * ‖u‖^2 := by
  filter_upwards [controlled_sphere_ae_distortion f hf] with z hz
  exact CannonMetricQC.linear_distortion_jacobian (by positivity) hz

end CannonMobius

end
end
section
noncomputable section
namespace CannonConformal
open Set MeasureTheory

variable {Γ X : Type*} [Group Γ] [MeasurableSpace X]

omit [MeasurableSpace X] in
lemma orbitCore_subset (A : Γ →* Equiv.Perm X) (S : Set X) : orbitCore A S ⊆ S := by
  intro x hx
  simpa using hx 1

omit [MeasurableSpace X] in
lemma orbitCore_invariant (A : Γ →* Equiv.Perm X) (S : Set X) (g : Γ) (x : X) :
    A g x ∈ orbitCore A S ↔ x ∈ orbitCore A S := by
  constructor
  · intro hx h
    simpa only [map_mul,Equiv.Perm.mul_apply,map_inv,Equiv.Perm.inv_def,
      Equiv.symm_apply_apply] using hx (h*g⁻¹)
  · intro hx h
    simpa only [map_mul,Equiv.Perm.mul_apply] using hx (h*g)

lemma orbitCore_measurable [Countable Γ] (A : Γ →* Equiv.Perm X) {S : Set X}
    (hS : MeasurableSet S) (hA : ∀ g, Measurable (A g)) : MeasurableSet (orbitCore A S) := by
  change MeasurableSet {x | ∀ g : Γ, A g x ∈ S}
  simp_rw [ofPred_forall]
  exact MeasurableSet.iInter (fun g => hS.preimage (hA g))

theorem ae_orbitCore [Countable Γ] (A : Γ →* Equiv.Perm X) (μ : Measure X)
    (hA : ∀ g, Measure.QuasiMeasurePreserving (A g) μ μ) {S : Set X}
    (hS : ∀ᵐ x ∂μ, x ∈ S) : ∀ᵐ x ∂μ, x ∈ orbitCore A S := by
  exact ae_all_iff.mpr (fun g => (hA g).ae hS)

end CannonConformal

end
end
noncomputable section
namespace CannonMobius
open Set Filter Topology MeasureTheory CannonMetricQC
open scoped OnePoint

variable {Γ : Type*} [Group Γ]

theorem controlled_action_derivative_core [Countable Γ]
    (A : Γ →* (Sphere ≃ₜ Sphere)) {η : CannonQM.Distortion}
    (hA : ∀ g, CannonQM.Controlled (A g) η) :
    ∃ K : Set Sphere, MeasurableSet K ∧ (∀ᵐ p ∂sphereMeasure, p ∈ K) ∧
      (∀ g p, A g p ∈ K ↔ p ∈ K) ∧
      ∀ p ∈ K, GoodDifferentials A (1+2*(η 2:ℝ)) p := by
  let P := GoodDifferentials A (1+2*(η 2:ℝ))
  have hp : ∀ᵐ p ∂sphereMeasure, P p := by
    rw [ae_sphere_iff]
    have hall : ∀ᵐ z : ℂ, ∀ g : Γ,
        A g (z:Sphere) ≠ ∞ ∧ DifferentiableAt ℝ (inChart false false (A g)) z ∧
        Function.Bijective (fderiv ℝ (inChart false false (A g)) z) ∧
        ∀ u : ℂ, ‖fderiv ℝ (inChart false false (A g)) z u‖^2 ≤
          (1+2*(η 2:ℝ))^2* |derivativeDet (fderiv ℝ (inChart false false (A g)) z)| * ‖u‖^2 := by
      apply ae_all_iff.mpr
      intro g
      filter_upwards [chartDomain_ae (A g) false false,
        controlled_sphere_ae_differentiable (A g) (hA g),
        controlled_sphere_ae_bijective_fderiv (A g) (hA g),
        controlled_sphere_ae_jacobian_bound (A g) (hA g)] with z hz hd hn hb
      exact ⟨hz,hd,hn,hb⟩
    filter_upwards [hall] with z hz
    exact ⟨OnePoint.coe_ne_infty z,by simpa only [sphereDerivative,coordinate_coe] using hz⟩
  let S : Set Sphere := (toMeasurable sphereMeasure {p | ¬P p})ᶜ
  have hSm : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hSp : ∀ᵐ p ∂sphereMeasure, p ∈ S := by
    rw [ae_iff]
    change sphereMeasure ((toMeasurable sphereMeasure {p | ¬P p})ᶜᶜ)=0
    rw [compl_compl,measure_toMeasurable]
    exact (ae_iff.mp hp)
  have hsub : S ⊆ {p | P p} := by
    intro p hpS
    by_contra hn
    exact hpS (subset_toMeasurable sphereMeasure {p | ¬P p} hn)
  let B := spherePermAction A
  have hBm (g : Γ) : Measure.QuasiMeasurePreserving (B g) sphereMeasure sphereMeasure :=
    controlled_sphere_quasiMeasurePreserving (A g) (hA g)
  refine ⟨CannonConformal.orbitCore B S,
    CannonConformal.orbitCore_measurable B hSm (fun g => (hBm g).measurable),
    CannonConformal.ae_orbitCore B sphereMeasure hBm hSp,?_,?_⟩
  · exact CannonConformal.orbitCore_invariant B S
  · intro p hpK
    exact hsub (CannonConformal.orbitCore_subset B S hpK)

theorem sphereDerivative_mul_on_core (A : Γ →* (Sphere ≃ₜ Sphere))
    {K : Set Sphere} {H : ℝ} (hK : ∀ g p, A g p ∈ K ↔ p ∈ K)
    (hgood : ∀ p ∈ K, GoodDifferentials A H p) {p : Sphere} (hp : p ∈ K) (g h : Γ) :
    sphereDerivative (A (g*h)) p =
      (sphereDerivative (A g) (A h p)).comp (sphereDerivative (A h) p) := by
  have hp0 := (hgood p hp).1
  have hh := (hgood p hp).2 h
  have hg := (hgood (A h p) ((hK h p).mpr hp)).2 g
  have hd : coordinate p ∈ chartDomain false false (A h) := by
    change A h (coordinate p:Sphere) ≠ ∞
    rw [coe_coordinate hp0]
    exact hh.1
  have he : inChart false false (A h) (coordinate p)=coordinate (A h p) := by
    change coordinate (A h (coordinate p:Sphere))=coordinate (A h p)
    rw [coe_coordinate hp0]
  have hgd : DifferentiableAt ℝ (inChart false false (A g)) (inChart false false (A h) (coordinate p)) := by
    rw [he]
    exact hg.2.1
  have hc := (hgd.hasFDerivAt.comp (coordinate p) hh.2.1.hasFDerivAt).congr_of_eventuallyEq
    (chart_mul_eventually (A g) (A h) hd)
  have hder := hc.fderiv
  rw [he,← map_mul] at hder
  exact hder

end CannonMobius

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
-- module Solutions.OAIQ046_CN.StdSimplexCompat
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.isProbabilityMeasure_map_fst _root_.OAI.isProbabilityMeasure_map_measurableEquiv _root_.OAI.isProbabilityMeasure_map_snd _root_.OAI.isProbabilityMeasure_map_subtype_val
/-!
# Standard simplex compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. Both have the structure `Convexity.StdSimplex`, but `0df444a`
lacks part of its API (the files `Mathlib.Geometry.Convex.ConvexSpace.{Topology,
CompactSpaceStdSimplex, Barycenter, PathConnectedSpaceStdSimplex}` and some lemmas of `Defs`),
and its `SimplexCategory.toTop` takes the topological simplex to be the subtype
`stdSimplex ℝ (Fin (n+1))`, where `d13f23b` takes the structure.

Part 1 adds the missing `d13f23b` API to `Convexity.StdSimplex` under its `d13f23b` names. It is
copied from Mathlib `d13f23b` (Copyright (c) 2025 Lean FRO, LLC, authors Kim Morrison, Andrew
Yang, Yaël Dillies; Copyright (c) 2026 Joël Riou; released under the Apache 2.0 license), adapted
to `0df444a` (module keywords removed).

Part 2 (`OAI.SStd`) is ours: the subtype `stdSimplex R X` on a finite type with the `d13f23b`
names, for ported code that identifies the simplex with `SimplexCategory.toTop.obj`; there the
port rewrites `Convexity.StdSimplex` to `OAI.SStd`.
-/

noncomputable section StdSimplexCompat

universe u v w

open Topology

/-! ## Part 1: the `d13f23b` API missing from `0df444a`, on `Convexity.StdSimplex` -/

namespace Convexity

namespace StdSimplex

section Semiring

variable {R : Type u} [PartialOrder R] [Semiring R] {X Y Z : Type*}

lemma range_toFun_comp_weights [Fintype X] :
    Set.range (fun t ↦ t.weights : StdSimplex R X → (X → R)) =
    (⋂ (i : X), { s | 0 ≤ s i }) ∩ { s | ∑ i, s i = 1 } := by
  ext s
  simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.weights_nonneg, by simp⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨{
      weights := Finsupp.equivFunOnFinite.symm s
      nonneg m := by simpa using h₁ m
      total := by simpa [Finsupp.sum_fintype] }, by simp⟩

variable [IsStrictOrderedRing R]

lemma map_id' : map (R := R) (id : X → X) = id := by
  funext f
  exact map_id f

end Semiring

end StdSimplex

/-! ### Topology (Mathlib `d13f23b`, `Geometry/Convex/ConvexSpace/Topology.lean`) -/

namespace StdSimplex

variable (R : Type u) [PartialOrder R] [Ring R] [TopologicalSpace R]

namespace topologicalSpaceInduced

attribute [local instance] topologicalSpaceInduced

lemma continuous_iff {T ι : Type*} [TopologicalSpace T] (f : T → StdSimplex R ι) :
    Continuous f ↔ ∀ (i : ι), Continuous (fun t ↦ (f t).weights i) := by
  rw [continuous_induced_rng]
  exact continuous_pi_iff

lemma continuous_map [IsStrictOrderedRing R] [IsTopologicalRing R]
    {ι₁ ι₂ : Type*} [Finite ι₁] (f : ι₁ → ι₂) :
    Continuous (map (R := R) f) := by
  rw [continuous_iff]
  fun_prop

end topologicalSpaceInduced

variable [IsStrictOrderedRing R] [IsTopologicalRing R]

lemma topologicalSpace_eq (M : Type v) [Finite M] :
    topologicalSpace R M = topologicalSpaceInduced _ _ := by
  refine le_antisymm ?_ ?_
  · exact iSup_le (fun ι ↦ iSup_le (fun _ ↦ iSup_le
      (fun f ↦ (topologicalSpaceInduced.continuous_map R f).coinduced_le)))
  · refine le_trans ?_ (le_iSup _ M)
    refine le_trans ?_ (le_iSup _ (by assumption))
    refine le_trans ?_ (le_iSup _ id)
    rw [map_id']
    rfl

lemma isEmbedding_toFun_comp_weights (M : Type*) [Finite M] :
    IsEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  eq_induced := by rw [topologicalSpace_eq]
  injective _ _ h := by ext; apply congr_fun h

lemma isClosedEmbedding_toFun_comp_weights
    [OrderClosedTopology R] (M : Type*) [Finite M] :
    IsClosedEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  toIsEmbedding := isEmbedding_toFun_comp_weights R M
  isClosed_range := by
    have := Fintype.ofFinite M
    rw [range_toFun_comp_weights]
    refine IsClosed.inter (isClosed_iInter (fun _ ↦ isClosed_le ?_ ?_))
      (isClosed_eq ?_ ?_)
    all_goals fun_prop

end StdSimplex

/-! ### Compactness (Mathlib `d13f23b`, `CompactSpaceStdSimplex.lean`) -/

namespace StdSimplex

instance compactSpace (R M : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [PartialOrder R] [IsStrictOrderedRing R] [CompactIccSpace R] [OrderClosedTopology R]
    [Finite M] :
    CompactSpace (StdSimplex R M) where
  isCompact_univ := by
    rw [(isEmbedding_toFun_comp_weights R M).isCompact_iff, Set.image_univ]
    refine IsCompact.of_isClosed_subset (s := Set.Icc 0 1) isCompact_Icc
      (isClosedEmbedding_toFun_comp_weights R M).isClosed_range ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨fun i => x.weights_nonneg i, fun i => x.weights_apply_le_one i⟩

end StdSimplex

/-! ### Barycenters (Mathlib `d13f23b`, `Barycenter.lean`) -/

/-! ### Path-connectedness (Mathlib `d13f23b`, `PathConnectedSpaceStdSimplex.lean`) -/

end Convexity

/-! ## Part 2: `OAI.SStd`, the subtype `stdSimplex R X` with the `d13f23b` names -/

end StdSimplexCompat
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

lemma determinant_continuous : Continuous determinant := by
  unfold determinant
  fun_prop

lemma evaluate_continuous (x y : ℝ) : Continuous (fun q : Form => evaluate q x y) := by
  unfold evaluate
  fun_prop

lemma evaluate_add (p q : Form) (x y : ℝ) :
    evaluate (p+q) x y=evaluate p x y+evaluate q x y := by
  simp only [evaluate,Pi.add_apply]
  ring

lemma evaluate_smul (a : ℝ) (p : Form) (x y : ℝ) :
    evaluate (a • p) x y=a*evaluate p x y := by
  simp only [evaluate,Pi.smul_apply,smul_eq_mul]
  ring

lemma lowerBound_positive {ε : ℝ} (hε : 0 < ε) {q : Form} (hq : LowerBound ε q) :
    Positive q := by
  have ha : ε ≤ q 0 := by simpa [evaluate] using hq 1 0
  have hap : 0 < q 0 := hε.trans_le ha
  refine ⟨hap,?_⟩
  have hp := hq (q 1) (-(q 0))
  have hid : evaluate q (q 1) (-(q 0))=q 0*determinant q := by
    simp only [evaluate,determinant]
    ring
  rw [hid] at hp
  have hsum : 0 < (q 1)^2+(-(q 0))^2 := by nlinarith [sq_nonneg (q 1)]
  have hpos := (mul_pos hε hsum).trans_le hp
  exact (mul_pos_iff_of_pos_left hap).mp hpos

lemma lowerBound_closed (ε : ℝ) : IsClosed {q : Form | LowerBound ε q} := by
  simp only [LowerBound,ofPred_forall]
  exact isClosed_iInter (fun x => isClosed_iInter (fun y =>
    isClosed_le continuous_const (evaluate_continuous x y)))

lemma lowerBound_convex (ε : ℝ) : Convex ℝ {q : Form | LowerBound ε q} := by
  intro p hp q hq a b ha hb hab x y
  rw [evaluate_add,evaluate_smul,evaluate_smul]
  have h₁ := mul_le_mul_of_nonneg_left (hp x y) ha
  have h₂ := mul_le_mul_of_nonneg_left (hq x y) hb
  calc
    ε*(x^2+y^2) = (a+b)*(ε*(x^2+y^2)) := by rw [hab,one_mul]
    _ = a*(ε*(x^2+y^2))+b*(ε*(x^2+y^2)) := by ring
    _ ≤ a*evaluate p x y+b*evaluate q x y := add_le_add h₁ h₂

lemma determinant_midpoint_identity (p q : Form) :
    4*p 0*q 0*determinant ((1/2:ℝ) • p+(1/2:ℝ) • q) =
      (p 0+q 0)*(q 0*determinant p+p 0*determinant q)+
      (p 0*q 1-q 0*p 1)^2 := by
  simp only [determinant,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

lemma determinant_midpoint_strict {p q : Form} (hp : Positive p) (hq : Positive q)
    (heq : determinant p=determinant q) (hne : p ≠ q) :
    determinant p < determinant ((1/2:ℝ) • p+(1/2:ℝ) • q) := by
  by_contra! hle
  have hid := determinant_midpoint_identity p q
  rw [← heq] at hid
  have hprod : 0 < 4*p 0*q 0 := mul_pos (mul_pos (by norm_num) hp.1) hq.1
  have hm := mul_le_mul_of_nonneg_left hle hprod.le
  have hsquare := sq_nonneg (p 0*q 1-q 0*p 1)
  have hid' : 4*p 0*q 0*(determinant ((1/2:ℝ) • p+(1/2:ℝ) • q)-determinant p) =
      (p 0-q 0)^2*determinant p+(p 0*q 1-q 0*p 1)^2 := by nlinarith only [hid]
  have hz : (p 0-q 0)^2*determinant p ≤ 0 := by nlinarith only [hid',hm,hsquare]
  have hs0 : (p 0-q 0)^2=0 := by nlinarith [sq_nonneg (p 0-q 0),hp.2]
  have h0 : p 0=q 0 := by nlinarith only [hs0]
  have hcross : p 0*q 1-q 0*p 1=0 := by
    rw [hs0,zero_mul,zero_add] at hid'
    have hh : (p 0*q 1-q 0*p 1)^2=0 := by nlinarith only [hid',hm,hsquare]
    exact sq_eq_zero_iff.mp hh
  have h1 : p 1=q 1 := by rw [← h0] at hcross; nlinarith [hp.1]
  have h2 : p 2=q 2 := by
    simp only [determinant,← h0,← h1] at heq
    nlinarith [hp.1]
  apply hne
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

lemma determinant_max_unique {K : Set Form} (hconv : Convex ℝ K)
    (hpos : ∀ q ∈ K, Positive q) {p q : Form} (hp : p ∈ K) (hq : q ∈ K)
    (hmaxp : IsMaxOn determinant K p) (hmaxq : IsMaxOn determinant K q) : p=q := by
  by_contra hne
  have heq : determinant p=determinant q := le_antisymm (hmaxq hp) (hmaxp hq)
  have hmid := hconv hp hq (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ)+1/2=1)
  exact not_lt_of_ge (hmaxp hmid) (determinant_midpoint_strict (hpos p hp) (hpos q hq) heq hne)

theorem exists_unique_maxdet {S : Set Form} (hne : S.Nonempty)
    (hbounded : Bornology.IsBounded S) {ε : ℝ} (hε : 0 < ε)
    (hlower : ∀ q ∈ S, LowerBound ε q) :
    ∃! q : Form, q ∈ closedConvexHull ℝ S ∧ IsMaxOn determinant (closedConvexHull ℝ S) q := by
  have hl : closedConvexHull ℝ S ⊆ {q | LowerBound ε q} :=
    closedConvexHull_min hlower (lowerBound_convex ε) (lowerBound_closed ε)
  have hb : Bornology.IsBounded (closedConvexHull ℝ S) := by
    rw [closedConvexHull_eq_closure_convexHull]
    exact (isBounded_convexHull.mpr hbounded).closure
  have hc : IsCompact (closedConvexHull ℝ S) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closedConvexHull,hb⟩
  obtain ⟨q,hq,hm⟩ := hc.exists_isMaxOn (hne.mono subset_closedConvexHull) determinant_continuous.continuousOn
  refine ⟨q,⟨hq,hm⟩,?_⟩
  rintro p ⟨hp,hpm⟩
  exact determinant_max_unique convex_closedConvexHull (fun z hz => lowerBound_positive hε (hl hz)) hp hq hpm hm

lemma center_spec {S : Set Form} (hne : S.Nonempty)
    (hb : Bornology.IsBounded S) {ε : ℝ} (hε : 0 < ε)
    (hl : ∀ q ∈ S, LowerBound ε q) :
    center S ∈ closedConvexHull ℝ S ∧ IsMaxOn determinant (closedConvexHull ℝ S) (center S) :=
  Classical.epsilon_spec (exists_unique_maxdet hne hb hε hl).exists

lemma center_eq {S : Set Form} (hne : S.Nonempty)
    (hb : Bornology.IsBounded S) {ε : ℝ} (hε : 0 < ε)
    (hl : ∀ q ∈ S, LowerBound ε q) {p : Form}
    (hp : p ∈ closedConvexHull ℝ S) (hmax : IsMaxOn determinant (closedConvexHull ℝ S) p) :
    center S = p := by
  have hc := center_spec hne hb hε hl
  exact (exists_unique_maxdet hne hb hε hl).unique hc ⟨hp,hmax⟩

lemma image_closedConvexHull (L : Form ≃L[ℝ] Form) (S : Set Form) :
    L '' closedConvexHull ℝ S = closedConvexHull ℝ (L '' S) := by
  rw [closedConvexHull_eq_closure_convexHull,closedConvexHull_eq_closure_convexHull]
  change L.toHomeomorph '' closure (convexHull ℝ S) = _
  rw [L.toHomeomorph.image_closure]
  congr 1
  exact L.toLinearMap.image_convexHull S

theorem center_equivariant (L : Form ≃L[ℝ] Form)
    (hdet : ∀ q, determinant (L q)=determinant q)
    {S T : Set Form} (hST : L '' S = T)
    (hS : S.Nonempty) (hbS : Bornology.IsBounded S)
    (hT : T.Nonempty) (hbT : Bornology.IsBounded T)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hlS : ∀ q ∈ S, LowerBound ε q) (hlT : ∀ q ∈ T, LowerBound δ q) :
    L (center S)=center T := by
  have hmap : L '' closedConvexHull ℝ S=closedConvexHull ℝ T := by
    rw [image_closedConvexHull,hST]
  have hc := center_spec hS hbS hε hlS
  symm
  apply center_eq hT hbT hδ hlT
  · rw [← hmap]
    exact mem_image_of_mem L hc.1
  · intro p hp
    rw [← hmap] at hp
    obtain ⟨q,hq,rfl⟩ := hp
    dsimp
    rw [hdet,hdet]
    exact hc.2 hq

lemma determinant_pullForm (A : PlaneLinear) (q : Form) :
    determinant (pullForm A q)=(planeDet A)^2*determinant q := by
  simp [determinant,pullForm,planeDet]
  ring

lemma determinant_smul (r : ℝ) (q : Form) :
    determinant (r • q)=r^2*determinant q := by
  simp [determinant]
  ring

lemma evaluate_pullForm (A : PlaneLinear) (q : Form) (x y : ℝ) :
    evaluate (pullForm A q) x y=evaluate q (A 0*x+A 1*y) (A 2*x+A 3*y) := by
  simp [evaluate,pullForm]
  ring

lemma normalizedPull_det (A : PlaneLinear) (hA : planeDet A ≠ 0) (q : Form) :
    determinant (normalizedPull A q)=determinant q := by
  rw [normalizedPull_apply,determinant_smul,determinant_pullForm]
  have ha : |planeDet A| ≠ 0 := abs_ne_zero.mpr hA
  have he : (|planeDet A|⁻¹)^2*(planeDet A)^2=1 := by
    rw [← sq_abs (planeDet A)]
    field_simp
  rw [← mul_assoc,he,one_mul]

lemma pullbackEquiv_det (A : PlaneLinear) (hA : planeDet A ≠ 0) (q : Form) :
    determinant (pullbackEquiv A hA q)=determinant q := normalizedPull_det A hA q

lemma planeDet_mul (A B : PlaneLinear) : planeDet (planeMul A B)=planeDet A*planeDet B := by
  simp [planeDet,planeMul]
  ring

lemma pullForm_mul (A B : PlaneLinear) (q : Form) :
    pullForm (planeMul A B) q=pullForm B (pullForm A q) := by
  ext i
  fin_cases i <;> simp [pullForm,planeMul] <;> ring

lemma normalizedPull_mul (A B : PlaneLinear) (q : Form) :
    normalizedPull (planeMul A B) q=normalizedPull B (normalizedPull A q) := by
  simp only [normalizedPull_apply,planeDet_mul,abs_mul,mul_inv_rev,pullForm_mul,map_smul,smul_smul]
  rw [mul_comm]

end CannonConformal

end
end
noncomputable section
namespace CannonConformal
open CannonMetricQC

lemma derivativeMatrix_comp (A B : ℂ →L[ℝ] ℂ) :
    derivativeMatrix (A.comp B)=planeMul (derivativeMatrix A) (derivativeMatrix B) := by
  have h1 := derivative_apply A (B 1)
  have hI := derivative_apply A (B Complex.I)
  ext i
  fin_cases i <;> simp [derivativeMatrix,planeMul,ContinuousLinearMap.comp_apply,
    h1,hI,Complex.add_re,Complex.add_im] <;> ring

lemma derivativeDet_comp (A B : ℂ →L[ℝ] ℂ) :
    derivativeDet (A.comp B)=derivativeDet A*derivativeDet B := by
  change planeDet (derivativeMatrix (A.comp B))=
    planeDet (derivativeMatrix A)*planeDet (derivativeMatrix B)
  rw [derivativeMatrix_comp,planeDet_mul]

lemma pull_round_derivative (A : ℂ →L[ℝ] ℂ) :
    pullForm (derivativeMatrix A) roundForm=derivativeForm A := by
  ext i
  fin_cases i <;> simp [pullForm,derivativeMatrix,roundForm,derivativeForm,
    Complex.sq_norm,Complex.normSq_apply] <;> ring

lemma evaluate_normalized_round (A : ℂ →L[ℝ] ℂ) (x y : ℝ) :
    evaluate (normalizedPull (derivativeMatrix A) roundForm) x y=
      |derivativeDet A|⁻¹*‖A (⟨x,y⟩ : ℂ)‖^2 := by
  rw [normalizedPull_apply,evaluate_smul,pull_round_derivative,derivativeForm_evaluate]
  rfl

theorem normalized_derivative_bounds (A B : ℂ →L[ℝ] ℂ) {H : ℝ}
    (hH : 0 < H) (hA : Function.Bijective A) (hBA : B.comp A=ContinuousLinearMap.id ℝ ℂ)
    (hu : ∀ v : ℂ, ‖A v‖^2 ≤ H^2*|derivativeDet A| * ‖v‖^2)
    (hi : ∀ v : ℂ, ‖B v‖^2 ≤ H^2*|derivativeDet B| * ‖v‖^2) :
    LowerBound ((H^2)⁻¹) (normalizedPull (derivativeMatrix A) roundForm) ∧
      UpperBound (H^2) (normalizedPull (derivativeMatrix A) roundForm) := by
  have ha : 0 < |derivativeDet A| := abs_pos.mpr (derivativeDet_ne_zero hA)
  have hH2 : 0 < H^2 := sq_pos_of_pos hH
  have hprod : |derivativeDet A| * |derivativeDet B|=1 := by
    have hh := congrArg derivativeDet hBA
    rw [derivativeDet_comp] at hh
    have hid : derivativeDet (ContinuousLinearMap.id ℝ ℂ)=1 := by norm_num [derivativeDet]
    rw [hid] at hh
    have haa := congrArg abs hh
    simpa only [abs_mul,abs_one,mul_comm] using haa
  have hleft (v : ℂ) : B (A v)=v := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hBA
  constructor
  · intro x y
    rw [evaluate_normalized_round]
    let v : ℂ := ⟨x,y⟩
    have hv : ‖v‖^2=x^2+y^2 := by
      rw [Complex.sq_norm]
      simp [v,Complex.normSq_apply,pow_two]
    have hh := hi (A v)
    rw [hleft] at hh
    have hmul := mul_le_mul_of_nonneg_right hh ha.le
    have hr : (H^2*|derivativeDet B| * ‖A v‖^2)*|derivativeDet A|=H^2*‖A v‖^2 := by
      calc
        _ = (|derivativeDet A| * |derivativeDet B|)*(H^2*‖A v‖^2) := by ring
        _ = _ := by rw [hprod,one_mul]
    rw [hr,hv] at hmul
    rw [← div_eq_inv_mul,← div_eq_inv_mul]
    exact (div_le_div_iff₀ hH2 ha).mpr (by simpa only [mul_comm] using hmul)
  · intro x y
    rw [evaluate_normalized_round,← div_eq_inv_mul]
    have hh := hu (⟨x,y⟩ : ℂ)
    have hv : ‖(⟨x,y⟩ : ℂ)‖^2=x^2+y^2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply,pow_two]
    rw [hv] at hh
    apply (div_le_iff₀ ha).mpr
    nlinarith only [hh]

end CannonConformal

end
end
section
noncomputable section
namespace CannonConformal
open Set Topology Metric

theorem continuous_unique_max_image {X C Y : Type*}
    [TopologicalSpace X] [TopologicalSpace C] [CompactSpace C]
    [TopologicalSpace Y] (F : X × C → Y) (hF : Continuous F)
    (V : Y → ℝ) (hV : Continuous V) (s : X → Y)
    (hs : ∀ x, ∃ c, F (x,c)=s x ∧ ∀ d, V (F (x,d)) ≤ V (s x))
    (hunique : ∀ x c, (∀ d, V (F (x,d)) ≤ V (F (x,c))) → F (x,c)=s x) :
    Continuous s := by
  rw [continuous_iff_isClosed]
  intro T hT
  let K : Set (X × C) := {p | F p ∈ T ∧ ∀ d : C, V (F (p.1,d)) ≤ V (F p)}
  have hK : IsClosed K := by
    change IsClosed ({p | F p ∈ T} ∩ {p | ∀ d : C, V (F (p.1,d)) ≤ V (F p)})
    refine (hT.preimage hF).inter ?_
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro d
    exact isClosed_le (hV.comp (hF.comp (continuous_fst.prodMk continuous_const))) (hV.comp hF)
  have heq : s ⁻¹' T=Prod.fst '' K := by
    ext x
    constructor
    · intro hx
      obtain ⟨c,hc,hmax⟩ := hs x
      exact ⟨(x,c),⟨hc ▸ hx,by simpa only [hc] using hmax⟩,rfl⟩
    · rintro ⟨⟨y,c⟩,⟨hy,hmax⟩,rfl⟩
      change s y ∈ T
      rw [← hunique y c hmax]
      exact hy
  rw [heq]
  exact isClosedMap_fst_of_compactSpace K hK

section Finite
variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma combination_apply (q : ι → Form) (w : ι → ℝ) :
    combination q w=∑ i, w i • q i := by simp [combination]

omit [Nonempty ι] in
lemma combination_image (q : ι → Form) :
    combination q '' {weights : ι → ℝ | (∀ index, 0 ≤ weights index) ∧
      ∑ index, weights index = 1}=convexHull ℝ (range q) := by
  classical
  have hconvex : Convex ℝ {weights : ι → ℝ | (∀ index, 0 ≤ weights index) ∧
      ∑ index, weights index = 1} := by
    intro weights hweights other hother left right hleft hright htotal
    constructor
    · intro index
      exact add_nonneg (mul_nonneg hleft (hweights.1 index))
        (mul_nonneg hright (hother.1 index))
    · simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
        ← Finset.mul_sum,hweights.2,hother.2,mul_one,htotal]
  apply subset_antisymm
  · rintro _ ⟨weights,hweights,rfl⟩
    rw [combination_apply]
    exact (convex_convexHull ℝ (range q)).sum_mem
      (fun index _ => hweights.1 index) hweights.2
      (fun index _ => subset_convexHull ℝ (range q) (mem_range_self index))
  · apply convexHull_min _ (hconvex.linear_image (combination q))
    rintro _ ⟨index,rfl⟩
    refine ⟨Pi.single index 1,?_,?_⟩
    · simp [Pi.single_apply]
      intro coordinate
      split_ifs <;> norm_num
    · simp [combination_apply,Pi.single_apply]

omit [Nonempty ι] in
lemma closedConvexHull_finite_range (q : ι → Form) :
    closedConvexHull ℝ (range q)=convexHull ℝ (range q) := by
  rw [closedConvexHull_eq_closure_convexHull]
  exact (finite_range q).isClosed_convexHull ℝ |>.closure_eq

lemma continuous_finite_center {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun q : FiniteForms ε ι => center (range q.val)) := by
  let weightsSet : Set (ι → ℝ) :=
    {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}
  have hcompact : IsCompact weightsSet := by
    have hcompact := isCompact_range
      (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous
    simpa only [Convexity.StdSimplex.range_toFun_comp_weights,weightsSet,
      ofPred_forall,ofPred_and] using hcompact
  let : CompactSpace weightsSet := isCompact_iff_compactSpace.mp hcompact
  let F : FiniteForms ε ι × weightsSet → Form :=
    fun p => combination p.1.val p.2.val
  have hF : Continuous F := by
    dsimp only [F]
    simp_rw [combination_apply]
    apply continuous_finsetSum
    intro i _hi
    exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).smul
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst))
  apply continuous_unique_max_image F hF determinant determinant_continuous
  · intro q
    have hc := center_spec (range_nonempty q.val) (finite_range q.val).isBounded hε
      (by rintro _ ⟨i,rfl⟩; exact q.property i)
    rw [closedConvexHull_finite_range,← combination_image] at hc
    obtain ⟨w,hw,hweq⟩ := hc.1
    refine ⟨⟨w,hw⟩,hweq,?_⟩
    intro w
    exact hc.2 (mem_image_of_mem _ w.property)
  · intro q w hmax
    symm
    apply center_eq (range_nonempty q.val) (finite_range q.val).isBounded hε
      (by rintro _ ⟨i,rfl⟩; exact q.property i)
    · rw [closedConvexHull_finite_range,← combination_image]
      exact mem_image_of_mem _ w.property
    · intro p hp
      rw [closedConvexHull_finite_range,← combination_image] at hp
      obtain ⟨v,hv,rfl⟩ := hp
      exact hmax ⟨v,hv⟩

end Finite

open Filter

lemma prefix_nonempty (q : ℕ → Form) (n : ℕ) : (orbitPrefix q n).Nonempty :=
  ⟨q 0,⟨⟨0,Nat.zero_lt_succ _⟩,rfl⟩⟩

lemma prefix_subset_range (q : ℕ → Form) (n : ℕ) : orbitPrefix q n ⊆ range q := by
  rintro p ⟨i,rfl⟩
  exact mem_range_self i.val

lemma prefix_monotone (q : ℕ → Form) : Monotone (orbitPrefix q) := by
  intro n m hnm p hp
  obtain ⟨i,rfl⟩ := hp
  exact ⟨⟨i.val,lt_of_lt_of_le i.isLt (Nat.add_le_add_right hnm 1)⟩,rfl⟩

lemma prefix_closure_union (q : ℕ → Form) :
    closure (⋃ n, closedConvexHull ℝ (orbitPrefix q n))=closedConvexHull ℝ (range q) := by
  let K := fun n => closedConvexHull ℝ (orbitPrefix q n)
  have hmono : Monotone K := (closedConvexHull ℝ).monotone.comp (prefix_monotone q)
  apply le_antisymm
  · apply closure_minimal _ isClosed_closedConvexHull
    exact iUnion_subset (fun n => (closedConvexHull ℝ).monotone (prefix_subset_range q n))
  · apply closedConvexHull_min _ (hmono.directed_le.convex_iUnion (fun n => convex_closedConvexHull)).closure isClosed_closure
    rintro p ⟨n,rfl⟩
    apply subset_closure
    apply mem_iUnion_of_mem n
    exact subset_closedConvexHull ⟨⟨n,Nat.lt_succ_self n⟩,rfl⟩

theorem prefix_center_tendsto (q : ℕ → Form)
    (hb : Bornology.IsBounded (range q)) {ε : ℝ} (hε : 0 < ε)
    (hl : ∀ n, LowerBound ε (q n)) :
    Tendsto (fun n => center (orbitPrefix q n)) atTop (𝓝 (center (range q))) := by
  let K := closedConvexHull ℝ (range q)
  have hbd : Bornology.IsBounded K := by
    dsimp [K]
    rw [closedConvexHull_eq_closure_convexHull]
    exact (isBounded_convexHull.mpr hb).closure
  have hK : IsCompact K := isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closedConvexHull,hbd⟩
  have hspec (n : ℕ) := center_spec (prefix_nonempty q n)
    (hb.subset (prefix_subset_range q n)) hε
    (fun p hp => by obtain ⟨i,rfl⟩ := hp; exact hl i.val)
  have hsub (n : ℕ) : closedConvexHull ℝ (orbitPrefix q n) ⊆ K :=
    (closedConvexHull ℝ).monotone (prefix_subset_range q n)
  apply hK.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall (fun n => hsub n (hspec n).1))
  intro p hp hcl
  symm
  apply center_eq (range_nonempty q) hb hε (by rintro _ ⟨n,rfl⟩; exact hl n) hp
  intro z hz
  have hD : IsClosed {z : Form | determinant z ≤ determinant p} :=
    isClosed_le determinant_continuous continuous_const
  have hall : closure (⋃ n, closedConvexHull ℝ (orbitPrefix q n)) ⊆
      {z : Form | determinant z ≤ determinant p} := by
    apply closure_minimal _ hD
    intro y hy
    obtain ⟨m,hm⟩ := mem_iUnion.mp hy
    have hclosed : IsClosed {r : Form | determinant y ≤ determinant r} :=
      isClosed_le continuous_const determinant_continuous
    apply hclosed.mem_of_mapClusterPt hcl
    filter_upwards [eventually_ge_atTop m] with n hmn
    exact (hspec n).2 ((closedConvexHull ℝ).monotone (prefix_monotone q hmn) hm)
  rw [prefix_closure_union] at hall
  exact hall hz

open MeasureTheory

lemma measurable_finite_center {X ι : Type*} [MeasurableSpace X]
    [Fintype ι] [Nonempty ι] {ε : ℝ} (hε : 0 < ε)
    (q : ι → X → Form) (hq : ∀ i, Measurable (q i))
    (hl : ∀ i x, LowerBound ε (q i x)) :
    Measurable (fun x => center (range (fun i => q i x))) := by
  let f : X → FiniteForms ε ι := fun x => ⟨fun i => q i x,fun i => hl i x⟩
  have hf : Measurable f := (Measurable.of_eval hq).subtype_mk
  have H : Measurable (fun q : FiniteForms ε ι => center (range q.val)) :=
    (continuous_finite_center (ι:=ι) hε).measurable
  change Measurable ((fun q : FiniteForms ε ι => center (range q.val)) ∘ f)
  exact H.comp hf

theorem measurable_countable_center {X : Type*} [MeasurableSpace X]
    (q : ℕ → X → Form) (hq : ∀ n, Measurable (q n))
    {ε : ℝ} (hε : 0 < ε) (hl : ∀ n x, LowerBound ε (q n x))
    (hb : ∀ x, Bornology.IsBounded (range (fun n => q n x))) :
    Measurable (fun x => center (range (fun n => q n x))) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n x => center (orbitPrefix (fun k => q k x) n))
  · intro n
    exact measurable_finite_center hε (fun i : Fin (n+1) => q i.val)
      (fun i => hq i.val) (fun i x => hl i.val x)
  · apply tendsto_pi_nhds.mpr
    intro x
    exact prefix_center_tendsto (fun n => q n x) (hb x) hε (fun n => hl n x)

lemma upperBound_closed (K : ℝ) : IsClosed {q : Form | UpperBound K q} := by
  simp only [UpperBound,ofPred_forall]
  exact isClosed_iInter (fun x => isClosed_iInter (fun y =>
    isClosed_le (evaluate_continuous x y) continuous_const))

lemma upperBound_convex (K : ℝ) : Convex ℝ {q : Form | UpperBound K q} := by
  intro p hp q hq a b ha hb hab x y
  rw [evaluate_add,evaluate_smul,evaluate_smul]
  calc
    a*evaluate p x y+b*evaluate q x y ≤ a*(K*(x^2+y^2))+b*(K*(x^2+y^2)) :=
      add_le_add (mul_le_mul_of_nonneg_left (hp x y) ha)
        (mul_le_mul_of_nonneg_left (hq x y) hb)
    _ = (a+b)*(K*(x^2+y^2)) := by ring
    _ = K*(x^2+y^2) := by rw [hab,one_mul]

lemma norm_le_of_bounds {ε K : ℝ} (hε : 0 ≤ ε) (hK : 0 ≤ K) {q : Form}
    (hl : LowerBound ε q) (hu : UpperBound K q) : ‖q‖ ≤ K := by
  have h0l : ε ≤ q 0 := by simpa [evaluate] using hl 1 0
  have h2l : ε ≤ q 2 := by simpa [evaluate] using hl 0 1
  have h0u : q 0 ≤ K := by simpa [evaluate] using hu 1 0
  have h2u : q 2 ≤ K := by simpa [evaluate] using hu 0 1
  have hp : q 0+2*q 1+q 2 ≤ 2*K := by
    have h := hu 1 1
    norm_num [evaluate] at h
    nlinarith
  have hn : q 0-2*q 1+q 2 ≤ 2*K := by
    have h := hu 1 (-1)
    norm_num [evaluate] at h
    nlinarith
  apply (pi_norm_le_iff_of_nonneg hK).mpr
  intro i
  rw [Real.norm_eq_abs,abs_le]
  fin_cases i
  · change -K ≤ q 0 ∧ q 0 ≤ K
    constructor <;> linarith
  · change -K ≤ q 1 ∧ q 1 ≤ K
    constructor <;> linarith
  · change -K ≤ q 2 ∧ q 2 ≤ K
    constructor <;> linarith

lemma bounded_of_bounds {S : Set Form} {ε K : ℝ} (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hl : ∀ q ∈ S, LowerBound ε q) (hu : ∀ q ∈ S, UpperBound K q) :
    Bornology.IsBounded S := by
  apply (Metric.isBounded_iff_subset_closedBall (0 : Form)).mpr
  refine ⟨K,?_⟩
  intro q hq
  simpa only [mem_closedBall,dist_zero_right] using norm_le_of_bounds hε hK (hl q hq) (hu q hq)

lemma center_bounds {S : Set Form} (hne : S.Nonempty)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hl : ∀ q ∈ S, LowerBound ε q) (hu : ∀ q ∈ S, UpperBound K q) :
    LowerBound ε (center S) ∧ UpperBound K (center S) := by
  have hc := center_spec hne (bounded_of_bounds hε.le hK hl hu) hε hl
  exact ⟨closedConvexHull_min hl (lowerBound_convex ε) (lowerBound_closed ε) hc.1,
    closedConvexHull_min hu (upperBound_convex K) (upperBound_closed K) hc.1⟩

lemma measurable_indexed_center {X ι : Type*} [MeasurableSpace X] [Countable ι] [Nonempty ι]
    (q : ι → X → Form) (hq : ∀ i, Measurable (q i))
    {ε : ℝ} (hε : 0 < ε) (hl : ∀ i x, LowerBound ε (q i x))
    (hb : ∀ x, Bornology.IsBounded (range (fun i => q i x))) :
    Measurable (fun x => center (range (fun i => q i x))) := by
  obtain ⟨e,he⟩ := exists_surjective_nat ι
  have hr (x : X) : range (fun n => q (e n) x)=range (fun i => q i x) :=
    he.range_comp (fun i => q i x)
  have hm := measurable_countable_center (fun n => q (e n)) (fun n => hq (e n)) hε
    (fun n => hl (e n)) (fun x => by rw [hr]; exact hb x)
  simpa only [hr] using hm

theorem invariant_measurable_form {Γ X : Type*} [Group Γ] [Countable Γ]
    [MeasurableSpace X] (A : Γ →* Equiv.Perm X)
    (L : Γ → X → Form ≃L[ℝ] Form) (round : X → Form)
    (hdet : ∀ g x q, determinant (L g x q)=determinant q)
    (hcocycle : ∀ g h x q, L (g*h) x q=L h x (L g (A h x) q))
    (hq : ∀ g, Measurable (fun x => L g x (round (A g x))))
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hl : ∀ g x, LowerBound ε (L g x (round (A g x))))
    (hu : ∀ g x, UpperBound K (L g x (round (A g x)))) :
    ∃ q : X → Form, Measurable q ∧ (∀ x, LowerBound ε (q x) ∧ UpperBound K (q x)) ∧
      ∀ g x, L g x (q (A g x))=q x := by
  let Q : Γ → X → Form := fun g x => L g x (round (A g x))
  let S : X → Set Form := fun x => range (fun g => Q g x)
  have hlow (x : X) : ∀ p ∈ S x, LowerBound ε p := by
    rintro p ⟨g,rfl⟩
    exact hl g x
  have hupp (x : X) : ∀ p ∈ S x, UpperBound K p := by
    rintro p ⟨g,rfl⟩
    exact hu g x
  have hb (x : X) := bounded_of_bounds hε.le hK (hlow x) (hupp x)
  refine ⟨fun x => center (S x),measurable_indexed_center Q hq hε hl hb,
    fun x => center_bounds (range_nonempty _) hε hK (hlow x) (hupp x),?_⟩
  intro h x
  apply center_equivariant (L h x) (hdet h x) _ (range_nonempty _) (hb _) (range_nonempty _) (hb _)
    hε hε (hlow _) (hlow _)
  ext p
  constructor
  · rintro ⟨q,⟨g,rfl⟩,rfl⟩
    refine ⟨g*h,?_⟩
    dsimp [Q]
    rw [hcocycle]
    simp only [map_mul,Equiv.Perm.mul_apply]
  · rintro ⟨g,rfl⟩
    refine ⟨Q (g*h⁻¹) (A h x),mem_range_self _,?_⟩
    dsimp only [Q]
    rw [← hcocycle]
    simp only [inv_mul_cancel_right,map_mul,Equiv.Perm.mul_apply,map_inv,Equiv.Perm.inv_def,
      Equiv.symm_apply_apply]

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
-- module Solutions.OAIQ046_CN.Cannon_Conformal_RestrictedSphereAction
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
noncomputable section
namespace CannonMobius
open Set Filter Topology MeasureTheory CannonMetricQC CannonConformal
open scoped OnePoint

variable {Γ : Type*} [Group Γ]

lemma sphereDerivative_one {p : Sphere} (hp : p ≠ ∞) :
    sphereDerivative (Homeomorph.refl Sphere) p=ContinuousLinearMap.id ℝ ℂ := by
  obtain ⟨point,rfl⟩ := OnePoint.ne_infty_iff_exists.mp hp
  have he : inChart false false (Homeomorph.refl Sphere)=id := by
    funext z
    simp [inChart,chart,coordinate_coe]
  rw [sphereDerivative,he]
  exact (hasFDerivAt_id (coordinate (point : Sphere))).fderiv

lemma continuous_derivativeMatrix : Continuous derivativeMatrix := by
  unfold derivativeMatrix
  fun_prop

lemma measurable_sphereDerivative_on (f : Sphere ≃ₜ Sphere) {K : Set Sphere}
    (hK : ∀ p ∈ K, p ≠ ∞) :
    Measurable (fun p : K => sphereDerivative f p) := by
  have hc : Continuous (fun p : K => coordinate p) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (continuousAt_coordinate (hK p p.property)).comp continuous_subtype_val.continuousAt
  exact (measurable_fderiv ℝ (inChart false false f)).comp hc.measurable

lemma measurable_normalized_round :
    Measurable (fun B : PlaneLinear => normalizedPull B roundForm) := by
  have hd : Continuous planeDet := by unfold planeDet; fun_prop
  have hp : Continuous (fun B : PlaneLinear => pullForm B roundForm) := by
    change Continuous (fun B : PlaneLinear =>
      ![roundForm 0*B 0^2+2*roundForm 1*B 0*B 2+roundForm 2*B 2^2,
        roundForm 0*B 0*B 1+roundForm 1*(B 0*B 3+B 1*B 2)+roundForm 2*B 2*B 3,
        roundForm 0*B 1^2+2*roundForm 1*B 1*B 3+roundForm 2*B 3^2])
    fun_prop
  exact (hd.measurable.abs.inv).smul hp.measurable

lemma measurable_normalized_round_on (f : Sphere ≃ₜ Sphere) {K : Set Sphere}
    (hK : ∀ p ∈ K, p ≠ ∞) :
    Measurable (fun p : K => normalizedPull (derivativeMatrix (sphereDerivative f p)) roundForm) :=
  measurable_normalized_round.comp (continuous_derivativeMatrix.measurable.comp
    (measurable_sphereDerivative_on f hK))

theorem controlled_action_invariant_structure [Countable Γ]
    (A : Γ →* (Sphere ≃ₜ Sphere)) {η : CannonQM.Distortion}
    (hA : ∀ g, CannonQM.Controlled (A g) η) :
    ∃ K : Set Sphere, MeasurableSet K ∧ (∀ᵐ p ∂sphereMeasure, p ∈ K) ∧
      (∀ g p, A g p ∈ K ↔ p ∈ K) ∧
      (∀ p ∈ K, GoodDifferentials A (1+2*(η 2:ℝ)) p) ∧
      ∃ q : K → Form, Measurable q ∧
        (∀ p, LowerBound (((1+2*(η 2:ℝ))^2)⁻¹) (q p) ∧
          UpperBound ((1+2*(η 2:ℝ))^2) (q p)) ∧
        ∀ g (p : K) (hg : A g (p:Sphere) ∈ K),
          normalizedPull (derivativeMatrix (sphereDerivative (A g) p)) (q ⟨A g p,hg⟩)=q p := by
  obtain ⟨K,hKm,hKae,hK,hgood⟩ := controlled_action_derivative_core A hA
  let H : ℝ := 1+2*(η 2:ℝ)
  have hH : 0 < H := by dsimp [H]; positivity
  have hd (g : Γ) (p : K) : planeDet (derivativeMatrix (sphereDerivative (A g) p)) ≠ 0 :=
    derivativeDet_ne_zero ((hgood p p.property).2 g).2.2.1
  let B := restrictedSphereAction A K hK
  let L (g : Γ) (p : K) : Form ≃L[ℝ] Form :=
    pullbackEquiv (derivativeMatrix (sphereDerivative (A g) p)) (hd g p)
  have hcocycle (g h : Γ) (p : K) (q : Form) : L (g*h) p q=L h p (L g (B h p) q) := by
    change normalizedPull (derivativeMatrix (sphereDerivative (A (g*h)) p)) q=
      normalizedPull (derivativeMatrix (sphereDerivative (A h) p))
        (normalizedPull (derivativeMatrix (sphereDerivative (A g) (A h p))) q)
    rw [sphereDerivative_mul_on_core A hK hgood p.property,derivativeMatrix_comp,normalizedPull_mul]
  have hbound (g : Γ) (p : K) :
      LowerBound ((H^2)⁻¹) (L g p roundForm) ∧ UpperBound (H^2) (L g p roundForm) := by
    have hg := (hgood p p.property).2 g
    have hg' := (hgood (A g p) ((hK g p).mpr p.property)).2 g⁻¹
    have hcomp : (sphereDerivative (A g⁻¹) (A g p)).comp (sphereDerivative (A g) p)=
        ContinuousLinearMap.id ℝ ℂ := by
      rw [← sphereDerivative_mul_on_core A hK hgood p.property,inv_mul_cancel,map_one]
      exact sphereDerivative_one (hgood p p.property).1
    exact normalized_derivative_bounds _ _ hH hg.2.2.1 hcomp hg.2.2.2 hg'.2.2.2
  have hmeas (g : Γ) : Measurable (fun p : K => L g p roundForm) :=
    measurable_normalized_round_on (A g) (fun p hp => (hgood p hp).1)
  obtain ⟨q,hqm,hqb,hqi⟩ := invariant_measurable_form B L (fun _ => roundForm)
    (fun g p => pullbackEquiv_det _ (hd g p)) hcocycle hmeas
    (inv_pos.mpr (sq_pos_of_pos hH)) (sq_nonneg H)
    (fun g p => (hbound g p).1) (fun g p => (hbound g p).2)
  refine ⟨K,hKm,hKae,hK,hgood,q,hqm,hqb,?_⟩
  intro g p hg
  exact hqi g p

end CannonMobius

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
noncomputable section
namespace CannonMobius
open Set Filter Topology MeasureTheory CannonMetricQC CannonConformal
open scoped OnePoint

variable {Γ : Type*} [Group Γ]

open Classical

lemma measurable_extend_form {K : Set Sphere} (hK : MeasurableSet K)
    (q : K → Form) (hq : Measurable q) :
    Measurable (fun z : ℂ => if hz : (z:Sphere) ∈ K then q ⟨z,hz⟩ else roundForm) := by
  have hm : Measurable (fun z : ℂ => (z:Sphere)) := OnePoint.continuous_coe.measurable
  have hs : MeasurableSet {z : ℂ | (z:Sphere) ∈ K} := hK.preimage hm
  have h1 : Measurable (fun z : {z : ℂ | (z:Sphere) ∈ K} => q ⟨z.val,z.property⟩) :=
    hq.comp ((hm.comp measurable_subtype_coe).subtype_mk)
  exact h1.dite measurable_const hs

lemma roundForm_bounds {ε K : ℝ} (hε : ε ≤ 1) (hK : 1 ≤ K) :
    LowerBound ε roundForm ∧ UpperBound K roundForm := by
  constructor
  · intro x y
    have hh := mul_le_mul_of_nonneg_right hε (show 0 ≤ x^2+y^2 by positivity)
    simpa [evaluate,roundForm] using hh
  · intro x y
    have hh := mul_le_mul_of_nonneg_right hK (show 0 ≤ x^2+y^2 by positivity)
    simpa [evaluate,roundForm] using hh

theorem controlled_action_structure_integration [Countable Γ]
    (A : Γ →* (Sphere ≃ₜ Sphere)) {η : CannonQM.Distortion}
    (hA : ∀ g, CannonQM.Controlled (A g) η) :
    ∃ q : ℂ → Form, Measurable q ∧
      (∀ z, LowerBound (((1+2*(η 2:ℝ))^2)⁻¹) (q z) ∧ UpperBound ((1+2*(η 2:ℝ))^2) (q z)) ∧
      (∀ g, ∀ᵐ z : ℂ, A g (z:Sphere) ≠ ∞ ∧
        normalizedPull (derivativeMatrix (fderiv ℝ (inChart false false (A g)) z))
          (q (inChart false false (A g) z))=q z) ∧
      ∃ C : ℝ, 0 < C ∧ ∃ F : ℂ ≃ₜ ℂ, F 0=0 ∧ F 1=1 ∧
        WeakQS F C ∧ WeakQS F.symm C ∧
        (∀ᵐ z : ℂ, DifferentiableAt ℝ (F : ℂ → ℂ) z ∧
          Function.Bijective (fderiv ℝ (F : ℂ → ℂ) z) ∧
          ∃ c : ℝ, 0 < c ∧ ∀ v : ℂ,
            Complex.normSq (fderiv ℝ (F : ℂ → ℂ) z v)=c*evaluate (q z) v.re v.im) := by
  classical
  obtain ⟨K,hKm,hKae,hKi,hgood,q,hqm,hqb,hqi⟩ := controlled_action_invariant_structure A hA
  let H : ℝ := 1+2*(η 2:ℝ)
  have hH : 1 ≤ H := by
    dsimp [H]
    have := (η 2).coe_nonneg
    linarith
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hH2 : 1 ≤ H^2 := one_le_pow₀ hH
  have hi : (H^2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hH2
  let Q : ℂ → Form := fun z => if hz : (z:Sphere) ∈ K then q ⟨z,hz⟩ else roundForm
  have hQm : Measurable Q := measurable_extend_form hKm q hqm
  have hQb (z : ℂ) : LowerBound ((H^2)⁻¹) (Q z) ∧ UpperBound (H^2) (Q z) := by
    dsimp [Q]
    split_ifs with hz
    · exact hqb ⟨z,hz⟩
    · exact roundForm_bounds hi hH2
  have hQeq (z : ℂ) (hz : (z:Sphere) ∈ K) : Q z=q ⟨z,hz⟩ := dite_eq_left hz
  have hQi (g : Γ) : ∀ᵐ z : ℂ, A g (z:Sphere) ≠ ∞ ∧
      normalizedPull (derivativeMatrix (fderiv ℝ (inChart false false (A g)) z))
        (Q (inChart false false (A g) z))=Q z := by
    filter_upwards [ae_sphere_iff.mp hKae] with z hz
    have hg := (hgood (z:Sphere) hz).2 g
    have hgK := (hKi g (z:Sphere)).mpr hz
    have hcoe : (inChart false false (A g) z : Sphere)=A g (z:Sphere) :=
      coe_coordinate hg.1
    refine ⟨hg.1,?_⟩
    rw [hQeq z hz,hQeq _ (hcoe.symm ▸ hgK)]
    have hh := hqi g ⟨z,hz⟩ hgK
    have he : (⟨(inChart false false (A g) z : Sphere), hcoe.symm ▸ hgK⟩ : K) = ⟨A g (z:Sphere),hgK⟩ := Subtype.ext hcoe
    rw [he]
    simpa only [sphereDerivative,coordinate_coe] using hh
  refine ⟨Q,hQm,hQb,hQi,?_⟩
  exact measurable_structure_integration Q hQm (inv_pos.mpr (sq_pos_of_pos hHp))
    (sq_pos_of_pos hHp) (fun z => (hQb z).1) (fun z => (hQb z).2)

end CannonMobius

end
end
section
noncomputable section

noncomputable section
namespace CannonConformal
open scoped RealInnerProductSpace
open CannonMetricQC

lemma isConformalMap_of_normSq (L : ℂ →L[ℝ] ℂ) {c : ℝ} (hc : 0 < c)
    (h : ∀ v : ℂ, Complex.normSq (L v)=c*Complex.normSq v) : IsConformalMap L := by
  apply (isConformalMap_iff L).mpr
  refine ⟨c,hc,fun u v => ?_⟩
  have hn (v : ℂ) : ‖L v‖^2=c*‖v‖^2 := by simpa only [Complex.sq_norm] using h v
  have hu := hn u
  have hv := hn v
  have huv := hn (u+v)
  rw [map_add,norm_add_sq_real,norm_add_sq_real] at huv
  nlinarith

lemma evaluate_pull_derivative (A : ℂ →L[ℝ] ℂ) (q : Form) (v : ℂ) :
    evaluate (pullForm (derivativeMatrix A) q) v.re v.im = evaluate q (A v).re (A v).im := by
  rw [evaluate_pullForm,derivative_apply A v]
  simp [derivativeMatrix,Complex.real_smul,mul_comm]

lemma invariant_form_evaluate {A : ℂ →L[ℝ] ℂ} {p q : Form}
    (hA : Function.Bijective A) (h : normalizedPull (derivativeMatrix A) q=p)
    (v : ℂ) : evaluate q (A v).re (A v).im=|derivativeDet A| *evaluate p v.re v.im := by
  have hh := congrArg (fun t : Form => evaluate t v.re v.im) h
  rw [normalizedPull_apply,evaluate_smul,evaluate_pull_derivative] at hh
  change |derivativeDet A|⁻¹*evaluate q (A v).re (A v).im=evaluate p v.re v.im at hh
  have hz := abs_ne_zero.mpr (derivativeDet_ne_zero hA)
  calc
    _ = |derivativeDet A| *(|derivativeDet A|⁻¹*evaluate q (A v).re (A v).im) := by
      rw [← mul_assoc,mul_inv_cancel₀ hz,one_mul]
    _ = _ := by rw [hh]

theorem integrated_invariant_form_conformal
    (A P Q R : ℂ →L[ℝ] ℂ) (p q : Form) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hA : Function.Bijective A)
    (hInv : P.comp R=ContinuousLinearMap.id ℝ ℂ)
    (hI : normalizedPull (derivativeMatrix A) q=p)
    (hP : ∀ v : ℂ, Complex.normSq (P v)=c*evaluate p v.re v.im)
    (hQ : ∀ v : ℂ, Complex.normSq (Q v)=d*evaluate q v.re v.im) :
    IsConformalMap (Q.comp (A.comp R)) := by
  have ha : 0 < |derivativeDet A| := abs_pos.mpr (derivativeDet_ne_zero hA)
  apply isConformalMap_of_normSq _ (div_pos (mul_pos hd ha) hc)
  intro v
  have hv : P (R v)=v := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hInv
  have hp := hP (R v)
  rw [hv] at hp
  change Complex.normSq (Q (A (R v)))=(d*|derivativeDet A|/c)*Complex.normSq v
  rw [hQ,invariant_form_evaluate hA hI,hp]
  field_simp

end CannonConformal

end
end
end
noncomputable section
namespace CannonMobius
open Set Filter Topology MeasureTheory CannonMetricQC CannonConformal
open scoped OnePoint

lemma coordinate_onePoint (F : ℂ ≃ₜ ℂ) (hF0 : F 0=0) (p : Sphere) :
    coordinate (F.onePointCongr p)=F (coordinate p) := by
  induction p using OnePoint.rec with
  | infty => simpa [coordinate] using hF0.symm
  | coe z => rfl

lemma chart_conjugate_onePoint (F : ℂ ≃ₜ ℂ) (hF0 : F 0=0) (f : Sphere ≃ₜ Sphere) :
    inChart false false (F.onePointCongr*f*F.onePointCongr.symm)=
      fun z => F (inChart false false f (F.symm z)) := by
  funext z
  exact coordinate_onePoint F hF0 (f (F.symm z : Sphere))

theorem integrated_conjugate_ae_conformal
    (f : Sphere ≃ₜ Sphere) {η : CannonQM.Distortion} (hf : CannonQM.Controlled f η)
    (q : ℂ → Form)
    (hI : ∀ᵐ z : ℂ, normalizedPull (derivativeMatrix (fderiv ℝ (inChart false false f) z))
      (q (inChart false false f z))=q z)
    (F : ℂ ≃ₜ ℂ) (hF0 : F 0=0) {C : ℝ} (hC : 0 < C)
    (hF : WeakQS F C) (hFi : WeakQS F.symm C)
    (hD : ∀ᵐ z : ℂ, DifferentiableAt ℝ (F : ℂ → ℂ) z ∧
      Function.Bijective (fderiv ℝ (F : ℂ → ℂ) z) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ v : ℂ,
        Complex.normSq (fderiv ℝ (F : ℂ → ℂ) z v)=c*evaluate (q z) v.re v.im) :
    ∀ᵐ y : ℂ, DifferentiableAt ℝ (inChart false false (F.onePointCongr*f*F.onePointCongr.symm)) y ∧
      IsConformalMap (fderiv ℝ (inChart false false (F.onePointCongr*f*F.onePointCongr.symm)) y) := by
  have hcore : ∀ᵐ z : ℂ, DifferentiableAt ℝ (inChart false false f) z ∧
      Function.Bijective (fderiv ℝ (inChart false false f) z) ∧
      normalizedPull (derivativeMatrix (fderiv ℝ (inChart false false f) z))
        (q (inChart false false f z))=q z ∧
      (DifferentiableAt ℝ (F : ℂ → ℂ) z ∧
        Function.Bijective (fderiv ℝ (F : ℂ → ℂ) z) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ v : ℂ, Complex.normSq (fderiv ℝ (F : ℂ → ℂ) z v)=c*evaluate (q z) v.re v.im) ∧
      (DifferentiableAt ℝ (F : ℂ → ℂ) (inChart false false f z) ∧
        Function.Bijective (fderiv ℝ (F : ℂ → ℂ) (inChart false false f z)) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ v : ℂ, Complex.normSq (fderiv ℝ (F : ℂ → ℂ) (inChart false false f z) v)=
          c*evaluate (q (inChart false false f z)) v.re v.im) := by
    filter_upwards [controlled_sphere_ae_differentiable f hf,
      controlled_sphere_ae_bijective_fderiv f hf,hI,hD,controlled_chart_ae_pullback f hf hD]
      with z hz hn hi hd he
    exact ⟨hz,hn,hi,hd,he⟩
  have hm := weakQS_quasiMeasurePreserving F.symm hC hF
  filter_upwards [hm.ae hcore,weakQS_ae_differentiable F.symm hC hFi] with y hy hiy
  rcases hy with ⟨hdy,hay,hiyq,hpy,hqy⟩
  rcases hpy with ⟨hp,hpn,c,hc,hpc⟩
  rcases hqy with ⟨hq,hqn,d,hd,hqd⟩
  have hId : (fderiv ℝ (F : ℂ → ℂ) (F.symm y)).comp
      (fderiv ℝ (F.symm : ℂ → ℂ) y)=ContinuousLinearMap.id ℝ ℂ := by
    have hh := hp.hasFDerivAt.comp y hiy.hasFDerivAt
    have he : (F : ℂ → ℂ) ∘ (F.symm : ℂ → ℂ)=id := by funext z; exact F.apply_symm_apply z
    rw [he] at hh
    exact hh.unique (hasFDerivAt_id y)
  have hchain := hq.hasFDerivAt.comp y (hdy.hasFDerivAt.comp y hiy.hasFDerivAt)
  have hnorm := integrated_invariant_form_conformal
    (fderiv ℝ (inChart false false f) (F.symm y))
    (fderiv ℝ (F : ℂ → ℂ) (F.symm y))
    (fderiv ℝ (F : ℂ → ℂ) (inChart false false f (F.symm y)))
    (fderiv ℝ (F.symm : ℂ → ℂ) y) (q (F.symm y)) (q (inChart false false f (F.symm y)))
    hc hd hay hId hiyq hpc hqd
  rw [chart_conjugate_onePoint F hF0 f]
  exact ⟨hchain.differentiableAt,hchain.fderiv ▸ hnorm⟩

end CannonMobius

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_PlaneWeakQSBounded
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
noncomputable section
namespace CannonQM
open Set Metric Filter Bornology

lemma plane_weakQS_of_bounded (f : ℂ ≃ₜ ℂ) {C : ℝ} (hC : 0 < C)
    (hf : ∀ x y z w : ℂ, Distinct x y z w → (crossRatio x y z w : ℝ) ≤ 2 →
      (crossRatio (f x) (f y) (f z) (f w) : ℝ) ≤ C) :
    CannonMetricQC.WeakQS f (1+2*C) := by
  intro x y z hxyz
  have hη0 : 0 ≤ C := hC.le
  have hH : 1 ≤ 1+2*C := by linarith
  by_cases hxy : x=y
  · subst y; simp; positivity
  by_cases hxz : x=z
  · subst z
    have : x=y := dist_eq_zero.mp (le_antisymm (by simpa using hxyz) dist_nonneg)
    exact (hxy this).elim
  by_cases hyz : y=z
  · subst z
    exact le_mul_of_one_le_left dist_nonneg hH
  have ht : Tendsto f (cobounded ℂ) (cobounded ℂ) := by
    simpa only [cobounded_eq_cocompact] using f.isClosedEmbedding.tendsto_cocompact
  have hs := eventually_dist_large y (dist z y)
  have hi := ht.eventually (eventually_dist_large (f z) (dist (f y) (f z)))
  obtain ⟨w,hw,hwi,hwx⟩ := (hs.and (hi.and (eventually_ne_cobounded x))).exists
  have hwy : w ≠ y := by intro he; rw [he,dist_self] at hw; exact not_lt_of_ge dist_nonneg hw
  have hwz : w ≠ z := by intro he; rw [he] at hw; exact (lt_irrefl _ hw)
  have hquad : Distinct x y w z := ⟨hxy,hwx.symm,hxz,hwy.symm,hyz,hwz⟩
  have hsource : dist w z ≤ 2*dist y w := by
    have hh := dist_triangle w y z
    rw [dist_comm z y] at hw
    rw [dist_comm w y] at hw hh
    linarith
  have htarget : dist (f y) (f w) ≤ 2*dist (f w) (f z) := by
    have hh := dist_triangle (f y) (f z) (f w)
    rw [dist_comm (f z) (f w)] at hh
    linarith
  have hp : 0 < dist x z := dist_pos.mpr hxz
  have hpy : 0 < dist y w := dist_pos.mpr hwy.symm
  have hrat : crossRatio x y w z ≤ 2 := by
    have hh : dist x y*dist w z ≤ 2*(dist x z*dist y w) := by
      calc
        _ ≤ dist x z*(2*dist y w) := mul_le_mul hxyz hsource dist_nonneg dist_nonneg
        _ = _ := by ring
    apply NNReal.coe_le_coe.mp
    change dist x y*dist w z/(dist x z*dist y w) ≤ (2:ℝ)
    exact (div_le_iff₀ (mul_pos hp hpy)).mpr hh
  have hc := hf x y w z hquad (by exact_mod_cast hrat)
  have hfxz : 0 < dist (f x) (f z) := dist_pos.mpr (fun he => hxz (f.injective he))
  have hfyw : 0 < dist (f y) (f w) := dist_pos.mpr (fun he => hwy (f.injective he).symm)
  have hfwz : 0 < dist (f w) (f z) := dist_pos.mpr (fun he => hwz (f.injective he))
  have hcR : dist (f x) (f y)*dist (f w) (f z) ≤
      C*(dist (f x) (f z)*dist (f y) (f w)) := by
    have hh := hc
    change dist (f x) (f y)*dist (f w) (f z)/(dist (f x) (f z)*dist (f y) (f w)) ≤ C at hh
    exact (div_le_iff₀ (mul_pos hfxz hfyw)).mp hh
  have he : dist (f x) (f y) ≤ 2*C*dist (f x) (f z) := by
    apply (mul_le_mul_iff_left₀ hfwz).mp
    calc
      _ ≤ C*(dist (f x) (f z)*dist (f y) (f w)) := hcR
      _ ≤ C*(dist (f x) (f z)*(2*dist (f w) (f z))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htarget dist_nonneg) hη0
      _ = _ := by ring
  nlinarith [dist_nonneg (x:=f x) (y:=f z)]

lemma BoundedCrossRatios.plane_weakQS (f : ℂ ≃ₜ ℂ) (hf : BoundedCrossRatios f) :
    ∃ H : ℝ, 0 < H ∧ CannonMetricQC.WeakQS f H := by
  obtain ⟨C,hC,hc⟩ := hf 2
  exact ⟨1+2*C,by positivity,plane_weakQS_of_bounded f hC hc⟩
end CannonQM

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Normalizer
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
noncomputable section
noncomputable section
open Set Filter Topology
open scoped OnePoint

noncomputable section
open Set Filter Topology

namespace CannonMobius
open Set Filter Topology CannonH3
open scoped OnePoint

lemma reflection_inv : boundaryReflection⁻¹=boundaryReflection :=
  inv_eq_of_mul_eq_one_left boundaryReflection_sq
lemma reflection_affine (a b : ℂ) (ha : a ≠ 0) :
    boundaryReflection*affine a b ha*boundaryReflection=affine (star a) (star b) (star_ne_zero.mpr ha) := by
  apply Homeomorph.ext
  intro p
  induction p using OnePoint.rec with
  | infty => rfl
  | coe z =>
    change ((star (a*star z+b):ℂ):Sphere)=((star a*z+star b:ℂ):Sphere)
    rw [star_add,star_mul,star_star,mul_comm z]
lemma reflection_inversion : boundaryReflection*inversion*boundaryReflection=inversion := by
  apply Homeomorph.ext
  intro p
  induction p using OnePoint.rec with
  | infty =>
    change boundaryReflection (inv ∞)=inv ∞
    rw [inv_infty]
    change ((star (0:ℂ):ℂ):Sphere)=((0:ℂ):Sphere)
    simp
  | coe z =>
    by_cases hz : z=0
    · subst z
      change boundaryReflection (inv ((star (0:ℂ):ℂ):Sphere))=inv ((0:ℂ):Sphere)
      simp only [star_zero,inv_zero]
      rfl
    · change boundaryReflection (inv ((star z:ℂ):Sphere))=inv (z:Sphere)
      rw [inv_coe (star_ne_zero.mpr hz),inv_coe hz]
      change ((star ((star z)⁻¹):ℂ):Sphere)=((z⁻¹:ℂ):Sphere)
      rw [star_inv₀,star_star]

lemma reflection_conjugate_biholomorphic {f : Sphere ≃ₜ Sphere} (hf : f ∈ biholomorphic) :
    boundaryReflection*f*boundaryReflection ∈ biholomorphic := by
  let C : MulAut (Sphere ≃ₜ Sphere) := MulAut.conj boundaryReflection
  have he (g : Sphere ≃ₜ Sphere) : C g=boundaryReflection*g*boundaryReflection := by
    simp [C,MulAut.conj_apply,reflection_inv]
  have ha (a b : ℂ) (h : a ≠ 0) : C (affine a b h) ∈ biholomorphic := by
    rw [he,reflection_affine]
    exact affine_biholomorphic _ _ _
  have hi : C inversion ∈ biholomorphic := by rw [he,reflection_inversion]; exact inversion_biholomorphic
  rw [← he]
  rcases biholomorphic_normal_form f hf with ⟨a,b,h,rfl⟩|⟨p,a,b,h,rfl⟩
  · exact ha a b h
  · rw [map_mul,map_mul]
    exact biholomorphic.mul_mem (biholomorphic.mul_mem (ha 1 p one_ne_zero) hi) (ha a b h)

end CannonMobius

end
end
end
end
noncomputable section
namespace CannonMobius
open Set Filter Topology MeasureTheory CannonMetricQC CannonConformal CannonQM CannonH3
open scoped OnePoint ComplexConjugate

lemma sendToInfty_biholomorphic (p : Sphere) : sendToInfty p ∈ biholomorphic := by
  by_cases hp : p=∞
  · simp [sendToInfty,hp]
  · rw [sendToInfty,ite_eq_right hp]
    exact biholomorphic.mul_mem inversion_biholomorphic (affine_biholomorphic 1 (-coordinate p) one_ne_zero)

lemma ae_conformal_post_biholomorphic (f M : Sphere ≃ₜ Sphere) (hM : M ∈ biholomorphic)
    (hf : ∀ᵐ z : ℂ, DifferentiableAt ℝ (inChart false false f) z ∧
      IsConformalMap (fderiv ℝ (inChart false false f) z)) :
    ∀ᵐ z : ℂ, DifferentiableAt ℝ (inChart false false (M*f)) z ∧
      IsConformalMap (fderiv ℝ (inChart false false (M*f)) z) := by
  filter_upwards [hf,chartDomain_ae f false false,chartDomain_ae (M*f) false false]
    with z hz hzdom hMz
  have hMd : inChart false false f z ∈ chartDomain false false M := by
    change M (coordinate (f (z:Sphere)):Sphere) ≠ ∞
    have hzfinite : f (z:Sphere) ≠ ∞ := hzdom
    rw [coe_coordinate hzfinite]
    exact hMz
  have hdM := (analytic_differentiableAt hM.1 false false hMd).restrictScalars ℝ
  have hm := analytic_chart_conformal M hM hMd
  have hc := (hdM.hasFDerivAt.comp z hz.1.hasFDerivAt).congr_of_eventuallyEq
    (chart_mul_eventually M f hzdom)
  exact ⟨hc.differentiableAt,hc.fderiv ▸ hm.comp hz.2⟩

lemma restriction_affine_or_anti (f : Sphere ≃ₜ Sphere) (hi : f ∞=∞)
    (h : (∃ a b : ℂ, a ≠ 0 ∧ ∀ z, finiteRestriction f hi z=a*z+b) ∨
      (∃ a b : ℂ, a ≠ 0 ∧ ∀ z, finiteRestriction f hi z=a*conj z+b)) :
    f ∈ biholomorphic ∨ boundaryReflection*f ∈ biholomorphic := by
  rcases h with ⟨a,b,ha,he⟩ | ⟨a,b,ha,he⟩
  · left
    have hEq : f=affine a b ha := by
      apply Homeomorph.ext
      intro p
      induction p using OnePoint.rec with
      | infty => exact hi
      | coe z =>
        have hz := congrArg (fun w : ℂ => (w:Sphere)) (he z)
        exact (coe_coordinate (coe_map_ne_infty f hi z)).symm.trans hz
    rw [hEq]
    exact affine_biholomorphic a b ha
  · right
    have hEq : f=affine a b ha*boundaryReflection := by
      apply Homeomorph.ext
      intro p
      induction p using OnePoint.rec with
      | infty => exact hi
      | coe z =>
        have hz := congrArg (fun w : ℂ => (w:Sphere)) (he z)
        exact (coe_coordinate (coe_map_ne_infty f hi z)).symm.trans hz
    rw [hEq,← mul_assoc,reflection_affine]
    exact affine_biholomorphic _ _ _

theorem sphere_ae_conformal_rigidity (f : Sphere ≃ₜ Sphere)
    (hf : BoundedCrossRatios f) (hi : BoundedCrossRatios f.symm)
    (hd : ∀ᵐ z : ℂ, DifferentiableAt ℝ (inChart false false f) z ∧
      IsConformalMap (fderiv ℝ (inChart false false f) z)) :
    f ∈ biholomorphic ∨ boundaryReflection*f ∈ biholomorphic := by
  let M := sendToInfty (f ∞)
  have hM : M ∈ biholomorphic := sendToInfty_biholomorphic _
  have hMc : Controlled M (OrderIso.refl _) := sendToInfty_controlled _
  have hInf : (M*f) ∞=∞ := sendToInfty_apply _
  have hC : BoundedCrossRatios (M*f) := hMc.boundedCrossRatios.comp hf f.injective
  have hCi : BoundedCrossRatios (M*f).symm :=
    hi.comp (hMc.inverse M).boundedCrossRatios M.symm.injective
  let P := finiteRestriction (M*f) hInf
  obtain ⟨H,hH,hP⟩ := BoundedCrossRatios.plane_weakQS P
    (boundedCrossRatios_restriction (M*f) hInf hC)
  obtain ⟨J,hJ,hPi⟩ := BoundedCrossRatios.plane_weakQS P.symm
    (boundedCrossRatios_restriction (M*f).symm (symm_infty _ hInf) hCi)
  have hpconf : ∀ᵐ z : ℂ, IsConformalMap (fderiv ℝ (P : ℂ → ℂ) z) := by
    filter_upwards [ae_conformal_post_biholomorphic f M hM hd] with z hz
    exact hz.2
  have hclass := weakQS_ae_conformal_affine_or_anti P hH hJ hP hPi hpconf
  rcases restriction_affine_or_anti (M*f) hInf hclass with hleft|hright
  · left
    have hh := biholomorphic.mul_mem (biholomorphic.inv_mem hM) hleft
    simpa only [← mul_assoc,inv_mul_cancel,one_mul] using hh
  · right
    have hm := reflection_conjugate_biholomorphic (biholomorphic.inv_mem hM)
    have hh := biholomorphic.mul_mem hm hright
    simp only [mul_assoc] at hh
    rw [← mul_assoc boundaryReflection boundaryReflection, boundaryReflection_sq, one_mul,
      ← mul_assoc M⁻¹ M, inv_mul_cancel, one_mul] at hh
    exact hh

end CannonMobius

end
end
noncomputable section
namespace CannonMobius
open Set Filter Topology MeasureTheory CannonMetricQC CannonConformal CannonQM CannonH3
open scoped OnePoint

variable {Γ : Type*} [Group Γ] [Countable Γ]

theorem sphere_action_straightening_oai (A : Γ →* (Sphere ≃ₜ Sphere))
    {η : Distortion} (hA : ∀ g, Controlled (A g) η) :
    ∃ F : Sphere ≃ₜ Sphere, ∀ g : Γ,
      F*A g*F.symm ∈ biholomorphic ∨ boundaryReflection*(F*A g*F.symm) ∈ biholomorphic := by
  obtain ⟨q,hqm,hqb,hqi,C,hC,F,hF0,hF1,hF,hFi,hD⟩ := controlled_action_structure_integration A hA
  refine ⟨F.onePointCongr,fun g => ?_⟩
  have hcr := weakQS_sphere_boundedCrossRatios F hC hF
  have hcri : BoundedCrossRatios F.onePointCongr.symm := weakQS_sphere_boundedCrossRatios F.symm hC hFi
  have hB : BoundedCrossRatios (F.onePointCongr*A g*F.onePointCongr.symm) :=
    (hcr.comp (hA g).boundedCrossRatios (A g).injective).comp hcri F.onePointCongr.symm.injective
  have hBi : BoundedCrossRatios (F.onePointCongr*A g*F.onePointCongr.symm).symm :=
    (hcr.comp ((hA g).inverse (A g)).boundedCrossRatios (A g).symm.injective).comp
      hcri F.onePointCongr.symm.injective
  apply sphere_ae_conformal_rigidity _ hB hBi
  exact integrated_conjugate_ae_conformal (A g) (hA g) q ((hqi g).mono (fun _ h => h.2))
    F hF0 hC hF hFi hD

end CannonMobius

end
end
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CannonMobius.sphere_action_straightening_oai.{u_1} := @OAI.CannonMobius.sphere_action_straightening_oai.{u_1}
