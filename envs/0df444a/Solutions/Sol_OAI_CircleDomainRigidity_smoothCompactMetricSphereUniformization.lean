-- Prove2me | solution 1 for OAI.CircleDomainRigidity.smoothCompactMetricSphereUniformization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:55:36.152347+00:00
-- url     : https://prove2.me/submissions/65441b10-f67c-40c9-bf80-ef9928a58a6e

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C007
import Definitions.Def_Q146C008

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

lemma norm_multiplier_eq (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    (hunit : ∀ᵐ x ∂ν, ‖m x‖=1) (f : Lp ℂ 2 ν) :
    ‖multiplier m hm zero_le_one (hunit.mono (fun _ h => h.le)) f‖=‖f‖ := by
  let g := multiplier m hm zero_le_one (hunit.mono (fun _ h => h.le)) f
  have he : ∀ᵐ x ∂ν, ‖g x‖=‖f x‖ := by
    filter_upwards [multiplier_ae m hm zero_le_one (hunit.mono (fun _ h => h.le)) f,hunit] with x hx hx'
    dsimp [g]
    rw [hx,norm_mul,hx',one_mul]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.le)))
    (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.ge)))

lemma norm_symbolMultiplier (f : PlaneL2) : ‖symbolMultiplier f‖=‖f‖ :=
  norm_multiplier_eq beurlingSymbol measurable_beurlingSymbol.aestronglyMeasurable
    (.of_forall norm_beurlingSymbol) f

lemma norm_beurling (f : PlaneL2) : ‖beurling f‖=‖f‖ := by
  change ‖planeFourier.symm (symbolMultiplier (planeFourier f))‖=‖f‖
  rw [planeFourier.symm.norm_map,norm_symbolMultiplier,planeFourier.norm_map]

lemma fourier_beurling_ae (f : PlaneL2) :
    planeFourier (beurling f) =ᵐ[volume] fun z => beurlingSymbol z*planeFourier f z := by
  have he : planeFourier (beurling f)=symbolMultiplier (planeFourier f) :=
    planeFourier.apply_symm_apply _
  rw [he]
  exact multiplier_ae _ _ _ _ _

theorem solve_beltrami_l2 (μ : ℂ → ℂ) (hm : AEStronglyMeasurable μ volume)
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k)
    (b : PlaneL2) :
    ∃ h : PlaneL2, h-multiplier μ hm hk hb (beurling h)=b ∧
      ‖h‖ ≤ ‖b‖/(1-k) ∧
      ∀ h' : PlaneL2, h'-multiplier μ hm hk hb (beurling h')=b → h'=h := by
  let T : PlaneL2 →L[ℂ] PlaneL2 := (multiplier μ hm hk hb).comp beurling
  have hT (h : PlaneL2) : ‖T h‖ ≤ k*‖h‖ := by
    change ‖multiplyLp μ hm hb (beurling h)‖ ≤ k*‖h‖
    exact (norm_multiplyLp_le μ hm hk hb (beurling h)).trans_eq (by rw [norm_beurling])
  let f : PlaneL2 → PlaneL2 := fun h => T h+b
  have hf : ContractingWith ⟨k,hk⟩ f := by
    refine ⟨hk1, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (T x+b) (T y+b) ≤ k*dist x y
    rw [dist_add_right,dist_eq_norm,← map_sub,dist_eq_norm]
    exact hT (x-y)
  let h := hf.fixedPoint f
  have hfix : f h=h := hf.fixedPoint_isFixedPt
  have heq : h-T h=b := by dsimp [f] at hfix; exact sub_eq_iff_eq_add.mpr (hfix.symm.trans (add_comm _ _))
  refine ⟨h,heq,?_,?_⟩
  · apply (le_div_iff₀ (sub_pos.mpr hk1)).mpr
    have hn : ‖h‖ ≤ k*‖h‖+‖b‖ := by
      calc
        ‖h‖ = ‖T h+b‖ := congrArg norm hfix.symm
        _ ≤ ‖T h‖+‖b‖ := norm_add_le _ _
        _ ≤ k*‖h‖+‖b‖ := add_le_add (hT h) le_rfl
    nlinarith
  · intro h' hh'
    apply hf.fixedPoint_unique
    change T h'+b=h'
    change h'-T h'=b at hh'
    exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hh').symm

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

lemma multiplier_coefficient_slope (a : ℝ → ℂ → ℂ)
    (hm : ∀ t, AEStronglyMeasurable (a t) volume)
    {k C : ℝ} (hk : 0 ≤ k) (hC : 0 ≤ C)
    (hb : ∀ t, ∀ᵐ z ∂volume, ‖a t z‖ ≤ k)
    (hq : ∀ t, ∀ᵐ z ∂volume, ‖t⁻¹ • (a t z-a 0 z)‖ ≤ C)
    (t : ℝ) (f : PlaneL2) :
    multiplier (fun z => t⁻¹ • (a t z-a 0 z))
      (((hm t).sub (hm 0)).const_smul t⁻¹) hC (hq t) f=
      t⁻¹ • (multiplier (a t) (hm t) hk (hb t) f-
        multiplier (a 0) (hm 0) hk (hb 0) f) := by
  apply Lp.ext
  filter_upwards [multiplier_ae (fun z => t⁻¹ • (a t z-a 0 z)) _ hC (hq t) f,
    Lp.coeFn_smul t⁻¹ (multiplier (a t) (hm t) hk (hb t) f-
      multiplier (a 0) (hm 0) hk (hb 0) f),
    Lp.coeFn_sub (multiplier (a t) (hm t) hk (hb t) f)
      (multiplier (a 0) (hm 0) hk (hb 0) f),
    multiplier_ae (a t) (hm t) hk (hb t) f,
    multiplier_ae (a 0) (hm 0) hk (hb 0) f] with z h1 h2 h3 h4 h5
  simp only [Pi.smul_apply,Pi.sub_apply] at h2 h3
  rw [h1,h2,h3,h4,h5,smul_mul_assoc,sub_mul]

theorem hasDerivAt_multiplier_product (a : ℝ → ℂ → ℂ) (d : ℂ → ℂ)
    (hm : ∀ t, AEStronglyMeasurable (a t) volume) (hdm : AEStronglyMeasurable d volume)
    {k C : ℝ} (hk : 0 ≤ k) (hC : 0 ≤ C)
    (hb : ∀ t, ∀ᵐ z ∂volume, ‖a t z‖ ≤ k)
    (hq : ∀ t, ∀ᵐ z ∂volume, ‖t⁻¹ • (a t z-a 0 z)‖ ≤ C)
    (hdb : ∀ᵐ z ∂volume, ‖d z‖ ≤ C)
    (hd : ∀ᵐ z ∂volume, HasDerivAt (fun t => a t z) (d z) 0)
    (f : ℝ → PlaneL2) (f' : PlaneL2) (hf : HasDerivAt f f' 0) :
    HasDerivAt (fun t => multiplier (a t) (hm t) hk (hb t) (f t))
      (multiplier (a 0) (hm 0) hk (hb 0) f'+multiplier d hdm hC hdb (f 0)) 0 := by
  let am : ∀ t, AEStronglyMeasurable (fun z => t⁻¹ • (a t z-a 0 z)) volume :=
    fun t => ((hm t).sub (hm 0)).const_smul t⁻¹
  have ht : ∀ᵐ z ∂volume, Tendsto (fun t : ℝ => a t z) (𝓝[≠] 0) (𝓝 (a 0 z)) :=
    hd.mono fun z hz => hz.continuousAt.tendsto.mono_left inf_le_left
  have hqt : ∀ᵐ z ∂volume,
      Tendsto (fun t : ℝ => t⁻¹ • (a t z-a 0 z)) (𝓝[≠] 0) (𝓝 (d z)) := by
    filter_upwards [hd] with z hz
    simpa only [zero_add] using hz.tendsto_slope_zero
  have hfirst := multiplier_variable_convergence a (a 0) hm (hm 0) hk hb (hb 0) ht
    (fun t : ℝ => t⁻¹ • (f t-f 0)) f' (by simpa using hf.tendsto_slope_zero)
  have hsecond := multiplier_strong_convergence_filter
    (fun t z => t⁻¹ • (a t z-a 0 z)) d am hdm hC hq hdb hqt (f 0)
  have he (t : ℝ) :
      multiplier (a t) (hm t) hk (hb t) (t⁻¹ • (f t-f 0))+
      multiplier (fun z => t⁻¹ • (a t z-a 0 z)) (am t) hC (hq t) (f 0)=
      t⁻¹ • (multiplier (a t) (hm t) hk (hb t) (f t)-
        multiplier (a 0) (hm 0) hk (hb 0) (f 0)) := by
    rw [multiplier_coefficient_slope a hm hk hC hb hq]
    have hsmul : multiplier (a t) (hm t) hk (hb t) (t⁻¹ • (f t-f 0))=
        t⁻¹ • multiplier (a t) (hm t) hk (hb t) (f t-f 0) :=
      (multiplier (a t) (hm t) hk (hb t)).toLinearMap.map_smul_of_tower _ _
    rw [hsmul]
    simp only [map_sub,smul_sub]
    abel
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [zero_add,he] using hfirst.add hsecond

lemma translate_multiplier (a : ℂ) (μ : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) {k : ℝ} (hk : 0 ≤ k)
    (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k) (f : PlaneL2) :
    translateL2 a (multiplier μ hm hk hb f)=
      multiplier (fun z => μ (z+a))
        (hm.comp_quasiMeasurePreserving (measurePreserving_add_right volume a).quasiMeasurePreserving)
        hk ((measurePreserving_add_right volume a).quasiMeasurePreserving.ae hb)
        (translateL2 a f) := by
  apply Lp.ext
  filter_upwards [translateL2_ae a (multiplier μ hm hk hb f),
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp
      (multiplier_ae μ hm hk hb f),
    multiplier_ae (fun z => μ (z+a)) _ hk _ (translateL2 a f),translateL2_ae a f]
      with z h1 h2 h3 h4
  simp only [Function.comp_def] at h2
  rw [h1,h2,h3,h4]

lemma lipschitz_coefficient_quotient (μ : ℂ → ℂ) {L : NNReal}
    (hL : LipschitzWith L μ) (v z : ℂ) (t : ℝ) :
    ‖t⁻¹ • (μ (z+t • v)-μ z)‖ ≤ L*‖v‖ := by
  by_cases ht : t=0
  · simp only [ht,inv_zero,zero_smul,norm_zero]
    positivity
  have hh := hL.dist_le_mul (z+t • v) z
  simp only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs] at hh
  rw [norm_smul,Real.norm_eq_abs,abs_inv]
  calc
    |t|⁻¹*‖μ (z+t • v)-μ z‖ ≤ |t|⁻¹*(L*(|t| *‖v‖)) :=
      mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (abs_nonneg _))
    _ = L*‖v‖ := by field_simp

theorem hasDerivAt_translate_multiplier (μ d : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) (hdm : AEStronglyMeasurable d volume)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k)
    {L : NNReal} (hL : LipschitzWith L μ) (v : ℂ)
    (hd : ∀ z, HasDerivAt (fun t : ℝ => μ (z+t • v)) (d z) 0)
    (hdb : ∀ᵐ z ∂volume, ‖d z‖ ≤ L*‖v‖)
    (f f' : PlaneL2) (hf : HasDerivAt (fun t : ℝ => translateL2 (t • v) f) f' 0) :
    HasDerivAt (fun t : ℝ => translateL2 (t • v) (multiplier μ hm hk hb f))
      (multiplier μ hm hk hb f'+
        multiplier d hdm (mul_nonneg L.coe_nonneg (norm_nonneg v)) hdb f) 0 := by
  let am (t : ℝ) := hm.comp_quasiMeasurePreserving
    (measurePreserving_add_right volume (t • v)).quasiMeasurePreserving
  let ab (t : ℝ) := (measurePreserving_add_right volume (t • v)).quasiMeasurePreserving.ae hb
  have hq (t : ℝ) : ∀ᵐ z ∂volume,
      ‖t⁻¹ • (μ (z+t • v)-μ (z+(0:ℝ) • v))‖ ≤ L*‖v‖ := by
    exact .of_forall fun z => by simpa using lipschitz_coefficient_quotient μ hL v z t
  have ht := hasDerivAt_multiplier_product (fun t z => μ (z+t • v)) d am hdm hk
    (mul_nonneg L.coe_nonneg (norm_nonneg v)) ab hq hdb (.of_forall hd)
    (fun t : ℝ => translateL2 (t • v) f) f' hf
  have he : (fun t : ℝ => multiplier (fun z => μ (z+t • v)) (am t) hk (ab t)
      (translateL2 (t • v) f))=
      (fun t : ℝ => translateL2 (t • v) (multiplier μ hm hk hb f)) := by
    funext t
    exact (translate_multiplier (t • v) μ hm hk hb f).symm
  rw [he] at ht
  simpa only [zero_smul,add_zero,translateL2_zero] using ht

theorem differentiated_beltrami (μ d : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) (hdm : AEStronglyMeasurable d volume)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k)
    {L : NNReal} (hL : LipschitzWith L μ) (v : ℂ)
    (hd : ∀ z, HasDerivAt (fun t : ℝ => μ (z+t • v)) (d z) 0)
    (hdb : ∀ᵐ z ∂volume, ‖d z‖ ≤ L*‖v‖)
    (h b h' b' : PlaneL2)
    (he : h-multiplier μ hm hk hb (beurling h)=b)
    (hh : HasDerivAt (fun t : ℝ => translateL2 (t • v) h) h' 0)
    (hb' : HasDerivAt (fun t : ℝ => translateL2 (t • v) b) b' 0) :
    h'-multiplier μ hm hk hb (beurling h')=
      b'+multiplier d hdm (mul_nonneg L.coe_nonneg (norm_nonneg v)) hdb (beurling h) := by
  have hs : HasDerivAt (fun t : ℝ => translateL2 (t • v) (beurling h)) (beurling h') 0 := by
    have ht := (beurling.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hh
    change HasDerivAt (fun t : ℝ => beurling (translateL2 (t • v) h)) (beurling h') 0 at ht
    simpa only [translate_beurling] using ht
  have hp := hasDerivAt_translate_multiplier μ d hm hdm hk hb hL v hd hdb (beurling h) (beurling h') hs
  have ht := hh.sub hp
  have hf : (fun t : ℝ => translateL2 (t • v) h-
      translateL2 (t • v) (multiplier μ hm hk hb (beurling h)))=
      (fun t : ℝ => translateL2 (t • v) b) := by
    funext t
    rw [← map_sub,he]
  change HasDerivAt (fun t : ℝ => translateL2 (t • v) h-
      translateL2 (t • v) (multiplier μ hm hk hb (beurling h))) _ 0 at ht
  rw [hf] at ht
  have hu := ht.unique hb'
  rw [← hu]
  abel

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

theorem beltrami_solution_difference
    (μ ν : ℂ → ℂ) (hm : AEStronglyMeasurable μ volume)
    (hn : AEStronglyMeasurable ν volume) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k) (hc : ∀ᵐ z ∂volume, ‖ν z‖ ≤ k)
    (h h' b b' : PlaneL2)
    (he : h-multiplier μ hm hk hb (beurling h)=b)
    (he' : h'-multiplier ν hn hk hc (beurling h')=b') :
    ‖h'-h‖ ≤ (‖b'-b‖+
      ‖multiplier ν hn hk hc (beurling h)-multiplier μ hm hk hb (beurling h)‖)/(1-k) := by
  let M := multiplier μ hm hk hb
  let N := multiplier ν hn hk hc
  have hid : h'-h = N (beurling (h'-h))+(b'-b)+(N (beurling h)-M (beurling h)) := by
    rw [map_sub,map_sub]
    change h-M (beurling h)=b at he
    change h'-N (beurling h')=b' at he'
    rw [← he,← he']
    abel
  have hnorm : ‖h'-h‖ ≤ k*‖h'-h‖+‖b'-b‖+‖N (beurling h)-M (beurling h)‖ := by
    calc
      ‖h'-h‖ = ‖N (beurling (h'-h))+(b'-b)+(N (beurling h)-M (beurling h))‖ := congrArg norm hid
      _ ≤ ‖N (beurling (h'-h))‖+‖b'-b‖+‖N (beurling h)-M (beurling h)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ k*‖h'-h‖+‖b'-b‖+‖N (beurling h)-M (beurling h)‖ := by
        gcongr
        exact (norm_multiplyLp_le ν hn hk hc (beurling (h'-h))).trans_eq
          (by rw [norm_beurling])
  apply (le_div_iff₀ (sub_pos.mpr hk1)).mpr
  nlinarith

theorem beltrami_translation_estimate (μ : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k) (h b : PlaneL2)
    (he : h-multiplier μ hm hk hb (beurling h)=b)
    (a : ℂ) {c : ℝ} (hc : ∀ᵐ z ∂volume, ‖μ (z+a)-μ z‖ ≤ c) :
    ‖translateL2 a h-h‖ ≤ (‖translateL2 a b-b‖+c*‖h‖)/(1-k) := by
  let hm' := hm.comp_quasiMeasurePreserving
    (measurePreserving_add_right volume a).quasiMeasurePreserving
  let hb' := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae hb
  have he' : translateL2 a h-
      multiplier (fun z => μ (z+a)) hm' hk hb' (beurling (translateL2 a h))=
      translateL2 a b := by
    have ht := congrArg (translateL2 a) he
    rw [map_sub,translate_multiplier,translate_beurling] at ht
    exact ht
  have hd := beltrami_solution_difference μ (fun z => μ (z+a)) hm hm' hk hk1 hb hb'
    h (translateL2 a h) b (translateL2 a b) he he'
  refine hd.trans (div_le_div_of_nonneg_right (add_le_add le_rfl ?_) (sub_pos.mpr hk1).le)
  rw [← norm_beurling h]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub
    (multiplier (fun z => μ (z+a)) hm' hk hb' (beurling h))
    (multiplier μ hm hk hb (beurling h)),
    multiplier_ae (fun z => μ (z+a)) hm' hk hb' (beurling h),
    multiplier_ae μ hm hk hb (beurling h),hc] with z h1 h2 h3 h4
  simp only [Pi.sub_apply] at h1
  rw [h1,h2,h3,← sub_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right h4 (norm_nonneg _)

theorem beltrami_difference_quotient_bound (μ : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k) (h b : PlaneL2)
    (he : h-multiplier μ hm hk hb (beurling h)=b)
    {L : NNReal} (hL : LipschitzWith L μ) {B : ℝ}
    (hB : ∀ a : ℂ, ‖translateL2 a b-b‖ ≤ B*‖a‖) (a : ℂ) :
    ‖translateL2 a h-h‖ ≤ ((B+L*‖h‖)/(1-k))*‖a‖ := by
  have hc : ∀ᵐ z ∂volume, ‖μ (z+a)-μ z‖ ≤ L*‖a‖ := by
    apply Filter.Eventually.of_forall
    intro z
    simpa only [dist_eq_norm,add_sub_cancel_left] using hL.dist_le_mul (z+a) z
  have hh := beltrami_translation_estimate μ hm hk hk1 hb h b he a hc
  calc
    ‖translateL2 a h-h‖ ≤ (‖translateL2 a b-b‖+(L*‖a‖)*‖h‖)/(1-k) := hh
    _ ≤ (B*‖a‖+(L*‖a‖)*‖h‖)/(1-k) :=
      div_le_div_of_nonneg_right (add_le_add (hB a) le_rfl) (sub_pos.mpr hk1).le
    _ = _ := by ring

lemma BoundedSmooth.zero {n : ℕ} {μ : ℂ → ℂ} (h : BoundedSmooth n μ) :
    BoundedSmooth 0 μ := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih h.1

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

lemma coefficient_derivative_bound (μ d : ℂ → ℂ) {L : NNReal}
    (hL : LipschitzWith L μ) (v : ℂ)
    (hd : ∀ z, HasDerivAt (fun t : ℝ => μ (z+t • v)) (d z) 0) (z : ℂ) :
    ‖d z‖ ≤ L*‖v‖ := by
  have ht : Tendsto (fun t : ℝ => ‖t⁻¹ • (μ (z+t • v)-μ z)‖)
      (𝓝[≠] 0) (𝓝 ‖d z‖) := by
    simpa only [zero_add,zero_smul,add_zero] using (hd z).tendsto_slope_zero.norm
  exact le_of_tendsto ht (.of_forall fun t => lipschitz_coefficient_quotient μ hL v z t)

lemma Sobolev.multiplier {n : ℕ} {f : PlaneL2} (hf : Sobolev n f)
    (μ : ℂ → ℂ) (hμ : BoundedSmooth n μ)
    (hm : AEStronglyMeasurable μ volume) {k : ℝ} (hk : 0 ≤ k)
    (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k) :
    Sobolev n (multiplier μ hm hk hb f) := by
  induction n generalizing f μ k with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih hf.1 μ hμ.1 hm hk hb, fun b => ?_⟩
    obtain ⟨L,hL,hds⟩ := hμ.2
    obtain ⟨d,hd,he⟩ := hds b
    obtain ⟨df,hdf,hrf⟩ := hf.2 b
    have hdb : ∀ᵐ z ∂volume, ‖d z‖ ≤ L*‖axis b‖ :=
      Filter.Eventually.of_forall (coefficient_derivative_bound μ d hL (axis b) he)
    let M := CannonBeltrami.multiplier d hd.zero.1 (mul_nonneg L.coe_nonneg (norm_nonneg (axis b))) hdb
    refine ⟨CannonBeltrami.multiplier μ hm hk hb df + M f, ?_, ?_⟩
    · exact hasDerivAt_translate_multiplier μ d hm hd.zero.1 hk hb hL (axis b) he hdb f df hdf
    · exact (ih hrf μ hμ.1 hm hk hb).add
        (ih hf.1 d hd hd.zero.1 (mul_nonneg L.coe_nonneg (norm_nonneg (axis b))) hdb)

lemma Sobolev.translation_bound {n : ℕ} {f : PlaneL2} (hf : Sobolev (n+1) f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : ℂ, ‖translateL2 a f-f‖ ≤ B*‖a‖ := by
  obtain ⟨fx,hx,_⟩ := hf.2 false
  obtain ⟨fy,hy,_⟩ := hf.2 true
  refine ⟨‖fx‖+‖fy‖, add_nonneg (norm_nonneg _) (norm_nonneg _), ?_⟩
  exact translation_bound_of_coordinate_derivatives f fx fy hx hy

theorem beltrami_sobolev {n : ℕ} (μ : ℂ → ℂ) (hμ : BoundedSmooth n μ)
    (hm : AEStronglyMeasurable μ volume) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k) (h b : PlaneL2)
    (he : h-multiplier μ hm hk hb (beurling h)=b) (hrb : Sobolev n b) :
    Sobolev n h := by
  induction n generalizing h b with
  | zero => trivial
  | succ n ih =>
    have hrh : Sobolev n h := ih hμ.1 h b he hrb.1
    obtain ⟨L,hL,hds⟩ := hμ.2
    obtain ⟨B,hB,hBt⟩ := hrb.translation_bound
    let C : ℝ := (B+L*‖h‖)/(1-k)
    have hC : 0 ≤ C := div_nonneg (add_nonneg hB (mul_nonneg L.coe_nonneg (norm_nonneg _)))
      (sub_pos.mpr hk1).le
    have hCt (a : ℂ) : ‖translateL2 a h-h‖ ≤ C*‖a‖ :=
      beltrami_difference_quotient_bound μ hm hk hk1 hb h b he hL hBt a
    refine ⟨hrh, fun j => ?_⟩
    let v := axis j
    let hd := (memLp_directionSymbol_of_translation_bound h hC hCt v).1
    let dh := planeFourier.symm (hd.toLp (fun z => directionSymbol v z*planeFourier h z))
    have hdh : HasDerivAt (fun t : ℝ => translateL2 (t • v) h) dh 0 :=
      hasDerivAt_translateL2 h v hd
    obtain ⟨d,hrd,hder⟩ := hds j
    obtain ⟨db,hdb,hrdb⟩ := hrb.2 j
    have hdbound : ∀ᵐ z ∂volume, ‖d z‖ ≤ L*‖v‖ :=
      Filter.Eventually.of_forall (coefficient_derivative_bound μ d hL v hder)
    let M := multiplier d hrd.zero.1 (mul_nonneg L.coe_nonneg (norm_nonneg v)) hdbound
    have hde : dh-multiplier μ hm hk hb (beurling dh)=db+M (beurling h) :=
      differentiated_beltrami μ d hm hrd.zero.1 hk hb hL v hder hdbound h b dh db he hdh hdb
    have hrs : Sobolev n (db+M (beurling h)) := hrdb.add
      (hrh.beurling.multiplier d hrd hrd.zero.1 (mul_nonneg L.coe_nonneg (norm_nonneg v)) hdbound)
    exact ⟨dh, hdh, ih hμ.1 dh (db+M (beurling h)) hde hrs⟩

open scoped SchwartzMap LineDeriv FourierTransform

lemma schwartz_lipschitz (f : SchwartzMap ℂ ℂ) : ∃ L : NNReal, LipschitzWith L f := by
  let d := SchwartzMap.fderivCLM ℝ ℂ ℂ f
  let K : NNReal := ⟨SchwartzMap.seminorm ℝ 0 0 d, apply_nonneg _ _⟩
  refine ⟨K, lipschitzWith_of_nnnorm_fderiv_le f.differentiable ?_⟩
  intro z
  change ‖fderiv ℝ f z‖₊ ≤ K
  exact_mod_cast d.norm_le_seminorm ℝ z

lemma schwartz_line_derivative (f : SchwartzMap ℂ ℂ) (v z : ℂ) :
    HasDerivAt (fun t : ℝ => f (z+t • v)) (∂_{v} f z) 0 := by
  have ht := ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z
  have hf := (f.hasFDerivAt (z+(0:ℝ) • v)).comp_hasDerivAt 0 ht
  convert hf using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [zero_smul,add_zero,one_smul, SchwartzMap.lineDerivOp_apply_eq_fderiv,Function.comp_def,id_eq])

lemma schwartz_boundedSmooth (n : ℕ) (f : SchwartzMap ℂ ℂ) : BoundedSmooth n f := by
  induction n generalizing f with
  | zero =>
    exact ⟨f.continuous.aestronglyMeasurable,
      ⟨⟨SchwartzMap.seminorm ℝ 0 0 f, apply_nonneg _ _⟩, f.norm_le_seminorm ℝ⟩⟩
  | succ n ih =>
    obtain ⟨L,hL⟩ := schwartz_lipschitz f
    exact ⟨ih f, L,hL,fun b => ⟨(∂_{axis b} f : SchwartzMap ℂ ℂ), ih _, schwartz_line_derivative f (axis b)⟩⟩

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

theorem solve_schwartz_beltrami (μ b : SchwartzMap ℂ ℂ) {k : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1) (hb : ∀ z, ‖μ z‖ ≤ k) :
    ∃ h : PlaneL2,
      h-multiplier μ μ.continuous.aestronglyMeasurable hk (.of_forall hb) (beurling h)=b.toLp 2 ∧
      ‖h‖ ≤ ‖b.toLp 2‖/(1-k) ∧ ∀ n : ℕ, Sobolev n h := by
  obtain ⟨h,he,hn,hu⟩ := solve_beltrami_l2 μ μ.continuous.aestronglyMeasurable hk hk1
    (.of_forall hb) (b.toLp 2)
  exact ⟨h,he,hn,fun n => beltrami_sobolev μ (schwartz_boundedSmooth n μ)
    μ.continuous.aestronglyMeasurable hk hk1 (.of_forall hb) h (b.toLp 2) he (schwartz_sobolev n b)⟩

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

lemma SmoothL2.contDiff {f : PlaneL2} (hf : SmoothL2 f) :
    ContDiff ℝ ∞ (smoothRepresentative f) := by
  have hc : ContDiff ℝ ∞ (𝓕 (planeFourier f : ℂ → ℂ)) :=
    Real.contDiff_fourier (fun n _ => hf.fourier_moments n)
  have he : smoothRepresentative f=(fun z => (𝓕 (planeFourier f : ℂ → ℂ)) (-z)) := by
    funext z
    exact Real.fourierInv_eq_fourier_neg _ _
  rw [he]
  exact hc.comp contDiff_neg

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

lemma fourierSMulRight_inverse (f : ℂ → ℂ) (z v : ℂ) :
    VectorFourier.fourierSMulRight (-(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) f z v =
      directionSymbol v z*f z := by
  change -(2*(Real.pi:ℂ)*Complex.I) • (-inner ℝ z v) • f z = directionSymbol v z*f z
  simp only [Complex.real_smul,smul_eq_mul,directionSymbol]
  push_cast
  rw [real_inner_comm z v]
  ring

end CannonBeltrami

namespace CannonBeltrami

lemma smooth_beltrami_equation (μ b : SchwartzMap ℂ ℂ) {k : ℝ} (hk : 0 ≤ k)
    (hb : ∀ z, ‖μ z‖ ≤ k) (h : PlaneL2) (hh : SmoothL2 h)
    (he : h-multiplier μ μ.continuous.aestronglyMeasurable hk (.of_forall hb) (beurling h)=b.toLp 2) :
    ∀ z, smoothRepresentative h z-μ z*smoothRepresentative (beurling h) z=b z := by
  have hae : (fun z => smoothRepresentative h z-μ z*smoothRepresentative (beurling h) z) =ᵐ[volume] b := by
    have he' := congrArg (fun f : PlaneL2 => (f : ℂ → ℂ)) he
    have h0 := Lp.coeFn_sub h (multiplier μ μ.continuous.aestronglyMeasurable hk (.of_forall hb) (beurling h))
    rw [he'] at h0
    filter_upwards [h0,multiplier_ae μ μ.continuous.aestronglyMeasurable hk (.of_forall hb) (beurling h),
      hh.representative_ae,hh.beurling.representative_ae,b.coeFn_toLp 2 volume] with z h1 h2 h3 h4 h5
    simp only [Pi.sub_apply] at h1
    rw [h2,h3,h4,h5] at h1
    exact h1.symm
  have heq := MeasureTheory.Measure.eq_of_ae_eq hae
    (hh.contDiff.continuous.sub (μ.continuous.mul hh.beurling.contDiff.continuous)) b.continuous
  exact congrFun heq

lemma smooth_beltrami_compactSupport (μ b : SchwartzMap ℂ ℂ)
    (hcμ : HasCompactSupport (μ : ℂ → ℂ)) (hcb : HasCompactSupport (b : ℂ → ℂ))
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ z, ‖μ z‖ ≤ k) (h : PlaneL2) (hh : SmoothL2 h)
    (he : h-multiplier μ μ.continuous.aestronglyMeasurable hk (.of_forall hb) (beurling h)=b.toLp 2) :
    HasCompactSupport (smoothRepresentative h) := by
  have hp := smooth_beltrami_equation μ b hk hb h hh he
  apply (hcμ.union hcb).of_isClosed_subset isClosed_closure
  apply closure_minimal _ ((isClosed_tsupport μ).union (isClosed_tsupport b))
  intro z hz
  by_contra hn
  have hμz : μ z=0 := image_eq_zero_of_notMem_tsupport (fun hz' => hn (Or.inl hz'))
  have hbz : b z=0 := image_eq_zero_of_notMem_tsupport (fun hz' => hn (Or.inr hz'))
  have hhz : smoothRepresentative h z=0 := by simpa [hμz,hbz] using hp z
  exact hz hhz

theorem solve_compact_smooth_beltrami (μ b : SchwartzMap ℂ ℂ)
    (hcμ : HasCompactSupport (μ : ℂ → ℂ)) (hcb : HasCompactSupport (b : ℂ → ℂ))
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (hb : ∀ z, ‖μ z‖ ≤ k) :
    ∃ h : SchwartzMap ℂ ℂ, HasCompactSupport (h : ℂ → ℂ) ∧
      ∀ z, h z-μ z*smoothRepresentative (beurling (h.toLp 2)) z=b z := by
  obtain ⟨h,he,hn,hh⟩ := solve_schwartz_beltrami μ b hk hk1 hb
  change SmoothL2 h at hh
  have hc := smooth_beltrami_compactSupport μ b hcμ hcb hk hb h hh he
  let hs : SchwartzMap ℂ ℂ := hc.toSchwartzMap hh.contDiff
  have hsLp : hs.toLp 2=h := by
    apply Lp.ext
    exact (hs.coeFn_toLp 2 volume).trans hh.representative_ae.symm
  refine ⟨hs,hc,?_⟩
  rw [hsLp]
  exact smooth_beltrami_equation μ b hk hb h hh he

end CannonBeltrami

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

namespace CannonBeltrami

lemma measurable_cauchySymbol : Measurable cauchySymbol := by
  unfold cauchySymbol
  fun_prop

lemma norm_cauchySymbol (z : ℂ) : ‖cauchySymbol z‖ = Real.pi⁻¹*‖z‖⁻¹ := by
  simp [cauchySymbol,abs_of_pos Real.pi_pos,mul_comm]

lemma cauchySymbol_le_on_compl {z : ℂ} (hz : z ∉ ball (0:ℂ) 1) :
    ‖cauchySymbol z‖ ≤ Real.pi⁻¹ := by
  have hz' : 1 ≤ ‖z‖ := by simpa only [mem_ball_zero_iff,not_lt] using hz
  rw [norm_cauchySymbol]
  exact mul_le_of_le_one_right (inv_pos.mpr Real.pi_pos).le (inv_le_one_of_one_le₀ hz')

lemma cauchy_fourier_moments (f : SchwartzMap ℂ ℂ) (n : ℕ) :
    Integrable (fun z => ‖z‖^n*‖cauchySymbol z*f z‖) volume := by
  let F : ℂ → ℝ := fun z => ‖z‖^n*‖cauchySymbol z*f z‖
  have hm : AEStronglyMeasurable F volume :=
    (continuous_norm.pow n).aestronglyMeasurable.mul
      (measurable_cauchySymbol.aestronglyMeasurable.mul f.continuous.aestronglyMeasurable).norm
  have hi : IntegrableOn F (ball (0:ℂ) 1) volume := by
    apply integrableOn_ball_of_norm_le_rpow (by norm_num : 1 ≤ Module.finrank ℝ ℂ)
      (α:=1) (C:=Real.pi⁻¹*SchwartzMap.seminorm ℝ 0 0 f) (by norm_num) _ hm
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hz' : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
    have hn : ‖z‖^n ≤ 1 := pow_le_one₀ (norm_nonneg _) hz'
    change ‖‖z‖^n*‖cauchySymbol z*f z‖‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),norm_mul,norm_cauchySymbol]
    rw [Real.rpow_neg_one]
    calc
      ‖z‖^n*(Real.pi⁻¹*‖z‖⁻¹*‖f z‖) ≤ 1*(Real.pi⁻¹*‖z‖⁻¹*SchwartzMap.seminorm ℝ 0 0 f) := by
        gcongr
        exact f.norm_le_seminorm ℝ z
      _ = _ := by ring
  have ho : IntegrableOn F (ball (0:ℂ) 1)ᶜ volume := by
    apply ((f.integrable_pow_mul volume n).const_mul Real.pi⁻¹).integrableOn.mono' hm.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with z hz
    change ‖‖z‖^n*‖cauchySymbol z*f z‖‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),norm_mul]
    calc
      ‖z‖^n*(‖cauchySymbol z‖*‖f z‖) ≤ ‖z‖^n*(Real.pi⁻¹*‖f z‖) := by
        gcongr
        exact cauchySymbol_le_on_compl hz
      _ = _ := by ring
  have hh := hi.union ho
  simpa only [union_compl_self,integrableOn_univ] using hh

lemma cauchy_fourier_integrable (f : SchwartzMap ℂ ℂ) :
    Integrable (fun z => cauchySymbol z*f z) volume := by
  apply integrable_norm_iff (measurable_cauchySymbol.aestronglyMeasurable.mul
    f.continuous.aestronglyMeasurable) |>.mp
  simpa using cauchy_fourier_moments f 0

lemma contDiff_cauchyTransform (f : SchwartzMap ℂ ℂ) :
    ContDiff ℝ ∞ (cauchyTransform f) := by
  have hc : ContDiff ℝ ∞ (𝓕 (fun z => cauchySymbol z*(𝓕 f) z)) :=
    Real.contDiff_fourier (fun n _ => cauchy_fourier_moments (𝓕 f) n)
  have he : cauchyTransform f=(fun z => (𝓕 (fun w => cauchySymbol w*(𝓕 f) w)) (-z)) := by
    funext z
    exact Real.fourierInv_eq_fourier_neg _ _
  rw [he]
  exact hc.comp contDiff_neg

lemma cauchyTransform_zero_at_infty (f : SchwartzMap ℂ ℂ) :
    Tendsto (cauchyTransform f) (cocompact ℂ) (𝓝 0) := by
  have ht : Tendsto (𝓕 (fun z => cauchySymbol z*(𝓕 f) z)) (cocompact ℂ) (𝓝 0) :=
    tendsto_integral_exp_inner_smul_cocompact _
  have he : cauchyTransform f=(fun z => (𝓕 (fun w => cauchySymbol w*(𝓕 f) w)) (-z)) := by
    funext z
    exact Real.fourierInv_eq_fourier_neg _ _
  rw [he]
  exact ht.comp (Homeomorph.neg ℂ).toCocompactMap.cocompact_tendsto'

end CannonBeltrami

namespace CannonBeltrami
open scoped RealInnerProductSpace

lemma schwartz_smoothL2 (f : SchwartzMap ℂ ℂ) : SmoothL2 (f.toLp 2) :=
  fun n => schwartz_sobolev n f

lemma contDiff_smoothBeurling (f : SchwartzMap ℂ ℂ) : ContDiff ℝ ∞ (smoothBeurling f) :=
  (schwartz_smoothL2 f).beurling.contDiff

lemma smoothBeurling_fourier (f : SchwartzMap ℂ ℂ) (x : ℂ) :
    smoothBeurling f x = 𝓕⁻ (fun z => beurlingSymbol z*(𝓕 f) z) x := by
  unfold smoothBeurling smoothRepresentative
  apply Real.fourierInv_congr_ae
  have hf : planeFourier (f.toLp 2)=(𝓕 f).toLp 2 := SchwartzMap.toLp_fourier_eq _
  have hB := fourier_beurling_ae (f.toLp 2)
  rw [hf] at hB
  filter_upwards [hB,(𝓕 f).coeFn_toLp 2 volume] with z hz hz'
  rw [hz,hz']

lemma inverse_fourier_derivative (f : ℂ → ℂ) (hf : Integrable f volume)
    (hm : Integrable (fun z => ‖z‖*‖f z‖) volume) (x v : ℂ) :
    fderiv ℝ (𝓕⁻ f) x v = 𝓕⁻ (fun z => directionSymbol v z*f z) x := by
  let L := -(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
  have hi : Integrable (VectorFourier.fourierSMulRight L f) volume := by
    apply (hm.const_mul (2*Real.pi*‖L‖)).mono' hf.1.fourierSMulRight
    filter_upwards with z
    simpa only [mul_assoc] using VectorFourier.norm_fourierSMulRight_le L f z
  have hd := VectorFourier.hasFDerivAt_fourierIntegral L hf hm x
  change HasFDerivAt (𝓕⁻ f) _ x at hd
  rw [hd.fderiv,Real.fourierIntegral_continuousLinearMap_apply' hi]
  have he : (fun z => VectorFourier.fourierSMulRight L f z v)=
      (fun z => directionSymbol v z*f z) := funext (fun z => fourierSMulRight_inverse f z v)
  rw [he]
  rfl

lemma cauchySymbol_x {z : ℂ} (hz : z ≠ 0) :
    directionSymbol 1 z*cauchySymbol z=1+beurlingSymbol z := by
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hx : inner ℝ (1:ℂ) z=z.re := by simp [real_inner_eq_re_inner,RCLike.inner_apply]
  rw [directionSymbol,hx,cauchySymbol,beurlingSymbol,ite_eq_right hz]
  field_simp
  simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.star_def] using (Complex.add_conj z).symm

lemma cauchySymbol_y {z : ℂ} (hz : z ≠ 0) :
    directionSymbol Complex.I z*cauchySymbol z=Complex.I*(beurlingSymbol z-1) := by
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hy : inner ℝ Complex.I z=z.im := by simp [real_inner_eq_re_inner,RCLike.inner_apply]
  rw [directionSymbol,hy,cauchySymbol,beurlingSymbol,ite_eq_right hz]
  field_simp
  have hz' := Complex.sub_conj z
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im]
  ring

lemma integrable_beurling_fourier (f : SchwartzMap ℂ ℂ) :
    Integrable (fun z => beurlingSymbol z*(𝓕 f) z) volume := by
  apply ((𝓕 f).integrable (μ:=volume)).norm.mono'
    (measurable_beurlingSymbol.aestronglyMeasurable.mul (𝓕 f).continuous.aestronglyMeasurable)
  filter_upwards with z
  simp [norm_beurlingSymbol]

lemma inverseFourier_add {f g : ℂ → ℂ} (hf : Integrable f volume)
    (hg : Integrable g volume) (x : ℂ) :
    𝓕⁻ (fun z => f z+g z) x=𝓕⁻ f x+𝓕⁻ g x := by
  exact congrFun (VectorFourier.fourierIntegral_add (e:=Real.fourierChar)
    (L:= -innerₗ ℂ) Real.continuous_fourierChar (by exact continuous_inner.neg) hf hg) x

lemma inverseFourier_mul (f : ℂ → ℂ) (a x : ℂ) :
    𝓕⁻ (fun z => a*f z) x=a*𝓕⁻ f x := by
  exact congrFun (VectorFourier.fourierIntegral_const_smul Real.fourierChar volume
    (-innerₗ ℂ) f a) x

lemma inverseFourier_sub {f g : ℂ → ℂ} (hf : Integrable f volume)
    (hg : Integrable g volume) (x : ℂ) :
    𝓕⁻ (fun z => f z-g z) x=𝓕⁻ f x-𝓕⁻ g x := by
  have he : (fun z => f z-g z)=(fun z => f z+(-1)*g z) := by ext z; ring
  rw [he,inverseFourier_add hf (hg.const_mul (-1)),inverseFourier_mul]
  ring

lemma cauchyTransform_derivative_x (f : SchwartzMap ℂ ℂ) (x : ℂ) :
    fderiv ℝ (cauchyTransform f) x 1 = f x+smoothBeurling f x := by
  have hm : Integrable (fun z => ‖z‖*‖cauchySymbol z*(𝓕 f) z‖) volume := by
    simpa only [pow_one] using cauchy_fourier_moments (𝓕 f) 1
  rw [cauchyTransform,inverse_fourier_derivative _ (cauchy_fourier_integrable _) hm]
  have hzero : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := volume.ae_ne 0
  have he : (fun z => directionSymbol 1 z*(cauchySymbol z*(𝓕 f) z)) =ᵐ[volume]
      fun z => (𝓕 f) z+beurlingSymbol z*(𝓕 f) z := by
    filter_upwards [hzero] with z hz
    rw [← mul_assoc,cauchySymbol_x hz]
    ring
  rw [Real.fourierInv_congr_ae he]
  rw [inverseFourier_add ((𝓕 f).integrable (μ:=volume)) (integrable_beurling_fourier f)]
  rw [← smoothBeurling_fourier,← SchwartzMap.fourierInv_coe,fourierInv_fourier_eq]

lemma cauchyTransform_derivative_y (f : SchwartzMap ℂ ℂ) (x : ℂ) :
    fderiv ℝ (cauchyTransform f) x Complex.I = Complex.I*(smoothBeurling f x-f x) := by
  have hm : Integrable (fun z => ‖z‖*‖cauchySymbol z*(𝓕 f) z‖) volume := by
    simpa only [pow_one] using cauchy_fourier_moments (𝓕 f) 1
  rw [cauchyTransform,inverse_fourier_derivative _ (cauchy_fourier_integrable _) hm]
  have hzero : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := volume.ae_ne 0
  have he : (fun z => directionSymbol Complex.I z*(cauchySymbol z*(𝓕 f) z)) =ᵐ[volume]
      fun z => Complex.I*(beurlingSymbol z*(𝓕 f) z-(𝓕 f) z) := by
    filter_upwards [hzero] with z hz
    rw [← mul_assoc,cauchySymbol_y hz]
    ring
  rw [Real.fourierInv_congr_ae he]
  rw [inverseFourier_mul,inverseFourier_sub (integrable_beurling_fourier f) ((𝓕 f).integrable (μ:=volume))]
  rw [← smoothBeurling_fourier,← SchwartzMap.fourierInv_coe,fourierInv_fourier_eq]

theorem cauchyTransform_partials (f : SchwartzMap ℂ ℂ) (z : ℂ) :
    partialBar (cauchyTransform f) z=f z ∧
    partialZ (cauchyTransform f) z=smoothBeurling f z := by
  simp only [partialZ,partialBar,cauchyTransform_derivative_x,cauchyTransform_derivative_y]
  constructor <;> ring_nf <;> simp [Complex.I_sq] <;> ring

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

lemma differentiableAt_of_partialBar_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (h0 : partialBar f z=0) : DifferentiableAt ℂ f z := by
  let A : ℂ →L[ℂ] ℂ := (partialZ f z) • ContinuousLinearMap.id ℂ ℂ
  apply (hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt (f':=A) ?_).differentiableAt
  ext v
  change partialZ f z*v = fderiv ℝ f z v
  rw [fderiv_wirtinger,h0,zero_mul,add_zero]

lemma partials_const (a z : ℂ) :
    partialZ (fun _ : ℂ => a) z=0 ∧ partialBar (fun _ : ℂ => a) z=0 := by
  simp [partialZ,partialBar]

lemma partials_id (z : ℂ) : partialZ (fun w : ℂ => w) z=1 ∧
    partialBar (fun w : ℂ => w) z=0 := by
  simp [partialZ,partialBar]

lemma partials_add {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    partialZ (fun w => f w+g w) z=partialZ f z+partialZ g z ∧
    partialBar (fun w => f w+g w) z=partialBar f z+partialBar g z := by
  unfold partialZ partialBar
  have hd : HasFDerivAt (fun w => f w+g w) (fderiv ℝ f z+fderiv ℝ g z) z :=
    hf.hasFDerivAt.add hg.hasFDerivAt
  rw [hd.fderiv]
  simp only [add_apply]
  constructor <;> ring

lemma partials_sub {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    partialZ (fun w => f w-g w) z=partialZ f z-partialZ g z ∧
    partialBar (fun w => f w-g w) z=partialBar f z-partialBar g z := by
  unfold partialZ partialBar
  have hd : HasFDerivAt (fun w => f w-g w) (fderiv ℝ f z-fderiv ℝ g z) z :=
    hf.hasFDerivAt.sub hg.hasFDerivAt
  rw [hd.fderiv]
  simp only [sub_apply]
  constructor <;> ring

lemma partials_mul {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    partialZ (fun w => f w*g w) z=partialZ f z*g z+f z*partialZ g z ∧
    partialBar (fun w => f w*g w) z=partialBar f z*g z+f z*partialBar g z := by
  unfold partialZ partialBar
  rw [show fderiv ℝ (fun w => f w*g w) z =
    f z • fderiv ℝ g z+g z • fderiv ℝ f z from (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  constructor <;> ring

lemma partials_exp {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    partialZ (fun w => Complex.exp (f w)) z=Complex.exp (f z)*partialZ f z ∧
    partialBar (fun w => Complex.exp (f w)) z=Complex.exp (f z)*partialBar f z := by
  simp only [partialZ,partialBar,hf.hasFDerivAt.cexp.fderiv,
    smul_apply,smul_eq_mul]
  constructor <;> ring

lemma wirtinger_commute {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    partialBar (partialZ f) z=partialZ (partialBar f) z := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m:=∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let Dx : ℂ → ℂ := fun w => fderiv ℝ f w 1
  let Dy : ℂ → ℂ := fun w => fderiv ℝ f w Complex.I
  have hx : DifferentiableAt ℝ Dx z := (hd z).clm_apply (differentiableAt_const _)
  have hy : DifferentiableAt ℝ Dy z := (hd z).clm_apply (differentiableAt_const _)
  have he (v w : ℂ) : fderiv ℝ (fun u => fderiv ℝ f u v) z w =
      fderiv ℝ (fderiv ℝ f) z w v := by
    rw [fderiv_clm_apply (hd z) (differentiableAt_const _)]
    simp
  have hxy : fderiv ℝ Dx z Complex.I = fderiv ℝ Dy z 1 := by
    rw [he,he]
    exact hf.contDiffAt.isSymmSndFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _ _
  have hpx : fderiv ℝ (partialZ f) z =
      (2:ℂ)⁻¹ • (fderiv ℝ Dx z-Complex.I • fderiv ℝ Dy z) := by
    have heq : partialZ f=(fun w => (2:ℂ)⁻¹*(Dx w-Complex.I*Dy w)) := by
      ext w; dsimp [partialZ,Dx,Dy] <;> ring
    rw [heq]
    exact ((hx.hasFDerivAt.sub (hy.hasFDerivAt.const_mul Complex.I)).const_mul (2:ℂ)⁻¹).fderiv
  have hpy : fderiv ℝ (partialBar f) z =
      (2:ℂ)⁻¹ • (fderiv ℝ Dx z+Complex.I • fderiv ℝ Dy z) := by
    have heq : partialBar f=(fun w => (2:ℂ)⁻¹*(Dx w+Complex.I*Dy w)) := by
      ext w; dsimp [partialBar,Dx,Dy] <;> ring
    rw [heq]
    exact ((hx.hasFDerivAt.add (hy.hasFDerivAt.const_mul Complex.I)).const_mul (2:ℂ)⁻¹).fderiv
  change (fderiv ℝ (partialZ f) z 1+Complex.I*fderiv ℝ (partialZ f) z Complex.I)/2 =
    (fderiv ℝ (partialBar f) z 1-Complex.I*fderiv ℝ (partialBar f) z Complex.I)/2
  rw [hpx,hpy]
  simp only [sub_apply,add_apply,smul_apply,smul_eq_mul]
  rw [hxy]
  ring

lemma liouville_partialBar {f : ℂ → ℂ} (hf : Differentiable ℝ f)
    (hbar : ∀ z, partialBar f z=0) {c : ℂ} (ht : Tendsto f (cocompact ℂ) (𝓝 c)) :
    ∀ z, f z=c := by
  have hc : Differentiable ℂ f := fun z => differentiableAt_of_partialBar_zero (hf z) (hbar z)
  exact fun z => hc.apply_eq_of_tendsto_cocompact z ht

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

lemma hasCompactSupport_partialZ {f : ℂ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (partialZ f) := by
  apply hf.of_isClosed_subset (isClosed_tsupport _) (closure_minimal ?_ (isClosed_tsupport f))
  intro z hz
  by_contra hn
  have hd := fderiv_of_notMem_tsupport (𝕜:=ℝ) hn
  exact hz (by simp [partialZ,hd])

lemma smoothBeurling_decay (f : SchwartzMap ℂ ℂ) :
    Tendsto (smoothBeurling f) (cocompact ℂ) (𝓝 0) := by
  have ht : Tendsto (𝓕 (fun z => beurlingSymbol z*(𝓕 f) z)) (cocompact ℂ) (𝓝 0) :=
    tendsto_integral_exp_inner_smul_cocompact _
  have he : smoothBeurling f=(fun z => (𝓕 (fun w => beurlingSymbol w*(𝓕 f) w)) (-z)) := by
    funext z
    rw [smoothBeurling_fourier,Real.fourierInv_eq_fourier_neg]
  rw [he]
  exact ht.comp (Homeomorph.neg ℂ).toCocompactMap.cocompact_tendsto'

lemma smoothBeurling_compatibility (f : SchwartzMap ℂ ℂ) (z : ℂ) :
    partialBar (smoothBeurling f) z=partialZ f z := by
  have hbar : partialBar (cauchyTransform f)=f := funext (fun z => (cauchyTransform_partials f z).1)
  have hz : partialZ (cauchyTransform f)=smoothBeurling f :=
    funext (fun z => (cauchyTransform_partials f z).2)
  rw [← hz,wirtinger_commute (contDiff_cauchyTransform f),hbar]

theorem smooth_nonvanishing_factor (μ : SchwartzMap ℂ ℂ)
    (hcμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ z, ‖μ z‖ ≤ k) :
    ∃ (h : SchwartzMap ℂ ℂ) (q : ℂ → ℂ), HasCompactSupport (h : ℂ → ℂ) ∧
      ContDiff ℝ ∞ q ∧ (∀ z, q z ≠ 0) ∧
      (∀ z, h z=μ z*q z) ∧ (∀ z, 1+smoothBeurling h z=q z) := by
  have hμ : ContDiff ℝ ∞ (μ : ℂ → ℂ) := μ.smooth ⊤
  let b : SchwartzMap ℂ ℂ := (hasCompactSupport_partialZ hcμ).toSchwartzMap (contDiff_partials hμ).1
  obtain ⟨w,hcw,hw⟩ := solve_compact_smooth_beltrami μ b hcμ
    (hasCompactSupport_partialZ hcμ) hk hk1 hb
  let q : ℂ → ℂ := fun z => Complex.exp (cauchyTransform w z)
  have hq : ContDiff ℝ ∞ q := (contDiff_cauchyTransform w).cexp
  have hc : HasCompactSupport (fun z => μ z*q z) := hcμ.mul_right
  let h : SchwartzMap ℂ ℂ := hc.toSchwartzMap (hμ.mul hq)
  refine ⟨h,q,hc,hq,fun z => Complex.exp_ne_zero _,fun z => rfl,?_⟩
  let g : ℂ → ℂ := fun z => q z-1-smoothBeurling h z
  have hg : ContDiff ℝ ∞ g := (hq.sub contDiff_const).sub (contDiff_smoothBeurling h)
  have hgz (z : ℂ) : partialBar g z=0 := by
    have hdq : DifferentiableAt ℝ q z := hq.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z
    have hdμ : DifferentiableAt ℝ (μ : ℂ → ℂ) z := hμ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z
    have hdC : DifferentiableAt ℝ (cauchyTransform w) z :=
      (contDiff_cauchyTransform w).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z
    have hbq : partialBar q z=q z*w z := by
      rw [partials_exp hdC |>.2,(cauchyTransform_partials w z).1]
    have hpq : partialZ q z=q z*smoothBeurling w z := by
      rw [partials_exp hdC |>.1,(cauchyTransform_partials w z).2]
    have hwp : w z-μ z*smoothBeurling w z=partialZ μ z := hw z
    have hph : partialZ h z=partialZ μ z*q z+μ z*partialZ q z :=
      (partials_mul hdμ hdq).1
    change partialBar (fun z => (q z-1)-smoothBeurling h z) z=0
    rw [(partials_sub (f:=fun z => q z-1) (g:=smoothBeurling h) (hdq.sub (differentiableAt_const 1))
      ((contDiff_smoothBeurling h).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z)).2]
    rw [(partials_sub (g:=fun _ => (1:ℂ)) hdq (differentiableAt_const 1)).2,(partials_const 1 z).2,
      smoothBeurling_compatibility,hph,hbq,hpq]
    linear_combination q z*hwp
  have hqt : Tendsto q (cocompact ℂ) (𝓝 1) := by
    simpa [q, Function.comp_def] using Complex.continuous_exp.continuousAt.tendsto.comp (cauchyTransform_zero_at_infty w)
  have hgt : Tendsto g (cocompact ℂ) (𝓝 0) := by
    simpa [g] using (hqt.sub (tendsto_const_nhds (x:=(1:ℂ)))).sub (smoothBeurling_decay h)
  intro z
  have he := liouville_partialBar (hg.differentiable (by simp)) hgz hgt z
  change q z-1-smoothBeurling h z=0 at he
  linear_combination -he

theorem smooth_beltrami_nondegenerate (μ : SchwartzMap ℂ ℂ)
    (hcμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ z, ‖μ z‖ ≤ k) :
    ∃ F : ℂ → ℂ, ContDiff ℝ ∞ F ∧
      Tendsto (fun z => F z-z) (cocompact ℂ) (𝓝 0) ∧
      (∀ z, partialBar F z=μ z*partialZ F z) ∧ (∀ z, partialZ F z ≠ 0) := by
  obtain ⟨h,q,hch,hq,hqne,hh,hB⟩ := smooth_nonvanishing_factor μ hcμ hk hk1 hb
  let F : ℂ → ℂ := fun z => z+cauchyTransform h z
  have hp (z : ℂ) : partialZ F z=q z ∧ partialBar F z=h z := by
    have hs := partials_add (f:=fun z : ℂ => z) (differentiableAt_id (𝕜:=ℝ))
      ((contDiff_cauchyTransform h).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z)
    refine ⟨?_,?_⟩
    · change partialZ (fun w => w+cauchyTransform h w) z=q z
      rw [hs.1,(partials_id z).1,(cauchyTransform_partials h z).2,hB]
    · change partialBar (fun w => w+cauchyTransform h w) z=h z
      rw [hs.2,(partials_id z).2,(cauchyTransform_partials h z).1,zero_add]
  refine ⟨F,contDiff_id.add (contDiff_cauchyTransform h),?_,?_,?_⟩
  · simpa [F] using cauchyTransform_zero_at_infty h
  · intro z; rw [(hp z).1,(hp z).2,hh]
  · intro z; rw [(hp z).1]; exact hqne z

lemma beltrami_fderiv_injective {F : ℂ → ℂ} {z μ : ℂ}
    (hμ : ‖μ‖ < 1) (he : partialBar F z=μ*partialZ F z)
    (hn : partialZ F z ≠ 0) : Function.Injective (fderiv ℝ F z) := by
  apply (fderiv ℝ F z).toLinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change fderiv ℝ F z v=0 at hv
  rw [fderiv_wirtinger,he] at hv
  have hv' : v+μ*star v=0 := by
    apply (mul_eq_zero.mp (show partialZ F z*(v+μ*star v)=0 by linear_combination hv)).resolve_left hn
  have hnorm : ‖v‖ ≤ ‖μ‖*‖v‖ := by
    have heq : v= -(μ*star v) := eq_neg_iff_add_eq_zero.mpr hv'
    nth_rw 1 [heq]
    simp
  have hz : ‖v‖=0 := by nlinarith [norm_nonneg v]
  exact norm_eq_zero.mp hz

lemma localHomeomorph_of_beltrami {F : ℂ → ℂ} (hf : ContDiff ℝ ∞ F)
    (μ : ℂ → ℂ) (hb : ∀ z, ‖μ z‖ < 1)
    (he : ∀ z, partialBar F z=μ z*partialZ F z) (hn : ∀ z, partialZ F z ≠ 0) :
    IsLocalHomeomorphOn F univ := by
  intro z _
  have hi := beltrami_fderiv_injective (hb z) (he z) (hn z)
  let A : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.ofBijective (fderiv ℝ F z)
    (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hi))
  have hd : HasFDerivAt F (A : ℂ →L[ℝ] ℂ) z :=
    (hf.differentiable (by simp) z).hasFDerivAt
  exact ⟨hf.contDiffAt.toOpenPartialHomeomorph F hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),
    hf.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),rfl⟩

lemma isProperMap_of_asymptotic_id {F : ℂ → ℂ} (hc : Continuous F)
    (ht : Tendsto (fun z => F z-z) (cocompact ℂ) (𝓝 0)) : IsProperMap F := by
  apply isProperMap_iff_tendsto_cocompact.mpr
  refine ⟨hc,?_⟩
  apply (show Tendsto (fun z => ‖F z‖) (cocompact ℂ) atTop →
    Tendsto F (cocompact ℂ) (cocompact ℂ) from fun h => by
      simpa only [← cobounded_eq_cocompact] using tendsto_norm_atTop_iff_cobounded.mp h)
  have he : ∀ᶠ z in cocompact ℂ, ‖F z-z‖ ≤ 1 :=
    (ht.norm.eventually (eventually_le_nhds (by norm_num : ‖(0:ℂ)‖ < 1)))
  have hn : Tendsto (fun z : ℂ => ‖z‖-1) (cocompact ℂ) atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right (cocompact ℂ) (-1)
      (tendsto_norm_cocompact_atTop (E:=ℂ))
  apply tendsto_atTop_mono' _ ?_ hn
  filter_upwards [he] with z hz
  have h := norm_sub_le (F z) (F z-z)
  have hh : F z-(F z-z)=z := by ring
  rw [hh] at h
  linarith

lemma global_homeomorph_of_proper_local {F : ℂ → ℂ} (hp : IsProperMap F)
    (hl : IsLocalHomeomorphOn F univ) : ∃ e : ℂ ≃ₜ ℂ, (e : ℂ → ℂ)=F := by
  have hcov : IsCoveringMap F := by
    apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
    apply hp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    · intro z _
      apply (hp.isCompact_preimage isCompact_singleton).finite
      apply IsDiscrete.of_openPartialHomeomorph F subset_rfl
      intro x hx
      obtain ⟨e,he,hFe⟩ := hl x (mem_univ _)
      exact ⟨e,he,hFe.symm⟩
    · simpa only [preimage_univ] using hl
  obtain ⟨g,⟨hg0,hg⟩,huniq⟩ := hcov.existsUnique_continuousMap_lifts
    (ContinuousMap.id ℂ) (F 0) 0 rfl
  have hright : Function.RightInverse g F := fun x => congrFun hg x
  have hleft : Function.LeftInverse g F := by
    have he : F ∘ (g ∘ F)=F ∘ id := by ext x; exact hright (F x)
    have hh := hcov.eq_of_comp_eq (g.continuous.comp hp.continuous) continuous_id he 0 hg0
    exact fun x => congrFun hh x
  exact ⟨{ toFun := F
           invFun := g
           left_inv := hleft
           right_inv := hright
           continuous_toFun := hp.continuous
           continuous_invFun := g.continuous },rfl⟩

theorem smooth_beltrami_homeomorph (μ : SchwartzMap ℂ ℂ)
    (hcμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ z, ‖μ z‖ ≤ k) :
    ∃ F : ℂ ≃ₜ ℂ, ContDiff ℝ ∞ (F : ℂ → ℂ) ∧
      Tendsto (fun z => F z-z) (cocompact ℂ) (𝓝 0) ∧
      (∀ z, partialBar F z=μ z*partialZ F z) ∧ (∀ z, partialZ F z ≠ 0) := by
  obtain ⟨F,hF,ht,he,hn⟩ := smooth_beltrami_nondegenerate μ hcμ hk hk1 hb
  obtain ⟨e,heF⟩ := global_homeomorph_of_proper_local
    (isProperMap_of_asymptotic_id hF.continuous ht)
    (localHomeomorph_of_beltrami hF μ (fun z => (hb z).trans_lt hk1) he hn)
  refine ⟨e,?_⟩
  simpa only [heF] using And.intro hF (And.intro ht (And.intro he hn))

lemma contDiff_symm_beltrami (F : ℂ ≃ₜ ℂ) (hf : ContDiff ℝ ∞ (F : ℂ → ℂ))
    (μ : ℂ → ℂ) (hb : ∀ z, ‖μ z‖ < 1)
    (he : ∀ z, partialBar F z=μ z*partialZ F z) (hn : ∀ z, partialZ F z ≠ 0) :
    ContDiff ℝ ∞ (F.symm : ℂ → ℂ) := by
  let A (z : ℂ) : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.ofBijective (fderiv ℝ F z)
    (LinearMap.ker_eq_bot.mpr (beltrami_fderiv_injective (hb z) (he z) (hn z)))
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp
      (beltrami_fderiv_injective (hb z) (he z) (hn z))))
  exact F.contDiff_symm (f₀':=A) (fun z => (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z).hasFDerivAt) hf

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
-- module Solutions.Q146_CD.CircleDomains_Uniformization_MetricConformality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_self _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.chart_infty_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Metric conformality in the concrete sphere charts

Metric conformality records the pullback Gram matrix and positive
orientation of the actual real differential. When the source metric is
a positive scalar multiple of the Euclidean metric, these equations
imply the complex Cauchy--Riemann equation and a nonzero derivative.
-/

open Set Filter
open scoped Topology OnePoint Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem complex_linear_of_positive_orthogonal_columns
    (A : ℂ →L[ℝ] ℂ) {q : ℝ} (hq : 0 < q)
    (hxx : (A 1).re ^ 2 + (A 1).im ^ 2 = q)
    (hyy : (A Complex.I).re ^ 2 + (A Complex.I).im ^ 2 = q)
    (hxy : (A 1).re * (A Complex.I).re + (A 1).im * (A Complex.I).im = 0)
    (hdet : 0 < (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im) :
    A Complex.I = Complex.I • A 1 ∧ A 1 ≠ 0 := by
  let a := (A 1).re
  let b := (A Complex.I).re
  let c := (A 1).im
  let d := (A Complex.I).im
  change a ^ 2 + c ^ 2 = q at hxx
  change b ^ 2 + d ^ 2 = q at hyy
  change a * b + c * d = 0 at hxy
  change 0 < a * d - b * c at hdet
  have hsquare : (a * d - b * c) ^ 2 = q ^ 2 := by
    calc
      _ = (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) - (a * b + c * d) ^ 2 := by ring
      _ = q ^ 2 := by rw [hxx, hyy, hxy]; ring
  have hdetq : a * d - b * c = q := (sq_eq_sq₀ hdet.le hq.le).mp hsquare
  have hsum : (a - d) ^ 2 + (b + c) ^ 2 = 0 := by nlinarith
  have had : a = d := by nlinarith [sq_nonneg (b + c)]
  have hbc : b = -c := by nlinarith [sq_nonneg (a - d)]
  constructor
  · apply Complex.ext
    · change b = (Complex.I * A 1).re
      simpa only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] using hbc
    · change d = (Complex.I * A 1).im
      simpa only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] using had.symm
  · intro hzero
    have ha : a = 0 := congrArg Complex.re hzero
    have hc : c = 0 := congrArg Complex.im hzero
    nlinarith

theorem IsMetricConformalAt.isConformalAt
    {g : (ℝ × ℝ) → PlanarMetric} {f : Sphere → Sphere} {p : Sphere}
    (hf : IsMetricConformalAt g f p)
    (hscalar : ∃ c : ℝ, 0 < c ∧ sphereChartMetric g p = c • (1 : PlanarMetric)) :
    IsConformalAt f p := by
  obtain ⟨hc, hd, scale, hscale, hxx, hyy, hxy, hdet⟩ := hf
  obtain ⟨c, hpos, hmetric⟩ := hscalar
  rw [hmetric] at hxx hyy hxy
  norm_num [Matrix.smul_apply, Matrix.one_apply] at hxx hyy hxy
  obtain ⟨hCR, hnonzero⟩ := complex_linear_of_positive_orthogonal_columns
    (fderiv ℝ (sphereLocalMap f p) (chart p p)) (mul_pos hscale hpos) hxx hyy hxy hdet
  refine ⟨hc, fderiv ℝ (sphereLocalMap f p) (chart p p) 1, hnonzero, ?_⟩
  exact complexOfReal_hasDerivAt hd hCR

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrincipalExteriorGerm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A holomorphic exterior map tending to the identity has an actual
principal Laurent germ. The first two divided differences give the
coefficient and the analytic remainder; no Laurent estimate is assumed. -/
open Set Filter Function Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem invertedPrincipalRemainder_analytic {F : ℂ → ℂ}
    (hF : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z)
    (ht : Tendsto (fun z => F z - z) (cobounded ℂ) (𝓝 0)) :
    AnalyticAt ℂ (invertedPrincipalRemainder F) 0 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · have hd := (tendsto_inv₀_nhdsNE_zero (α := ℂ)).eventually hF
    filter_upwards [hd, self_mem_nhdsWithin] with w hw hw0
    have hn : w ≠ 0 := hw0
    have hi : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) w := differentiableAt_inv hn
    have hh := (hw.comp w hi).sub hi
    apply hh.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hn] with z hz
    exact Function.update_of_ne hz _ _
  · exact continuousAt_update_same.mpr
      (ht.comp (tendsto_inv₀_nhdsNE_zero (α := ℂ)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrincipalInversionGerm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inversion conjugate of a principal holomorphic exterior map has
an analytic germ at zero with derivative one. -/
open Filter Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma principalInversionGerm_eq (F : ℂ → ℂ) :
    principalInversionGerm F =
      fun w => w / (1 + w * invertedPrincipalRemainder F w) := by
  funext w
  by_cases hw : w = 0
  · subst w
    simp [principalInversionGerm]
  · simp only [principalInversionGerm, invertedPrincipalRemainder,
      Function.update_of_ne hw]
    have he : 1 + w * (F w⁻¹ - w⁻¹) = w * F w⁻¹ := by
      rw [mul_sub, mul_inv_cancel₀ hw]
      ring
    rw [he]
    simp only [div_eq_mul_inv, mul_inv_rev]
    calc
      _ = (w * w⁻¹) * (F w⁻¹)⁻¹ := by rw [mul_inv_cancel₀ hw, one_mul]
      _ = _ := by ring

lemma principalInversionGerm_analytic_deriv {F : ℂ → ℂ}
    (hF : ∀ᶠ z in Bornology.cobounded ℂ, DifferentiableAt ℂ F z)
    (ht : Tendsto (fun z => F z - z) (Bornology.cobounded ℂ) (𝓝 0)) :
    AnalyticAt ℂ (principalInversionGerm F) 0 ∧
      HasDerivAt (principalInversionGerm F) 1 0 := by
  have hR := invertedPrincipalRemainder_analytic hF ht
  have hden : 1 + (0 : ℂ) * invertedPrincipalRemainder F 0 ≠ 0 := by simp
  rw [principalInversionGerm_eq]
  constructor
  · exact analyticAt_id.div (analyticAt_const.add (analyticAt_id.mul hR)) hden
  · have hd := (hasDerivAt_id (0 : ℂ)).div
      ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).add ((hasDerivAt_id (0 : ℂ)).mul hR.differentiableAt.hasDerivAt)) hden
    convert hd using 1 <;> first
      | rfl
      | (funext w; rfl)
      | simp

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

lemma analyticAt_inverse_sphereLocalMap_infty
    (e : Sphere ≃ₜ Sphere) (he : e OnePoint.infty = OnePoint.infty)
    (ha : AnalyticAt ℂ (sphereLocalMap e OnePoint.infty) 0)
    (hd : deriv (sphereLocalMap e OnePoint.infty) 0 ≠ 0) :
    AnalyticAt ℂ (sphereLocalMap e.symm OnePoint.infty) 0 := by
  have hei : e.symm OnePoint.infty = OnePoint.infty := by
    apply e.injective
    rw [e.apply_symm_apply, he]
  have hzero : sphereLocalMap e OnePoint.infty 0 = 0 := by
    simp [sphereLocalMap, he, chartSymm, sphereInv, finiteCoord]
  have ht : Tendsto (fun z : ℂ => e (chartSymm OnePoint.infty z)) (𝓝 0) (𝓝 (OnePoint.infty : Sphere)) := by
    have hc : ContinuousAt (fun z : ℂ => e (chartSymm OnePoint.infty z)) 0 :=
      e.continuous.continuousAt.comp (continuous_chartSymm OnePoint.infty).continuousAt
    simpa [chartSymm, sphereInv, he] using hc.tendsto
  have hinv : (sphereLocalMap e.symm OnePoint.infty ∘ sphereLocalMap e OnePoint.infty) =ᶠ[𝓝 0] id := by
    filter_upwards [ht.eventually (eventually_chartSymm_chart OnePoint.infty)] with z hz
    change chart (e.symm OnePoint.infty) (e.symm (chartSymm OnePoint.infty
      (chart (e OnePoint.infty) (e (chartSymm OnePoint.infty z))))) = z
    rw [he, hz, e.symm_apply_apply, hei, chart_chartSymm]
  have hcomp : AnalyticAt ℂ (sphereLocalMap e.symm OnePoint.infty ∘ sphereLocalMap e OnePoint.infty) 0 :=
    analyticAt_id.congr hinv.symm
  simpa only [hzero] using (analyticAt_comp_iff_of_deriv_ne_zero ha hd).mp hcomp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_MetricBeltramiCoefficient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.blendMetric_identity _root_.OAI.CircleDomainRigidity.FiniteTransfer.covectorEnergy_identity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded complex coefficient of a positive planar metric. This is
 the coefficient needed for the smooth metric-sphere uniformization input. -/
open Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma metricBeltramiDenominator_pos {A : PlanarMetric} (hA : A.PosDef) :
    0 < metricBeltramiDenominator A := by
  have h0 : 0 < A 0 0 := hA.diag_pos
  have h1 : 0 < A 1 1 := hA.diag_pos
  have hs := Real.sqrt_nonneg A.det
  dsimp [metricBeltramiDenominator]
  linarith

lemma metricBeltramiCoefficient_norm_lt_one {A : PlanarMetric} (hA : A.PosDef) :
    ‖metricBeltramiCoefficient A‖ < 1 := by
  have hsym : A 1 0 = A 0 1 := by
    have h := congrFun (congrFun hA.isHermitian.eq (0 : Fin 2)) (1 : Fin 2)
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have hdet : A.det = A 0 0 * A 1 1 - (A 0 1)^2 := by
    rw [Matrix.det_fin_two, hsym]
    ring
  have hd := metricBeltramiDenominator_pos hA
  have hs := Real.sqrt_pos.2 hA.det_pos
  have hsq := Real.sq_sqrt hA.det_pos.le
  have hid : (A 0 0 - A 1 1)^2 + (2 * A 0 1)^2 =
      (metricBeltramiDenominator A)^2 -
        4 * Real.sqrt A.det * metricBeltramiDenominator A := by
    dsimp [metricBeltramiDenominator]
    rw [hdet] at hsq ⊢
    nlinarith only [hsq]
  have hn : ‖metricBeltramiCoefficient A‖^2 =
      ((A 0 0 - A 1 1)^2 + (2 * A 0 1)^2) /
        (metricBeltramiDenominator A)^2 := by
    rw [metricBeltramiCoefficient, norm_div, div_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, Complex.sq_norm]
    simp only [Complex.normSq_apply]
    ring
  have hlt : ‖metricBeltramiCoefficient A‖^2 < 1 := by
    rw [hn, div_lt_one (sq_pos_of_pos hd), hid]
    have hpos := mul_pos hs hd
    nlinarith
  nlinarith [norm_nonneg (metricBeltramiCoefficient A)]

lemma contDiff_metricBeltramiCoefficient
    {g : (ℝ × ℝ) → PlanarMetric} (hg : ContDiff ℝ ∞ g)
    (hPD : ∀ x, (g x).PosDef) :
    ContDiff ℝ ∞ (fun x => metricBeltramiCoefficient (g x)) := by
  have hc (i j : Fin 2) : ContDiff ℝ ∞ (fun x => g x i j) := by
    fun_prop
  have hd : ContDiff ℝ ∞ (fun x => (g x).det) := by
    simp only [Matrix.det_fin_two]
    exact ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))
  have hs := hd.sqrt (fun x => (hPD x).det_pos.ne')
  have hden : ContDiff ℝ ∞ (fun x => metricBeltramiDenominator (g x)) :=
    ((hc 0 0).add (hc 1 1)).add (contDiff_const.mul hs)
  have hn : ContDiff ℝ ∞ (fun x => (⟨g x 0 0 - g x 1 1, 2 * g x 0 1⟩ : ℂ)) := by
    have he (x : ℝ × ℝ) : (⟨g x 0 0 - g x 1 1, 2 * g x 0 1⟩ : ℂ) =
        ((g x 0 0 - g x 1 1 : ℝ) : ℂ) + ((2 * g x 0 1 : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    simp_rw [he]
    exact (Complex.ofRealCLM.contDiff.comp ((hc 0 0).sub (hc 1 1))).add
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (hc 0 1))).mul contDiff_const)
  have hinv := hden.inv (fun x => (metricBeltramiDenominator_pos (hPD x)).ne')
  simpa only [metricBeltramiCoefficient, div_eq_mul_inv, Function.comp_apply,
    Pi.inv_apply, Complex.ofRealCLM_apply, Complex.ofReal_inv]
    using hn.mul (Complex.ofRealCLM.contDiff.comp hinv)

lemma metricBeltramiCoefficient_compact_support
    {g : (ℝ × ℝ) → PlanarMetric} {R : ℝ}
    (hfar : ∀ x ∉ Metric.closedBall 0 R, ∃ r : ℝ, g x = r • 1) :
    HasCompactSupport (fun x => metricBeltramiCoefficient (g x)) := by
  apply (isCompact_closedBall (0 : ℝ × ℝ) R).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hball
  obtain ⟨r, hr⟩ := hfar x hball
  exact hx (by simp only [hr, metricBeltramiCoefficient_scalar])

lemma metricBeltramiCoefficient_uniform_bound
    {g : (ℝ × ℝ) → PlanarMetric} (hg : ContDiff ℝ ∞ g)
    (hPD : ∀ x, (g x).PosDef) {R : ℝ} (hR : 0 < R)
    (hfar : ∀ x ∉ Metric.closedBall 0 R, ∃ r : ℝ, g x = r • 1) :
    ∃ k : ℝ≥0, k < 1 ∧ ∀ x, ‖metricBeltramiCoefficient (g x)‖ ≤ k := by
  have hc := (contDiff_metricBeltramiCoefficient hg hPD).continuous.norm
  have hne : (Metric.closedBall (0 : ℝ × ℝ) R).Nonempty :=
    ⟨0, Metric.mem_closedBall_self hR.le⟩
  obtain ⟨a, ha, hmax⟩ := (isCompact_closedBall (0 : ℝ × ℝ) R).exists_isMaxOn
    hne hc.continuousOn
  let k : ℝ≥0 := ⟨(‖metricBeltramiCoefficient (g a)‖ + 1) / 2, by positivity⟩
  have hlt := metricBeltramiCoefficient_norm_lt_one (hPD a)
  refine ⟨k, ?_, ?_⟩
  · change (‖metricBeltramiCoefficient (g a)‖ + 1) / 2 < (1 : ℝ)
    linarith
  · intro x
    change ‖metricBeltramiCoefficient (g x)‖ ≤
      (‖metricBeltramiCoefficient (g a)‖ + 1) / 2
    by_cases hx : x ∈ Metric.closedBall 0 R
    · have hb : ‖metricBeltramiCoefficient (g x)‖ ≤
          ‖metricBeltramiCoefficient (g a)‖ := hmax hx
      linarith
    · obtain ⟨r, hr⟩ := hfar x hx
      simp only [hr, metricBeltramiCoefficient_scalar, norm_zero]
      positivity

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_MetricBeltramiReconstruction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.blendMetric_identity _root_.OAI.CircleDomainRigidity.FiniteTransfer.covectorEnergy_identity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The metric is recovered exactly, including its positive scale, from
its bounded complex coefficient. -/
open Matrix
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma metricBeltramiCoefficient_reconstruction {A : PlanarMetric} (hA : A.PosDef) :
    let μ := metricBeltramiCoefficient A
    let d := metricBeltramiDenominator A
    A 0 0 = (d / 4) * ((1 + μ.re)^2 + μ.im^2) ∧
    A 1 1 = (d / 4) * ((1 - μ.re)^2 + μ.im^2) ∧
    A 0 1 = (d / 2) * μ.im := by
  have hsym : A 1 0 = A 0 1 := by
    have h := congrFun (congrFun hA.isHermitian.eq (0 : Fin 2)) (1 : Fin 2)
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have hdet : A.det = A 0 0 * A 1 1 - (A 0 1)^2 := by
    rw [Matrix.det_fin_two, hsym]
    ring
  have hd := metricBeltramiDenominator_pos hA
  have hs : (Real.sqrt A.det)^2 = A 0 0 * A 1 1 - (A 0 1)^2 := by
    rw [Real.sq_sqrt hA.det_pos.le, hdet]
  have hr : (metricBeltramiCoefficient A).re =
      (A 0 0 - A 1 1) / metricBeltramiDenominator A := by
    simp only [metricBeltramiCoefficient, Complex.div_ofReal_re]
  have hi : (metricBeltramiCoefficient A).im =
      (2 * A 0 1) / metricBeltramiDenominator A := by
    simp only [metricBeltramiCoefficient, Complex.div_ofReal_im]
  dsimp only
  rw [hr, hi]
  constructor
  · field_simp [hd.ne']
    dsimp [metricBeltramiDenominator]
    nlinarith only [hs]
  constructor
  · field_simp [hd.ne']
    dsimp [metricBeltramiDenominator]
    nlinarith only [hs]
  · field_simp [hd.ne']

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_MetricBeltramiLinear
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.blendMetric_identity _root_.OAI.CircleDomainRigidity.FiniteTransfer.covectorEnergy_identity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact positive metric-conformality equations for a real differential
solving the associated complex Beltrami equation. -/
open Matrix
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma metric_gram_of_beltrami_linear {A : PlanarMetric} (hA : A.PosDef)
    (L : ℂ →L[ℝ] ℂ) (a : ℂ) (ha : a ≠ 0)
    (hL : ∀ z, L z = a * z + (metricBeltramiCoefficient A * a) * star z) :
    ∃ scale : ℝ, 0 < scale ∧
      (L 1).re^2 + (L 1).im^2 = scale * A 0 0 ∧
      (L Complex.I).re^2 + (L Complex.I).im^2 = scale * A 1 1 ∧
      (L 1).re * (L Complex.I).re + (L 1).im * (L Complex.I).im = scale * A 0 1 ∧
      0 < (L 1).re * (L Complex.I).im - (L Complex.I).re * (L 1).im := by
  let μ := metricBeltramiCoefficient A
  have h1 : L 1 = a * (1 + μ) := by rw [hL]; dsimp [μ] <;> simp <;> ring
  have hI : L Complex.I = a * (1 - μ) * Complex.I := by
    rw [hL]
    dsimp [μ]
    simp only [Complex.conj_I]
    ring
  have hxx : (L 1).re^2 + (L 1).im^2 =
      ‖a‖^2 * ((1 + μ.re)^2 + μ.im^2) := by
    rw [h1, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_add]
    ring
  have hyy : (L Complex.I).re^2 + (L Complex.I).im^2 =
      ‖a‖^2 * ((1 - μ.re)^2 + μ.im^2) := by
    rw [hI, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im]
    ring
  have hxy : (L 1).re * (L Complex.I).re + (L 1).im * (L Complex.I).im =
      ‖a‖^2 * (2 * μ.im) := by
    rw [h1, hI, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    ring
  have hdet : (L 1).re * (L Complex.I).im - (L Complex.I).re * (L 1).im =
      ‖a‖^2 * (1 - ‖μ‖^2) := by
    rw [h1, hI]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    ring
  have hd := metricBeltramiDenominator_pos hA
  have ha2 : 0 < ‖a‖^2 := sq_pos_of_pos (norm_pos_iff.mpr ha)
  have hr := metricBeltramiCoefficient_reconstruction hA
  change A 0 0 = _ ∧ A 1 1 = _ ∧ A 0 1 = _ at hr
  refine ⟨4 * ‖a‖^2 / metricBeltramiDenominator A, div_pos (by positivity) hd, ?_, ?_, ?_, ?_⟩
  · rw [hxx, hr.1]
    field_simp [hd.ne']
    ring
  · rw [hyy, hr.2.1]
    field_simp [hd.ne']
    ring
  · rw [hxy, hr.2.2]
    field_simp [hd.ne']
    ring
  · rw [hdet]
    apply mul_pos ha2
    have hm : ‖μ‖ < 1 := metricBeltramiCoefficient_norm_lt_one hA
    nlinarith [norm_nonneg μ]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_SmoothMetricCoefficient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual compactly supported smooth coefficient of the prescribed
metric, in the complex plane used by the existing Beltrami solver. -/
open Set
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_smooth_metric_coefficient
    (g : (ℝ × ℝ) → PlanarMetric) (hg : ContDiff ℝ ∞ g)
    (hPD : ∀ x, (g x).PosDef)
    (hfar : ∃ R : ℝ, 0 < R ∧ ∀ x ∉ Metric.closedBall 0 R,
      ∃ r : ℝ, g x = r • 1) :
    ∃ μ : SchwartzMap ℂ ℂ, HasCompactSupport (μ : ℂ → ℂ) ∧
      (∀ z, μ z = metricBeltramiCoefficient (g (Complex.equivRealProdCLM z))) ∧
      ∃ k : ℝ≥0, k < 1 ∧ ∀ z, ‖μ z‖ ≤ k := by
  obtain ⟨R, hR, hfar⟩ := hfar
  let u : ℂ → ℂ := fun z => metricBeltramiCoefficient (g (Complex.equivRealProdCLM z))
  have hu : ContDiff ℝ ∞ u :=
    (contDiff_metricBeltramiCoefficient hg hPD).comp Complex.equivRealProdCLM.contDiff
  have hs : HasCompactSupport u :=
    (metricBeltramiCoefficient_compact_support hfar).comp_homeomorph
      Complex.equivRealProdCLM.toHomeomorph
  obtain ⟨k, hk, hbound⟩ := metricBeltramiCoefficient_uniform_bound hg hPD hR hfar
  exact ⟨hs.toSchwartzMap hu, hs, fun _ => rfl, k, hk,
    fun z => hbound (Complex.equivRealProdCLM z)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_SmoothMetricPlaneModel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_self _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.chart_infty_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.finiteCoord_coe _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A principally normalized smooth plane model for the actual metric.
The finite-point metric equations are derived from the constructed coefficient. -/
open Set Filter
open scoped Matrix.Norms.Elementwise Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma sphereLocalMap_onePointCongr_coe (F : ℂ ≃ₜ ℂ) (z : ℂ) :
    sphereLocalMap F.onePointCongr (z : Sphere) = F := by
  funext w
  simp [sphereLocalMap, Homeomorph.onePointCongr_apply, chart, chartSymm, finiteCoord]

lemma smooth_metric_plane_model
    (g : (ℝ × ℝ) → PlanarMetric) (hg : ContDiff ℝ ∞ g)
    (hPD : ∀ z, (g z).PosDef)
    (hfar : ∃ R : ℝ, 0 < R ∧ ∀ z ∉ Metric.closedBall 0 R,
      g z = sphericalMetricFactor z • 1) :
    ∃ F : ℂ ≃ₜ ℂ, ContDiff ℝ ∞ (F : ℂ → ℂ) ∧
      ContDiff ℝ ∞ (F.symm : ℂ → ℂ) ∧
      Tendsto (fun z => F z - z) (Filter.cocompact ℂ) (𝓝 0) ∧
      ∀ z : ℂ, IsMetricConformalAt g F.onePointCongr (z : Sphere) := by
  obtain ⟨μ, hμc, hμ, k, hk, hbound⟩ := exists_smooth_metric_coefficient g hg hPD (by
    obtain ⟨R, hR, hout⟩ := hfar
    exact ⟨R, hR, fun z hz => ⟨sphericalMetricFactor z, hout z hz⟩⟩)
  obtain ⟨F, hF, hlim, he, hn⟩ := CannonBeltrami.smooth_beltrami_homeomorph μ hμc
    k.coe_nonneg (by exact_mod_cast hk) hbound
  have hFi := CannonBeltrami.contDiff_symm_beltrami F hF μ
    (fun z => (hbound z).trans_lt (by exact_mod_cast hk)) he hn
  refine ⟨F, hF, hFi, hlim, ?_⟩
  intro z
  have hL (w : ℂ) : fderiv ℝ (F : ℂ → ℂ) z w =
      CannonBeltrami.partialZ F z * w +
        (metricBeltramiCoefficient (g (Complex.equivRealProdCLM z)) *
          CannonBeltrami.partialZ F z) * star w := by
    rw [CannonBeltrami.fderiv_wirtinger, he, hμ]
  obtain ⟨s, hs, hxx, hyy, hxy, hdet⟩ := metric_gram_of_beltrami_linear
    (hPD (Complex.equivRealProdCLM z)) (fderiv ℝ (F : ℂ → ℂ) z)
    (CannonBeltrami.partialZ F z) (hn z) hL
  have hchart : chart (z : Sphere) (z : Sphere) = z := by
    simp [chart, finiteCoord]
  have hmetric : sphereChartMetric g (z : Sphere) = g (Complex.equivRealProdCLM z) := by
    simp [sphereChartMetric, finiteCoord]
  refine ⟨F.onePointCongr.continuous.continuousAt, ?_, ?_⟩
  · rw [sphereLocalMap_onePointCongr_coe]
    exact hF.differentiable (by simp) _
  · simpa only [sphereLocalMap_onePointCongr_coe, hchart, hmetric] using
      (show ∃ s : ℝ, 0 < s ∧
        (fderiv ℝ (F : ℂ → ℂ) z 1).re^2 + (fderiv ℝ (F : ℂ → ℂ) z 1).im^2 =
          s * g (Complex.equivRealProdCLM z) 0 0 ∧
        (fderiv ℝ (F : ℂ → ℂ) z Complex.I).re^2 +
          (fderiv ℝ (F : ℂ → ℂ) z Complex.I).im^2 = s * g (Complex.equivRealProdCLM z) 1 1 ∧
        (fderiv ℝ (F : ℂ → ℂ) z 1).re * (fderiv ℝ (F : ℂ → ℂ) z Complex.I).re +
          (fderiv ℝ (F : ℂ → ℂ) z 1).im * (fderiv ℝ (F : ℂ → ℂ) z Complex.I).im =
            s * g (Complex.equivRealProdCLM z) 0 1 ∧
        0 < (fderiv ℝ (F : ℂ → ℂ) z 1).re * (fderiv ℝ (F : ℂ → ℂ) z Complex.I).im -
          (fderiv ℝ (F : ℂ → ℂ) z Complex.I).re * (fderiv ℝ (F : ℂ → ℂ) z 1).im from
        ⟨s, hs, hxx, hyy, hxy, hdet⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_SmoothMetricUniformizationProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth compact metric uniformization for the exact application,
constructed from the existing smooth principal Beltrami solution. -/
open Set Filter Function
open scoped Matrix.Norms.Elementwise Topology ContDiff OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma metric_plane_model_exterior_holomorphic
    {g : (ℝ × ℝ) → PlanarMetric} {F : ℂ ≃ₜ ℂ}
    (hmetric : ∀ z : ℂ, IsMetricConformalAt g F.onePointCongr (z : Sphere))
    (hfar : ∃ R : ℝ, 0 < R ∧ ∀ z ∉ Metric.closedBall 0 R,
      g z = sphericalMetricFactor z • 1) :
    ∀ᶠ z in Bornology.cobounded ℂ, DifferentiableAt ℂ (F : ℂ → ℂ) z := by
  obtain ⟨R, _, hR⟩ := hfar
  have hc : IsCompact (Complex.equivRealProdCLM ⁻¹' Metric.closedBall 0 R) :=
    Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  rw [Metric.cobounded_eq_cocompact]
  filter_upwards [hc.compl_mem_cocompact] with z hz
  have hg := hR (Complex.equivRealProdCLM z) hz
  have hm := (hmetric z).isConformalAt
    ⟨sphericalMetricFactor (Complex.equivRealProdCLM z), sphericalMetricFactor_pos _, by
      simpa [sphereChartMetric, finiteCoord] using hg⟩
  obtain ⟨_, d, _, hd⟩ := hm
  have hd' : HasDerivAt (F : ℂ → ℂ) d z := by
    change HasDerivAt (sphereLocalMap F.onePointCongr (z : Sphere)) d
      (chart (z : Sphere) (z : Sphere)) at hd
    simpa only [sphereLocalMap_onePointCongr_coe, chart_coe_self] using hd
  exact hd'.differentiableAt

lemma smoothCompactMetricSphereUniformization_oai : SmoothCompactMetricSphereUniformization := by
  intro g hg hPD hfar
  obtain ⟨F, hF, hFi, hlim, hmetric⟩ := smooth_metric_plane_model g hg hPD hfar
  have hhol := metric_plane_model_exterior_holomorphic hmetric hfar
  have hlim' : Tendsto (fun z => F z - z) (Bornology.cobounded ℂ) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using hlim
  obtain ⟨ha, hd⟩ := principalInversionGerm_analytic_deriv hhol hlim'
  have halocal : AnalyticAt ℂ (sphereLocalMap F.onePointCongr ∞) 0 := by
    rwa [sphereLocalMap_onePointCongr_infty]
  have hdlocal : HasDerivAt (sphereLocalMap F.onePointCongr ∞) 1 0 := by
    rwa [sphereLocalMap_onePointCongr_infty]
  have hfix : F.onePointCongr ∞ = (∞ : Sphere) := rfl
  have hai := analyticAt_inverse_sphereLocalMap_infty F.onePointCongr hfix halocal
    (by rw [hdlocal.deriv]; exact one_ne_zero)
  refine ⟨F.onePointCongr, ?_, ?_, ?_⟩
  · intro p
    cases p using OnePoint.rec with
    | infty =>
      have hconf : IsConformalAt F.onePointCongr OnePoint.infty :=
        ⟨F.onePointCongr.continuous.continuousAt, 1, one_ne_zero,
          by
            convert hdlocal using 1 <;> first | rfl | exact chart_infty_self⟩
      exact hconf.isMetricConformalAt_of_scalar (c := 4)
        (by norm_num) (by simp [sphereChartMetric])
    | coe z => exact hmetric z
  · intro p
    cases p using OnePoint.rec with
    | infty => exact ⟨F.onePointCongr.continuous.continuousAt,
        by simpa only [chart_infty_self] using halocal.contDiffAt.restrict_scalars ℝ⟩
    | coe z =>
      refine ⟨F.onePointCongr.continuous.continuousAt, ?_⟩
      rw [sphereLocalMap_onePointCongr_coe, chart_coe_self]
      exact hF.contDiffAt
  · intro p
    cases p using OnePoint.rec with
    | infty => exact ⟨F.onePointCongr.symm.continuous.continuousAt,
        by simpa only [chart_infty_self] using hai.contDiffAt.restrict_scalars ℝ⟩
    | coe z =>
      refine ⟨F.onePointCongr.symm.continuous.continuousAt, ?_⟩
      change ContDiffAt ℝ (↑(⊤ : ENat)) (sphereLocalMap F.symm.onePointCongr (z : Sphere))
        (chart (z : Sphere) (z : Sphere))
      rw [sphereLocalMap_onePointCongr_coe, chart_coe_self]
      exact hFi.contDiffAt

end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.smoothCompactMetricSphereUniformization_oai := @OAI.CircleDomainRigidity.smoothCompactMetricSphereUniformization_oai
