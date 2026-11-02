-- Prove2me | solution 1 for OAI.CircleDomainRigidity.exists_round_invariant_principal_approximation_with_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T06:06:12.806548+00:00
-- url     : https://prove2.me/submissions/2c3aa008-8d87-4ece-be71-ff11fa308975

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C011
import Theorems.Thm_OAI_CannonBeltrami_smooth_principal_solution
import Theorems.Thm_OAI_CircleDomainRigidity_PrincipalSmoothApproximation_exists_principal_limit_data
import Theorems.Thm_OAI_CircleDomainRigidity_exteriorCoefficientAreaTheorem
import Theorems.Thm_OAI_CircleDomainRigidity_unorientedFiniteCircleGreenFormula

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

lemma reflection_image_closedBall :
    reflection '' ((↑) '' closedBall (0:ℂ) 1 : Set S)=
      (((↑) '' ball (0:ℂ) 1 : Set S))ᶜ := by
  ext p
  constructor
  · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩ hp
    obtain ⟨w,hw,he⟩:=hp
    by_cases hz0 : z=0
    · subst z
      rw [reflection_zero] at he
      exact OnePoint.coe_ne_infty w he
    rw [reflection_coe hz0] at he
    have he' : w=(starRingEnd ℂ z)⁻¹ := OnePoint.coe_injective he
    rw [mem_ball,dist_zero_right,he',norm_inv,Complex.norm_conj] at hw
    rw [mem_closedBall,dist_zero_right] at hz
    have hn : 0<‖z‖ := norm_pos_iff.mpr hz0
    have hi : 1≤‖z‖⁻¹ := (one_le_inv₀ hn).mpr hz
    exact (not_lt_of_ge hi) hw
  · intro hp
    have hq : reflection p∈((↑) '' closedBall (0:ℂ) 1 : Set S) := by
      induction p using OnePoint.rec with
      | infty => rw [reflection_infty]; exact ⟨0,by simp,rfl⟩
      | coe z =>
        have hz : 1≤‖z‖ := by
          by_contra hh
          exact hp ⟨z,by simpa only [mem_ball,dist_zero_right] using lt_of_not_ge hh,rfl⟩
        have hz0 : z≠0 := by intro he; norm_num [he] at hz
        rw [reflection_coe hz0]
        refine ⟨(starRingEnd ℂ z)⁻¹,?_,rfl⟩
        rw [mem_closedBall,dist_zero_right,norm_inv,Complex.norm_conj]
        exact (inv_le_one₀ (norm_pos_iff.mpr hz0)).mpr hz
    exact ⟨reflection p,hq,reflection_involutive p⟩
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
-- module Solutions.Q146_CD.Cannon_Beltrami_Mollifier
attribute [-instance] _root_.ContinuousMap.measurableSpace
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

lemma mollify_zero {μ : ℂ → ℂ} {R : ℝ} (hs : ∀ z, R ≤ ‖z‖ → μ z=0)
    (n : ℕ) {z : ℂ} (hz : R+2 ≤ ‖z‖) : mollify μ n z=0 := by
  by_contra hh
  have hm : z ∈ support (mollify μ n) := hh
  obtain ⟨x,hx,y,hy,hxy⟩ := support_convolution_subset (lsmul ℝ ℝ) hm
  have hxr : ‖x‖ < 2 := by
    rw [(mollifier n).support_normed_eq] at hx
    have hx' : ‖x‖ < 2 / ((n : ℝ)+1) := by simpa only [mem_ball,dist_zero_right,mollifier] using hx
    exact hx'.trans_le ((div_le_iff₀ (by positivity)).mpr (by nlinarith [Nat.cast_nonneg (α:=ℝ) n]))
  have hyr : ‖y‖ < R := by
    by_contra hy'
    exact hy (hs y (le_of_not_gt hy'))
  have htri := norm_add_le x y
  change x+y=z at hxy
  rw [hxy] at htri
  linarith

lemma mollify_compact {μ : ℂ → ℂ} {R : ℝ} (hs : ∀ z, R ≤ ‖z‖ → μ z=0) (n : ℕ) :
    HasCompactSupport (mollify μ n) := by
  apply (isCompact_closedBall (0 : ℂ) (R+2)).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  have hn : ‖z‖ < R+2 := by
    by_contra hh
    exact hz (mollify_zero hs n (le_of_not_gt hh))
  simpa only [mem_closedBall,dist_zero_right] using hn.le

lemma mollify_ae_tendsto {μ : ℂ → ℂ} (hm : LocallyIntegrable μ volume) :
    ∀ᵐ z ∂volume, Tendsto (fun n => mollify μ n z) atTop (𝓝 (μ z)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (K:=2) _ _ hm
  · have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2:ℝ)
    simpa [mollifier,div_eq_mul_inv] using h
  · exact .of_forall (fun n => by dsimp [mollifier]; ring_nf; exact le_refl _)

theorem exists_smooth_coefficient_approximation {μ : ℂ → ℂ}
    (hm : AEStronglyMeasurable μ volume) {k R : ℝ} (hk : 0 ≤ k)
    (hb : ∀ z, ‖μ z‖ ≤ k) (hs : ∀ z, R ≤ ‖z‖ → μ z=0) :
    ∃ ν : ℕ → SchwartzMap ℂ ℂ,
      (∀ n, HasCompactSupport (ν n : ℂ → ℂ)) ∧
      (∀ n z, ‖ν n z‖ ≤ k) ∧
      (∀ n z, R+2 ≤ ‖z‖ → ν n z=0) ∧
      (∀ᵐ z ∂volume, Tendsto (fun n => ν n z) atTop (𝓝 (μ z))) := by
  let ν (n : ℕ) := (mollify_compact hs n).toSchwartzMap
    (mollify_smooth (locallyIntegrable_bounded hm hk hb) n)
  exact ⟨ν,fun n => mollify_compact hs n,mollify_bound hm hk hb,
    fun n z hz => mollify_zero hs n hz,mollify_ae_tendsto (locallyIntegrable_bounded hm hk hb)⟩

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
-- module Solutions.Q146_CD.CircleDomains_Modulus_SphericalChartCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square-integrable planar derivatives give the finite spherical
weights used by each local tag payment measure. The inverse chart is
Borel, including its arbitrary value at infinity. -/

open Set Function MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_7
theorem measurable_finiteCoord : Measurable finiteCoord := by
  classical
  obtain ⟨j, hj, he⟩ := OnePoint.isOpenEmbedding_coe.measurableEmbedding.exists_measurable_extend
    (measurable_id (α := ℂ)) (fun _ => inferInstance)
  have hfun : ({OnePoint.infty} : Set Sphere).piecewise (fun _ => (0 : ℂ)) j = finiteCoord := by
    funext p
    cases p using OnePoint.rec with
    | infty => simp [finiteCoord]
    | coe z =>
      simpa only [mem_singleton_iff, OnePoint.coe_ne_infty, not_false_eq_true, piecewise_eq_of_notMem,
        finiteCoord_coe, comp_apply, id_eq] using congrFun he z
  rw [← hfun]
  exact measurable_const.piecewise (measurableSet_singleton _) hj

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PrincipalDensityStability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong L2 stability of the actual principal density under uniformly
bounded almost-everywhere coefficient approximation. -/
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma schwartz_principal_density_equation (μ h : SchwartzMap ℂ ℂ)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ z, ‖μ z‖ ≤ k)
    (he : ∀ z, h z-μ z*smoothBeurling h z=μ z) :
    h.toLp 2 (μ:=volume)-multiplier μ μ.continuous.aestronglyMeasurable hk
      (.of_forall hb) (beurling (h.toLp 2 (μ:=volume)))=μ.toLp 2 (μ:=volume) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (h.toLp 2 (μ:=volume))
    (multiplier μ μ.continuous.aestronglyMeasurable hk (.of_forall hb)
      (beurling (h.toLp 2 (μ:=volume)))),
    multiplier_ae μ μ.continuous.aestronglyMeasurable hk (.of_forall hb)
      (beurling (h.toLp 2 (μ:=volume))),
    h.coeFn_toLp 2 volume, μ.coeFn_toLp 2 volume,
    (schwartz_smoothL2 h).beurling.representative_ae] with z h1 h2 h3 h4 h5
  simp only [Pi.sub_apply] at h1
  rw [h1,h2,h3,h4,h5]
  exact he z

lemma principal_density_strong_convergence
    (μ : ℂ → ℂ) (ν : ℕ → ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume)
    (hn : ∀ n, AEStronglyMeasurable (ν n) volume)
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k)
    (hc : ∀ n, ∀ᵐ z ∂volume, ‖ν n z‖ ≤ k)
    (ht : ∀ᵐ z ∂volume, Tendsto (fun n => ν n z) atTop (𝓝 (μ z)))
    (g b : PlaneL2) (gₙ bₙ : ℕ → PlaneL2)
    (he : g-multiplier μ hm hk hb (beurling g)=b)
    (heₙ : ∀ n, gₙ n-multiplier (ν n) (hn n) hk (hc n) (beurling (gₙ n))=bₙ n)
    (hlim : Tendsto bₙ atTop (𝓝 b)) : Tendsto gₙ atTop (𝓝 g) := by
  have hmul := multiplier_strong_convergence_filter ν μ hn hm hk hc hb ht (beurling g)
  have hbn := (tendsto_iff_norm_sub_tendsto_zero.mp hlim)
  have hmn := (tendsto_iff_norm_sub_tendsto_zero.mp hmul)
  have hmajor := (hbn.add hmn).div_const (1-k)
  simp only [zero_add, zero_div] at hmajor
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hmajor
  exact beltrami_solution_difference μ (ν n) hm (hn n) hk hk1 hb (hc n)
    g (gₙ n) b (bₙ n) he (heₙ n)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_ReflectionTiles
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint reflected copies of the exterior of finitely many disjoint caps.
Only the elementary side swapping and involution of each reflection are used. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

variable {X I : Type*} [TopologicalSpace X]

lemma reflectionTile_cons (R : I → X ≃ₜ X) (K : I → Set X) (i : I) (w : List I) :
    reflectionTile R K (i::w)=R i '' reflectionTile R K w := by
  change ((R i) ∘ reflectionWord R w) '' (⋃j,K j)ᶜ=_
  rw [image_comp]
  rfl

lemma reflectionTile_cons_subset (R : I → X ≃ₜ X) (K U : I → Set X)
    (hUK : ∀i,U i⊆K i) (hd : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hr : ∀i,R i '' (K i)ᶜ⊆U i) (i : I) (w : List I)
    (hw : (i::w).IsChain (·≠·)) : reflectionTile R K (i::w)⊆U i := by
  induction w generalizing i with
  | nil =>
    rw [reflectionTile_cons,reflectionTile_nil]
    exact (image_mono (compl_subset_compl.mpr (subset_iUnion K i))).trans (hr i)
  | cons j w ih =>
    obtain ⟨hij,ht⟩ := List.isChain_cons_cons.mp hw
    rw [reflectionTile_cons]
    apply Subset.trans (image_mono ?_) (hr i)
    intro x hx hxi
    exact Set.disjoint_left.mp (hd hij) hxi (hUK j (ih j ht hx))

lemma reflectionTiles_pairwise_disjoint (R : I → X ≃ₜ X) (K U : I → Set X)
    (hUK : ∀i,U i⊆K i) (hd : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hr : ∀i,R i '' (K i)ᶜ⊆U i) :
    Pairwise (fun w v : {w : List I // w.IsChain (·≠·)} =>
      Disjoint (reflectionTile R K w.val) (reflectionTile R K v.val)) := by
  classical
  have hbase (i : I) : Disjoint ((⋃j,K j)ᶜ) (U i) := by
    apply Set.disjoint_left.mpr
    intro x hx hi
    exact hx (mem_iUnion.mpr ⟨i,hUK i hi⟩)
  have haux (w : List I) : ∀v : List I,w.IsChain (·≠·) → v.IsChain (·≠·) → w≠v →
      Disjoint (reflectionTile R K w) (reflectionTile R K v) := by
    induction w with
    | nil =>
      intro v _ hv hne
      cases v with
      | nil => exact (hne rfl).elim
      | cons j v =>
        rw [reflectionTile_nil]
        exact (hbase j).mono_right (reflectionTile_cons_subset R K U hUK hd hr j v hv)
    | cons i w ih =>
      intro v hw hv hne
      cases v with
      | nil =>
        rw [reflectionTile_nil]
        exact ((hbase i).mono_right (reflectionTile_cons_subset R K U hUK hd hr i w hw)).symm
      | cons j v =>
        by_cases hij : i=j
        · subst j
          have hn : w≠v := fun he => hne (congrArg (List.cons i) he)
          have hdis := ih v (List.isChain_cons.mp hw).2 (List.isChain_cons.mp hv).2 hn
          rw [reflectionTile_cons,reflectionTile_cons]
          apply Set.disjoint_left.mpr
          rintro y ⟨a,ha,rfl⟩ ⟨b,hb,he⟩
          have hba := (R i).injective he
          exact Set.disjoint_left.mp hdis ha (hba ▸ hb)
        · exact (hd hij).mono
            ((reflectionTile_cons_subset R K U hUK hd hr i w hw).trans (hUK i))
            ((reflectionTile_cons_subset R K U hUK hd hr j v hv).trans (hUK j))
  intro w v hne
  exact haux w.val v.val w.property v.property (fun he => hne (Subtype.ext he))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_ReflectionTileAction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact action of a generating reflection on reduced words and their
geometric tiles, including cancellation of the leading generator. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity
variable {X I : Type*} [TopologicalSpace X] [DecidableEq I]

lemma reflectionReduceStep_isChain (i : I) (w : List I) (hw : w.IsChain (·≠·)) :
    (reflectionReduceStep i w).IsChain (·≠·) := by
  cases w with
  | nil => simp [reflectionReduceStep]
  | cons j w =>
    by_cases hij : i=j
    · simpa only [reflectionReduceStep,ite_eq_left hij] using (List.isChain_cons.mp hw).2
    · simpa only [reflectionReduceStep,ite_eq_right hij,List.isChain_cons_cons] using And.intro hij hw

lemma reflectionWord_reduceStep (R : I → X ≃ₜ X) (hR : ∀i,Involutive (R i))
    (i : I) (w : List I) (x : X) :
    reflectionWord R (reflectionReduceStep i w) x=R i (reflectionWord R w x) := by
  cases w with
  | nil => rfl
  | cons j w =>
    by_cases hij : i=j
    · subst j
      simp only [reflectionReduceStep,ite_true, if_true,reflectionWord,Homeomorph.trans_apply]
      exact (hR i _).symm
    · simp only [reflectionReduceStep,ite_eq_right hij,reflectionWord,Homeomorph.trans_apply]

lemma reflectionTile_reduceStep (R : I → X ≃ₜ X) (hR : ∀i,Involutive (R i))
    (K : I → Set X) (i : I) (w : List I) :
    reflectionTile R K (reflectionReduceStep i w)=R i '' reflectionTile R K w := by
  unfold reflectionTile
  rw [image_image]
  exact image_congr (fun x _ => reflectionWord_reduceStep R hR i w x)

lemma reflection_tiles_union_invariant (R : I → X ≃ₜ X) (hR : ∀i,Involutive (R i))
    (K : I → Set X) (i : I) :
    R i '' (⋃w : {w : List I // w.IsChain (·≠·)},reflectionTile R K w.val)=
      ⋃w : {w : List I // w.IsChain (·≠·)},reflectionTile R K w.val := by
  apply Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨w,hw⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨⟨reflectionReduceStep i w.val,reflectionReduceStep_isChain i w.val w.property⟩,?_⟩
    rw [reflectionTile_reduceStep R hR]
    exact mem_image_of_mem (R i) hw
  · intro x hx
    obtain ⟨w,hw⟩ := mem_iUnion.mp hx
    refine ⟨R i x,?_,hR i x⟩
    refine mem_iUnion.mpr ⟨⟨reflectionReduceStep i w.val,reflectionReduceStep_isChain i w.val w.property⟩,?_⟩
    rw [reflectionTile_reduceStep R hR]
    exact mem_image_of_mem (R i) hw

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_ReflectionCoefficientWords
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficient transport through reduced reflection words. The pointwise
involution is proved before gluing the disjoint geometric copies. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity
variable {X I : Type*} [TopologicalSpace X]

lemma reflectionCoefficientWord_bound (R : I → X ≃ₜ X) (V : I → X → ℂ → ℂ)
    (hV : ∀i x a,‖V i x a‖=‖a‖) (f : X → ℂ) {k : ℝ}
    (hf : ∀x,‖f x‖≤k) (w : List I) :
    ∀x,‖reflectionCoefficientWord R V w f x‖≤k := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
    intro x
    change ‖V i x (reflectionCoefficientWord R V w f (R i x))‖≤k
    rw [hV]
    exact ih _

lemma reflectionCoefficientWord_measurable [MeasurableSpace X] [BorelSpace X]
    (R : I → X ≃ₜ X) (V : I → X → ℂ → ℂ)
    (hV : ∀i,Measurable (fun p : X × ℂ => V i p.1 p.2))
    (f : X → ℂ) (hf : Measurable f) (w : List I) :
    Measurable (reflectionCoefficientWord R V w f) := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
    exact (hV i).comp (measurable_id.prodMk (ih.comp (R i).continuous.measurable))

lemma reflectionCoefficientWord_reduceStep [DecidableEq I]
    (R : I → X ≃ₜ X) (hR : ∀i,Involutive (R i)) (V : I → X → ℂ → ℂ)
    (hV : ∀i x a,V i x (V i (R i x) a)=a) (f : X → ℂ) (i : I) (w : List I) (x : X) :
    reflectionCoefficientWord R V (reflectionReduceStep i w) f x=
      V i x (reflectionCoefficientWord R V w f (R i x)) := by
  cases w with
  | nil => rfl
  | cons j w =>
    by_cases hij : i=j
    · subst j
      simp only [reflectionReduceStep,ite_true, if_true,reflectionCoefficientWord]
      rw [hR i]
      exact (hV i x _).symm
    · simp only [reflectionReduceStep,ite_eq_right hij,reflectionCoefficientWord]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_ReflectionCoefficientExtension
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded measurable coefficient on the base exterior extends over all
reflected tiles. The extension is zero on the residual set and satisfies
every generating reflection identity. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity
variable {X I : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [Countable I] [DecidableEq I]

lemma exists_reflection_coefficient_extension
    (R : I → X ≃ₜ X) (hR : ∀i,Involutive (R i)) (K U : I → Set X)
    (hUK : ∀i,U i⊆K i) (hd : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hr : ∀i,R i '' (K i)ᶜ⊆U i)
    (htm : ∀w : List I,MeasurableSet (reflectionTile R K w))
    (V : I → X → ℂ → ℂ)
    (hVinv : ∀i x a,V i x (V i (R i x) a)=a)
    (hVzero : ∀i x,V i x 0=0) (hVnorm : ∀i x a,‖V i x a‖=‖a‖)
    (hVm : ∀i,Measurable (fun p : X × ℂ => V i p.1 p.2))
    (f : X → ℂ) (hf : Measurable f) {k : ℝ} (hk : 0≤k) (hb : ∀x,‖f x‖≤k) :
    ∃ E : X → ℂ,Measurable E ∧ (∀x,‖E x‖≤k) ∧
      EqOn E f (⋃i,K i)ᶜ ∧
      (∀x,x∉⋃w : {w : List I // w.IsChain (·≠·)},reflectionTile R K w.val → E x=0) ∧
      ∀i x,E x=V i x (E (R i x)) := by
  classical
  let W := {w : List I // w.IsChain (·≠·)}
  let B := ⋃w : W,reflectionTile R K w.val
  let T : Option W → Set X := fun a => match a with
    | none => Bᶜ
    | some w => reflectionTile R K w.val
  let g : Option W → X → ℂ := fun a => match a with
    | none => fun _ => 0
    | some w => reflectionCoefficientWord R V w.val f
  have hTm : ∀a,MeasurableSet (T a) := by
    intro a
    cases a with
    | none => exact (MeasurableSet.iUnion (fun w : W => htm w.val)).compl
    | some w => exact htm w.val
  have hgm : ∀a,Measurable (g a) := by
    intro a
    cases a with
    | none => exact measurable_const
    | some w => exact reflectionCoefficientWord_measurable R V hVm f hf w.val
  have hTd : Pairwise (fun a b => Disjoint (T a) (T b)) := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => exact (hab rfl).elim
      | some w =>
        apply Set.disjoint_left.mpr
        intro x hx hxw
        exact hx (mem_iUnion.mpr ⟨w,hxw⟩)
    | some w =>
      cases b with
      | none =>
        apply Set.disjoint_left.mpr
        intro x hxw hx
        exact hx (mem_iUnion.mpr ⟨w,hxw⟩)
      | some v =>
        exact reflectionTiles_pairwise_disjoint R K U hUK hd hr
          (fun he => hab (congrArg some he))
  obtain ⟨E,hEm,hE⟩ := exists_measurable_piecewise T hTm g hgm (by
    intro a b hab x hx
    exact (Set.disjoint_left.mp (hTd hab) hx.1 hx.2).elim)
  have hEoff (x : X) (hx : x∉B) : E x=0 := hE none hx
  have hEtile (w : W) {x : X} (hx : x∈reflectionTile R K w.val) :
      E x=reflectionCoefficientWord R V w.val f x := hE (some w) hx
  refine ⟨E,hEm,?_,?_,hEoff,?_⟩
  · intro x
    by_cases hx : x∈B
    · obtain ⟨w,hw⟩ := mem_iUnion.mp hx
      rw [hEtile w hw]
      exact reflectionCoefficientWord_bound R V hVnorm f hb w.val x
    · rw [hEoff x hx,norm_zero]
      exact hk
  · intro x hx
    let w : W := ⟨[],by simp⟩
    exact hEtile w (by simpa only [w,reflectionTile_nil] using hx)
  · intro i x
    by_cases hx : x∈B
    · obtain ⟨w,hw⟩ := mem_iUnion.mp hx
      let v : W := ⟨reflectionReduceStep i w.val,reflectionReduceStep_isChain i w.val w.property⟩
      have hv : R i x∈reflectionTile R K v.val := by
        rw [show v.val=reflectionReduceStep i w.val from rfl,reflectionTile_reduceStep R hR]
        exact mem_image_of_mem (R i) hw
      rw [hEtile w hw,hEtile v hv]
      change reflectionCoefficientWord R V w.val f x=
        V i x (reflectionCoefficientWord R V (reflectionReduceStep i w.val) f (R i x))
      rw [reflectionCoefficientWord_reduceStep R hR V hVinv,hR i]
      exact (hVinv i x _).symm
    · have hy : R i x∉B := by
        intro hy
        have hm := mem_image_of_mem (R i) hy
        rw [reflection_tiles_union_invariant R hR K i] at hm
        rw [hR i] at hm
        exact hx hm
      rw [hEoff x hx,hEoff (R i x) hy,hVzero]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ExteriorDiskNormalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit Möbius normalization of a finite circular exterior to the
unit disk. This converts the actual circularization maps to the target
used by the boundary-continuation argument. -/
open Set Function Filter Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity

lemma affineSphere_image_unit_closedBall (c : ℂ) {r : ℝ} (hr : 0 < r) :
    affineSphere (r:ℂ) c (by exact_mod_cast hr.ne') ''
      (((↑) : ℂ → Sphere) '' closedBall 0 1) =
      ((↑) : ℂ → Sphere) '' closedBall c r := by
  rw [closedBall_eq_affine_image hr.le c,image_image,image_image]
  congr 1
  funext z
  rw [affineSphere_coe]
  congr 1
  simp only [Complex.real_smul,mul_comm,add_comm]

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

lemma affineSphere_image_unit_ball (c : ℂ) {r : ℝ} (hr : 0 < r) :
    affineSphere (r:ℂ) c (by exact_mod_cast hr.ne') ''
      (((↑) : ℂ → Sphere) '' ball 0 1)=((↑) : ℂ → Sphere) '' ball c r := by
  have hb : ball c r=(fun z : ℂ => c+r • z) '' ball 0 1 := by
    rw [←affinity_unitBall hr c]
    change (fun z : ℂ => c+z) '' ((fun z : ℂ => r • z) '' ball 0 1)=_
    rw [image_image]
  rw [hb,image_image,image_image]
  congr 1
  funext z
  rw [affineSphere_coe]
  congr 1
  simp only [Complex.real_smul,mul_comm,add_comm]

lemma roundDiskReflection_closed_image (c : ℂ) {r : ℝ} (hr : 0 < r) :
    roundDiskReflection c r hr '' (((↑) : ℂ → Sphere) '' closedBall c r)=
      (((↑) : ℂ → Sphere) '' ball c r)ᶜ := by
  let A := affineSphere (r:ℂ) c (by exact_mod_cast hr.ne')
  have hc : A '' (((↑) : ℂ → Sphere) '' closedBall 0 1)=
      ((↑) : ℂ → Sphere) '' closedBall c r := affineSphere_image_unit_closedBall c hr
  have ho : A '' (((↑) : ℂ → Sphere) '' ball 0 1)=
      ((↑) : ℂ → Sphere) '' ball c r := affineSphere_image_unit_ball c hr
  have hai : A.symm '' (((↑) : ℂ → Sphere) '' closedBall c r)=
      ((↑) : ℂ → Sphere) '' closedBall 0 1 := by
    rw [←hc,image_image]
    simp only [A.symm_apply_apply,image_id']
  calc
    _ = A '' (CannonSphereReflection.reflection ''
        (A.symm '' (((↑) : ℂ → Sphere) '' closedBall c r))) := by
      simp only [image_image]
      rfl
    _ = _ := by rw [hai,CannonSphereReflection.reflection_image_closedBall,A.image_compl,ho]

lemma roundDiskReflection_outer_image (c : ℂ) {r : ℝ} (hr : 0 < r) :
    roundDiskReflection c r hr '' ((((↑) : ℂ → Sphere) '' closedBall c r)ᶜ)=
      ((↑) : ℂ → Sphere) '' ball c r := by
  rw [(roundDiskReflection c r hr).image_compl,roundDiskReflection_closed_image c hr,compl_compl]

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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
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

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_8
lemma sphereCoefficient_measurable (a : ℂ) {f : ℂ → ℂ} (hf : Measurable f) :
    Measurable (sphereCoefficient a f) := by
  classical
  have he : sphereCoefficient a f=({∞} : Set Sphere).piecewise (fun _ => a) (f ∘ finiteCoord) := by
    funext p
    induction p using OnePoint.rec with
    | infty => simp [sphereCoefficient]
    | coe z => simp [sphereCoefficient,OnePoint.coe_ne_infty]
  rw [he]
  exact measurable_const.piecewise (measurableSet_singleton _) (hf.comp measurable_finiteCoord)

lemma circleReflectionPhase_norm (c z : ℂ) : ‖circleReflectionPhase c z‖=1 := by
  classical
  by_cases hz : z=c
  · simp [circleReflectionPhase,hz]
  · simp only [circleReflectionPhase,ite_eq_right hz,norm_pow,norm_div,Complex.norm_conj,
      div_self (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)),one_pow]

lemma sphereReflectionPhase_norm (c : ℂ) (p : Sphere) : ‖sphereReflectionPhase c p‖=1 := by
  induction p using OnePoint.rec with
  | infty => exact norm_one (α := ℂ)
  | coe z => exact circleReflectionPhase_norm c z

lemma circleReflectionPhase_measurable (c : ℂ) : Measurable (circleReflectionPhase c) := by
  classical
  apply Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
  exact ((measurable_id.sub_const c).div (Complex.continuous_conj.measurable.comp (measurable_id.sub_const c))).pow_const 2

lemma sphereReflectionPhase_measurable (c : ℂ) : Measurable (sphereReflectionPhase c) :=
  sphereCoefficient_measurable 1 (circleReflectionPhase_measurable c)

lemma sphereReflectionPhase_reflection (c : ℂ) {r : ℝ} (hr : 0 < r) (p : Sphere) :
    sphereReflectionPhase c (roundDiskReflection c r hr p)=sphereReflectionPhase c p := by
  classical
  induction p using OnePoint.rec with
  | infty => simp [roundDiskReflection_infty,sphereReflectionPhase,circleReflectionPhase]
  | coe z =>
    by_cases hz : z=c
    · subst z
      simp [roundDiskReflection_center,sphereReflectionPhase,circleReflectionPhase]
    · rw [roundDiskReflection_coe c hr hz]
      have hn : c+(r:ℂ)^2/(starRingEnd ℂ (z-c))≠c := by
        have hrC : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
        intro hh
        have he : (r:ℂ)^2/(starRingEnd ℂ (z-c))=0 := by linear_combination hh
        exact (div_ne_zero (pow_ne_zero 2 hrC) (map_ne_zero (starRingEnd ℂ) |>.mpr (sub_ne_zero.mpr hz))) he
      simp only [sphereReflectionPhase,sphereCoefficient_coe,circleReflectionPhase,ite_eq_right hz,
        ite_eq_right hn,add_sub_cancel_left,map_div₀,map_pow,Complex.conj_ofReal,Complex.conj_conj]
      have hrC : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
      field_simp [hrC,sub_ne_zero.mpr hz]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_RoundReflectionCoefficient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual norm-preserving coefficient transport for circular reflection. -/
open Set Function MeasureTheory
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_9
lemma roundReflectionCoefficient_zero (c : ℂ) (p : Sphere) :
    roundReflectionCoefficient c p 0=0 := by simp [roundReflectionCoefficient]

lemma roundReflectionCoefficient_norm (c : ℂ) (p : Sphere) (a : ℂ) :
    ‖roundReflectionCoefficient c p a‖=‖a‖ := by
  rw [roundReflectionCoefficient,norm_mul,sphereReflectionPhase_norm,one_mul,Complex.norm_conj]

lemma roundReflectionCoefficient_measurable (c : ℂ) :
    Measurable (fun p : Sphere × ℂ => roundReflectionCoefficient c p.1 p.2) :=
  ((sphereReflectionPhase_measurable c).comp measurable_fst).mul (Complex.continuous_conj.measurable.comp measurable_snd)

lemma roundReflectionCoefficient_involutive (c : ℂ) {r : ℝ} (hr : 0 < r)
    (p : Sphere) (a : ℂ) :
    roundReflectionCoefficient c p
      (roundReflectionCoefficient c (roundDiskReflection c r hr p) a)=a := by
  simp only [roundReflectionCoefficient,map_mul,sphereReflectionPhase_reflection,Complex.conj_conj]
  have hphase : sphereReflectionPhase c p * starRingEnd ℂ (sphereReflectionPhase c p)=1 := by
    rw [Complex.mul_conj]
    simp only [Complex.normSq_eq_norm_sq,sphereReflectionPhase_norm,one_pow,Complex.ofReal_one]
  rw [←mul_assoc,hphase,one_mul]

lemma exists_round_reflection_coefficient {I : Type*} [Finite I]
    (c : I → ℂ) (r : I → ℝ) (hr : ∀i,0 < r i)
    (hd : Pairwise (fun i j => Disjoint
      (((↑) : ℂ → Sphere) '' Metric.closedBall (c i) (r i))
      (((↑) : ℂ → Sphere) '' Metric.closedBall (c j) (r j))))
    (f : Sphere → ℂ) (hf : Measurable f) {k : ℝ} (hk : 0≤k) (hb : ∀p,‖f p‖≤k) :
    ∃E : Sphere → ℂ,Measurable E ∧ (∀p,‖E p‖≤k) ∧
      EqOn E f (⋃i,((↑) : ℂ → Sphere) '' Metric.closedBall (c i) (r i))ᶜ ∧
      ∀i p,E p=roundReflectionCoefficient (c i) p
        (E (roundDiskReflection (c i) (r i) (hr i) p)) := by
  classical
  let R := fun i => roundDiskReflection (c i) (r i) (hr i)
  let K := fun i => ((↑) : ℂ → Sphere) '' Metric.closedBall (c i) (r i)
  let U := fun i => ((↑) : ℂ → Sphere) '' Metric.ball (c i) (r i)
  have hK : ∀i,IsClosed (K i) := fun i =>
    ((isCompact_closedBall (c i) (r i)).image OnePoint.continuous_coe).isClosed
  have hbase : IsOpen (⋃i,K i)ᶜ := (isClosed_iUnion_of_finite hK).isOpen_compl
  have htm : ∀w : List I,MeasurableSet (reflectionTile R K w) := by
    intro w
    exact ((reflectionWord R w).isOpenMap _ hbase).measurableSet
  obtain ⟨E,hEm,hEb,hEf,_hEz,hEinv⟩ := exists_reflection_coefficient_extension R
    (fun i => roundDiskReflection_involutive (c i) (hr i)) K U
    (fun _ => image_mono Metric.ball_subset_closedBall) hd
    (fun i => (roundDiskReflection_outer_image (c i) (hr i)).subset) htm
    (fun i => roundReflectionCoefficient (c i))
    (fun i => roundReflectionCoefficient_involutive (c i) (hr i))
    (fun i => roundReflectionCoefficient_zero (c i))
    (fun i => roundReflectionCoefficient_norm (c i))
    (fun i => roundReflectionCoefficient_measurable (c i)) f hf hk hb
  exact ⟨E,hEm,hEb,hEf,hEinv⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_CompactReflectionCoefficient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reflection-invariant extension remains compactly supported: every
non-base tile lies inside one of the original finitely many disks. -/
open Set Function MeasureTheory Metric Bornology
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_10
lemma exists_compact_reflection_coefficient {I : Type*} [Finite I]
    (c : I → ℂ) (r : I → ℝ) (hr : ∀i,0 < r i)
    (hd : Pairwise (fun i j => Disjoint
      (((↑) : ℂ → Sphere) '' closedBall (c i) (r i))
      (((↑) : ℂ → Sphere) '' closedBall (c j) (r j))))
    (μ : ℂ → ℂ) (hm : Measurable μ) {k R : ℝ}
    (hk : 0≤k) (hb : ∀z,‖μ z‖≤k) (hz : ∀z,R≤‖z‖ → μ z=0) :
    ∃ (E : Sphere → ℂ) (S : ℝ),Measurable E ∧ 0<S ∧ (∀p,‖E p‖≤k) ∧
      (∀z : ℂ,S≤‖z‖ → E (z : Sphere)=0) ∧
      EqOn E (sphereCoefficient 0 μ)
        (⋃i,((↑) : ℂ → Sphere) '' closedBall (c i) (r i))ᶜ ∧
      ∀i p,E p=roundReflectionCoefficient (c i) p
        (E (roundDiskReflection (c i) (r i) (hr i) p)) := by
  have hμb (p : Sphere) : ‖sphereCoefficient 0 μ p‖≤k := by
    induction p using OnePoint.rec with
    | infty => simpa only [sphereCoefficient_infty,norm_zero] using hk
    | coe z => exact hb z
  obtain ⟨E,hEm,hEb,hbase,hEinv⟩ := exists_round_reflection_coefficient c r hr hd
    (sphereCoefficient 0 μ) (sphereCoefficient_measurable 0 hm) hk hμb
  obtain ⟨B,hB,hbound⟩ := (isCompact_iUnion (fun i => isCompact_closedBall (c i) (r i))).isBounded.exists_pos_norm_lt
  let S := max B R
  have hS : 0<S := hB.trans_le (le_max_left B R)
  refine ⟨E,S,hEm,hS,hEb,?_,hbase,hEinv⟩
  intro z hsz
  have hout : (z : Sphere)∉⋃i,((↑) : ℂ → Sphere) '' closedBall (c i) (r i) := by
    intro hz'
    obtain ⟨i,w,hw,he⟩ := mem_iUnion.mp hz'
    have hwz : w=z := OnePoint.coe_injective he
    subst w
    have hlt := hbound z (mem_iUnion.mpr ⟨i,hw⟩)
    exact (not_lt_of_ge ((le_max_left B R).trans hsz)) hlt
  rw [hbase hout,sphereCoefficient_coe,hz z ((le_max_right B R).trans hsz)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_PrincipalCoefficientConvergence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform compact support turns bounded coefficient approximation into
strong L2 convergence. The bound retains the same coefficient radius. -/
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma compact_coefficient_L2_convergence {μ : ℂ → ℂ} {ν : ℕ → ℂ → ℂ}
    {K : Set ℂ} {k : ℝ}
    (hm : AEStronglyMeasurable μ volume)
    (hn : ∀ n, AEStronglyMeasurable (ν n) volume)
    (hK : IsCompact K) (hk : 0 ≤ k)
    (hb : ∀ z, ‖μ z‖ ≤ k) (hc : ∀ n z, ‖ν n z‖ ≤ k)
    (hs : ∀ z ∉ K, μ z = 0) (ht : ∀ n z, z ∉ K → ν n z = 0)
    (hl : ∀ᵐ z ∂volume, Tendsto (fun n => ν n z) atTop (𝓝 (μ z))) :
    Tendsto (fun n => (compact_coefficient_memLp (hn n) hK hk (hc n) (ht n)).toLp (ν n))
      atTop (𝓝 ((compact_coefficient_memLp hm hK hk hb hs).toLp μ)) := by
  let hμ := compact_coefficient_memLp hm hK hk hb hs
  let hν := fun n => compact_coefficient_memLp (hn n) hK hk (hc n) (ht n)
  have hB : MemLp (K.indicator (fun _ : ℂ => ((2*k : ℝ) : ℂ))) 2 volume :=
    memLp_indicator_const 2 hK.measurableSet _ (Or.inr hK.measure_lt_top.ne)
  have hdom : ∀ n, ∀ᵐ z ∂volume,
      ‖(ν n - μ) z‖ ≤ ‖K.indicator (fun _ : ℂ => ((2*k : ℝ) : ℂ)) z‖ := by
    intro n
    filter_upwards [] with z
    by_cases hz : z ∈ K
    · simp only [Pi.sub_apply, indicator_of_mem hz, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ 2*k by linarith)]
      exact (norm_sub_le _ _).trans (by linarith [hc n z, hb z])
    · simp only [Pi.sub_apply, hs z hz, ht n z hz, sub_self, norm_zero,
        indicator_of_notMem hz, le_refl]
  have hzero := dominated_toLp_zero_filter (fun n => (hν n).sub hμ) hB hdom
    (hl.mono (fun z hz => by simpa only [Pi.sub_apply, sub_self] using hz.sub_const (μ z)))
  change Tendsto (fun n => (hν n).toLp (ν n) - hμ.toLp μ) atTop (𝓝 0) at hzero
  simpa only [zero_add, sub_add_cancel] using hzero.add_const (hμ.toLp μ)

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

lemma exists_principal_smooth_approximation_with_coefficient (μ : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) {k R : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1) (hb : ∀ z, ‖μ z‖ ≤ k)
    (hs : ∀ z, R ≤ ‖z‖ → μ z=0) (g : PlaneL2)
    (he : ∀ᵐ z ∂volume, g z=μ z*(1+beurling g z)) :
    ∃ S : PrincipalSmoothApproximation g k R,
      ∀ᵐz ∂volume,Tendsto (fun n => S.coefficient n z) atTop (𝓝 (μ z)) := by
  classical
  obtain ⟨ν, hνc, hνb, hνs, hνlim⟩ := exists_smooth_coefficient_approximation hm hk hb hs
  have hsol (n : ℕ) := smooth_principal_solution (ν n) (hνc n) hk hk1 (hνb n)
  choose h F hhc hF hsm hsmi heq hpart hnorm using hsol
  let K := Metric.closedBall (0 : ℂ) (R+2)
  have hzμ : ∀ z ∉ K, μ z=0 := by
    intro z hz
    apply hs
    have hh : R+2 < ‖z‖ := by simpa only [K, Metric.mem_closedBall, dist_zero_right, not_le] using hz
    linarith
  have hzν : ∀ n z, z ∉ K → ν n z=0 := by
    intro n z hz
    apply hνs n z
    have hh : R+2 < ‖z‖ := by simpa only [K, Metric.mem_closedBall, dist_zero_right, not_le] using hz
    exact hh.le
  let hμ := compact_coefficient_memLp hm (isCompact_closedBall _ _) hk hb hzμ
  have hcoeff : Tendsto (fun n => (ν n).toLp 2 (μ:=volume)) atTop (𝓝 (hμ.toLp μ)) := by
    simpa only [SchwartzMap.toLp] using compact_coefficient_L2_convergence hm
      (fun n => (ν n).continuous.aestronglyMeasurable) (isCompact_closedBall _ _)
      hk hb hνb hzμ hzν hνlim
  have hdens : Tendsto (fun n => (h n).toLp 2 (μ:=volume)) atTop (𝓝 g) := by
    apply principal_density_strong_convergence μ (fun n => (ν n : ℂ → ℂ)) hm
      (fun n => (ν n).continuous.aestronglyMeasurable) hk hk1
      (.of_forall hb) (fun n => .of_forall (hνb n)) hνlim g (hμ.toLp μ)
      (fun n => (h n).toLp 2 (μ:=volume)) (fun n => (ν n).toLp 2 (μ:=volume))
      (density_operator_equation hμ hk (.of_forall hb) g he) _ hcoeff
    intro n
    apply schwartz_principal_density_equation (ν n) (h n) hk (hνb n)
    intro z
    have h1 := heq n z
    rw [(hpart n z).1, (hpart n z).2] at h1
    linear_combination h1
  exact ⟨⟨ν, h, F, hνc, hνb, hνs, hhc, hF, hsm, hsmi, heq, hpart, hdens⟩,hνlim⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_PrincipalComplexBeltrami
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compactly supported complex-coefficient principal solution used in
finite reflection constructions. The L2 density is solved by the actual
Beurling contraction and the homeomorphism is the strong smooth limit. -/
open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma exists_compact_complex_beltrami_density (μ : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) {k R : ℝ}
    (hk : 0≤k) (hk1 : k<1) (hb : ∀z,‖μ z‖≤k)
    (hs : ∀z,R≤‖z‖ → μ z=0) :
    ∃g : PlaneL2, ∀ᵐ z ∂volume,g z=μ z*(1+beurling g z) := by
  let hμ := compact_coefficient_memLp hm (isCompact_closedBall 0 R) hk hb
    (fun z hz => hs z (le_of_lt (by simpa only [mem_closedBall,dist_zero_right,not_le] using hz)))
  obtain ⟨g,he,_,_⟩ := solve_beltrami_l2 μ hm hk hk1 (.of_forall hb) (hμ.toLp μ)
  refine ⟨g,?_⟩
  have hea := Lp.ext_iff.mp he
  filter_upwards [hea,Lp.coeFn_sub g (multiplier μ hm hk (.of_forall hb) (beurling g)),
    multiplier_ae μ hm hk (.of_forall hb) (beurling g),hμ.coeFn_toLp] with z hz hsub hmul hval
  simp only [Pi.sub_apply] at hsub
  rw [hsub,hmul,hval] at hz
  linear_combination hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_PrincipalComplexCoefficientData
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retain the actual smooth coefficient convergence together with the
principal homeomorphism limit. It comes from the same bounded mollification
used in constructing the principal solution. -/
open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma exists_principal_complex_coefficient_data (μ : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) {k R : ℝ}
    (hk : 0≤k) (hk1 : k<1) (hb : ∀z,‖μ z‖≤k)
    (hs : ∀z,R≤‖z‖ → μ z=0) :
    ∃ (g : PlaneL2) (S : PrincipalSmoothApproximation g k R) (_L : PrincipalMapLimit S),
      (∀ᵐz ∂volume,g z=μ z*(1+beurling g z)) ∧
      ∀ᵐz ∂volume,Tendsto (fun n => S.coefficient n z) atTop (𝓝 (μ z)) := by
  obtain ⟨g,he⟩ := exists_compact_complex_beltrami_density μ hm hk hk1 hb hs
  obtain ⟨S,hc⟩ := exists_principal_smooth_approximation_with_coefficient μ hm hk hk1 hb hs g he
  let T := max (R+2) 1
  have hT : 0<T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨L⟩ := S.exists_principal_limit_data
    (exteriorCoefficientAreaTheorem planarSchoenflies unorientedFiniteCircleGreenFormula)
    hk hk1 hT (le_max_left _ _)
  exact ⟨g,S,L,he,hc⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_ReflectionPrincipalSolution
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Solve the actual bounded, compact, reflection-invariant coefficient field.
The original coefficient is retained exactly on the circular exterior. -/
open Set Function Filter MeasureTheory
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami
attribute [local instance] sphereMetric sphereBorel

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_11
lemma exists_round_invariant_principal_approximation_with_coefficient_oai {I : Type*} [Finite I]
    (c : I → ℂ) (r : I → ℝ) (hr : ∀i,0 < r i)
    (hd : Pairwise (fun i j => Disjoint
      (((↑) : ℂ → Sphere) '' Metric.closedBall (c i) (r i))
      (((↑) : ℂ → Sphere) '' Metric.closedBall (c j) (r j))))
    (μ : ℂ → ℂ) (hm : Measurable μ) {k R : ℝ}
    (hk : 0≤k) (hk1 : k<1) (hb : ∀z,‖μ z‖≤k) (hz : ∀z,R≤‖z‖ → μ z=0) :
    ∃ (E : Sphere → ℂ) (T : ℝ) (g : PlaneL2)
      (S : PrincipalSmoothApproximation g k T) (_L : PrincipalMapLimit S),
      Measurable E ∧ (∀z : ℂ,T≤‖z‖ → E (z : Sphere)=0) ∧ (∀p,‖E p‖≤k) ∧
      EqOn E (sphereCoefficient 0 μ)
        (⋃i,((↑) : ℂ → Sphere) '' Metric.closedBall (c i) (r i))ᶜ ∧
      (∀i p,E p=roundReflectionCoefficient (c i) p
        (E (roundDiskReflection (c i) (r i) (hr i) p))) ∧
      (∀ᵐz ∂volume,g z=E (z : Sphere)*(1+beurling g z)) ∧
      ∀ᵐz ∂volume,Tendsto (fun n => S.coefficient n z) atTop (𝓝 (E (z : Sphere))) := by
  obtain ⟨E,T,hEm,hT,hEb,hEz,hEf,hEinv⟩ := exists_compact_reflection_coefficient c r hr hd μ hm hk hb hz
  have hμm : AEStronglyMeasurable (fun z : ℂ => E (z : Sphere)) volume :=
    (hEm.comp OnePoint.continuous_coe.measurable).aestronglyMeasurable
  obtain ⟨g,S,L,he,hc⟩ := exists_principal_complex_coefficient_data (fun z : ℂ => E (z : Sphere))
    hμm hk hk1 (fun z => hEb (z : Sphere)) hEz
  exact ⟨E,T,g,S,L,hEm,hEz,hEb,hEf,hEinv,he,hc⟩

end CircleDomainRigidity

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CircleDomainRigidity.exists_round_invariant_principal_approximation_with_coefficient_oai.{u_1} := @OAI.CircleDomainRigidity.exists_round_invariant_principal_approximation_with_coefficient_oai.{u_1}
