-- Prove2me | solution 1 for OAI.CircleDomainRigidity.PrincipalSmoothApproximation.exists_principal_limit_data
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:38:39.238026+00:00
-- url     : https://prove2.me/submissions/37a16568-9253-4a6e-9a7d-72279c6156b5

import Mathlib
import Definitions.Def_Q146C001
import Definitions.Def_Q146C002

section
-- module Solutions.Q146_CD.Cannon_Beltrami_MultiplyLp
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
-- module Solutions.Q146_CD.Cannon_Beltrami_Axis
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
-- module Solutions.Q146_CD.Cannon_Beltrami_DirichletPullback
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
-- module Solutions.Q146_CD.Cannon_Beltrami_ContinuousMemLpRestrict
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

lemma tendsto_l2_test (f : ℕ → Lp ℂ 2 (volume : Measure ℂ))
    {g : Lp ℂ 2 (volume : Measure ℂ)} (ht : Tendsto f atTop (𝓝 g)) (φ : SchwartzMap ℂ ℂ) :
    Tendsto (fun n => ∫ z, φ z*f n z) atTop (𝓝 (∫ z, φ z*g z)) := by
  have h := ((Lp.toTemperedDistributionCLM ℂ volume 2).continuous.tendsto g).comp ht
  have h' := PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp h φ
  simpa only [Function.comp_def,Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistribution_apply,smul_eq_mul] using h'

lemma integral_test_add_const (f : Lp ℂ 2 (volume : Measure ℂ))
    (φ : SchwartzMap ℂ ℂ) (v : ℂ) :
    (∫ z, (v+f z)*φ z) = v*(∫ z, φ z)+(∫ z, φ z*f z) := by
  have hi : Integrable (fun z => φ z*f z) := (φ.memLp 2 volume).integrable_mul (Lp.memLp f)
  simp_rw [add_mul]
  rw [integral_add (φ.integrable.const_mul v) (by simpa only [mul_comm] using hi),integral_const_mul]
  congr 1
  apply integral_congr_ae
  exact .of_forall (fun z => mul_comm _ _)

lemma bounded_displacement_test_tendsto (F : ℕ → ℂ → ℂ) (G : ℂ → ℂ)
    (hf : ∀ n, Continuous (F n)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n z, ‖F n z-z‖ ≤ C)
    (ht : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (G z)))
    (φ : SchwartzMap ℂ ℂ) (hc : HasCompactSupport (φ : ℂ → ℂ)) (v : ℂ) :
    Tendsto (fun n => ∫ z, F n z*fderiv ℝ (φ : ℂ → ℂ) z v) atTop
      (𝓝 (∫ z, G z*fderiv ℝ (φ : ℂ → ℂ) z v)) := by
  let D : ℂ → ℂ := fun z => fderiv ℝ (φ : ℂ → ℂ) z v
  have hd : Continuous D := (φ.smooth'.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcD : HasCompactSupport D := hc.fderiv_apply ℝ v
  have hdom : Integrable (fun z => (‖z‖+‖C‖)*‖D z‖) :=
    ((continuous_norm.add continuous_const).mul hd.norm).integrable_of_hasCompactSupport
      hcD.norm.mul_left
  apply tendsto_integral_of_dominated_convergence (fun z => (‖z‖+‖C‖)*‖D z‖)
    (fun n => ((hf n).mul hd).aestronglyMeasurable) hdom
  · intro n
    exact .of_forall (fun z => by
      change ‖F n z*D z‖ ≤ _
      rw [norm_mul, Real.norm_of_nonneg hC]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hh := norm_le_norm_add_norm_sub z (F n z)
      rw [norm_sub_rev] at hh
      exact hh.trans (add_le_add le_rfl (hb n z)))
  · exact .of_forall (fun z => (ht z).mul_const (D z))

theorem smooth_limit_weak_derivative (F : ℕ → ℂ → ℂ) (G : ℂ → ℂ)
    (hf : ∀ n, ContDiff ℝ 1 (F n)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n z, ‖F n z-z‖ ≤ C) (ht : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (G z)))
    (v : ℂ) (d : ℕ → Lp ℂ 2 (volume : Measure ℂ)) (a : Lp ℂ 2 (volume : Measure ℂ))
    (hd : ∀ n, ∀ᵐ z ∂volume, fderiv ℝ (F n) z v=v+d n z)
    (hdt : Tendsto d atTop (𝓝 a)) :
    ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, G z*fderiv ℝ (φ : ℂ → ℂ) z v) = -(∫ z, (v+a z)*φ z) := by
  intro φ hc
  have hleft := bounded_displacement_test_tendsto F G (fun n => (hf n).continuous) hC hb ht φ hc v
  have hright : Tendsto (fun n => -(∫ z, (v+d n z)*φ z)) atTop
      (𝓝 (-(∫ z, (v+a z)*φ z))) := by
    simp_rw [integral_test_add_const]
    exact (tendsto_const_nhds.add (tendsto_l2_test d hdt φ)).neg
  apply tendsto_nhds_unique hleft
  apply hright.congr
  intro n
  rw [smooth_integration_by_parts (F n) (hf n) φ hc v]
  congr 1
  apply integral_congr_ae
  filter_upwards [hd n] with z hz
  rw [hz]

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
-- module Solutions.Q146_CD.Cannon_Beltrami_RectCrossing
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
      (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableOn (.of_forall (fun t _ => hb t))
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
    ((hu.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp (continuous_const.prodMk continuous_id)).norm
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
    ((hu.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp (continuous_id.prodMk continuous_const)).norm
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
-- module Solutions.Q146_CD.Cannon_Energy_ClopenNeighborhoodComponent
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
-- module Solutions.Q146_CD.Cannon_Conformal_OpenMapMaxSphere
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

end OAI
end

section
-- module Solutions.Q146_CD.Cannon_Energy_StopInside
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
-- module Solutions.Q146_CD.Cannon_Topology_PlaneBox
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
    ((hu.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp e.continuous).norm.pow 2
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
    (Real.smoothTransition.contDiff (n:=1) |>.continuous_deriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).abs
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
    (contDiffAt_id.norm ℝ hz : ContDiffAt ℝ 1 (fun w : ℂ => ‖w‖) z).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdiv : HasFDerivAt (fun w : ℂ => ‖w‖/r) (r⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) z) z := by
    simpa only [Pi.smul_def,smul_eq_mul,div_eq_mul_inv,mul_comm] using hn.hasFDerivAt.const_smul r⁻¹
  have hlog := (Real.hasDerivAt_log (div_ne_zero hzn.ne' hr.ne')).comp_hasFDerivAt z hdiv
  have hscale : HasFDerivAt (fun w : ℂ => Real.log (‖w‖/r)/L)
      (L⁻¹ • ((‖z‖/r)⁻¹ • (r⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) z))) z := by
    simpa only [Function.comp_def,Pi.smul_def,smul_eq_mul,div_eq_mul_inv,mul_comm] using hlog.const_smul L⁻¹
  have ht := (Real.smoothTransition.contDiff (n:=1) |>.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (Real.log (‖z‖/r)/L)).hasDerivAt
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
-- module Solutions.Q146_CD.Cannon_Modulus_AnnularCutoffEnergy
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
  have hq : Continuous q := ((annularCutoff_contDiff hr hrR').continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).norm.pow 2
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
        _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul] <;> ring
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
  have hid : (2*Real.pi*C^2/L^2)*(2*L)=4*Real.pi*C^2/L := by field_simp <;> ring
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
-- module Solutions.Q146_CD.Cannon_Modulus_AnnularCutoffEnergy2
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
  have hq : Continuous q := ((annularCutoff_contDiff hr hrR').continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).norm.pow 2
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
  have hu : ContDiff ℝ 1 u := (annularCutoff_contDiff hr hrR').of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
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
-- module Solutions.Q146_CD.Cannon_Topology_CenteredHomeomorph
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
  have ht : 1 ≤ t := by dsimp [t] <;> linarith [div_nonneg hM.le hb0.le]
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
  have hd : 0 < d := by dsimp [d] <;> positivity
  have hdA : d < ‖F a‖ := by have := min_le_left ‖F a‖ ‖F b‖; dsimp [d] <;> linarith
  have hdB : d ≤ ‖F b‖ := by have := min_le_right ‖F a‖ ‖F b‖; dsimp [d] <;> linarith
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
  have h := ((hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (z+F x)).hasFDerivAt.comp z
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
  have hL : 0 < L := by dsimp [L] <;> positivity
  have hble : A+B ≤ L := by dsimp [L] <;> linarith [le_max_left (A+B) 0]
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
-- module Solutions.Q146_CD.CircleDomains_Selection_ExteriorDecay
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A uniform principal remainder estimate

The same coefficient-area input gives decay at infinity, uniformly in
the finite model. This is stronger than a uniform bounded remainder and
preserves the zero constant term when passing to a limit.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem norm_exterior_series_le_two_inv {c : ℕ → ℂ} {z w : ℂ}
    (hc : ∀ n, ‖c n‖ ≤ 1) (hz : 2 ≤ ‖z‖)
    (hw : HasSum (fun n => c n * (z⁻¹) ^ (n + 1)) w) : ‖w‖ ≤ 2 * ‖z‖⁻¹ := by
  let r : ℝ := ‖z‖⁻¹
  have hr0 : 0 ≤ r := inv_nonneg.mpr (norm_nonneg z)
  have hrhalf : r ≤ 1 / 2 := by
    dsimp only [r]
    simpa only [one_div] using
      (inv_le_inv₀ (by linarith : 0 < ‖z‖) (by norm_num : (0 : ℝ) < 2)).mpr hz
  have hr1 : r < 1 := by linarith
  have hg : HasSum (fun n : ℕ => r ^ (n + 1)) (r / (1 - r)) := by
    simpa only [pow_succ', div_eq_mul_inv] using (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
  have hle := hw.norm_le_of_bounded hg (fun n => show ‖c n * (z⁻¹) ^ (n + 1)‖ ≤ r ^ (n + 1) from by
    rw [norm_mul, norm_pow, norm_inv]
    exact mul_le_of_le_one_left (pow_nonneg hr0 _) (hc n))
  refine hle.trans ?_
  change r / (1 - r) ≤ 2 * r
  apply (div_le_iff₀ (by linarith : 0 < 1 - r)).mpr
  nlinarith [mul_nonneg hr0 (show 0 ≤ 1 - 2 * r by linarith)]

theorem ExteriorCoefficientAreaTheorem.exterior_decay
    (harea : ExteriorCoefficientAreaTheorem) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z | 1 < ‖z‖}) (hinj : InjOn F {z | 1 < ‖z‖})
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ z : ℂ, 2 ≤ ‖z‖ → ‖F z - z‖ ≤ 2 * ‖z‖⁻¹ := by
  obtain ⟨c, hc, hbound, hseries⟩ := harea F hF hinj hnorm
  intro z hz
  exact norm_exterior_series_le_two_inv (norm_coefficient_le_one hc hbound) hz
    (hseries z (by linarith))

theorem ExteriorCoefficientAreaTheorem.scaled_exterior_decay
    (harea : ExteriorCoefficientAreaTheorem) {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (hinj : InjOn F {z | R < ‖z‖})
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖F z - z‖ ≤ 2 * R ^ 2 / ‖z‖ := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hnormR : ‖(R : ℂ)‖ = R := by simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  let H : ℂ → ℂ := fun z => F ((R : ℂ) * z) / (R : ℂ)
  have harg {z : ℂ} (hz : 1 < ‖z‖) : R < ‖(R : ℂ) * z‖ := by
    rw [norm_mul, hnormR]
    nlinarith
  have hH : DifferentiableOn ℂ H {z | 1 < ‖z‖} := by
    intro z hz
    have hfd := (hF _ (harg hz)).differentiableAt
      ((isOpen_lt continuous_const continuous_norm).mem_nhds (harg hz))
    exact ((hfd.comp z ((differentiableAt_id.const_mul (R : ℂ)))).div_const _).differentiableWithinAt
  have hHi : InjOn H {z | 1 < ‖z‖} := by
    intro z hz w hw heq
    have heq' : F ((R : ℂ) * z) = F ((R : ℂ) * w) := (div_left_inj' hRc).mp heq
    exact mul_left_cancel₀ hRc (hinj (harg hz) (harg hw) heq')
  have hnH := principal_remainder_rescale hRc hnorm
  intro z hz
  have hnormquot : ‖z / (R : ℂ)‖ = ‖z‖ / R := by rw [norm_div, hnormR]
  have hquot : 2 ≤ ‖z / (R : ℂ)‖ := by
    rw [hnormquot]
    exact (le_div_iff₀ hR).mpr (by linarith)
  have hb := harea.exterior_decay hH hHi hnH (z / (R : ℂ)) hquot
  have heq : H (z / (R : ℂ)) - z / (R : ℂ) = (F z - z) / (R : ℂ) := by
    dsimp only [H]
    rw [mul_div_cancel₀ z hRc]
    ring
  rw [heq, norm_div, hnormR, hnormquot] at hb
  have hzn : 0 < ‖z‖ := by linarith
  have hb' := (div_le_iff₀ hR).mp hb
  calc
    ‖F z - z‖ ≤ 2 * (‖z‖ / R)⁻¹ * R := hb'
    _ = 2 * R ^ 2 / ‖z‖ := by field_simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrincipalExteriorGerm
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

 theorem principal_bigO_of_exterior_holomorphic {F : ℂ → ℂ}
    (hF : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z)
    (ht : Tendsto (fun z => F z - z) (cobounded ℂ) (𝓝 0)) :
    (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  let u := invertedPrincipalRemainder F
  have hu : AnalyticAt ℂ u 0 := invertedPrincipalRemainder_analytic hF ht
  have hu0 : u 0 = 0 := Function.update_self _ _ _
  let v := dslope u 0
  have hv : AnalyticAt ℂ v 0 := analyticAt_dslope_zero hu
  have hb : (fun z : ℂ => v z⁻¹) =O[cobounded ℂ] (fun _ => (1 : ℂ)) := by
    simpa only [Function.comp_def] using
      (hv.continuousAt.isBigO (F := ℂ)).comp_tendsto (tendsto_inv₀_cobounded (α := ℂ))
  have hp := (isBigO_refl (fun z : ℂ => z⁻¹) (cobounded ℂ)).mul hb
  apply hp.congr'
  · have hn : ∀ᶠ z : ℂ in cobounded ℂ, z ≠ 0 := by
      rw [Metric.cobounded_eq_cocompact]
      exact (isCompact_singleton.compl_mem_cocompact : {0}ᶜ ∈ cocompact ℂ)
    filter_upwards [hn] with z hz
    have hh := sub_smul_dslope u 0 z⁻¹
    simp only [sub_zero, smul_eq_mul] at hh
    change z⁻¹ * v z⁻¹ = u z⁻¹ - u 0 at hh
    rw [hu0, sub_zero] at hh
    simpa only [u, invertedPrincipalRemainder,
      Function.update_of_ne (inv_ne_zero hz), inv_inv] using hh
  · exact Eventually.of_forall (fun z => mul_one z⁻¹)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalSmoothExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed smooth principal maps obey one common exterior bound
and decay estimate, obtained from the coefficient area theorem. -/
open Set Filter Asymptotics Bornology
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

namespace PrincipalSmoothApproximation
variable {g : PlaneL2} {k R : ℝ} (S : PrincipalSmoothApproximation g k R)

lemma holomorphic_exterior (n : ℕ) {z : ℂ} (hz : R+2 ≤ ‖z‖) :
    DifferentiableAt ℂ (S.map n : ℂ → ℂ) z := by
  apply differentiableAt_of_partialBar_zero ((S.smooth n).differentiable (by simp) z)
  rw [S.equation n z, S.coefficient_zero n z hz, zero_mul]

lemma principal (n : ℕ) :
    Tendsto (fun z => S.map n z-z) (cobounded ℂ) (𝓝 0) := by
  have h := cauchyTransform_zero_at_infty (S.density n)
  rw [Metric.cobounded_eq_cocompact]
  simpa only [S.values, add_sub_cancel_left] using h

lemma principal_bigO (n : ℕ) :
    (fun z => S.map n z-z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  apply principal_bigO_of_exterior_holomorphic _ (S.principal n)
  exact (eventually_cobounded_le_norm (R+2)).mono fun z hz => S.holomorphic_exterior n hz

lemma exterior_bounds (harea : ExteriorCoefficientAreaTheorem) {T : ℝ}
    (hT : 0 < T) (hRT : R+2 ≤ T) :
    (∀ n z, 2*T ≤ ‖z‖ → ‖S.map n z-z‖ ≤ T) ∧
    ∀ n z, 2*T ≤ ‖z‖ → ‖S.map n z-z‖ ≤ 2*T^2/‖z‖ := by
  have hd (n : ℕ) : DifferentiableOn ℂ (S.map n : ℂ → ℂ) {z | T < ‖z‖} :=
    fun z hz => (S.holomorphic_exterior n (hRT.trans hz.le)).differentiableWithinAt
  exact ⟨fun n => harea.scaled_exterior_bound hT (hd n)
      (S.map n).injective.injOn (S.principal_bigO n),
    fun n => harea.scaled_exterior_decay hT (hd n)
      (S.map n).injective.injOn (S.principal_bigO n)⟩

end PrincipalSmoothApproximation
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PrincipalHomeomorphBounds
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative bounds for a principally normalized plane homeomorphism.
A topological plane homeomorphism cannot maximize its image norm in the
interior of a disk. No holomorphic assumption inside the disk is used. -/
open Set Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma homeomorph_disk_bound (F : ℂ ≃ₜ ℂ) {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hb : ∀ z, ‖z‖ = r → ‖F z‖ ≤ M) :
    ∀ z, ‖z‖ ≤ r → ‖F z‖ ≤ M := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_closedBall (0 : ℂ) r).exists_isMaxOn
    (nonempty_closedBall.mpr hr.le) F.continuous.norm.continuousOn
  have hxn : ‖x‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hx
  have hxbound : ‖F x‖ ≤ M := by
    by_contra hn
    have hnorm : 0 < ‖F x‖ := lt_of_le_of_lt hM (lt_of_not_ge hn)
    have hxlt : ‖x‖ < r := lt_of_le_of_ne hxn (fun he => hn (hb x he))
    have hnhds : closedBall (0 : ℂ) r ∈ 𝓝 x :=
      Filter.mem_of_superset (isOpen_ball.mem_nhds (by
        simpa only [mem_ball, dist_zero_right] using hxlt)) ball_subset_closedBall
    have hl : IsLocalMax (fun z => ‖F z‖) x := hmax.isLocalMax hnhds
    have hsq : IsLocalMax (fun z => ‖F z‖^2) x := by
      filter_upwards [hl] with z hz
      nlinarith [norm_nonneg (F z), norm_nonneg (F x)]
    have hsq' : IsLocalMax (fun z : ℂ => ‖z‖^2) (F x) := by
      have hsq'' : IsLocalMax (fun z => ‖F z‖^2) (F.symm (F x)) := by
        simpa only [F.symm_apply_apply] using hsq
      simpa only [Function.comp_def, F.apply_symm_apply] using
        hsq''.comp_continuous F.symm.continuous.continuousAt
    have he := hsq'.hasFDerivAt_eq_zero (hasStrictFDerivAt_norm_sq (F x)).hasFDerivAt
    have hz := congrArg (fun L : ℂ →L[ℝ] ℝ => L (F x)) he
    simp only [two_smul, add_apply, innerSL_apply_apply,
      zero_apply, real_inner_self_eq_norm_sq] at hz
    nlinarith
  intro z hz
  exact (hmax (by simpa only [mem_closedBall, dist_zero_right] using hz)).trans hxbound

lemma principal_homeomorph_pointwise_bounds (F : ℂ ≃ₜ ℂ) {R : ℝ} (hR : 0 < R)
    (hb : ∀ z, 2*R ≤ ‖z‖ → ‖F z-z‖ ≤ R) :
    (∀ z, ‖F z‖ ≤ max (3*R) (‖z‖+R)) ∧
      ∀ w, ‖F.symm w‖ ≤ max (2*R) (‖w‖+R) := by
  have hinner : ∀ z, ‖z‖ ≤ 2*R → ‖F z‖ ≤ 3*R := by
    apply homeomorph_disk_bound F (by positivity) (by positivity)
    intro z hz
    have := hb z hz.ge
    have := norm_le_norm_sub_add (F z) z
    linarith
  constructor
  · intro z
    by_cases hz : 2*R ≤ ‖z‖
    · apply le_trans _ (le_max_right _ _)
      linarith [norm_le_norm_sub_add (F z) z, hb z hz]
    · exact (hinner z (le_of_not_ge hz)).trans (le_max_left _ _)
  · intro w
    by_cases hw : 2*R ≤ ‖F.symm w‖
    · have hh := hb (F.symm w) hw
      rw [F.apply_symm_apply] at hh
      have hn := norm_le_norm_sub_add (F.symm w) w
      rw [norm_sub_rev] at hn
      apply le_trans _ (le_max_right _ _)
      linarith
    · exact (le_of_not_ge hw).trans (le_max_left _ _)

lemma principal_homeomorph_displacement_bound (F : ℂ ≃ₜ ℂ) {R : ℝ} (hR : 0 < R)
    (hb : ∀ z, 2*R ≤ ‖z‖ → ‖F z-z‖ ≤ R) :
    ∀ z, ‖F z-z‖ ≤ 5*R := by
  intro z
  by_cases hz : 2*R ≤ ‖z‖
  · exact (hb z hz).trans (by linarith)
  · have hzn : ‖z‖ < 2*R := lt_of_not_ge hz
    have hF := (principal_homeomorph_pointwise_bounds F hR hb).1 z
    have hm : max (3*R) (‖z‖+R) = 3*R := max_eq_left (by linarith)
    rw [hm] at hF
    exact (norm_sub_le (F z) z).trans (by linarith)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalWeakDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The strong principal density limit supplies the actual directional weak
derivatives of the locally uniform homeomorphism limit. -/
open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma principalDirectionalCorrection_ae (g : PlaneL2) (v : ℂ) :
    principalDirectionalCorrection g v =ᵐ[volume]
      fun z => v*beurling g z + star v*g z := by
  filter_upwards [Lp.coeFn_add (v • beurling g) (star v • g),
    Lp.coeFn_smul v (beurling g), Lp.coeFn_smul (star v) g] with z h1 h2 h3
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3
  exact h1.trans (congrArg₂ (· + ·) h2 h3)

lemma principalDirectionalCorrection_tendsto {gₙ : ℕ → PlaneL2} {g : PlaneL2}
    (hg : Tendsto gₙ atTop (𝓝 g)) (v : ℂ) :
    Tendsto (fun n => principalDirectionalCorrection (gₙ n) v) atTop
      (𝓝 (principalDirectionalCorrection g v)) :=
  (((beurling.continuous.tendsto g).comp hg).const_smul v).add (hg.const_smul (star v))

namespace PrincipalSmoothApproximation
variable {g : PlaneL2} {k R : ℝ} (S : PrincipalSmoothApproximation g k R)

lemma directional_derivative_ae (n : ℕ) (v : ℂ) :
    (fun z => fderiv ℝ (S.map n : ℂ → ℂ) z v) =ᵐ[volume]
      fun z => v+principalDirectionalCorrection ((S.density n).toLp 2 (μ:=volume)) v z := by
  filter_upwards [principalDirectionalCorrection_ae ((S.density n).toLp 2 (μ:=volume)) v,
    (S.density n).coeFn_toLp 2 volume,
    (schwartz_smoothL2 (S.density n)).beurling.representative_ae] with z hc hd hB
  change (beurling ((S.density n).toLp 2 (μ:=volume))) z =
    smoothBeurling (S.density n) z at hB
  rw [hc, hd, hB, fderiv_wirtinger, (S.partials n z).1, (S.partials n z).2]
  ring

lemma limit_weak_direction {H : ℂ → ℂ} {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (ht : ∀ z, Tendsto (fun n => S.map (σ n) z) atTop (𝓝 (H z)))
    {T : ℝ} (hT : 0 < T)
    (hb : ∀ n z, 2*T ≤ ‖z‖ → ‖S.map n z-z‖ ≤ T) (v : ℂ) :
    ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, H z*fderiv ℝ (φ : ℂ → ℂ) z v) =
        -(∫ z, (v+principalDirectionalCorrection g v z)*φ z) := by
  apply smooth_limit_weak_derivative (fun n z => S.map (σ n) z) H
    (fun n => (S.smooth (σ n)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (by positivity : 0 ≤ 5*T)
    (fun n => principal_homeomorph_displacement_bound (S.map (σ n)) hT (hb (σ n))) ht v
    (fun n => principalDirectionalCorrection ((S.density (σ n)).toLp 2 (μ:=volume)) v)
    (principalDirectionalCorrection g v) (fun n => S.directional_derivative_ae (σ n) v)
  exact (principalDirectionalCorrection_tendsto S.strong_density v).comp hσ.tendsto_atTop

end PrincipalSmoothApproximation
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PrincipalHomeomorphCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common exterior principal bound gives compactness of the maps and
inverses directly. The limits keep the original principal scale. -/
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonPlane

lemma principal_smooth_homeomorph_subsequence (F : ℕ → ℂ ≃ₜ ℂ)
    (hF : ∀ n, ContDiff ℝ 1 (F n : ℂ → ℂ))
    (hFi : ∀ n, ContDiff ℝ 1 ((F n).symm : ℂ → ℂ))
    {K R : ℝ} (hK : 0 ≤ K) (hR : 0 < R)
    (hD : ∀ n z, ‖fderiv ℝ (F n : ℂ → ℂ) z‖^2 ≤
      K*|(fderiv ℝ (F n : ℂ → ℂ) z).det|)
    (hDi : ∀ n z, ‖fderiv ℝ ((F n).symm : ℂ → ℂ) z‖^2 ≤
      K*|(fderiv ℝ ((F n).symm : ℂ → ℂ) z).det|)
    (hb : ∀ n z, 2*R ≤ ‖z‖ → ‖F n z-z‖ ≤ R) :
    ∃ H : ℂ ≃ₜ ℂ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n => homeomorphMap (F (σ n))) atTop (𝓝 (homeomorphMap H)) ∧
      Tendsto (fun n => homeomorphMap (F (σ n)).symm) atTop
        (𝓝 (homeomorphMap H.symm)) := by
  have hr : UniformRelativeControl (fun n z => F n z) := by
    intro ε hε
    obtain ⟨η, hη, h⟩ := smooth_qc_uniform_shrink hK ε hε
    exact ⟨η, hη, fun n => h (F n) (hFi n) (hDi n)⟩
  have hri : UniformRelativeControl (fun n z => (F n).symm z) := by
    intro ε hε
    obtain ⟨η, hη, h⟩ := smooth_qc_uniform_shrink hK ε hε
    exact ⟨η, hη, fun n => h (F n).symm (hF n) (hD n)⟩
  have hbounds := fun n => principal_homeomorph_pointwise_bounds (F n) hR (hb n)
  have hbf : ∀ z, ∃ B, ∀ n, ‖F n z‖ ≤ B :=
    fun z => ⟨max (3*R) (‖z‖+R), fun n => (hbounds n).1 z⟩
  have hbi : ∀ z, ∃ B, ∀ n, ‖(F n).symm z‖ ≤ B :=
    fun z => ⟨max (2*R) (‖z‖+R), fun n => (hbounds n).2 z⟩
  exact pointwise_bounded_homeomorph_subsequence F
    (relative_control_equicontinuous _ hr hbf)
    (relative_control_equicontinuous _ hri hbi) hbf hbi

lemma principal_limit_decay {F : ℕ → ℂ → ℂ} {H : ℂ → ℂ} {R : ℝ}
    (hlim : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (H z)))
    (hb : ∀ n z, 2*R ≤ ‖z‖ → ‖F n z-z‖ ≤ 2*R^2/‖z‖) :
    Tendsto (fun z => H z-z) (Bornology.cobounded ℂ) (𝓝 0) := by
  have hbound (z : ℂ) (hz : 2*R ≤ ‖z‖) : ‖H z-z‖ ≤ 2*R^2/‖z‖ :=
    le_of_tendsto ((hlim z).sub_const z |>.norm) (.of_forall (fun n => hb n z hz))
  apply squeeze_zero_norm' (a := fun z : ℂ => 2*R^2/‖z‖) ?_ ?_
  · filter_upwards [eventually_cobounded_le_norm (2*R)] with z hz
    exact hbound z hz
  · simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp tendsto_norm_cobounded_atTop) :
        Tendsto (fun z : ℂ => (2*R^2)*‖z‖⁻¹) (Bornology.cobounded ℂ) (𝓝 ((2*R^2)*0)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalSmoothLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the principal plane homeomorphism with the specified strong
L2 density. Retain the actual smooth approximants and both convergences
for the subsequent scalar transport application. -/
open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami CannonPlane

namespace PrincipalSmoothApproximation
variable {g : PlaneL2} {k R : ℝ} (S : PrincipalSmoothApproximation g k R)

lemma exists_principal_limit_data_oai (harea : ExteriorCoefficientAreaTheorem)
    (hk : 0 ≤ k) (hk1 : k < 1) {T : ℝ} (hT : 0 < T) (hRT : R+2 ≤ T) :
    Nonempty (PrincipalMapLimit S) := by
  have hK : 0 ≤ (1+k)/(1-k) := div_nonneg (by linarith) (by linarith)
  have hdist (n : ℕ) := smooth_beltrami_two_sided_distortion (S.map n)
    (S.smooth n) (S.inverse_smooth n) (S.coefficient n) hk hk1
    (S.coefficient_bound n) (S.equation n)
  obtain ⟨hb, hdecay⟩ := S.exterior_bounds harea hT hRT
  obtain ⟨H, σ, hσ, hlim, hinverse⟩ := principal_smooth_homeomorph_subsequence S.map
    (fun n => (S.smooth n).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (fun n => (S.inverse_smooth n).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hK hT
    (fun n => (hdist n).1) (fun n => (hdist n).2) hb
  have hp (z : ℂ) : Tendsto (fun n => S.map (σ n) z) atTop (𝓝 (H z)) :=
    (continuous_eval_const z).tendsto (homeomorphMap H) |>.comp hlim
  exact ⟨⟨H, σ, hσ, hlim, hinverse,
    principal_limit_decay hp (fun n => hdecay (σ n)),
    fun v => S.limit_weak_direction hσ hp hT hb v⟩⟩

end PrincipalSmoothApproximation
end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.PrincipalSmoothApproximation.exists_principal_limit_data_oai := @OAI.CircleDomainRigidity.PrincipalSmoothApproximation.exists_principal_limit_data_oai
