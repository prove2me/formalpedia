-- Prove2me | solution 1 for LogLogJam.Supplement.one_readout_localization
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T19:29:25.295914+00:00
-- url     : https://prove2.me/submissions/e64b671c-e783-42d6-9301-a824af4cd6c0

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_LogLogJam_Supplement_IsGaussQP
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47
import Theorems.Thm_BosonicLearn_fockPOVM_of_effect
import Theorems.Thm_BosonicLearn_fockPOVM_postprocess
import Theorems.Thm_BosonicLearn_state_ext_characteristic
import Theorems.Thm_LogLogJam_Supplement_nonadaptive_transcript_product
import Theorems.Thm_LogLogJam_Supplement_squeezed_decoder
import Theorems.Thm_LogLogJam_Supplement_squeezed_disk_readout
import Theorems.Thm_LogLogJam_Supplement_squeezed_fock_realization
import Theorems.Thm_LogLogJam_Supplement_squeezed_trace_distance
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
open MeasureTheory BosonicLearn Filter
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open scoped Classical ComplexConjugate ENNReal Topology
namespace LogLogJam.Supplement.OneObservationProof
abbrev Idx := Occupation (Fin 1)
abbrev XY := ℝ × ℝ
def c (n : ℕ) : ℝ := Real.sqrt (n.centralBinom : ℝ) / 2^n
def deg (i : Idx) := i 0 / 2
def arc (b : ℝ) : Measure ℝ := ENNReal.ofReal b⁻¹ • (volume.restrict (Set.Ico 0 b))
def nu : Measure XY := (arc Real.pi).prod (arc (2*Real.pi))
instance arc_finite (b : ℝ) : IsFiniteMeasure (arc b) := by
  constructor;simp [arc,Measure.smul_apply,Real.volume_Ico];finiteness
lemma arc_probability {b : ℝ} (hb : 0<b) : IsProbabilityMeasure (arc b) := by
  constructor; simp [arc,Measure.smul_apply,Real.volume_Ico,ENNReal.ofReal_inv_of_pos hb,ENNReal.ofReal_ne_top,(ENNReal.ofReal_pos.mpr hb).ne'];exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hb).ne' ENNReal.ofReal_ne_top
instance nu_probability : IsProbabilityMeasure nu := by
  unfold nu;let _ := arc_probability Real.pi_pos;let _ := arc_probability (show 0<2*Real.pi by positivity);infer_instance
def zObs (x : XY) : ℂ := (Real.sin x.1 : ℂ)*Complex.exp (-Complex.I*x.2)
def psi (q : ℂ) (N : ℝ) (i : Idx) : ℂ := if Even (i 0) then ((N*c (deg i):ℝ):ℂ)*q^(deg i) else 0
lemma normZ (x : XY) : ‖zObs x‖ ≤ 1 := by
  rw [zObs,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp];simp only [Complex.neg_re,Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,neg_zero,Real.exp_zero,mul_one]; simpa using Real.abs_sin_le_one x.1
lemma zsmall {q : ℂ} (hq : ‖q‖<1) (x) : ‖q*zObs x‖<1 := (norm_mul_le _ _).trans_lt ((show ‖q‖*‖zObs x‖ ≤ ‖q‖ by simpa using mul_le_mul_of_nonneg_left (normZ x) (norm_nonneg q)).trans_lt hq)
end LogLogJam.Supplement.OneObservationProof
open MeasureTheory BosonicLearn Filter Matrix
open LogLogJam LogLogJam.Supplement
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open scoped Classical ComplexConjugate ENNReal
namespace LogLogJam.Supplement.OneObservationProof
def point (r θ : ℝ) : ℂ := (Real.tanh r : ℂ)*Complex.exp ((2*θ:ℝ)*Complex.I)
def gap (q : ℂ) : ℝ := 1-‖q‖^2
def cov (q : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1+‖q‖^2+2*q.re)/gap q, 2*q.im/gap q; 2*q.im/gap q, (1+‖q‖^2-2*q.re)/gap q]
lemma norm_point (r θ : ℝ) (hr : 0≤r) : ‖point r θ‖ = Real.tanh r := by
  rw [point,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ((show 0 ≤ Real.tanh r by rw [Real.tanh_eq_sinh_div_cosh];exact div_nonneg (Real.sinh_nonneg_iff.mpr hr) (Real.cosh_pos _).le))]
lemma point_re (r θ : ℝ) : (point r θ).re = Real.tanh r * Real.cos (2*θ) := by simp only [point,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.exp_ofReal_mul_I_re]
lemma point_im (r θ : ℝ) : (point r θ).im = Real.tanh r * Real.sin (2*θ) := by simp only [point,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,Complex.exp_ofReal_mul_I_im]
lemma exp_ratio (r : ℝ) : Real.exp (2*r) = (1+Real.tanh r)/(1-Real.tanh r) := by
  rw [Real.tanh_eq,Real.exp_neg,show 2*r = r+r by ring,Real.exp_add]
  field_simp
  ring
lemma pgap {q : ℂ} (hq : ‖q‖<1) : 0<gap q := by dsimp [gap];nlinarith [norm_nonneg q]
lemma cov_point (r θ : ℝ) (hr : 0≤r) : cov (point r θ) = Vsq (Real.exp (2*r)) θ := by
  have h := Real.tanh_lt_one r
  have h0 := (show 0 ≤ Real.tanh r by rw [Real.tanh_eq_sinh_div_cosh];exact div_nonneg (Real.sinh_nonneg_iff.mpr hr) (Real.cosh_pos _).le)
  have h₂ : (1-Real.tanh r^2)≠0 := by nlinarith
  have hc := Real.sin_sq_add_cos_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cov,gap,norm_point _ _ hr,point_re,point_im,Vsq,rot,Matrix.mul_apply,Fin.sum_univ_two,exp_ratio,Real.sin_two_mul,Real.cos_two_mul] <;>
    field_simp [h₂,sub_ne_zero.mpr h.ne',show 1+Real.tanh r ≠ 0 by linarith] <;>
    grind
lemma norm_two (q : ℂ) : ‖q‖^2 = q.re^2+q.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply];ring
lemma det_cov {q p : ℂ} (hq : ‖q‖<1) (hp : ‖p‖<1) :
    (cov q + cov p).det = 4*(1+‖q-p‖^2/(gap q*gap p)) := by
  have hq' := (pgap hq).ne'
  have hp' := (pgap hp).ne'
  simp [det_fin_two,Matrix.add_apply,cov]
  field_simp [hq',hp']
  simp only [gap,norm_two,Complex.sub_re,Complex.sub_im]
  ring
end LogLogJam.Supplement.OneObservationProof
open MeasureTheory BosonicLearn Filter Matrix
open LogLogJam LogLogJam.Supplement
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open scoped Classical ComplexConjugate ENNReal
namespace LogLogJam.Supplement.OneObservationProof
def rel (q p : ℂ) : ℝ := ‖q-p‖^2/(gap q*gap p)
def diskDist (q p : ℂ) : ℝ := Real.sqrt (1-1/Real.sqrt (1+rel q p))
lemma rel_nonneg {q p : ℂ} (hq : ‖q‖<1) (hp : ‖p‖<1) : 0 ≤ rel q p := div_nonneg (sq_nonneg _) (mul_nonneg (pgap hq).le (pgap hp).le)
lemma disk_born (ρ σ : State (Occupation (Fin 1))) (r θ s φ : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hρ : squeezedAt ρ r θ) (hσ : squeezedAt σ s φ) :
    traceDist ρ.coefficients σ.coefficients = ENNReal.ofReal (diskDist (point r θ) (point s φ)) := by
  have hq : ‖point r θ‖<1 := (norm_point r θ hr).trans_lt (Real.tanh_lt_one _)
  have hp : ‖point s φ‖<1 := (norm_point s φ hs).trans_lt (Real.tanh_lt_one _)
  rw [squeezed_trace_distance ρ σ r θ s φ hρ hσ,← cov_point _ _ hr,← cov_point _ _ hs,det_cov hq hp,Real.sqrt_mul (by norm_num : 0 ≤ (4:ℝ))]
  dsimp [diskDist,rel];norm_num;congr 3; field_simp
lemma sq_dist {q p : ℂ} (hq : ‖q‖<1) (hp : ‖p‖<1) :
    diskDist q p ^2 = 1-1/Real.sqrt (1+rel q p) := by
  have h : 1  ≤  Real.sqrt (1+rel q p) := by rw [Real.one_le_sqrt];linarith [rel_nonneg hq hp]
  apply Real.sq_sqrt
  have hp' : 0<Real.sqrt (1+rel q p) := by linarith
  have := (div_le_iff₀ hp').mpr (show 1  ≤  1*Real.sqrt (1+rel q p) by linarith)
  linarith
lemma rel_lower {q p : ℂ} (hq : ‖q‖<1) (hp : ‖p‖<1) : diskDist q p ^2  ≤  rel q p := by
  have h := rel_nonneg hq hp
  let F := Real.sqrt (1+rel q p)
  have hF : 1 ≤ F := by apply Real.one_le_sqrt.mpr;linarith
  have hFs : F^2=1+rel q p := Real.sq_sqrt (by linarith)
  have h0 : 0<F := by linarith
  rw [sq_dist hq hp]
  change 1-1/F ≤ _
  have hF1 : 1-1/F  ≤  F-1 := by apply (sub_le_iff_le_add).mpr; field_simp; nlinarith [sq_nonneg (F-1)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hF) (show 0 ≤ F by linarith)]
lemma gap_lo (q : ℂ) (hq : ‖q‖<1) : 1-‖q‖  ≤  gap q := by
  dsimp [gap]; nlinarith [mul_nonneg (norm_nonneg q) (sub_nonneg.mpr hq.le)]
lemma gap_hi (q : ℂ) : gap q  ≤  2*(1-‖q‖) := by dsimp [gap]; nlinarith [sq_nonneg (1-‖q‖)]
lemma near_suffices {q p : ℂ} (hq : ‖q‖<1) {e : ℝ} (he : 0 ≤ e) (hsmall : e ≤ 1/3)
    (hle : ‖q-p‖  ≤  e*(1-‖q‖)/4) : ‖p‖ < 1 ∧ diskDist q p  ≤  e := by
  let A := 1-‖q‖
  have hA : 0<A := sub_pos.mpr hq
  have hpq := norm_sub_norm_le p q
  rw [norm_sub_rev] at hpq
  change ‖q-p‖  ≤  e*A/4 at hle
  have hhalf : A/2  ≤  1-‖p‖ := by dsimp [A] at *;nlinarith [mul_le_mul_of_nonneg_right hsmall hA.le]
  have hp : ‖p‖<1 := by linarith
  refine ⟨hp,?_⟩
  have h1 : A^2/2  ≤  gap q * gap p := by
    have hg := mul_le_mul (gap_lo q hq) (hhalf.trans (gap_lo p hp)) (by positivity : 0 ≤ A/2) (pgap hq).le
    change A*(A/2)  ≤  _ at hg;linarith
  have hg := mul_le_mul_of_nonneg_left h1 (sq_nonneg e)
  have hs := mul_le_mul hle hle (norm_nonneg _) (by positivity)
  have hrel : rel q p  ≤  e^2 := by apply (div_le_iff₀ (mul_pos (pgap hq) (pgap hp))).mpr;nlinarith [sq_nonneg (e*A)]
  have := rel_lower hq hp
  nlinarith [Real.sqrt_nonneg (1-1/Real.sqrt (1+rel q p))]
end LogLogJam.Supplement.OneObservationProof
open MeasureTheory BosonicLearn Filter Matrix
open LogLogJam LogLogJam.Supplement
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State NuclearExpansion traceSize)
open scoped Classical ComplexConjugate ENNReal Topology
namespace LogLogJam.Supplement.OneObservationProof
def unpolar (q : ℂ) : ℝ × ℝ := (Real.artanh ‖q‖,q.arg/2)
lemma meas_unpolar : Measurable unpolar := by unfold unpolar Real.artanh;fun_prop
lemma inv_unpolar (q : ℂ) (hq : ‖q‖<1) : point (unpolar q).1 (unpolar q).2 = q := by
  dsimp only [unpolar,point]; rw [Real.tanh_artanh ⟨by linarith [norm_nonneg q],hq⟩,show 2*(q.arg/2)=q.arg by ring,Complex.norm_mul_exp_arg_mul_I]
end LogLogJam.Supplement.OneObservationProof
open MeasureTheory BosonicLearn ProbabilityTheory Filter Matrix
open LogLogJam LogLogJam.Supplement
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity)
open scoped Classical ComplexConjugate ENNReal Topology
namespace LogLogJam.Supplement.OneObservationProof
lemma pad (M : FockPOVM (Occupation (Fin 1)) (ℝ×ℝ)) (D : ℝ×ℝ → State (Occupation (Fin 1))) (hD : Measurable D)
    (ε p : ℝ) (h : ∀ ρ : State (Occupation (Fin 1)), IsPureCentGauss ρ →
     ∃ E : Set (ℝ×ℝ), MeasurableSet E ∧ ENNReal.ofReal p  ≤  M.law ρ.coefficients E ∧
     ∀ x∈E, IsPureCentGauss (D x) ∧ traceDist ρ.coefficients (D x).coefficients  ≤  ENNReal.ofReal ε)
    (m : ℕ) (hm : 1 ≤ m) :
      ∃ (S : AdaptiveScheme 1 m ℝ) (est : Kernel (Fin m → ℝ) (State (Occupation (Fin 1)))),
        (∀ (t : Fin m) (x x' : Fin t → ℝ), S.povm t x = S.povm t x') ∧ IsMarkovKernel est ∧
        ∀ ρ : State (Occupation (Fin 1)), IsPureCentGauss ρ →
          ENNReal.ofReal p  ≤  ∫⁻ x, est x {σ | IsPureCentGauss σ ∧
                traceDist ρ.coefficients σ.coefficients  ≤  ENNReal.ofReal ε} ∂(transcriptLaw S ρ.coefficients) := by
  let e : (ℝ×ℝ) ≃ᵐ ℝ := PolishSpace.measurableEquivOfNotCountable not_countable not_countable
  obtain ⟨P,hP⟩ := fockPOVM_postprocess M (Kernel.deterministic e e.measurable) (by infer_instance)
  have hmap (ρ) : P.law ρ = (M.law ρ).map e := (hP ρ).trans (Measure.bind_dirac_eq_map _ e.measurable)
  let ν (ρ : Matrix (Occupation (Fin 1)) (Occupation (Fin 1)) ℂ) := if IsDensity ρ then P.law ρ else Measure.dirac 0
  have hν (ρ) : IsProbabilityMeasure (ν ρ) := by
    dsimp [ν];split
    · exact P.law_prob _ ‹_›
    · infer_instance
  let S : AdaptiveScheme 1 m ℝ := {
    povm := fun _ _ => P
    round := fun ρ _ => Kernel.const _ (ν ρ)
    round_markov := fun ρ _ => by let _ := hν ρ;infer_instance
    round_born := fun ρ hρ _ _ => by simp [ν,hρ] }
  have hS : ∀ (t : Fin m) (x x' : Fin t → ℝ), S.povm t x = S.povm t x' := fun _ _ _ => rfl
  let i : Fin m := ⟨0,by omega⟩
  let read (x : Fin m → ℝ) := e.symm (x i)
  have hr : Measurable read := e.symm.measurable.comp (measurable_pi_apply i)
  refine ⟨S,Kernel.deterministic (D ∘ read) (hD.comp hr),hS,inferInstance,?_⟩
  intro ρ hρ
  obtain ⟨E,hE,hprob,hgood⟩ := h ρ hρ
  let μ := P.law ρ.coefficients
  let _ : IsProbabilityMeasure μ := P.law_prob _ ρ.density
  have htr : transcriptLaw S ρ.coefficients = Measure.pi (fun _ : Fin m => μ) := nonadaptive_transcript_product S ρ hS
  have hfirst : MeasurePreserving read (transcriptLaw S ρ.coefficients) (M.law ρ.coefficients) := by
    rw [htr]
    apply MeasurePreserving.comp _ (measurePreserving_eval (fun _ : Fin m => μ) i)
    refine ⟨e.symm.measurable,?_⟩
    dsimp only [μ];rw [hmap,Measure.map_map e.symm.measurable e.measurable]
    simpa using Measure.map_id (M.law ρ.coefficients)
  have hpre := hfirst.measure_preimage hE.nullMeasurableSet
  refine hprob.trans ?_;rw [← hpre,← lintegral_indicator_one (hr hE)]
  apply lintegral_mono;intro x
  by_cases hx : x∈read ⁻¹' E
  · rw [Set.indicator_of_mem hx,Pi.one_apply]
    change 1 ≤ Measure.dirac (D (read x)) _
    rw [Measure.dirac_apply_of_mem];exact hgood _ hx
  · simp [Set.indicator_of_notMem hx]
end LogLogJam.Supplement.OneObservationProof
open MeasureTheory BosonicLearn Filter
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open scoped Classical ComplexConjugate ENNReal Topology
namespace LogLogJam.Supplement.OneObservationProof
def cis (x : ℝ) := Complex.exp ((x:ℂ)*Complex.I)
lemma ncis (x) : ‖cis x‖ = 1 := Complex.norm_exp_ofReal_mul_I _
lemma acis (x y : ℝ) : ‖cis x-cis y‖  ≤  |x-y| := by
  have h : cis x-cis y = (Complex.exp (Complex.I*((x-y:ℝ):ℂ))-1)*cis y := by
    dsimp [cis];rw [sub_mul,one_mul,← Complex.exp_add];push_cast;ring_nf
  rw [h,norm_mul,ncis,mul_one];exact Real.norm_exp_I_mul_ofReal_sub_one_le
lemma choose_phase (q : ℂ) : ∃ α ∈ Set.Icc 0 (2*Real.pi), q = (‖q‖:ℂ)*cis α := by
  by_cases h : 0  ≤  q.arg
  · exact ⟨q.arg,⟨h,by linarith [Complex.arg_le_pi q,Real.pi_pos]⟩,(Complex.norm_mul_exp_arg_mul_I _).symm⟩
  · refine ⟨q.arg+2*Real.pi,⟨by linarith [Complex.neg_pi_lt_arg q,Real.pi_pos],by linarith⟩,?_⟩
    dsimp [cis];push_cast;rw [add_mul,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one,Complex.norm_mul_exp_arg_mul_I]
lemma slot {α h : ℝ} (ha : α ∈ Set.Icc 0 (2*Real.pi)) (hh : 0<h) (hπ : h  ≤  Real.pi) :
    ∃ l : ℝ, 0  ≤  l ∧ l+h  ≤  2*Real.pi ∧ ∀ x∈Set.Ico l (l+h), |x-α|  ≤  h := by
  by_cases hs : α+h  ≤  2*Real.pi
  · exact ⟨α,ha.1,hs,fun x hx => by rw [abs_of_nonneg (sub_nonneg.mpr hx.1)];linarith [hx.2]⟩
  · refine ⟨α-h,by linarith,by linarith [ha.2],fun x hx => ?_⟩
    apply abs_le.mpr;constructor <;> linarith [hx.1,hx.2]
lemma radial {a e : ℝ} (ha : 0  ≤  a) (ha1 : a < 1) (he : 0 < e) (he1 : e  ≤  1/3) :
    let B := Real.sqrt (1-a^2)
    let h := e*(1-a)/16
    let s := Real.arcsin a
    0 < B ∧ 0 < h ∧ 0  ≤  s ∧ s+h/B  ≤  Real.pi ∧
    ∀ t ∈ Set.Ico s (s+h/B), |Real.sin t-a|  ≤  h := by
  dsimp only
  let B := Real.sqrt (1-a^2)
  let h := e*(1-a)/16
  let s := Real.arcsin a
  have hB : 0<B := Real.sqrt_pos.mpr (by nlinarith)
  have hBs : B^2=1-a^2 := Real.sq_sqrt (by nlinarith)
  have hh : 0<h := by dsimp [h];positivity [sub_pos.mpr ha1]
  have h0 : 0 ≤ s := Real.arcsin_nonneg.mpr ha
  have hS : Real.sin s = a := Real.sin_arcsin (by linarith) ha1.le
  have hC : Real.cos s = B := Real.cos_arcsin _
  have hπ : s  ≤  Real.pi/2 := Real.arcsin_le_pi_div_two _
  have hb : B  ≤  Real.pi/2 - s := by simpa only [Real.sin_pi_div_two_sub,hC] using Real.sin_le (sub_nonneg.mpr hπ)
  have hl : h/B  ≤  B := by
    apply (div_le_iff₀ hB).mpr;dsimp [h]
    nlinarith [mul_le_mul_of_nonneg_right he1 (sub_nonneg.mpr ha1.le),mul_nonneg ha (sub_nonneg.mpr ha1.le)]
  refine ⟨hB,hh,h0,by change s+h/B  ≤  _;linarith [Real.pi_pos],?_⟩
  intro t ht
  change s ≤ t ∧ t<s+h/B at ht
  have hts : -(Real.pi/2)  ≤  s := by linarith [Real.pi_pos]
  have htp : t  ≤  Real.pi/2 := by linarith [ht.2]
  have hsa := Real.sin_le_sin_of_le_of_le_pi_div_two hts htp ht.1
  rw [hS] at hsa
  rw [abs_of_nonneg (sub_nonneg.mpr hsa),show t=s+(t-s) by ring,Real.sin_add,hS,hC]
  have hs₁ := mul_le_mul_of_nonneg_left (Real.cos_le_one (t-s)) ha
  have hs₂ := mul_le_mul_of_nonneg_left (Real.sin_le (sub_nonneg.mpr ht.1)) hB.le
  have hs₃ := (lt_div_iff₀ hB).mp (show t-s<h/B by linarith [ht.2])
  change _  ≤  h;linarith
lemma arc_interval {l h b : ℝ} (hl : 0  ≤  l) (hh : 0  ≤  h) (hb : l+h  ≤  b) :
    arc b (Set.Ico l (l+h)) = ENNReal.ofReal (b⁻¹*h) := by
  have hb0 : 0 ≤ b := by linarith
  rw [arc,Measure.smul_apply,Measure.restrict_apply measurableSet_Ico,Set.inter_eq_left.mpr (Set.Ico_subset_Ico hl hb),Real.volume_Ico,add_sub_cancel_left,ENNReal.ofReal_mul (inv_nonneg.mpr hb0)];rfl
lemma obs_conj (x : XY) : conj (zObs x) = (Real.sin x.1 : ℂ)*cis x.2 := by
  dsimp [zObs,cis];rw [map_mul,Complex.conj_ofReal,← Complex.exp_conj];simp only [map_mul,map_neg,Complex.conj_I,neg_neg,Complex.conj_ofReal];congr 2;ring
lemma box {q : ℂ} (hq : ‖q‖<1) {ε : ℝ} (he : 0<ε) (he1 : ε  ≤  1/3) :
    let A := 1-‖q‖
    let B := Real.sqrt (1-‖q‖^2)
    let h := ε*A/16
    ∃ E : Set XY, MeasurableSet E ∧
      nu E = ENNReal.ofReal (Real.pi⁻¹*(h/B)*((2*Real.pi)⁻¹*h)) ∧
      ∀ x ∈ E, ‖q-conj (zObs x)‖  ≤  2*h := by
  let a := ‖q‖
  let A := 1-a
  let B := Real.sqrt (1-a^2)
  let h := ε*A/16
  let s := Real.arcsin a
  obtain ⟨hB,hh,hs,hπ,hr⟩ := radial (norm_nonneg q) hq he he1
  obtain ⟨α,hα,hqα⟩ := choose_phase q
  have hA : 0<A := sub_pos.mpr hq
  have hle : h  ≤  Real.pi := by dsimp [h,A,a];nlinarith [Real.pi_gt_three,mul_nonneg he.le (norm_nonneg q)]
  obtain ⟨l,hl,hlπ,hφ⟩ := slot hα hh hle
  refine ⟨(Set.Ico s (s+h/B)) ×ˢ (Set.Ico l (l+h)),measurableSet_Ico.prod measurableSet_Ico,?_,?_⟩
  · rw [nu,Measure.prod_prod,arc_interval hs (div_nonneg hh.le hB.le) hπ,arc_interval hl hh.le hlπ,← ENNReal.ofReal_mul (by positivity)]
  · rintro ⟨t,φ⟩ hx
    obtain ⟨ht,hφ'⟩ := hx
    rw [obs_conj];dsimp only [Prod.fst,Prod.snd]
    have hij : q-(Real.sin t:ℂ)*cis φ = (a:ℂ)*(cis α-cis φ)+((a:ℂ)-(Real.sin t:ℂ))*cis φ := by
      dsimp [a];nth_rw 1 [hqα];ring
    rw [hij];apply (norm_add_le ..).trans
    rw [norm_mul,norm_mul,ncis,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg q),← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
    have hp : ‖cis α-cis φ‖ ≤ h := (acis α φ).trans (by simpa only [abs_sub_comm α φ] using hφ _ hφ')
    have hn := (mul_le_mul_of_nonneg_left hp (norm_nonneg q)).trans (mul_le_mul_of_nonneg_right hq.le hh.le)
    change ‖q‖ * ‖cis α-cis φ‖ + |Real.sin t - ‖q‖| ≤ 2*h;change ‖q‖ * ‖cis α-cis φ‖ ≤ 1*h at hn;have hr' : |Real.sin t - ‖q‖| ≤ h := hr _ ht;linarith
end LogLogJam.Supplement.OneObservationProof
open MeasureTheory BosonicLearn Filter
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open scoped Classical ComplexConjugate ENNReal Topology
namespace LogLogJam.Supplement.OneObservationProof
lemma small_mass {q : ℂ} (hq : ‖q‖<1) {ε N : ℝ} (he : 0 < ε) (he1 : ε ≤ 1/3)
    (hN : N^2=Real.sqrt (1-‖q‖^2)) :
    ∃ E : Set XY, MeasurableSet E ∧ (∀ x∈E,‖q-conj (zObs x)‖ ≤ ε*(1-‖q‖)/4) ∧
      ENNReal.ofReal (ε^2/(4608*Real.pi^2)) ≤ ENNReal.ofReal (∫ x in E, ‖(N:ℂ)*(1-q*zObs x)⁻¹‖^2 ∂nu) := by
  let A := 1-‖q‖
  let B := Real.sqrt (1-‖q‖^2)
  let h := ε*A/16
  have hA : 0<A := sub_pos.mpr hq
  have hB : 0<B := Real.sqrt_pos.mpr (by nlinarith [norm_nonneg q])
  obtain ⟨E,hm,hmass,hpoint⟩ := box hq he he1
  change nu E = ENNReal.ofReal (Real.pi⁻¹*(h/B)*((2*Real.pi)⁻¹*h)) at hmass
  have hp (x) (hx : x∈E) : ‖q-conj (zObs x)‖ ≤ ε*A/4 := by have := hpoint x hx;dsimp [A];nlinarith [mul_pos he hA]
  refine ⟨E,hm,hp,?_⟩
  let F (x : XY) := ‖(N:ℂ)*(1-q*zObs x)⁻¹‖^2
  have hden (x) : 0 < ‖1-q*zObs x‖ := by
    have hs := zsmall hq x
    have ht := norm_sub_norm_le (1:ℂ) (q*zObs x)
    rw [norm_one] at ht;linarith
  have hmin (x) : A ≤ ‖1-q*zObs x‖ := by
    have hs : ‖q*zObs x‖ ≤ ‖q‖ := by rw [norm_mul];simpa using mul_le_mul_of_nonneg_left (normZ x) (norm_nonneg q)
    have ht := norm_sub_norm_le (1:ℂ) (q*zObs x)
    rw [norm_one] at ht;dsimp [A];linarith
  have hF (x) : F x = B/‖1-q*zObs x‖^2 := by
    dsimp only [F];rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,hN,inv_pow,div_eq_mul_inv]
  have hFi : Integrable F nu := by
    apply (integrable_const (B/A^2)).mono' (by dsimp [F,zObs];fun_prop)
    filter_upwards with x
    rw [hF,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_left hB.le (sq_pos_of_pos hA)
    nlinarith [mul_self_le_mul_self hA.le (hmin x)]
  have hupper (x) (hx : x∈E) : ‖1-q*zObs x‖ ≤ 3*A := by
    let p := conj (zObs x)
    have h₁ : 1-q*zObs x = (1-q*conj q)+q*conj (q-p) := by dsimp [p];simp only [map_sub,Complex.conj_conj];ring
    rw [h₁];apply (norm_add_le ..).trans
    rw [Complex.mul_conj,← Complex.sq_norm,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by nlinarith [norm_nonneg q]),norm_mul,Complex.norm_conj]
    have h' : ‖q-p‖ ≤ ε*A/4 := hp _ hx
    have h₃ := mul_le_mul_of_nonneg_right hq.le (norm_nonneg (q-p))
    have h₄ := mul_le_mul_of_nonneg_right he1 hA.le
    have h₅ : 1-‖q‖^2 ≤ 2*A := by dsimp [A];nlinarith [sq_nonneg (1-‖q‖)]
    linarith
  have hconst (x) (hx : x∈E) : B/(9*A^2) ≤ F x := by
    rw [hF];apply div_le_div_of_nonneg_left hB.le (sq_pos_of_pos (hden x))
    nlinarith [mul_self_le_mul_self (norm_nonneg _) (hupper x hx)]
  have hmono := integral_mono_ae (μ:=nu.restrict E) (f:=fun _ => B/(9*A^2)) (g:=F)
    (integrable_const _) hFi.integrableOn ((ae_restrict_iff' hm).mpr (ae_of_all _ hconst))
  rw [setIntegral_const,Measure.real,hmass,ENNReal.toReal_ofReal (by positivity),smul_eq_mul] at hmono
  apply ENNReal.ofReal_le_ofReal;apply le_trans _ hmono
  dsimp [h];apply le_of_eq;field_simp;ring
end LogLogJam.Supplement.OneObservationProof
open MeasureTheory BosonicLearn ProbabilityTheory Filter Matrix
open LogLogJam LogLogJam.Supplement
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity)
open scoped Classical ComplexConjugate ENNReal Topology
namespace LogLogJam.Supplement.OneObservationProof
lemma normal (r : ℝ) : (Real.sqrt (Real.cosh r))⁻¹ ^2 = Real.sqrt (1-Real.tanh r^2) := by
  have hc := Real.cosh_pos r
  rw [inv_pow,Real.sq_sqrt hc.le,Real.tanh_eq_sinh_div_cosh]
  have h : 1-(Real.sinh r/Real.cosh r)^2 = (Real.cosh r)⁻¹^2 := by
    field_simp; nlinarith [Real.cosh_sq_sub_sinh_sq r]
  rw [h,Real.sqrt_sq (inv_nonneg.mpr hc.le)]
lemma fock (ρ : State (Occupation (Fin 1))) (r θ : ℝ) (hρ : squeezedAt ρ r θ) :
    ∀ i j, ρ.coefficients i j = psi (point r θ) (Real.sqrt (Real.cosh r))⁻¹ i *
      conj (psi (point r θ) (Real.sqrt (Real.cosh r))⁻¹ j) := by
  obtain ⟨σ,hσ,hc⟩ := squeezed_fock_realization r θ hρ.1
  have eqc := state_ext_characteristic ρ σ (fun ξ => (hρ.2.2 ξ).trans (hσ.2.2 ξ).symm)
  intro i j;rw [eqc,hc]
  simp only [psi,c,deg,point,Complex.star_def]
  ring_nf
theorem one_done :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 3 →
    ∀ m : ℕ, 1 ≤ m →
      ∃ (S : AdaptiveScheme 1 m ℝ)
        (est : Kernel (Fin m → ℝ) (State (Occupation (Fin 1)))),
        (∀ (t : Fin m) (x x' : Fin t → ℝ), S.povm t x = S.povm t x') ∧ IsMarkovKernel est ∧
        ∀ ρ : State (Occupation (Fin 1)), IsPureCentGauss ρ →
          ENNReal.ofReal (c * ε^2) ≤
            ∫⁻ x, est x {σ | IsPureCentGauss σ ∧ traceDist ρ.coefficients σ.coefficients ≤ ENNReal.ofReal ε}
              ∂(transcriptLaw S ρ.coefficients) := by
  obtain ⟨M,hM⟩ := squeezed_disk_readout
  obtain ⟨D,hD,hstate,hcover,-,-⟩ := squeezed_decoder
  let out (x : XY) := D (unpolar (conj (zObs x)))
  have hout : Measurable out := hD.comp (meas_unpolar.comp (Complex.continuous_conj.measurable.comp (by unfold zObs;fun_prop)))
  refine ⟨1/(4608*Real.pi^2),by positivity,?_⟩
  intro ε he he1 m hm
  apply pad M out hout _ _ _ m hm
  intro ρ hρ
  obtain ⟨r,θ,hr,rfl⟩ := hcover ρ hρ
  let q := point r θ
  let N := (Real.sqrt (Real.cosh r))⁻¹
  have hq : ‖q‖<1 := (norm_point r θ hr).trans_lt (Real.tanh_lt_one _)
  have hN : N^2=Real.sqrt (1-‖q‖^2) := by rw [show ‖q‖=Real.tanh r from norm_point _ _ hr];exact normal _
  obtain ⟨E,hmE,hpoint,hmass⟩ := small_mass hq he he1 hN
  refine ⟨E,hmE,?_,?_⟩
  · rw [hM q N hq _ (fock _ r θ (hstate _ _ hr).1) E hmE]
    simpa only [div_eq_inv_mul,mul_one,zObs,nu,arc] using hmass
  · intro x hx
    let p := conj (zObs x)
    have hnear := near_suffices hq he.le he1 (hpoint _ hx)
    have hp : ‖p‖ < 1 := hnear.1
    have hr' : 0 ≤ (unpolar p).1 := Real.artanh_nonneg (norm_nonneg _)
    refine ⟨(hstate _ _ hr').2,?_⟩
    change traceDist (D (r,θ)).coefficients (D (unpolar p)).coefficients ≤ _
    rw [disk_born _ _ _ _ _ _ hr hr' (hstate _ _ hr).1 (hstate _ _ hr').1, inv_unpolar _ hp]
    exact ENNReal.ofReal_le_ofReal hnear.2
end LogLogJam.Supplement.OneObservationProof

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 3 →
    ∀ m : ℕ, 1 ≤ m →
      ∃ (S : BosonicLearn.AdaptiveScheme 1 m ℝ)
        (est : Kernel (Fin m → ℝ) (State (Occupation (Fin 1)))),
        (∀ (t : Fin m) (x x' : Fin t → ℝ), S.povm t x = S.povm t x') ∧
        IsMarkovKernel est ∧
        ∀ ρ : State (Occupation (Fin 1)), IsPureCentGauss ρ →
          ENNReal.ofReal (c * ε^2) ≤
            ∫⁻ x, est x {σ | IsPureCentGauss σ ∧
                BosonicLearn.traceDist ρ.coefficients σ.coefficients ≤ ENNReal.ofReal ε}
              ∂(BosonicLearn.transcriptLaw S ρ.coefficients) := LogLogJam.Supplement.OneObservationProof.one_done
