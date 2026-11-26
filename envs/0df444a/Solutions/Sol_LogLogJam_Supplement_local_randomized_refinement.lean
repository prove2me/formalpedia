-- Prove2me | solution 1 for LogLogJam.Supplement.local_randomized_refinement
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T19:28:12.877057+00:00
-- url     : https://prove2.me/submissions/f3293b3b-3304-446b-bc2d-bd2fc7d0b59d

import Mathlib
import Theorems.Thm_BosonicLearn_state_ext_characteristic
import Theorems.Thm_LogLogJam_Supplement_squeezed_decoder
import Theorems.Thm_LogLogJam_Supplement_squeezed_fock_realization
import Theorems.Thm_LogLogJam_Supplement_squeezed_trace_distance
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
open MeasureTheory BosonicLearn Filter Matrix
open LogLogJam LogLogJam.Supplement
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open scoped Classical ComplexConjugate ENNReal
namespace LogLogJam.Supplement.WeakProof
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
end LogLogJam.Supplement.WeakProof
open MeasureTheory BosonicLearn Filter Matrix
open LogLogJam LogLogJam.Supplement
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open scoped Classical ComplexConjugate ENNReal
namespace LogLogJam.Supplement.WeakProof
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
lemma rel_upper {q p : ℂ} (hq : ‖q‖<1) (hp : ‖p‖<1) {d : ℝ} (hd : 0 ≤ d) (hsmall : d  ≤  1/3)
    (h : diskDist q p  ≤  d) : rel q p  ≤  4*d^2 := by
  have hrel := rel_nonneg hq hp
  let F := Real.sqrt (1+rel q p)
  have hF : 1 ≤ F := by apply Real.one_le_sqrt.mpr;linarith
  have hFs : F^2=1+rel q p := Real.sq_sqrt (by linarith)
  have h0 : 0<F := by linarith
  have hD : 0  ≤  diskDist q p := Real.sqrt_nonneg _
  have hs := sq_dist hq hp
  change _ = 1-1/F at hs
  have hm := mul_le_mul h h hD hd
  have h₁ : (1-d^2)*F  ≤  1 := by
    rw [← le_div_iff₀ h0];nlinarith
  have h₂ : F  ≤  3/2 := by
    have he : 1-d^2  ≥  8/9 := by nlinarith [mul_nonneg hd (sub_nonneg.mpr hsmall)]
    nlinarith [mul_le_mul_of_nonneg_right he h0.le]
  have h₃ : F-1  ≤  3/2*d^2 := by nlinarith [mul_le_mul_of_nonneg_right h₂ (sq_nonneg d)]
  have h₄ := mul_le_mul h₃ (show F+1  ≤  5/2 by linarith) (show 0 ≤ F+1 by linarith) (show 0 ≤ 3/2*d^2 by positivity)
  nlinarith [sq_nonneg d]

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
lemma near_necessary {q p : ℂ} (hq : ‖q‖<1) (hp : ‖p‖<1) {d : ℝ} (hd : 0 ≤ d) (hsmall : d ≤ 1/3)
    (h : diskDist q p  ≤  d) : ‖q-p‖  ≤  8*d*(1-‖q‖) := by
  let A := 1-‖q‖
  let B := 1-‖p‖
  let u := ‖q-p‖
  have hA : 0<A := sub_pos.mpr hq
  have hB : 0<B := sub_pos.mpr hp
  have hu : 0 ≤ u := norm_nonneg _
  have hBA : B ≤ A+u := by dsimp [A,B,u];linarith [norm_sub_norm_le q p]
  have ht := (div_le_iff₀ (mul_pos (pgap hq) (pgap hp))).mp (rel_upper hq hp hd hsmall h)
  have hg := mul_le_mul (gap_hi q) (gap_hi p) (pgap hp).le (by change 0 ≤ 2*A;positivity)
  change gap q * gap p  ≤  2*A*(2*B) at hg
  have hs : u^2  ≤  16*d^2*A*(A+u) := by
    have hg' := mul_le_mul_of_nonneg_left hg (show 0 ≤ 4*d^2 by positivity)
    have hb' := mul_le_mul_of_nonneg_left hBA (show 0 ≤ 16*d^2*A by positivity)
    dsimp only [u];nlinarith only [ht,hg',hb']
  change u ≤ 8*d*A
  by_contra! hf
  have h1 := mul_self_lt_mul_self (by positivity : 0 ≤ 8*d*A) hf
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf.le hd) hu
  have h3 := mul_le_mul_of_nonneg_left hsmall (sq_nonneg u)
  nlinarith only [h1,h2,h3,hs]
end LogLogJam.Supplement.WeakProof
open MeasureTheory BosonicLearn Filter Matrix
open LogLogJam LogLogJam.Supplement
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State NuclearExpansion traceSize)
open scoped Classical ComplexConjugate ENNReal Topology
namespace LogLogJam.Supplement.WeakProof
lemma coefficient_bound {I : Type} (A : Matrix I I ℂ) (i j : I) :
    ENNReal.ofReal ‖A i j‖ ≤ traceSize A := by
  apply le_iInf; intro e
  apply ENNReal.ofReal_le_ofReal
  let f := fun n : ℕ => e.left n i * star (e.right n j)
  have hdom (n : ℕ) : ‖f n‖ ≤ ‖e.left n‖ * ‖e.right n‖ := by
    rw [show ‖f n‖ = ‖e.left n i‖ * ‖e.right n j‖ by simp [f,norm_mul]]
    exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) _ _) (lp.norm_apply_le_norm (by norm_num) _ _) (norm_nonneg _) (norm_nonneg _)
  have hs := e.summable.of_nonneg_of_le (fun n => norm_nonneg (f n)) hdom
  rw [e.coefficients]
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hdom e.summable)
lemma coeff_cont {I : Type} (i j : I) : Continuous (fun ρ : State I => ρ.coefficients i j) := by
  apply continuous_iff_continuousAt.mpr;intro ρ
  apply Metric.tendsto_nhds.mpr;intro ε he
  let U := {σ : State I | traceSize (σ.coefficients-ρ.coefficients) < ENNReal.ofReal ε}
  have hu : IsOpen U := TopologicalSpace.isOpen_generateFrom_of_mem ⟨ρ,ε,he,rfl⟩
  have hz : traceSize ((ρ.coefficients)-(ρ.coefficients)) = 0 := by
    rw [sub_self]
    let e : NuclearExpansion (0 : Matrix I I ℂ) := {left := fun _ => 0, right := fun _ => 0, summable := by simp, coefficients := by simp}
    apply le_antisymm _ bot_le
    refine (iInf_le _ e).trans ?_;simp [e]
  have hx : ρ∈U := by change traceSize _ < _;rw [hz];exact ENNReal.ofReal_pos.mpr he
  filter_upwards [hu.mem_nhds hx] with σ hσ
  change traceSize (σ.coefficients-ρ.coefficients) < ENNReal.ofReal ε at hσ
  rw [dist_eq_norm]
  apply lt_of_not_ge;intro hbad
  exact (not_lt_of_ge ((ENNReal.ofReal_le_ofReal hbad).trans (coefficient_bound (σ.coefficients-ρ.coefficients) i j))) hσ
def index (k : ℕ) : Occupation (Fin 1) := fun _ => k
def encode (ρ : State (Occupation (Fin 1))) : ℂ := 2*(ρ.coefficients (index 2) (index 0)) /
  ((Real.sqrt 2 : ℂ)*ρ.coefficients (index 0) (index 0))
lemma meas_encode : Measurable encode := by
  let _ : BorelSpace (State (Occupation (Fin 1))) := ⟨rfl⟩
  unfold encode
  exact (measurable_const.mul (coeff_cont _ _).measurable).div (measurable_const.mul (coeff_cont _ _).measurable)
lemma encoding (ρ : State (Occupation (Fin 1))) (r θ : ℝ) (hρ : squeezedAt ρ r θ) : encode ρ = point r θ := by
  obtain ⟨σ,hσ,hc⟩ := squeezed_fock_realization r θ hρ.1
  have e := state_ext_characteristic ρ σ (fun ξ => (hρ.2.2 ξ).trans (hσ.2.2 ξ).symm)
  simp only [encode,e,hc,index,show Even 0 by decide,show Even 2 by decide,if_true, Nat.reduceDiv,Nat.centralBinom_zero,show Nat.centralBinom 1 = 2 by decide,point,pow_zero,pow_one,Nat.cast_one,Nat.cast_ofNat,Real.sqrt_one,mul_one,one_mul,Complex.star_def,map_mul,Complex.conj_ofReal,map_one]
  push_cast
  field_simp [show (Real.sqrt (Real.cosh r) : ℂ)≠0 by exact_mod_cast (Real.sqrt_pos.mpr (Real.cosh_pos _)).ne', show (Real.sqrt 2 : ℂ) ≠ 0 by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : 0 < (2:ℝ))).ne'] <;> ring
def unpolar (q : ℂ) : ℝ × ℝ := (Real.artanh ‖q‖,q.arg/2)
lemma meas_unpolar : Measurable unpolar := by unfold unpolar Real.artanh;fun_prop
lemma inv_unpolar (q : ℂ) (hq : ‖q‖<1) : point (unpolar q).1 (unpolar q).2 = q := by
  dsimp only [unpolar,point]; rw [Real.tanh_artanh ⟨by linarith [norm_nonneg q],hq⟩,show 2*(q.arg/2)=q.arg by ring,Complex.norm_mul_exp_arg_mul_I]
end LogLogJam.Supplement.WeakProof
open MeasureTheory BosonicLearn ProbabilityTheory Filter Matrix
open LogLogJam LogLogJam.Supplement
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open scoped Classical ComplexConjugate ENNReal Topology
namespace LogLogJam.Supplement.WeakProof
def unitLaw : Measure ℂ := (NNReal.pi : ℝ≥0∞)⁻¹ • volume.restrict (Metric.ball (0:ℂ) 1)
instance unitProb : IsProbabilityMeasure unitLaw := by
  constructor;simp [unitLaw,Measure.smul_apply];exact ENNReal.inv_mul_cancel (by exact_mod_cast NNReal.pi_pos.ne') ENNReal.coe_ne_top
lemma unit_ball (v : ℂ) (s : ℝ) (hs : 0 ≤ s) (h : ‖v‖+s ≤ 1) :
    unitLaw (Metric.ball v s) = ENNReal.ofReal (s^2) := by
  have hsub : Metric.ball v s ⊆ Metric.ball (0:ℂ) 1 := by
    intro w hw;rw [Metric.mem_ball,dist_zero_right]
    rw [Metric.mem_ball,dist_eq_norm] at hw
    have h' := norm_sub_norm_le w v
    linarith
  rw [unitLaw,Measure.smul_apply,Measure.restrict_apply Metric.isOpen_ball.measurableSet,Set.inter_eq_left.mpr hsub,Complex.volume_ball,ENNReal.ofReal_pow hs]
  rw [smul_eq_mul,mul_left_comm,ENNReal.inv_mul_cancel (by exact_mod_cast NNReal.pi_pos.ne') ENNReal.coe_ne_top,mul_one]
def sampled {A B X : Type} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (f : A × X → B) (hf : Measurable f) : Kernel A B where
  toFun a := μ.map (fun x => f (a,x))
  measurable' := by
    apply Measure.measurable_of_measurable_coe;intro s hs
    have hmap (a : A) : (μ.map (fun x => f (a,x))) s = μ ((fun x => (a,x)) ⁻¹' (f ⁻¹' s)) :=
      Measure.map_apply (hf.comp (measurable_const.prodMk measurable_id)) hs
    simp_rw [hmap];exact measurable_measure_prodMk_left (hf hs)
instance sampled_markov {A B X : Type} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : A × X → B) (hf : Measurable f) : IsMarkovKernel (sampled μ f hf) :=
  ⟨fun a => Measure.isProbabilityMeasure_map (hf.comp (measurable_const.prodMk measurable_id)).aemeasurable⟩
lemma distsymm (q p : ℂ) : diskDist q p = diskDist p q := by simp only [diskDist,rel,norm_sub_rev q p,mul_comm (gap q) (gap p)]
theorem refined :
    ∃ a > (0 : ℝ), ∀ ε d : ℝ, 0 < ε → ε ≤ d → d ≤ 1 / 3 →
      ∃ L : Kernel (State (Occupation (Fin 1))) (State (Occupation (Fin 1))),
        IsMarkovKernel L ∧ ∀ σ ρ : State (Occupation (Fin 1)), IsPureCentGauss σ → IsPureCentGauss ρ →
          traceDist ρ.coefficients σ.coefficients ≤ ENNReal.ofReal d →
          ENNReal.ofReal (a * (ε/d)^2) ≤ L σ {τ | IsPureCentGauss τ ∧
            traceDist ρ.coefficients τ.coefficients ≤ ENNReal.ofReal ε} := by
  obtain ⟨D,hD,hstate,hcover,-,-⟩ := squeezed_decoder
  refine ⟨1/256^2,by norm_num,?_⟩
  intro ε d he hed hsmall
  have hd := he.trans_le hed
  let R (z : ℂ) := 16*d*(1-‖z‖)
  let move (p : State (Occupation (Fin 1)) × ℂ) := encode p.1 + (R (encode p.1) : ℂ)*p.2
  have hm : Measurable move := by
    unfold move R
    have h : Measurable (fun p : State (Occupation (Fin 1)) × ℂ => encode p.1) := meas_encode.comp measurable_fst
    fun_prop
  let f (p : State (Occupation (Fin 1)) × ℂ) := D (unpolar (move p))
  have hf : Measurable f := hD.comp (meas_unpolar.comp hm)
  refine ⟨sampled unitLaw f hf, inferInstance,?_⟩
  intro σ ρ hσ hρ hdist
  obtain ⟨r,θ,hr,rfl⟩ := hcover ρ hρ
  obtain ⟨s,φ,hs,rfl⟩ := hcover σ hσ
  let q := point r θ
  let z := point s φ
  have hq : ‖q‖<1 := (norm_point r θ hr).trans_lt (Real.tanh_lt_one _)
  have hz : ‖z‖<1 := (norm_point s φ hs).trans_lt (Real.tanh_lt_one _)
  have hqz : diskDist q z ≤ d := by
    rw [disk_born _ _ _ _ _ _ hr hs (hstate _ _ hr).1 (hstate _ _ hs).1] at hdist
    exact (ENNReal.ofReal_le_ofReal_iff hd.le).mp hdist
  have hu := near_necessary hq hz hd.le hsmall hqz
  have hv := near_necessary hz hq hd.le hsmall (by rwa [distsymm])
  have hcomp : 1-‖z‖ ≤ 4*(1-‖q‖) := by
    have h1 := norm_sub_norm_le q z
    have h2 := mul_le_mul_of_nonneg_right hsmall (sub_nonneg.mpr hq.le)
    linarith
  let T := (q-z)/(R z : ℂ)
  let k := ε/(256*d)
  have hR : 0<R z := by dsimp [R];positivity [sub_pos.mpr hz]
  have hk : 0<k := by dsimp [k];positivity
  have hk' : k ≤ 1/256 := by apply (div_le_iff₀ (by positivity)).mpr;linarith
  have hT : ‖T‖ ≤ 1/2 := by
    dsimp [T];rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR];apply (div_le_iff₀ hR).mpr
    rw [norm_sub_rev];dsimp [R];linarith
  let S := {τ : State (Occupation (Fin 1)) | IsPureCentGauss τ ∧ traceDist (D (r,θ)).coefficients τ.coefficients ≤ ENNReal.ofReal ε}
  have hsmallball : Metric.ball T k ⊆ (fun x => f (D (s,φ),x)) ⁻¹' S := by
    intro x hx
    rw [Metric.mem_ball,dist_eq_norm] at hx
    let p := move (D (s,φ),x)
    have hez : encode (D (s,φ)) = z := encoding _ s φ (hstate _ _ hs).1
    have hpq : p-q = (R z : ℂ)*(x-T) := by
      dsimp [p,move,T];rw [hez];field_simp [show (R z : ℂ) ≠ 0 by exact_mod_cast hR.ne'];ring
    have hle : ‖q-p‖ ≤ ε*(1-‖q‖)/4 := by
      rw [norm_sub_rev,hpq,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
      apply (mul_le_mul_of_nonneg_left hx.le hR.le).trans
      dsimp [R,k];field_simp; nlinarith [mul_le_mul_of_nonneg_left hcomp he.le]
    obtain ⟨hp,hdist'⟩ := near_suffices hq he.le (hed.trans hsmall) hle
    have hr' : 0 ≤ (unpolar p).1 := Real.artanh_nonneg (norm_nonneg _)
    refine ⟨(hstate _ _ hr').2,?_⟩
    change traceDist (D (r,θ)).coefficients (D (unpolar p)).coefficients ≤ _
    rw [disk_born _ _ r θ (unpolar p).1 (unpolar p).2 hr hr' (hstate _ _ hr).1 (hstate _ _ hr').1,inv_unpolar _ hp]
    exact ENNReal.ofReal_le_ofReal hdist'
  change _ ≤ (unitLaw.map (fun x => f (D (s,φ),x))) S
  refine le_trans ?_ ((measure_mono hsmallball).trans (Measure.le_map_apply (hf.comp (measurable_const.prodMk measurable_id)).aemeasurable S))
  rw [unit_ball _ _ hk.le (by linarith)]
  apply ENNReal.ofReal_le_ofReal;dsimp [k];ring_nf;exact le_rfl
end LogLogJam.Supplement.WeakProof

theorem solution :
    ∃ a > (0 : ℝ), ∀ ε d : ℝ, 0 < ε → ε ≤ d → d ≤ 1 / 3 →
      ∃ L : Kernel (State (Occupation (Fin 1))) (State (Occupation (Fin 1))),
        IsMarkovKernel L ∧ ∀ σ ρ : State (Occupation (Fin 1)), IsPureCentGauss σ → IsPureCentGauss ρ →
          BosonicLearn.traceDist ρ.coefficients σ.coefficients ≤ ENNReal.ofReal d →
          ENNReal.ofReal (a * (ε/d)^2) ≤ L σ {τ | IsPureCentGauss τ ∧
            BosonicLearn.traceDist ρ.coefficients τ.coefficients ≤ ENNReal.ofReal ε} := LogLogJam.Supplement.WeakProof.refined
