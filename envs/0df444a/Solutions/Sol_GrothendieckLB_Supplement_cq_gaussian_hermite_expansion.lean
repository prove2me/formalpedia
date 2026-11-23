-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_gaussian_hermite_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T18:35:02.954486+00:00
-- url     : https://prove2.me/submissions/9cfb486e-78df-43ad-82cd-aa891e19556a

import Definitions.Def_QuadSDE_GaussHermite
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_9
import Definitions.Def_KrivineSchemeDefs
import Definitions.Def_GrothendieckLB_Supplement_cqCorr
import Definitions.Def_GrothendieckLB_Supplement_cqA
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Ring.InfiniteSum
namespace GaussianHermiteNorm
open Real Set Polynomial MeasureTheory ProbabilityTheory Filter
open scoped Topology
private noncomputable def weight (x : ℝ) := exp (-(x^2)/2)
private noncomputable def herm (n : ℕ) (x : ℝ) : ℝ := aeval x (hermite n)
private noncomputable def hg (n : ℕ) (x : ℝ) : ℝ := herm n x*weight x
private theorem poly_integrable (p : ℤ[X]) :
    Integrable fun x : ℝ => aeval x p * weight x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hi : Integrable (fun x : ℝ => aeval x p * weight x + aeval x q * weight x) := hp.add hq
    simpa only [map_add,add_mul] using hi
  | monomial n a =>
    have h : Integrable fun x : ℝ => x^n * exp (-(1/2:ℝ)*x^2) := by
      simpa only [rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
        (lt_of_lt_of_le (by norm_num : (-1:ℝ)<0) (Nat.cast_nonneg n))
    convert h.const_mul ((algebraMap ℤ ℝ) a) using 1
    ext x
    rw [aeval_monomial]
    dsimp only [weight]
    ring_nf


private theorem deriv_hg (n : ℕ) (x : ℝ) : HasDerivAt (hg n) (-hg (n+1) x) x := by
  have hw : HasDerivAt weight ((-x)*weight x) x := by
    apply ((((hasDerivAt_pow 2 x).neg).div_const 2).exp).congr_deriv
    dsimp [weight]
    ring
  apply (((hermite n).hasDerivAt_aeval x).mul hw).congr_deriv
  simp only [hg,herm,hermite_succ,map_sub,map_mul,aeval_X]
  ring


private theorem dh (n : ℕ) : derivative (hermite (n+1)) = C ((n+1:ℕ):ℤ)*hermite n := by
  induction n with
  | zero => simp [hermite_succ,hermite_zero]
  | succ n ih =>
    rw [hermite_succ (n+1),ih,derivative_sub,derivative_mul,derivative_X,
      derivative_mul,derivative_C,zero_mul,zero_add,one_mul,ih]
    rw [hermite_succ n]
    push_cast
    simp only [map_add,map_one]
    ring


private theorem deriv_herm (n : ℕ) (x : ℝ) :
    HasDerivAt (herm (n+1)) (((n:ℝ)+1)*herm n x) x := by
  have h := Polynomial.hasDerivAt_aeval (hermite (n+1)) x
  rw [dh] at h
  change HasDerivAt (fun z : ℝ => aeval z (hermite (n+1))) _ x
  simpa only [map_mul,aeval_C,Nat.cast_succ,Nat.cast_add,Nat.cast_one,map_add,map_one,map_natCast,herm] using h

private theorem sq_int (n : ℕ) : Integrable (fun x : ℝ => (herm n x)^2*weight x) := by
  convert poly_integrable ((hermite n)^2) using 1
  ext x
  simp [herm]

private theorem weighted_norm (n : ℕ) :
    (∫ x : ℝ, (herm n x)^2*weight x)=(n.factorial:ℝ)*(∫ x : ℝ, weight x) := by
  induction n with
  | zero => simp [herm,hermite_zero]
  | succ n ih =>
    let f := fun x : ℝ => herm (n+1) x*hg n x
    let d := fun x : ℝ => ((n:ℝ)+1)*((herm n x)^2*weight x)-(herm (n+1) x)^2*weight x
    have hd (x : ℝ) : HasDerivAt f (d x) x := by
      apply ((deriv_herm n x).mul (deriv_hg n x)).congr_deriv
      dsimp [d,hg]
      ring
    have hf : Integrable f := by
      simpa only [f,hg,herm,map_mul,mul_assoc] using poly_integrable (hermite (n+1)*hermite n)
    have hdint : Integrable d := ((sq_int n).const_mul ((n:ℝ)+1)).sub (sq_int (n+1))
    have h := integral_eq_zero_of_hasDerivAt_of_integrable hd hdint hf
    change ∫ x : ℝ, ((n:ℝ)+1)*((herm n x)^2*weight x)-(herm (n+1) x)^2*weight x = 0 at h
    rw [integral_sub ((sq_int n).const_mul _) (sq_int (n+1)),integral_const_mul,ih] at h
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
    linarith only [h]

theorem weighted (n : ℕ) :
    Integrable (fun x : ℝ => QuadSDE.hermiteN n x*gaussianPDFReal 0 1 x) ∧
    (∫ x : ℝ, (QuadSDE.hermiteN n x)^2*gaussianPDFReal 0 1 x)=1 ∧
    (∫ x : ℝ, |QuadSDE.hermiteN n x| *gaussianPDFReal 0 1 x) ≤ 1 := by
  let d : ℝ := (Real.sqrt (2*Real.pi))⁻¹
  let k : ℝ := Real.sqrt (n.factorial:ℝ)
  have hk : k^2=(n.factorial:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hk0 : k ≠ 0 := by dsimp [k]; positivity
  have hpdf (x : ℝ) : gaussianPDFReal 0 1 x = d*weight x := by simp [gaussianPDFReal,d,weight]
  have hfirst (x : ℝ) : QuadSDE.hermiteN n x*gaussianPDFReal 0 1 x = (d/k)*(herm n x*weight x) := by
    rw [hpdf]; change (herm n x/k)*(d*weight x)=_; ring
  have hsec (x : ℝ) : (QuadSDE.hermiteN n x)^2*gaussianPDFReal 0 1 x =
      (d/(n.factorial:ℝ))*((herm n x)^2*weight x) := by
    rw [hpdf]; change (herm n x/k)^2*(d*weight x)=_; rw [div_pow,hk]; ring
  have h1 : Integrable (fun x : ℝ => QuadSDE.hermiteN n x*gaussianPDFReal 0 1 x) := by
    simp_rw [hfirst]
    exact (poly_integrable (hermite n)).const_mul _
  have h2 : Integrable (fun x : ℝ => (QuadSDE.hermiteN n x)^2*gaussianPDFReal 0 1 x) := by
    simp_rw [hsec]
    exact (sq_int n).const_mul _
  have hnorm := integral_gaussianPDFReal_eq_one 0 (v:=1) (by norm_num)
  have hpdfint : d*(∫ x : ℝ, weight x)=1 := by
    simpa only [hpdf,integral_const_mul] using hnorm
  have h2val : (∫ x : ℝ, (QuadSDE.hermiteN n x)^2*gaussianPDFReal 0 1 x)=1 := by
    simp_rw [hsec]
    rw [integral_const_mul,weighted_norm]
    calc _ = d*(∫ x : ℝ, weight x) := by field_simp
         _ = 1 := hpdfint
  refine ⟨h1,h2val,?_⟩
  have h1abs : Integrable (fun x : ℝ => |QuadSDE.hermiteN n x| *gaussianPDFReal 0 1 x) := by
    simpa only [abs_mul,abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)] using h1.abs
  have hi := integral_mono (h1abs.const_mul 2) ((integrable_gaussianPDFReal 0 1).add h2)
      (fun x => by
        change 2*(|QuadSDE.hermiteN n x| *gaussianPDFReal 0 1 x) ≤
          gaussianPDFReal 0 1 x+(QuadSDE.hermiteN n x)^2*gaussianPDFReal 0 1 x
        have hsq := sq_nonneg (|QuadSDE.hermiteN n x|-1)
        have hadd : 2*|QuadSDE.hermiteN n x| ≤ 1+(QuadSDE.hermiteN n x)^2 := by
          nlinarith only [hsq,sq_abs (QuadSDE.hermiteN n x)]
        simpa only [mul_assoc,add_mul,one_mul] using
          mul_le_mul_of_nonneg_right hadd (gaussianPDFReal_nonneg _ _ _))
  change (∫ x : ℝ, 2*(|QuadSDE.hermiteN n x| *gaussianPDFReal 0 1 x)) ≤
    ∫ x : ℝ, gaussianPDFReal 0 1 x+(QuadSDE.hermiteN n x)^2*gaussianPDFReal 0 1 x at hi
  rw [integral_const_mul,integral_add (integrable_gaussianPDFReal 0 1) h2,hnorm,h2val] at hi
  linarith only [hi]
end GaussianHermiteNorm
namespace GaussianDensitySeries

open Polynomial Finset Real MeasureTheory ProbabilityTheory
open PrivateAgnosticHalfspace.Gaussian

private theorem herm_compat (n : ℕ) (x : ℝ) : AMPLowDeg.RankOne.hermNorm n x = QuadSDE.hermiteN n x := by
  unfold AMPLowDeg.RankOne.hermNorm QuadSDE.hermiteN
  rw [eval_map]
  rfl

private theorem scalar_mehler (r x y : ℝ) (hr : |r| < 1) :
    HasSum (fun n : ℕ => r^n * QuadSDE.hermiteN n x * QuadSDE.hermiteN n y)
      ((1-r^2)^(-(1:ℝ)/2) * exp ((2*r*x*y-r^2*(x^2+y^2))/(2*(1-r^2)))) := by
  let X : Vec 1 := WithLp.toLp 2 (fun _ => x)
  let Y : Vec 1 := WithLp.toLp 2 (fun _ => y)
  have hm := lemma_B_9 1 X Y r (abs_lt.mp hr)
  let e := (Equiv.funUnique (Fin 1) ℕ).symm
  have h := e.hasSum_iff.mpr hm
  have e0 (n : ℕ) : e n 0 = n := rfl
  have hnX : ‖X‖^2=x^2 := by simp [X,EuclideanSpace.norm_sq_eq,Fin.sum_univ_one,Real.norm_eq_abs]
  have hnY : ‖Y‖^2=y^2 := by simp [Y,EuclideanSpace.norm_sq_eq,Fin.sum_univ_one,Real.norm_eq_abs]
  have hxy : inner ℝ X Y = x*y := by simp [PiLp.inner_apply,X,Y,Fin.sum_univ_one,Real.inner_apply,mul_comm]
  rw [hxy,hnX,hnY] at h
  simpa only [Function.comp_def,PrivateAgnosticHalfspace.Gaussian.hermite,PrivateAgnosticHalfspace.Gaussian.degree,Fin.sum_univ_one,Fin.prod_univ_one,e0,
    X,Y,WithLp.ofLp_toLp,herm_compat,Nat.cast_one,mul_assoc] using h

private theorem density_factor (r x y : ℝ) (hr : |r| < 1) :
    ((1-r^2)^(-(1:ℝ)/2)*exp ((2*r*x*y-r^2*(x^2+y^2))/(2*(1-r^2)))) *
      (gaussianPDFReal 0 1 x * gaussianPDFReal 0 1 y) =
    GrothendieckConstant.gaussianPairDensity 1 r (fun _ => x) (fun _ => y) := by
  have h1 := abs_lt.mp hr
  have hd : 0 < 1-r^2 := by nlinarith only [mul_pos (sub_pos.mpr h1.2) (by linarith only [h1.1] : 0 < 1+r)]
  let d : ℝ := Real.sqrt (2*Real.pi)
  have hpdf (z : ℝ) : gaussianPDFReal 0 1 z = d⁻¹*exp (-(z^2)/2) := by simp [gaussianPDFReal,d]
  have hsq : d*d=2*Real.pi := by simpa only [←pow_two] using Real.sq_sqrt (by positivity : 0≤2*Real.pi)
  have hc : d ≠ 0 := by dsimp [d]; positivity
  have hh : Real.sqrt (1-r^2) ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  rw [show -(1:ℝ)/2=-(1/2) by ring,Real.rpow_neg hd.le,← Real.sqrt_eq_rpow,hpdf,hpdf]
  simp only [GrothendieckConstant.gaussianPairDensity, Fin.prod_univ_one]
  have he : (2*r*x*y-r^2*(x^2+y^2))/(2*(1-r^2)) + (-(x^2)/2) + (-(y^2)/2) =
      -(x^2-2*r*x*y+y^2)/(2*(1-r^2)) := by field_simp [hd.ne'] <;> ring
  rw [←he,exp_add,exp_add]
  field_simp [hc,hh,Real.pi_ne_zero]
  nlinarith only [hsq]

theorem mehler (r x y : ℝ) (hr : |r| < 1) :
    HasSum (fun n : ℕ => r^n*QuadSDE.hermiteN n x*QuadSDE.hermiteN n y*
      (gaussianPDFReal 0 1 x*gaussianPDFReal 0 1 y))
      (GrothendieckConstant.gaussianPairDensity 1 r (fun _ => x) (fun _ => y)) := by
  rw [←density_factor r x y hr]
  exact (scalar_mehler r x y hr).mul_right _
end GaussianDensitySeries
open MeasureTheory ProbabilityTheory Real GrothendieckLB.Supplement
open ENNReal NNReal
open scoped ENNReal
set_option maxHeartbeats 500000
namespace CorrelationSeries

private abbrev E := ℝ × ℝ
private noncomputable def h (n : ℕ) (x : ℝ) := QuadSDE.hermiteN n x * gaussianPDFReal 0 1 x
private noncomputable def B (f : E → ℝ) (p : ℕ × ℕ) (z : E) := f z * (h p.1 z.1 * h p.2 z.2)
private noncomputable def K (r x y : ℝ) := GrothendieckConstant.gaussianPairDensity 1 r (fun _ => x) (fun _ => y)

private theorem h_meas (n : ℕ) : Measurable (h n) := by
  unfold h QuadSDE.hermiteN
  exact (((Polynomial.hermite n).continuous_aeval.div_const _).measurable).mul (measurable_gaussianPDFReal _ _)

private theorem h_int (n : ℕ) : Integrable (h n) := (GaussianHermiteNorm.weighted n).1
private theorem h_norm (n : ℕ) : (∫ x, ‖h n x‖) ≤ 1 := by
  simpa only [h,Real.norm_eq_abs,abs_mul,abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)] using
    (GaussianHermiteNorm.weighted n).2.2

private theorem B_bound {f : E → ℝ} (hf : ∀ z, ‖f z‖ ≤ 1) (p : ℕ × ℕ) (z : E) :
    ‖B f p z‖ ≤ ‖h p.1 z.1‖ * ‖h p.2 z.2‖ := by
  rw [B,norm_mul,norm_mul]
  exact mul_le_of_le_one_left (by positivity) (hf z)

private theorem B_int {f : E → ℝ} (hm : Measurable f) (hf : ∀ z, ‖f z‖ ≤ 1) (p : ℕ × ℕ) :
    Integrable (B f p) := by
  apply ((h_int p.1).norm.mul_prod (h_int p.2).norm).mono'
  · exact (hm.mul (((h_meas _).comp measurable_fst).mul ((h_meas _).comp measurable_snd))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (B_bound hf p)

private theorem B_norm {f : E → ℝ} (hm : Measurable f) (hf : ∀ z, ‖f z‖ ≤ 1) (p : ℕ × ℕ) :
    (∫ z, ‖B f p z‖) ≤ 1 := by
  calc _ ≤ ∫ z : E, ‖h p.1 z.1‖ * ‖h p.2 z.2‖ :=
         integral_mono (B_int hm hf p).norm ((h_int _).norm.mul_prod (h_int _).norm) (B_bound hf p)
       _ = (∫ x : ℝ, ‖h p.1 x‖) * (∫ x : ℝ, ‖h p.2 x‖) := integral_prod_mul (μ:=volume) (ν:=volume) (fun x : ℝ => ‖h p.1 x‖) (fun x : ℝ => ‖h p.2 x‖)
       _ ≤ 1 := mul_le_one₀ (h_norm _) (integral_nonneg (fun _ => norm_nonneg _)) (h_norm _)

private theorem pair_series {r : ℝ} (hr : |r| < 1) (x y : ℝ) :
    HasSum (fun n : ℕ => r^n * h n x * h n y) (K r x y) := by
  unfold K
  convert GaussianDensitySeries.mehler r x y hr using 1
  funext n
  unfold h
  ring

private theorem double_series {r t : ℝ} (hr : |r| < 1) (ht : |t| < 1) (x y : E) :
    HasSum (fun p : ℕ × ℕ => (r^p.1*h p.1 x.1*h p.1 y.1)*(t^p.2*h p.2 x.2*h p.2 y.2))
      (K r x.1 y.1 * K t x.2 y.2) := by
  have ha := pair_series hr x.1 y.1
  have hb := pair_series ht x.2 y.2
  have ha2 : Summable (fun n : ℕ => ‖r^n*h n x.1*h n y.1‖) := summable_norm_iff.mpr ha.summable
  have hb2 : Summable (fun n : ℕ => ‖t^n*h n x.2*h n y.2‖) := summable_norm_iff.mpr hb.summable
  exact ha.mul hb (summable_mul_of_summable_norm ha2 hb2)

private theorem integrate_series {ι X : Type*} [Countable ι] [MeasurableSpace X]
    {μ : Measure X} {F : ι → X → ℝ} {G : X → ℝ} (hG : Measurable G)
    (hi : ∀ i, Integrable (F i) μ) (hs : Summable (fun i => ∫ x, ‖F i x‖ ∂μ))
    (hp : ∀ x, HasSum (fun i => F i x) (G x)) :
    Integrable G μ ∧ HasSum (fun i => ∫ x, F i x ∂μ) (∫ x, G x ∂μ) := by
  have he (i : ι) : (∫⁻ x, ‖F i x‖ₑ ∂μ) = ‖∫ x, ‖F i x‖ ∂μ‖ₑ := by
    rw [show (fun x => ‖F i x‖ₑ) = (fun x => ENNReal.ofReal ‖F i x‖) by funext x; exact (ofReal_norm (F i x)).symm]
    rw [← ofReal_integral_eq_lintegral_ofReal (hi i).norm (Filter.Eventually.of_forall fun x => norm_nonneg _)]
    rw [← ofReal_norm,Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (F i x))]
  have hefin : (∑' i, ∫⁻ x, ‖F i x‖ₑ ∂μ) ≠ ∞ := by
    simp_rw [he]
    exact tsum_enorm_ne_top_iff_summable_norm.mpr (summable_norm_iff.mpr hs)
  have hfint : HasFiniteIntegral G μ := by
    refine lt_of_le_of_lt (lintegral_mono (g:=fun x => ∑' i, ‖F i x‖ₑ) (fun x => ?_)) ?_
    · rw [←(hp x).tsum_eq]
      exact enorm_tsum_le_tsum_enorm
    · rw [lintegral_tsum (fun i => (hi i).aestronglyMeasurable.enorm)]
      exact lt_top_iff_ne_top.mpr hefin
  refine ⟨⟨hG.aestronglyMeasurable,hfint⟩,?_⟩
  simpa only [fun x => (hp x).tsum_eq] using hasSum_integral_of_summable_integral_norm hi hs

private theorem K_meas (r : ℝ) : Measurable (fun z : E => K r z.1 z.2) := by
  unfold K GrothendieckConstant.gaussianPairDensity
  simp only [Fin.prod_univ_one]
  fun_prop

private theorem integrated_mehler {f g : E → ℝ} (hmf : Measurable f) (hmg : Measurable g)
    (hf : ∀ z, ‖f z‖ ≤ 1) (hg : ∀ z, ‖g z‖ ≤ 1) {r t : ℝ} (hr : |r| < 1) (ht : |t| < 1) :
    HasSum (fun p : ℕ × ℕ => (r^p.1*t^p.2)*((∫ x, B f p x)*(∫ y, B g p y)))
      (∫ x : E, ∫ y : E, f x*g y*(K r x.1 y.1*K t x.2 y.2)) := by
  let F (p : ℕ × ℕ) (z : E × E) := (r^p.1*t^p.2)*(B f p z.1*B g p z.2)
  let G (z : E × E) := f z.1*g z.2*(K r z.1.1 z.2.1*K t z.1.2 z.2.2)
  have Gm : Measurable G := by
    dsimp only [G,K,GrothendieckConstant.gaussianPairDensity,Fin.prod_univ_one]
    fun_prop
  have Fi (p : ℕ × ℕ) : Integrable (F p) :=
    ((B_int hmf hf p).mul_prod (B_int hmg hg p)).const_mul _
  have Fz (p : ℕ × ℕ) : (∫ z : E × E, ‖F p z‖) ≤ |r|^p.1*|t|^p.2 := by
    rw [Measure.volume_eq_prod E E]
    simp only [F, norm_mul,norm_pow,Real.norm_eq_abs,integral_const_mul]
    rw [integral_prod_mul (μ:=volume) (ν:=volume) (fun z => |B f p z|) (fun z => |B g p z|)]
    apply mul_le_of_le_one_right (by positivity)
    exact mul_le_one₀ (B_norm hmf hf p) (integral_nonneg (fun z => abs_nonneg (B g p z))) (B_norm hmg hg p)
  have S : Summable (fun p => ∫ z : E × E, ‖F p z‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) Fz
      ((summable_geometric_of_lt_one (abs_nonneg r) hr).mul_of_nonneg
        (summable_geometric_of_lt_one (abs_nonneg t) ht) (fun _ => by positivity) (fun _ => by positivity))
  have point (z : E × E) : HasSum (fun p => F p z) (G z) := by
    apply ((double_series hr ht z.1 z.2).mul_left (f z.1*g z.2)).congr_fun
    intro p
    dsimp [F,B]
    ring
  obtain ⟨Gi,integ⟩ := integrate_series Gm Fi S point
  rw [Measure.volume_eq_prod E E,integral_prod G Gi] at integ
  apply integ.congr_fun
  intro p
  dsimp only [F]
  rw [integral_const_mul,integral_prod_mul (μ:=volume) (ν:=volume) (B f p) (B g p)]

end CorrelationSeries
open GrothendieckLB GrothendieckLB.Supplement MeasureTheory Real
namespace CorrelationSeries

private theorem rho_contracts (u v t : ℝ) (ht : |t| ≤ 1) : |(cqRhoPoly u v).eval t| ≤ |t| := by
  let V := 1+u^2+v^2
  have hp : 0 < V := by dsimp [V]; positivity
  have h3 := pow_le_of_le_one (abs_nonneg t) ht (by decide : 3 ≠ 0)
  have h5 := pow_le_of_le_one (abs_nonneg t) ht (by decide : 5 ≠ 0)
  simp only [cqRhoPoly,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_sub,
    Polynomial.eval_pow,Polynomial.eval_X]
  change |1/V*(t-u^2*t^3+v^2*t^5)| ≤ |t|
  rw [abs_mul,abs_of_pos (one_div_pos.mpr hp),one_div,mul_comm,←div_eq_mul_inv,div_le_iff₀ hp]
  calc _ ≤ |t-u^2*t^3|+|v^2*t^5| := abs_add_le _ _
       _ ≤ (|t|+|u^2*t^3|)+|v^2*t^5| := add_le_add_left (abs_sub _ _) _
       _ = |t|+u^2*|t|^3+v^2*|t|^5 := by simp [abs_mul,abs_pow,sq_abs]
       _ ≤ |t|+u^2*|t|+v^2*|t| := by gcongr
       _ = |t| *V := by dsimp [V]; ring

private noncomputable def f (c u v : ℝ) (z : E) := cqF c u v z.1 z.2
private noncomputable def g (c u v : ℝ) (z : E) := cqG c u v z.1 z.2

private theorem f_meas (c u v : ℝ) : Measurable (f c u v) := by
  unfold f cqF
  change Measurable (fun z : E => if 0 ≤ z.1+c / Real.sqrt (1+u^2+v^2)*((z.2^3-3*z.2)/Real.sqrt 6) then (1:ℝ) else -1)
  apply Measurable.ite (measurableSet_le measurable_const ?_) measurable_const measurable_const
  fun_prop

private theorem f_bounded (c u v : ℝ) (z : E) : ‖f c u v z‖ ≤ 1 := by unfold f cqF; split <;> simp

private theorem coeff (c u v : ℝ) (p : ℕ × ℕ) : (∫ z, B (f c u v) p z) = cqA c u v p.1 p.2 := by
  rw [Measure.volume_eq_prod ℝ ℝ,integral_prod _ (B_int (f_meas c u v) (f_bounded c u v) p)]
  unfold cqA
  congr 1
  funext w
  congr 1
  funext x
  dsimp [B,h,f]
  ring

private theorem reflection (c u v : ℝ) (w x : ℝ) : g c u v (w,-x) = f c u v (w,x) := by
  unfold f g cqF cqG
  change (if 0 ≤ w-c/Real.sqrt (1+u^2+v^2)*(((-x)^3-3*(-x))/Real.sqrt 6) then (1:ℝ) else -1) = _
  have h : w-c/Real.sqrt (1+u^2+v^2)*(((-x)^3-3*(-x))/Real.sqrt 6) =
    w+c/Real.sqrt (1+u^2+v^2)*((x^3-3*x)/Real.sqrt 6) := by ring
  rw [h]
  rfl

private theorem K_reflect (t x y : ℝ) : K t x (-y)=K (-t) x y := by
  simp only [K,GrothendieckConstant.gaussianPairDensity,Fin.prod_univ_one,neg_sq]
  congr 3 <;> ring

private theorem reflect_integral (H : E → ℝ) : (∫ y : E, H (y.1,-y.2)) = ∫ y : E, H y := by
  let e := (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)
  have hm : MeasurePreserving e (volume : Measure E) volume :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod (Measure.measurePreserving_neg (volume : Measure ℝ))
  exact hm.integral_comp' H

private theorem to_pair_integral (H : E → ℝ) : (∫ y : Fin 2 → ℝ, H (y 0,y 1)) = ∫ y : E, H y :=
  (volume_preserving_finTwoArrow ℝ).integral_comp' H

private theorem correlation (c u v t : ℝ) :
    cqCorr c u v t = pi/2 * ∫ x : E, ∫ y : E,
      f c u v x*f c u v y*(K ((cqRhoPoly u v).eval t) x.1 y.1*K (-t) x.2 y.2) := by
  unfold cqCorr multiCorr
  congr 1
  simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
  calc _ = ∫ x : E, ∫ y : E,
          f c u v x*g c u v y*(K ((cqRhoPoly u v).eval t) x.1 y.1*K t x.2 y.2) := by
         let J (x y : E) := f c u v x*g c u v y*(K ((cqRhoPoly u v).eval t) x.1 y.1*K t x.2 y.2)
         change (∫ x : Fin 2 → ℝ, ∫ y : Fin 2 → ℝ, J (x 0,x 1) (y 0,y 1)) = ∫ x, ∫ y, J x y
         simp_rw [fun x => to_pair_integral (J x)]
         exact to_pair_integral (fun x => ∫ y, J x y)
       _ = _ := by
         congr 1
         funext x
         rw [←reflect_integral (fun y : E => f c u v x*g c u v y*(K ((cqRhoPoly u v).eval t) x.1 y.1*K t x.2 y.2))]
         simp only [reflection,K_reflect]

end CorrelationSeries

open CorrelationSeries in
theorem solution (η s₃ s₅ : ℝ) :
    (∀ t : ℝ, |t| < 1 → HasSum (fun p : ℕ × ℕ =>
       Real.pi / 2 * (cqA η s₃ s₅ p.1 p.2)^2 * ((cqRhoPoly s₃ s₅).eval t)^p.1 * (-t)^p.2)
       (cqCorr η s₃ s₅ t)) ∧
    (∀ a b : ℕ, |cqA η s₃ s₅ a b| ≤ 1) := by
  constructor
  · intro t ht
    rw [correlation]
    have h := integrated_mehler (f_meas η s₃ s₅) (f_meas η s₃ s₅) (f_bounded η s₃ s₅) (f_bounded η s₃ s₅)
        (lt_of_le_of_lt (rho_contracts s₃ s₅ t ht.le) ht) (by simpa only [abs_neg] using ht : |-t| < 1)
    apply (h.mul_left (Real.pi/2 : ℝ)).congr_fun
    intro p
    rw [coeff]
    ring
  · intro a b
    rw [←coeff η s₃ s₅ (a,b),←Real.norm_eq_abs]
    exact (norm_integral_le_integral_norm _).trans (B_norm (f_meas η s₃ s₅) (f_bounded η s₃ s₅) (a,b))

