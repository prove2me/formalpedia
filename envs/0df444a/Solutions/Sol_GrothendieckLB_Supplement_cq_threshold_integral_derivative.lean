-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_threshold_integral_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T22:15:52.184201+00:00
-- url     : https://prove2.me/submissions/dbda9514-4a37-46bf-9c77-5a40dfe65482

import Definitions.Def_GrothendieckLB_Supplement_cqPriceKernels
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Theorems.Thm_GrothendieckLB_Supplement_cq_complex_gaussian_density_envelope
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral
import Definitions.Def_GrothendieckLB_Supplement_cqThresholdKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_GrothendieckLB_Supplement_cq_gaussian_fourier_inversion
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_GrothendieckLB_Supplement_cq_gaussian_fourier_moment_bound
import Theorems.Thm_GrothendieckLB_Supplement_cq_fourier_moment_derivatives
import Theorems.Thm_GrothendieckLB_Supplement_cq_gaussian_price_under_integral

section
open MeasureTheory Real GrothendieckLB.Supplement.CQPrice
namespace CQGaussianMoment

noncomputable def raw (b : ℝ) (k : ℕ) := ∫ x : ℝ, |x|^k * exp (-b*x^2)

theorem raw_integrable (b : ℝ) (hb : 0<b) (k : ℕ) :
    Integrable (fun x : ℝ => |x|^k*exp (-b*x^2)) := by
  have hk : -1 < (k:ℝ) := by linarith [(show 0≤(k:ℝ) by positivity)]
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb hk).norm
  simpa only [Real.rpow_natCast, Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos (exp_pos _)] using h

theorem raw_zero (b : ℝ) : raw b 0=Real.sqrt (Real.pi/b) := by simpa only [raw,pow_zero,one_mul] using integral_gaussian b
noncomputable def normal (k : ℕ) := ∫ x : ℝ, normalTwo x * |x|^k
theorem normal_eq (k : ℕ) : normal k = (1/(2*Real.sqrt Real.pi))*raw (1/4) k := by
  dsimp [normal,raw,normalTwo]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [show -(1/4:ℝ)*x^2= -(x^2)/4 by ring]
  ring

theorem normal_integrable (k : ℕ) : Integrable (fun x : ℝ => normalTwo x * |x|^k) := by
  convert (raw_integrable (1/4) (by norm_num) k).const_mul (1/(2*Real.sqrt Real.pi)) using 1
  funext x
  dsimp [normalTwo]
  rw [show -(1/4:ℝ)*x^2= -(x^2)/4 by ring]
  ring

theorem normal_zero : normal 0=1 := by
  rw [normal_eq,raw_zero,show Real.pi/(1/4)=4*Real.pi by ring, Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
  rw [show Real.sqrt (4:ℝ)=2 by rw [show (4:ℝ)=2^2 by norm_num,Real.sqrt_sq (by norm_num)]]
  field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne']
end CQGaussianMoment
end

section
open GrothendieckLB.Supplement.CQPrice Filter
open scoped Topology
namespace CQSpatialPrice
noncomputable def D (t : ℂ) := 1-t^2
noncomputable def Q (t x y : ℂ) := x^2-2*t*x*y+y^2
noncomputable def A (t : ℂ) := (D t)^(-(1/2:ℂ)) / ((2*Real.pi:ℝ):ℂ)
noncomputable def B (t x y : ℂ) := -Q t x y/(2*D t)
noncomputable def G (t x y : ℂ) := A t*Complex.exp (B t x y)

theorem slit (t : ℂ) (ht : ‖t‖<1) : D t∈Complex.slitPlane := by
  unfold D
  rw [sub_eq_add_neg]
  apply Complex.mem_slitPlane_of_norm_lt_one
  rw [norm_neg,norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) ht (by decide)

theorem density_eq (t : ℂ) (ht : ‖t‖<1) (x y : ℝ) : density t x y=G t x y := by
  have h₀ : 1-t^2≠0 := Complex.slitPlane_ne_zero (slit t ht)
  have h₁ : 1+t≠0 := by intro e;apply h₀;linear_combination (1-t)*e
  have h₂ : 1-t≠0 := by intro e;apply h₀;linear_combination (1+t)*e
  dsimp [density,G,A,B,Q,D]
  push_cast
  congr 2
  field_simp [h₁,h₂,h₀]
  <;> ring

private lemma dD (t : ℂ) : HasDerivAt D (-2*t) t := by
  apply ((hasDerivAt_const t (1:ℂ)).sub ((hasDerivAt_id t).pow 2)).congr_deriv
  dsimp <;> ring
private lemma dA {t : ℂ} (ht : ‖t‖<1) : HasDerivAt A (A t*t/D t) t := by
  have hn := Complex.slitPlane_ne_zero (slit t ht)
  apply (((dD t).cpow_const (c:=(-(1/2:ℂ))) (slit t ht)).div_const ((2*Real.pi:ℝ):ℂ)).congr_deriv
  dsimp only [A]
  rw [Complex.cpow_sub _ _ hn,Complex.cpow_one]
  ring

private lemma dxB (t x y : ℂ) (ht : D t ≠ 0) :
    HasDerivAt (fun X => B t X y) ((t*y-x)/D t) x := by
  have hQ := (((hasDerivAt_id x).pow 2).sub (((hasDerivAt_id x).const_mul (2*t)).mul_const y)).add_const (y^2)
  apply (hQ.neg.div_const (2*D t)).congr_deriv
  dsimp
  field_simp [ht] <;> ring
private lemma dyB (t x y : ℂ) (ht : D t ≠ 0) :
    HasDerivAt (fun Y => B t x Y) ((t*x-y)/D t) y := by
  have hQ := ((hasDerivAt_const y (x^2)).sub ((hasDerivAt_id y).const_mul (2*t*x))).add ((hasDerivAt_id y).pow 2)
  apply (hQ.neg.div_const (2*D t)).congr_deriv
  dsimp
  field_simp [ht] <;> ring

private lemma dtB (t x y : ℂ) (ht : D t ≠ 0) :
    HasDerivAt (fun s => B s x y) (((t*y-x)*(t*x-y))/(D t)^2) t := by
  have hQ := ((hasDerivAt_const t (x^2)).sub ((((hasDerivAt_id t).const_mul 2).mul_const x).mul_const y)).add_const (y^2)
  apply (hQ.neg.div ((dD t).const_mul 2) (mul_ne_zero (by norm_num) ht)).congr_deriv
  dsimp
  unfold D at *
  field_simp [ht] <;> ring

private lemma dxg (t x y : ℂ) (ht : D t ≠ 0) :
    HasDerivAt (fun X => G t X y) (G t x y * ((t*y-x)/D t)) x := by
  apply ((dxB t x y ht).cexp.const_mul (A t)).congr_deriv
  dsimp [G]; ring
private lemma dyg (t x y : ℂ) (ht : D t ≠ 0) :
    HasDerivAt (fun Y => G t x Y) (G t x y * ((t*x-y)/D t)) y := by
  apply ((dyB t x y ht).cexp.const_mul (A t)).congr_deriv
  dsimp [G]; ring


noncomputable def Lx (t x y : ℂ) := (t*y-x)/D t
noncomputable def Ly (t x y : ℂ) := (t*x-y)/D t
noncomputable def Lxy (t x y : ℂ) := Lx t x y*Ly t x y+t/D t

theorem paramG (t x y : ℂ) (ht : ‖t‖<1) :
    HasDerivAt (fun s => G s x y) (G t x y*Lxy t x y) t := by
  have hn := Complex.slitPlane_ne_zero (slit t ht)
  apply ((dA ht).mul (dtB t x y hn).cexp).congr_deriv
  dsimp only [G,Lxy,Lx,Ly]
  field_simp [hn]
  <;> ring

theorem xG (t : ℂ) (ht : ‖t‖<1) (x y : ℝ) :
    HasDerivAt (fun X : ℝ => G t X y) (G t x y*Lx t x y) x :=
  (dxg t x y (Complex.slitPlane_ne_zero (slit t ht))).comp_ofReal

theorem yG (t : ℂ) (ht : ‖t‖<1) (x y : ℝ) :
    HasDerivAt (fun Y : ℝ => G t x Y) (G t x y*Ly t x y) y :=
  (dyg t x y (Complex.slitPlane_ne_zero (slit t ht))).comp_ofReal

theorem xyG (t : ℂ) (ht : ‖t‖<1) (x y : ℝ) :
    HasDerivAt (fun X : ℝ => G t X y*Ly t X y) (G t x y*Lxy t x y) x := by
  have hn := Complex.slitPlane_ne_zero (slit t ht)
  have hlin := (((hasDerivAt_id (x:ℂ)).const_mul t).sub_const (y:ℂ)).div_const (D t)
  apply ((dxg t x y hn).mul hlin).comp_ofReal.congr_deriv
  dsimp [Lxy,Lx,Ly]
  ring

end CQSpatialPrice
end

section
open MeasureTheory Real GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice CQGaussianMoment CQSpatialPrice Filter
open scoped Topology
namespace CQPriceGrowth

noncomputable def weight (w : ℝ×ℝ) := (1+|w.1|)*(1+|w.2|)
theorem wone (w : ℝ×ℝ) : 1≤weight w := by unfold weight;nlinarith [abs_nonneg w.1,abs_nonneg w.2,mul_nonneg (abs_nonneg w.1) (abs_nonneg w.2)]
theorem wpos (w : ℝ×ℝ) : 0≤weight w := zero_le_one.trans (wone w)

def Growth {ι : Type*} (f : ι → ℝ×ℝ → ℂ) : Prop :=
  ∃ C : ℝ, 0≤C ∧ ∃ n : ℕ, ∀ i w, ‖f i w‖ ≤ C*(weight w)^n

theorem Growth.of_bound {ι : Type*} {f : ι→ℝ×ℝ→ℂ} {C : ℝ} (hC : 0≤C) (h : ∀ i w, ‖f i w‖≤C) : Growth f :=
  ⟨C,hC,0,fun i w => by simpa using h i w⟩

theorem Growth.const {ι : Type*} (c : ℂ) : Growth (fun (_ : ι) (_ : ℝ×ℝ) => c) :=
  Growth.of_bound (norm_nonneg _) fun _ _ => le_rfl

theorem Growth.comp {ι κ : Type*} {f : ι→ℝ×ℝ→ℂ} (hf : Growth f) (q : κ→ι) :
    Growth (fun j w => f (q j) w) := by
  obtain ⟨C,hC,n,h⟩ := hf
  exact ⟨C,hC,n,fun j w => h _ w⟩

theorem Growth.mul {ι : Type*} {f g : ι→ℝ×ℝ→ℂ} (hf : Growth f) (hg : Growth g) :
    Growth (fun i w => f i w*g i w) := by
  obtain ⟨C,hC,n,hf⟩ := hf
  obtain ⟨B,hB,k,hg⟩ := hg
  refine ⟨C*B,mul_nonneg hC hB,n+k,fun i w => ?_⟩
  rw [norm_mul,pow_add]
  exact (mul_le_mul (hf i w) (hg i w) (norm_nonneg _) (mul_nonneg hC (pow_nonneg (wpos w) _))).trans_eq (by ring)

theorem Growth.add {ι : Type*} {f g : ι→ℝ×ℝ→ℂ} (hf : Growth f) (hg : Growth g) :
    Growth (fun i w => f i w+g i w) := by
  obtain ⟨C,hC,n,hf⟩ := hf
  obtain ⟨B,hB,k,hg⟩ := hg
  refine ⟨C+B,add_nonneg hC hB,max n k,fun i w => ?_⟩
  rw [add_mul]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (hf _ _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (wone w) (le_max_left _ _)) hC)
  · exact (hg _ _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (wone w) (le_max_right _ _)) hB)

theorem Growth.neg {ι : Type*} {f : ι→ℝ×ℝ→ℂ} (hf : Growth f) :
    Growth (fun i w => -f i w) := by simpa only [Growth,norm_neg] using hf

theorem Growth.sub {ι : Type*} {f g : ι→ℝ×ℝ→ℂ} (hf : Growth f) (hg : Growth g) :
    Growth (fun i w => f i w-g i w) := by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem Growth.pow {ι : Type*} {f : ι→ℝ×ℝ→ℂ} (hf : Growth f) (k : ℕ) :
    Growth (fun i w => f i w^k) := by
  induction k with
  | zero => simpa using (Growth.const (ι:=ι) 1)
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem Growth.first {ι : Type*} : Growth (fun (_ : ι) (w : ℝ×ℝ) => (w.1:ℂ)) := by
  refine ⟨1,by norm_num,1,fun i w => ?_⟩
  simp only [Complex.norm_real,Real.norm_eq_abs,pow_one,one_mul,weight]
  nlinarith [abs_nonneg w.2,mul_nonneg (abs_nonneg w.1) (abs_nonneg w.2)]
theorem Growth.second {ι : Type*} : Growth (fun (_ : ι) (w : ℝ×ℝ) => (w.2:ℂ)) := by
  refine ⟨1,by norm_num,1,fun i w => ?_⟩
  simp only [Complex.norm_real,Real.norm_eq_abs,pow_one,one_mul,weight]
  nlinarith [abs_nonneg w.1,mul_nonneg (abs_nonneg w.1) (abs_nonneg w.2)]

theorem disk_gap {R : ℝ} (hR : 0≤R) (hR' : R<1) : 0<1-R^2 := by nlinarith [mul_pos (show 0<1-R by linarith) (show 0<1+R by linarith)]
theorem det_lower {t : ℂ} {R : ℝ} (ht : ‖t‖≤R) : 1-R^2 ≤ ‖D t‖ := by
  have hh := norm_sub_norm_le (1:ℂ) (t^2)
  rw [norm_one,norm_pow] at hh
  exact (sub_le_sub_left (pow_le_pow_left₀ (norm_nonneg t) ht 2) 1).trans hh

abbrev Disc (R : ℝ) := {z : ℂ // ‖z‖≤R}
theorem growth_z {R : ℝ} (hR : 0≤R) : Growth (fun i : Disc R => fun _ => (i.val:ℂ)) := Growth.of_bound hR fun i _ => i.property
theorem growth_inv {R : ℝ} (hR : 0≤R) (hR' : R<1) : Growth (fun i : Disc R => fun _ => (D i.val)⁻¹) := by
  refine Growth.of_bound (inv_nonneg.mpr (disk_gap hR hR').le) fun i _ => ?_
  rw [norm_inv]
  exact inv_anti₀ (disk_gap hR hR') (det_lower i.property)

theorem growth_x {R : ℝ} (hR : 0≤R) (hR' : R<1) : Growth (fun i : Disc R => fun w => Lx i.val w.1 w.2) := by
  simpa only [Lx,div_eq_mul_inv] using (((growth_z hR).mul Growth.second).sub Growth.first).mul (growth_inv hR hR')
theorem growth_y {R : ℝ} (hR : 0≤R) (hR' : R<1) : Growth (fun i : Disc R => fun w => Ly i.val w.1 w.2) := by
  simpa only [Ly,div_eq_mul_inv] using (((growth_z hR).mul Growth.first).sub Growth.second).mul (growth_inv hR hR')
theorem growth_xy {R : ℝ} (hR : 0≤R) (hR' : R<1) : Growth (fun i : Disc R => fun w => Lxy i.val w.1 w.2) := by
  simpa only [Lxy,div_eq_mul_inv] using ((growth_x hR hR').mul (growth_y hR hR')).add ((growth_z hR).mul (growth_inv hR hR'))

theorem gaussian_kernel {R : ℝ} (hR : 0≤R) (hR' : R<1) (i : Disc R) (w : ℝ×ℝ) :
    ‖G i.val w.1 w.2‖ ≤ (2/Real.sqrt (1-R^2))*(normalTwo w.1*normalTwo w.2) := by
  rw [← density_eq _ (i.property.trans_lt hR')]
  apply (cq_complex_gaussian_density_envelope i.val (i.property.trans_lt hR') w.1 w.2).trans
  apply mul_le_mul_of_nonneg_right _ (by unfold normalTwo;positivity)
  exact div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr (disk_gap hR hR')) (Real.sqrt_le_sqrt (det_lower i.property))

private theorem nInt (k j : ℕ) : Integrable (fun x : ℝ => normalTwo x*(1+|x|)^k*|x|^j) := by
  induction k generalizing j with
  | zero => simpa only [pow_zero,mul_one] using normal_integrable j
  | succ k ih =>
    have h := (ih j).add (ih (j+1))
    convert! h using 1
    funext x
    simp only [Pi.add_apply,pow_succ]
    ring

theorem gaussian_poly_int (k : ℕ) :
    Integrable (fun w : ℝ×ℝ => normalTwo w.1*normalTwo w.2*weight w^k) := by
  have h : Integrable (fun x : ℝ => normalTwo x*(1+|x|)^k) := by simpa only [pow_zero,mul_one] using nInt k 0
  convert! h.mul_prod h using 1
  funext w
  dsimp [weight]
  rw [mul_pow]
  ring

theorem majorant {ι : Type*} {f : ι→ℝ×ℝ→ℂ} (hf : Growth f) {R : ℝ} (hR : 0≤R) (hR' : R<1) :
    ∃ B : ℝ×ℝ→ℝ, Integrable B ∧ ∀ (i : Disc R) (j : ι) (w : ℝ×ℝ), ‖G i.val w.1 w.2*f j w‖≤B w := by
  obtain ⟨C,hC,n,hf⟩ := hf
  let c := 2/Real.sqrt (1-R^2)
  refine ⟨fun w => c*C*(normalTwo w.1*normalTwo w.2*weight w^n), (gaussian_poly_int n).const_mul _,fun i j w => ?_⟩
  rw [norm_mul]
  exact (mul_le_mul (gaussian_kernel hR hR' i w) (hf j w) (norm_nonneg _) (by unfold normalTwo;positivity)).trans_eq (by unfold c;ring)
end CQPriceGrowth
end

section
open MeasureTheory Real GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice CQSpatialPrice CQPriceGrowth Filter
open scoped Topology
namespace CQPriceIntegration
set_option maxHeartbeats 1200000

abbrev Static (f : ℝ×ℝ→ℂ) := Growth (fun _ : Unit => f)
noncomputable def Z (t : ℂ) (w : ℝ×ℝ) := G t w.1 w.2
theorem contZ (t : ℂ) : Continuous (Z t) := by unfold Z G B Q;fun_prop
theorem contLy (t : ℂ) : Continuous (fun w : ℝ×ℝ => Ly t w.1 w.2) := by unfold Ly;fun_prop
theorem contLxy (t : ℂ) : Continuous (fun w : ℝ×ℝ => Lxy t w.1 w.2) := by unfold Lxy Lx Ly;fun_prop

theorem integrate (t : ℂ) (ht : ‖t‖<1) {f : ℝ×ℝ→ℂ} (hf : Static f) (hm : Measurable f) :
    Integrable (fun w => Z t w*f w) := by
  obtain ⟨B,hB,h⟩ := majorant hf (norm_nonneg t) ht
  exact hB.mono' ((contZ t).measurable.mul hm).aestronglyMeasurable (Eventually.of_forall (h ⟨t,le_rfl⟩ ()))

end CQPriceIntegration
end

section
open MeasureTheory Real GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice CQSpatialPrice CQPriceGrowth CQPriceIntegration Filter
open scoped Topology
namespace CQPriceIntegration

theorem under_integral (f g : ℂ→ℝ×ℝ→ℂ) (z : ℂ) (hz : ‖z‖<1)
    (m₀ : ∀ t : ℂ, ‖t‖<1 → Measurable (f t))
    (m₁ : ∀ t : ℂ, ‖t‖<1 → Measurable (g t))
    (h₀ : ∀ R : ℝ, 0≤R → R<1 → Growth (fun i : Disc R => f i.val))
    (h₁ : ∀ R : ℝ, 0≤R → R<1 → Growth (fun i : Disc R => g i.val))
    (hd : ∀ (t : ℂ), ‖t‖<1 → ∀ w : ℝ×ℝ, HasDerivAt (fun t => f t w) (g t w) t) :
    HasDerivAt (fun t => ∫ w : ℝ×ℝ, density (-t) w.1 w.2*f t w)
      ((∫ w : ℝ×ℝ, Z (-z) w*g z w) - ∫ w : ℝ×ℝ, Z (-z) w*(Lxy (-z) w.1 w.2*f z w)) z := by
  let R := (‖z‖+1)/2
  have hR : 0≤R := by dsimp [R];positivity
  have hlt : R<1 := by dsimp [R];linarith
  have hin : ‖z‖<R := by dsimp [R];linarith
  let sn := fun (i : Disc R) => (⟨-i.val,by simpa using i.property⟩ : Disc R)
  let o : Disc R := ⟨z,hin.le⟩
  let F := fun t : ℂ => fun w : ℝ×ℝ => Z (-t) w*f t w
  let P := fun t : ℂ => fun w : ℝ×ℝ => Lxy (-t) w.1 w.2*f t w
  let J := fun t : ℂ => fun w : ℝ×ℝ => Z (-t) w*(g t w-P t w)
  have hP : Growth (fun i : Disc R => P i.val) := ((growth_xy hR hlt).comp sn).mul (h₀ _ hR hlt)
  have mP (t : ℂ) (ht : ‖t‖<1) : Measurable (P t) := (contLxy (-t)).measurable.mul (m₀ t ht)
  have subG : Growth (fun i : Disc R => fun w => g i.val w-P i.val w) := (h₁ _ hR hlt).sub hP
  obtain ⟨M,hM,hbound⟩ := majorant subG hR hlt
  have hneg : ‖-z‖<1 := by simpa
  have hFint : Integrable (F z) := integrate (-z) hneg ((h₀ R hR hlt).comp (fun _ : Unit => o)) (m₀ z hz)
  have mJ : Measurable (J z) := (contZ (-z)).measurable.mul ((m₁ z hz).sub (mP z hz))
  have hs : Metric.ball (0:ℂ) R ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds (by simpa using hin)
  have mF : ∀ᶠ t in 𝓝 z,AEStronglyMeasurable (F t) volume := by
    filter_upwards [hs] with t ht
    have hn : ‖t‖<R := by simpa using ht
    exact ((contZ (-t)).measurable.mul (m₀ t (hn.trans hlt))).aestronglyMeasurable
  have hJ (w : ℝ×ℝ) (t : ℂ) (ht : t∈Metric.ball 0 R) : ‖J t w‖≤M w := by
    have hn : ‖t‖<R := by simpa using ht
    exact hbound (sn ⟨t,hn.le⟩) ⟨t,hn.le⟩ w
  have hdiff (w : ℝ×ℝ) (t : ℂ) (ht : t∈Metric.ball 0 R) : HasDerivAt (fun s => F s w) (J t w) t := by
    have hn : ‖t‖<R := by simpa using ht
    have hpos := hn.trans hlt
    have hneg' : ‖-t‖<1 := by simpa
    have hg := (paramG (-t) w.1 w.2 hneg').comp t ((hasDerivAt_id t).neg)
    apply (hg.mul (hd t hpos w)).congr_deriv
    dsimp only [Function.comp_apply,id_eq,F,J,P,Z]
    ring
  have derivJ := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=volume) (F:=F) (F':=J)
    hs mF hFint mJ.aestronglyMeasurable (Eventually.of_forall hJ) hM (Eventually.of_forall hdiff)).2
  have heq : (fun t => ∫ w : ℝ×ℝ, density (-t) w.1 w.2*f t w) =ᶠ[𝓝 z] fun t => ∫ w : ℝ×ℝ, F t w := by
    filter_upwards [hs] with t ht
    have hn : ‖t‖<R := by simpa using ht
    have := hn.trans hlt
    simp only [F,Z,density_eq (-t) (by simpa) ]
  apply (derivJ.congr_of_eventuallyEq heq).congr_deriv
  have ihg := integrate (-z) hneg ((h₁ R hR hlt).comp (fun _ : Unit => o)) (m₁ z hz)
  have ihp := integrate (-z) hneg (hP.comp (fun _ : Unit => o)) (mP z hz)
  change (∫ w : ℝ×ℝ, Z (-z) w*(g z w-P z w))=_
  simp_rw [mul_sub]
  exact integral_sub ihg ihp

end CQPriceIntegration
end

section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace GrothendieckLB.Supplement.CQThreshold
theorem normS (u x : ℝ) : ‖S u x‖=1 := by unfold S;split <;> simp
theorem measurableS {X : Type*} [MeasurableSpace X] {u x : X→ℝ} (hu : Measurable u) (hx : Measurable x) :
    Measurable (fun w => S (u w) (x w)) :=
  Measurable.ite (measurableSet_le hu.neg hx) measurable_const measurable_const

theorem signed_integral (u : ℝ) (f : ℝ→ℂ) (hf : Integrable f) :
    (∫ x : ℝ,S u x*f x)=2*(∫ x in Ioi (-u),f x) - ∫ x : ℝ,f x := by
  have e (x : ℝ) : S u x*f x=2*(Ici (-u)).indicator f x-f x := by
    by_cases h : -u≤x
    · simp [S,h,Set.indicator_of_mem h];ring
    · simp [S,h,Set.indicator_of_notMem h]
  simp_rw [e]
  rw [integral_sub ((hf.indicator measurableSet_Ici).const_mul _) hf,integral_const_mul,integral_indicator measurableSet_Ici,integral_Ici_eq_integral_Ioi]

theorem jump (u : ℝ) (f f' : ℝ→ℂ) (hf : Integrable f) (hd : Integrable f')
    (h : ∀x,HasDerivAt f (f' x) x) :
    (∫ x : ℝ,S u x*f' x) = -2*f (-u) := by
  have ht := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := -u) (fun x _ => h x) hd.integrableOn hf.integrableOn
  rw [signed_integral u f' hd,integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => h x) hd.integrableOn ht,
    integral_eq_zero_of_hasDerivAt_of_integrable h hd hf]
  ring

theorem dshift (u : ℝ) (f : ℝ→ℂ) (hf : Integrable f) (hc : Continuous f) :
    HasDerivAt (fun t : ℝ => ∫ x : ℝ,S t x*f x) (2*f (-u)) u := by
  let c := ∫ x in Ioi (0:ℝ), f x
  have he (t : ℝ) : (∫ x : ℝ,S t x*f x)=2*(c-∫ x in (0:ℝ)..(-t),f x) - ∫ x : ℝ,f x := by
    rw [signed_integral t f hf]
    have e := intervalIntegral.integral_interval_add_Ioi (a:=0) (b:=-t) hf.integrableOn hf.integrableOn
    dsimp only [c]
    rw [← e]
    abel
  have hprim := intervalIntegral.integral_hasDerivAt_right (a:=0) (b:=-u) (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hn := hprim.scomp u ((hasDerivAt_id u).neg)
  have h := (((hn.const_sub c).const_mul (2:ℂ)).sub_const (∫ x : ℝ,f x)).congr_of_eventuallyEq (Eventually.of_forall he)
  apply h.congr_deriv
  simp [Complex.real_smul]

end GrothendieckLB.Supplement.CQThreshold
end

section
open MeasureTheory Real Filter GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice
open CQPriceGrowth CQSpatialPrice CQPriceIntegration CQGaussianMoment
open scoped Topology
namespace GrothendieckLB.Supplement.CQThreshold

private theorem npos (x : ℝ) : 0≤normalTwo x := by unfold normalTwo;positivity
theorem nbound (x : ℝ) : normalTwo x≤1/(2*Real.sqrt Real.pi) := by
  unfold normalTwo
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg x]
theorem nint : Integrable normalTwo := by simpa only [pow_zero,mul_one] using normal_integrable 0
theorem nval : (∫ x : ℝ,normalTwo x)=1 := by simpa only [normal,pow_zero,mul_one] using normal_zero

noncomputable def constD (q : ℂ) := 2/Real.sqrt ‖1-q^2‖
theorem constD_nonneg (q : ℂ) : 0≤constD q := by unfold constD;positivity
theorem constD_le (q : ℂ) {R : ℝ} (hR : 0≤R) (hR' : R<1) (h : ‖q‖≤R) :
    constD q≤2/Real.sqrt (1-R^2) :=
  div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr (disk_gap hR hR')) (Real.sqrt_le_sqrt (det_lower h))

theorem mK (q : ℂ) : Measurable (fun w : ℝ×ℝ => K q w.1 w.2) := by
  unfold K
  apply measurable_const.mul
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right' (f:=fun p : (ℝ×ℝ)×(ℝ×ℝ) => density q p.2.1 p.2.2*(S p.1.1 p.2.1*S p.1.2 p.2.2))
  apply Measurable.stronglyMeasurable
  apply Measurable.mul
  · unfold density
    fun_prop
  · apply Measurable.mul
    · exact measurableS (measurable_fst.comp measurable_fst) (measurable_fst.comp measurable_snd)
    · exact measurableS (measurable_snd.comp measurable_fst) (measurable_snd.comp measurable_snd)
theorem mJ (q : ℂ) : Measurable (fun w : ℝ×ℝ => J q w.1 w.2) := by
  unfold J
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right' (f:=fun p : (ℝ×ℝ)×ℝ => S p.1.2 p.2*density q (-p.1.1) p.2)
  apply Measurable.stronglyMeasurable
  apply Measurable.mul (measurableS (measurable_snd.comp measurable_fst) measurable_snd)
  unfold density
  fun_prop

theorem nK (q : ℂ) (hq : ‖q‖<1) (u v : ℝ) : ‖K q u v‖≤(Real.pi/2)*constD q := by
  rw [K,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0<Real.pi/2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hi := (nint.mul_prod nint).const_mul (constD q)
  apply (norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall fun w => ?_)).trans_eq
  · rw [integral_const_mul,integral_prod_mul,nval]
    ring
  · rw [norm_mul,norm_mul,normS,normS,mul_one,mul_one]
    exact cq_complex_gaussian_density_envelope q hq w.1 w.2

theorem nJ (q : ℂ) (hq : ‖q‖<1) (u v : ℝ) : ‖J q u v‖≤constD q*normalTwo (-u) := by
  unfold J
  apply (norm_integral_le_of_norm_le (nint.const_mul (constD q*normalTwo (-u))) (Filter.Eventually.of_forall fun y => ?_)).trans_eq
  · rw [integral_const_mul,nval,mul_one]
  · rw [norm_mul,normS,one_mul,mul_assoc]
    exact cq_complex_gaussian_density_envelope q hq (-u) y

theorem slice_int (q : ℂ) (hq : ‖q‖<1) (x : ℝ) : Integrable (fun y : ℝ => density q x y) := by
  apply (nint.const_mul (constD q*normalTwo x)).mono'
  · unfold density
    fun_prop
  · filter_upwards with y
    rw [mul_assoc]
    exact cq_complex_gaussian_density_envelope q hq x y

theorem slice_cont (q : ℂ) (hq : ‖q‖<1) (v : ℝ) :
    Continuous (fun x : ℝ => J q (-x) v) := by
  change Continuous (fun x : ℝ => ∫ y : ℝ,S v y*density q (- -x) y)
  simp only [neg_neg]
  apply continuous_of_dominated (bound:=fun y => (constD q*(1/(2*Real.sqrt Real.pi)))*normalTwo y)
  · intro x
    apply Measurable.aestronglyMeasurable
    apply (measurableS measurable_const measurable_id).mul
    unfold density
    fun_prop
  · intro x
    filter_upwards with y
    rw [norm_mul,normS,one_mul,mul_assoc]
    apply (cq_complex_gaussian_density_envelope q hq x y).trans
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (nbound x) (npos y)) (constD_nonneg _)
  · exact nint.const_mul _
  · filter_upwards with y
    apply continuous_const.mul
    unfold density
    fun_prop

private theorem integrableSigns (q : ℂ) (hq : ‖q‖<1) (u v : ℝ) :
    Integrable (fun w : ℝ×ℝ => density q w.1 w.2*(S u w.1*S v w.2)) := by
  apply ((nint.mul_prod nint).const_mul (constD q)).mono'
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · unfold density;fun_prop
    · exact (measurableS measurable_const measurable_fst).mul (measurableS measurable_const measurable_snd)
  · filter_upwards with w
    rw [norm_mul,norm_mul,normS,normS,mul_one,mul_one]
    exact cq_complex_gaussian_density_envelope q hq w.1 w.2

private theorem iteratedK (q : ℂ) (hq : ‖q‖<1) (u v : ℝ) :
    K q u v=((Real.pi/2:ℝ):ℂ)*∫ x : ℝ,S u x*J q (-x) v := by
  unfold K
  congr 1
  change (∫ w : ℝ×ℝ, density q w.1 w.2*(S u w.1*S v w.2) ∂volume.prod volume)=_
  rw [integral_prod _ (integrableSigns q hq u v)]
  apply integral_congr_ae
  filter_upwards with x
  rw [J,neg_neg,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  ring

theorem dJ (q : ℂ) (hq : ‖q‖<1) (u v : ℝ) :
    HasDerivAt (J q u) (2*density q (-u) (-v)) v := by
  apply dshift _ _ (slice_int q hq _)
  unfold density;fun_prop
theorem dKshift (q : ℂ) (hq : ‖q‖<1) (u v : ℝ) :
    HasDerivAt (fun s : ℝ => K q s v) ((Real.pi:ℂ)*J q u v) u := by
  have hc := slice_cont q hq v
  have hi : Integrable (fun x : ℝ => J q (-x) v) := by
    apply (nint.const_mul (constD q)).mono' hc.aestronglyMeasurable
    filter_upwards with x
    simpa only [neg_neg] using nJ q hq (-x) v
  have h := (dshift u (fun x : ℝ => J q (-x) v) hi hc).const_mul ((Real.pi/2:ℝ):ℂ)
  apply (h.congr_of_eventuallyEq (Eventually.of_forall (fun s => iteratedK q hq s v))).congr_deriv
  simp only [neg_neg]
  push_cast
  ring

end GrothendieckLB.Supplement.CQThreshold
end

section
open MeasureTheory Real GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice CQGaussianMoment CQPriceGrowth CQPriceIntegration CQSpatialPrice Filter
open scoped Topology
namespace GrothendieckLB.Supplement.CQThreshold

private theorem pow_weight (k j : ℕ) : Integrable (fun y : ℝ => normalTwo y*(1+|y|)^k*|y|^j) := by
  induction k generalizing j with
  | zero => simpa only [pow_zero,mul_one] using normal_integrable j
  | succ k ih =>
    convert! (ih j).add (ih (j+1)) using 1
    funext y
    simp only [Pi.add_apply,pow_succ]
    ring

private theorem slice_weighted (q : ℂ) (hq : ‖q‖<1) (x : ℝ) (f : ℝ×ℝ→ℂ) (hf : Static f) (hm : Measurable f) :
    Integrable (fun y : ℝ => G q x y*f (x,y)) := by
  obtain ⟨C,hC,k,h⟩ := hf
  have hi : Integrable (fun y : ℝ => normalTwo y*(1+|y|)^k) := by simpa only [pow_zero,mul_one] using pow_weight k 0
  apply (hi.const_mul (constD q*normalTwo x*C*(1+|x|)^k)).mono'
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · unfold G B Q;fun_prop
    · exact hm.comp (measurable_const.prodMk measurable_id)
  · filter_upwards with y
    rw [norm_mul,← density_eq q hq]
    apply (mul_le_mul (cq_complex_gaussian_density_envelope q hq x y) (h () (x,y)) (norm_nonneg _)
      (by unfold normalTwo;positivity)).trans_eq
    dsimp [weight,constD]
    rw [mul_pow]
    ring

private theorem covjump (q : ℂ) (hq : ‖q‖<1) (u v : ℝ) :
    (∫ w : ℝ×ℝ,Z q w*(Lxy q w.1 w.2*(S u w.1*S v w.2)))=4*density q (-u) (-v) := by
  let signs := fun w : ℝ×ℝ => S u w.1*S v w.2
  let dy := fun w : ℝ×ℝ => Ly q w.1 w.2
  let xy := fun w : ℝ×ℝ => Lxy q w.1 w.2
  let sel := fun _ : Unit => (⟨q,le_rfl⟩ : Disc ‖q‖)
  have gs : Static signs := Growth.of_bound (C:=1) zero_le_one (fun _ w => by simp [signs,norm_mul,normS])
  have ms : Measurable signs := (measurableS measurable_const measurable_fst).mul (measurableS measurable_const measurable_snd)
  have gy : Static dy := (growth_y (norm_nonneg q) hq).comp sel
  have gxy : Static xy := (growth_xy (norm_nonneg q) hq).comp sel
  have iy := integrate q hq (f:=dy) gy (contLy q).measurable
  have ixy := integrate q hq (f:=xy) gxy (contLxy q).measurable
  have I := integrate q hq (f:=fun w => xy w*signs w) (gxy.mul gs) ((contLxy q).measurable.mul ms)
  change (∫ w : ℝ×ℝ,Z q w*(xy w*signs w) ∂volume.prod volume)=_
  rw [integral_prod_symm _ I]
  have first : (∫ y : ℝ, ∫ x : ℝ,Z q (x,y)*(xy (x,y)*signs (x,y))) =
      ∫ y : ℝ, S v y*(-2*(G q ((-u:ℝ):ℂ) y*Ly q ((-u:ℝ):ℂ) y)) := by
    apply integral_congr_ae
    filter_upwards [iy.prod_left_ae,ixy.prod_left_ae] with y hy hxy
    have h := jump u (fun x : ℝ => G q x y*Ly q x y) (fun x : ℝ => G q x y*Lxy q x y) hy hxy (fun x => xyG q hq x y)
    rw [← h,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [Z,xy,signs]
    ring
  rw [first]
  have h0 : Integrable (fun y : ℝ => G q ((-u:ℝ):ℂ) y) := by simpa only [density_eq _ hq] using slice_int q hq (-u)
  have h1 : Integrable (fun y : ℝ => G q ((-u:ℝ):ℂ) y*Ly q ((-u:ℝ):ℂ) y) := slice_weighted q hq (-u) dy gy (contLy q).measurable
  have h := jump v (fun y : ℝ => G q ((-u:ℝ):ℂ) y) (fun y : ℝ => G q ((-u:ℝ):ℂ) y*Ly q ((-u:ℝ):ℂ) y) h0 h1 (fun y => yG q hq (-u) y)
  calc
    _ = (-2:ℂ)*(∫ y : ℝ,S v y*(G q ((-u:ℝ):ℂ) y*Ly q ((-u:ℝ):ℂ) y)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = _ := by rw [h,density_eq q hq];ring

theorem density_even (q : ℂ) (x y : ℝ) : density q (-x) (-y)=density q x y := by
  unfold density
  rw [show -x+-y= -(x+y) by ring,show -x- -y= -(x-y) by ring,neg_sq,neg_sq]

theorem dKcov (q : ℂ) (hq : ‖q‖<1) (u v : ℝ) :
    HasDerivAt (fun s : ℂ => K s u v) (fourierMoment q u v 0 0) q := by
  let signs := fun w : ℝ×ℝ => S u w.1*S v w.2
  have ms : Measurable signs := (measurableS measurable_const measurable_fst).mul (measurableS measurable_const measurable_snd)
  have gs {ι : Type} : Growth (fun _ : ι => signs) := Growth.of_bound (C:=1) zero_le_one (fun _ w => by simp [signs,norm_mul,normS])
  have hneg : ‖-q‖<1 := by simpa
  have h := under_integral (fun _ => signs) (fun _ _ => 0) (-q) hneg (fun _ _ => ms) (fun _ _ => measurable_const)
    (fun _ _ _ => gs) (fun _ _ _ => Growth.const 0) (fun t _ w => hasDerivAt_const t (signs w))
  have j := h.comp q ((hasDerivAt_id q).neg)
  simp only [Function.comp_def,id_eq,neg_neg,mul_zero,integral_zero,zero_sub,mul_neg,mul_one] at j
  have jj : HasDerivAt (fun s : ℂ => ∫ w : ℝ×ℝ,density s w.1 w.2*signs w) (4*density q (-u) (-v)) q := by
    simpa only [← covjump q hq u v,signs] using j
  apply (jj.const_mul ((Real.pi/2:ℝ):ℂ)).congr_deriv
  rw [cq_gaussian_fourier_inversion q hq,density_even]
  push_cast
  ring

end GrothendieckLB.Supplement.CQThreshold
end

section
open GrothendieckLB.Supplement.CQPrice
namespace CQBellLinear
set_option maxHeartbeats 2500000
noncomputable def thr' (x : ℝ) := delta*(3*x^2-3)
theorem dthreshold (x : ℝ) : HasDerivAt threshold (thr' x) x := by
  apply ((((hasDerivAt_id x).pow 3).sub ((hasDerivAt_id x).const_mul 3)).const_mul delta).congr_deriv
  simp [thr',id_eq]
end CQBellLinear
end

section
open MeasureTheory GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice CQBellLinear CQPriceGrowth
namespace CQMixedIntegrals

noncomputable def V (z : ℂ) (w : ℝ×ℝ) (m n : ℕ) := fourierMoment (eval rho z) (threshold w.1) (threshold w.2) m n
noncomputable def dr (z : ℂ) := deriv (eval rho) z

private theorem rho_sum (ts : List (ℕ×ℤ)) (z : ℂ) (hz : ‖z‖≤1) (h : ∀ e∈ts,0<e.1) :
    ‖(ts.map (fun e => (e.2:ℂ)*z^e.1)).sum‖ ≤
      (ts.map (fun e => |(e.2:ℝ)|)).sum*‖z‖ := by
  induction ts with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons,List.sum_cons,add_mul]
    apply (norm_add_le _ _).trans
    apply add_le_add _ (ih fun j hj => h j (by simp [hj]))
    rw [norm_mul,norm_pow,show ‖(e.2:ℂ)‖=|(e.2:ℝ)| by norm_cast]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (h e (by simp)))
    rw [hj,pow_succ]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)

theorem rho_norm (z : ℂ) (hz : ‖z‖<1) : ‖eval rho z‖≤‖z‖ := by
  rw [eval,norm_div]
  have h : ∀ t∈rho.terms,0<t.1 := by simp [rho]
  have ht := rho_sum rho.terms z hz.le h
  norm_num [rho] at ht ⊢
  linarith

theorem rho_re (z : ℂ) (hz : ‖z‖<1) : |(eval rho z).re|<1 :=
  ((Complex.abs_re_le_norm _).trans (rho_norm z hz)).trans_lt hz

theorem rho_formula : eval rho=(fun z : ℂ => (10000000000000000*z-1162886658063376*z^3+27837347284321*z^5)/11190724005347697) := by
  funext z
  norm_num [eval,rho] <;> ring

theorem deriv_rho (z : ℂ) : HasDerivAt (eval rho) (dr z) z := by
  apply DifferentiableAt.hasDerivAt
  rw [rho_formula]
  fun_prop

theorem cont_dr : Continuous dr := by
  have h : ContDiff ℂ 1 (eval rho) := by rw [rho_formula];fun_prop
  exact h.continuous_deriv (by decide)

end CQMixedIntegrals
end

section
open MeasureTheory GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice CQBellLinear CQPriceGrowth
namespace CQMixedIntegrals
set_option maxHeartbeats 1200000

theorem growth_V {R : ℝ} (hR : 0≤R) (hlt : R<1) (m n : ℕ) : Growth (fun i : Disc R => fun w => V i.val w m n) := by
  let v := (Real.sqrt (1-R^2))⁻¹
  let M := Real.sqrt ((momentDF m:ℝ)*(momentDF n:ℝ))
  apply Growth.of_bound (C:=v^(m+n+1)*M) (by dsimp [v,M];positivity)
  intro i w
  have hi := i.property.trans_lt hlt
  have h := cq_gaussian_fourier_moment_bound _ (rho_re i.val hi) (threshold w.1) (threshold w.2) m n
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply pow_le_pow_left₀ (by positivity)
  apply inv_anti₀ (Real.sqrt_pos.mpr (disk_gap hR hlt))
  apply Real.sqrt_le_sqrt
  have hh := ((Complex.abs_re_le_norm _).trans (rho_norm i.val hi)).trans i.property
  have hh₂ := pow_le_pow_left₀ (abs_nonneg _) hh 2
  rw [sq_abs] at hh₂
  linarith

theorem cont_V (z : ℂ) (hz : ‖z‖<1) (m n : ℕ) : Continuous (fun w => V z w m n) := by
  have hc := (cq_fourier_moment_derivatives _ (rho_re z hz) 0 0 m n).2.2.2
  have h : Continuous (fun w : ℝ×ℝ => (threshold w.1,threshold w.2)) := by unfold threshold;fun_prop
  unfold V
  simpa only [Function.comp_def] using hc.comp h

theorem growth_dr {R : ℝ} (hR : 0≤R) : Growth (fun i : Disc R => fun _ => dr i.val) := by
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0:ℂ) R).bddAbove_image cont_dr.norm.continuousOn
  apply Growth.of_bound (C:=max B 0) (le_max_right _ _)
  intro i _
  exact (hB (Set.mem_image_of_mem _ (show i.val∈Metric.closedBall (0:ℂ) R by simpa using i.property))).trans (le_max_left _ _)

end CQMixedIntegrals
end

section
open MeasureTheory GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice CQThreshold CQPriceGrowth CQBellLinear CQMixedIntegrals

set_option maxHeartbeats 600000
set_option maxRecDepth 8000
namespace CQThresholdPrice
private theorem low10 (z : ℂ) :
    partialTerm z 1 0 = ∫ w : ℝ×ℝ,density (-z) w.1 w.2*V z w 0 0 := by
  have hi : indices 1 0 = [(0,0)] := by decide +kernel
  simp [partialTerm,hi,bell,pieces,V]

private theorem low01 (z : ℂ) :
    partialTerm z 0 1 = ∫ w : ℝ×ℝ,density (-z) w.1 w.2*((thr' w.1:ℂ)*(thr' w.2:ℂ)*V z w 0 0) := by
  have hi : indices 0 1 = [(1,1)] := by decide +kernel
  have hb (x : ℝ) : bell 1 1 x=thr' x := by
    change delta^1*((3:ℝ)*x^0*(x^2-1)^1+0)=delta*(3*x^2-3)
    ring
  simp [partialTerm,hi,hb,V]

private theorem polynomial_growth {ι : Type*} (p : ℝ×ℝ→ℝ) (h : Growth (fun (_ : ι) w => (p w:ℂ))) :
    Growth (fun (_ : ι) w => (thr' (p w):ℂ)) := by
  simpa [thr'] using (Growth.const (delta:ℂ)).mul (((Growth.const (3:ℂ)).mul (h.pow 2)).sub (Growth.const (3:ℂ)))


private noncomputable def f (t : ℂ) := (fun w : ℝ×ℝ => K (eval rho t) w.1 w.2) ∘ (fun w : ℝ×ℝ => (threshold w.1, threshold w.2))
private noncomputable def g := fun t (w : ℝ×ℝ) => dr t*V t w 0 0
private noncomputable def fx := fun t (w : ℝ×ℝ) => ((thr' w.1:ℂ)*(Real.pi:ℂ))*J (eval rho t) (threshold w.1) (threshold w.2)
private noncomputable def fxy := fun t (w : ℝ×ℝ) => (thr' w.1:ℂ)*(thr' w.2:ℂ)*V t w 0 0

private theorem qr (t : ℂ) (ht : ‖t‖<1) : ‖eval rho t‖<1 := (rho_norm t ht).trans_lt ht

private theorem mth : Measurable (fun w : ℝ×ℝ => (threshold w.1, threshold w.2)) := by unfold threshold;fun_prop
private theorem mx : Measurable (fun w : ℝ×ℝ => (thr' w.1:ℂ)) := by unfold thr';fun_prop
private theorem my : Measurable (fun w : ℝ×ℝ => (thr' w.2:ℂ)) := by unfold thr';fun_prop
private theorem hf (t : ℂ) (_ht : ‖t‖<1) : Measurable (f t) := (mK (eval rho t)).comp mth
private theorem hg (t : ℂ) (ht : ‖t‖<1) : Measurable (g t) := (measurable_const (a:=dr t)).mul (cont_V t ht 0 0).measurable
private theorem hfx (t : ℂ) (_ht : ‖t‖<1) : Measurable (fx t) := (mx.mul (measurable_const (a:=(Real.pi:ℂ)))).mul ((mJ (eval rho t)).comp mth)
private theorem hfxy (t : ℂ) (ht : ‖t‖<1) : Measurable (fxy t) := (mx.mul my).mul (cont_V t ht 0 0).measurable

private theorem mF (A) (h : A∈[f,g,fx,fxy]) : ∀ t : ℂ, ‖t‖<1 → Measurable (A t) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl
  · exact hf
  · exact hg
  · exact hfx
  · exact hfxy

private theorem gF (A) (h : A∈[f,g,fx,fxy]) (R : ℝ) (hR : 0≤R) (hR' : R<1) :
    ∃ C : ℝ, 0≤C ∧ ∃ k : ℕ, ∀ t : ℂ, ‖t‖≤R → ∀ w : ℝ×ℝ, ‖A t w‖≤ C*((1+|w.1|)*(1+|w.2|))^k := by
  have qle (i : Disc R) : ‖eval rho i.val‖≤R := (rho_norm i.val (i.property.trans_lt hR')).trans i.property
  have gK : Growth (fun i : Disc R => f i.val) := by
    apply Growth.of_bound (C:=(Real.pi/2)*(2/Real.sqrt (1-R^2))) (by positivity)
    intro i w
    exact (nK _ ((qle i).trans_lt hR') _ _).trans (mul_le_mul_of_nonneg_left (constD_le _ hR hR' (qle i)) (by positivity))
  have gJ : Growth (fun i : Disc R => fun w : ℝ×ℝ => J (eval rho i.val) (threshold w.1) (threshold w.2)) := by
    apply Growth.of_bound (C:=(2/Real.sqrt (1-R^2))*(1/(2*Real.sqrt Real.pi))) (by positivity)
    intro i w
    exact (nJ _ ((qle i).trans_lt hR') _ _).trans (mul_le_mul (constD_le _ hR hR' (qle i)) (nbound _) (by unfold normalTwo;positivity) (by positivity))
  have gx := polynomial_growth Prod.fst (Growth.first (ι:=Disc R))
  have gy := polynomial_growth Prod.snd (Growth.second (ι:=Disc R))
  have G : Growth (fun i : Disc R => A i.val) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl
    · exact gK
    · exact (growth_dr hR).mul (growth_V hR hR' 0 0)
    · exact (gx.mul (Growth.const (Real.pi:ℂ))).mul gJ
    · exact (gx.mul gy).mul (growth_V hR hR' 0 0)
  obtain ⟨C,hC,k,hk⟩ := G
  exact ⟨C,hC,k,fun t ht w => hk ⟨t,ht⟩ w⟩

private theorem hd (t : ℂ) (ht : ‖t‖<1) (w : ℝ×ℝ) : HasDerivAt (fun s : ℂ => f s w) (g t w) t := by
  simpa only [f,g,V,Function.comp_def,mul_comm] using (dKcov _ (qr t ht) (threshold w.1) (threshold w.2)).comp t (deriv_rho t)
private theorem hx (z : ℂ) (hz : ‖z‖<1) (x y : ℝ) : HasDerivAt (fun X : ℝ => f z (X,y)) (fx z (x,y)) x := by
  simpa only [f,fx,Function.comp_def,Complex.real_smul,mul_assoc] using
    (dKshift _ (qr z hz) (threshold x) (threshold y)).scomp x (dthreshold x)
private theorem hy (z : ℂ) (hz : ‖z‖<1) (x y : ℝ) : HasDerivAt (fun Y : ℝ => fx z (x,Y)) (fxy z (x,y)) y := by
  have h := ((dJ _ (qr z hz) (threshold x) (threshold y)).scomp y (dthreshold y)).const_mul ((thr' x:ℂ)*(Real.pi:ℂ))
  apply h.congr_deriv
  dsimp only [fxy,V]
  rw [Complex.real_smul,cq_gaussian_fourier_inversion _ (qr z hz),density_even]
  push_cast
  ring

end CQThresholdPrice

open CQThresholdPrice
theorem solution (z : ℂ) (hz : ‖z‖<1) :
    HasDerivAt H (deriv (eval rho) z * partialTerm z 1 0 - partialTerm z 0 1) z := by
  have h := cq_gaussian_price_under_integral f g fx fxy z hz mF gF hd (hx z hz) (hy z hz)
  rw [low10,low01]
  apply h.congr_deriv
  dsimp only [g,fxy,dr]
  rw [← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with w
  ring
end
