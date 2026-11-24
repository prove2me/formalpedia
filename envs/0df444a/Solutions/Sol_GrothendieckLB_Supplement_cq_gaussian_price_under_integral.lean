-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_gaussian_price_under_integral
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:52:59.151822+00:00
-- url     : https://prove2.me/submissions/366d940c-7f7c-4efb-98f8-8b6f246a782a

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


open MeasureTheory Real GrothendieckLB.Supplement.CQPrice
namespace CQGaussianMoment

noncomputable def raw (b : ℝ) (k : ℕ) := ∫ x : ℝ, |x|^k * exp (-b*x^2)

theorem raw_integrable (b : ℝ) (hb : 0<b) (k : ℕ) :
    Integrable (fun x : ℝ => |x|^k*exp (-b*x^2)) := by
  have hk : -1 < (k:ℝ) := by linarith [(show 0≤(k:ℝ) by positivity)]
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb hk).norm
  simpa only [Real.rpow_natCast, Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos (exp_pos _)] using h

theorem raw_gamma (b : ℝ) (hb : 0<b) (k : ℕ) :
    raw b k=b^(-((k:ℝ)+1)/2)*Gamma (((k:ℝ)+1)/2) := by
  have hk : -1 < (k:ℝ) := by linarith [(show 0≤(k:ℝ) by positivity)]
  have h := integral_rpow_mul_exp_neg_mul_rpow (p:=(2:ℝ)) two_pos hk hb
  simp only [Real.rpow_natCast,Real.rpow_two] at h
  have hspec := integral_comp_abs (f := fun x : ℝ => x^k*exp (-b*x^2))
  simp only [sq_abs] at hspec
  rw [raw,hspec,h]
  ring

theorem raw_step (b : ℝ) (hb : 0<b) (k : ℕ) :
    raw b (k+2)=((k:ℝ)+1)/(2*b)*raw b k := by
  have h0 : ((k:ℝ)+1)/2≠0 := by positivity
  rw [raw_gamma b hb (k+2),raw_gamma b hb k]
  push_cast
  rw [show ((k:ℝ)+2+1)/2 = ((k:ℝ)+1)/2+1 by ring,
    show -((k:ℝ)+2+1)/2 = -((k:ℝ)+1)/2+(-1) by ring,
    Real.rpow_add hb, Real.rpow_neg_one, Real.Gamma_add_one h0]
  ring

theorem raw_zero (b : ℝ) : raw b 0=Real.sqrt (Real.pi/b) := by simpa only [raw,pow_zero,one_mul] using integral_gaussian b
theorem raw_first_quarter : raw (1/4) 1=4 := by
  rw [raw_gamma (1/4) (by norm_num)]
  norm_num [Real.Gamma_one]

theorem df_step (m : ℕ) : momentDF (m+1)=(2*m+1)*momentDF m := by
  unfold momentDF
  rw [show 2*(m+1)-1 = 2*m+1 by omega,Nat.doubleFactorial_add_one]

theorem even (b : ℝ) (hb : 0<b) (m : ℕ) :
    raw b (2*m)=Real.sqrt (Real.pi/b)*(1/(2*b))^m*(momentDF m:ℝ) := by
  induction m with
  | zero => simp [momentDF,Nat.doubleFactorial,raw_zero]
  | succ m ih =>
    rw [show 2*(m+1)=2*m+2 by omega,raw_step b hb,ih,pow_succ,df_step]
    push_cast
    ring

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

theorem normal_step (k : ℕ) : normal (k+2)=2*((k:ℝ)+1)*normal k := by
  rw [normal_eq,raw_step _ (by norm_num),normal_eq]
  ring

theorem normal_zero : normal 0=1 := by
  rw [normal_eq,raw_zero,show Real.pi/(1/4)=4*Real.pi by ring, Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
  rw [show Real.sqrt (4:ℝ)=2 by rw [show (4:ℝ)=2^2 by norm_num,Real.sqrt_sq (by norm_num)]]
  field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne']
theorem normal_one : normal 1=2/Real.sqrt Real.pi := by rw [normal_eq,raw_first_quarter]; ring
end CQGaussianMoment


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


open MeasureTheory Real GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice CQSpatialPrice CQPriceGrowth Filter
open scoped Topology
namespace CQPriceIntegration
set_option maxHeartbeats 1200000

private theorem partsX (u ux v vx : ℝ×ℝ→ℂ)
    (hu : ∀ x y : ℝ,HasDerivAt (fun X => u (X,y)) (ux (x,y)) x)
    (hv : ∀ x y : ℝ,HasDerivAt (fun X => v (X,y)) (vx (x,y)) x)
    (h₁ : Integrable (fun w => u w*vx w)) (h₂ : Integrable (fun w => ux w*v w))
    (h₀ : Integrable (fun w => u w*v w)) :
    (∫ w : ℝ×ℝ, u w*vx w) = -(∫ w : ℝ×ℝ, ux w*v w) := by
  change (∫ w : ℝ×ℝ, u w*vx w ∂volume.prod volume)= -(∫ w : ℝ×ℝ, ux w*v w ∂volume.prod volume)
  rw [integral_prod_symm _ h₁,integral_prod_symm _ h₂,← integral_neg]
  apply integral_congr_ae
  filter_upwards [h₁.prod_left_ae,h₂.prod_left_ae,h₀.prod_left_ae] with y hy₁ hy₂ hy₀
  exact integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hu x y) (fun x _ => hv x y) hy₁ hy₂ hy₀

private theorem partsY (u uy v vy : ℝ×ℝ→ℂ)
    (hu : ∀ x y : ℝ,HasDerivAt (fun Y => u (x,Y)) (uy (x,y)) y)
    (hv : ∀ x y : ℝ,HasDerivAt (fun Y => v (x,Y)) (vy (x,y)) y)
    (h₁ : Integrable (fun w => u w*vy w)) (h₂ : Integrable (fun w => uy w*v w))
    (h₀ : Integrable (fun w => u w*v w)) :
    (∫ w : ℝ×ℝ, u w*vy w) = -(∫ w : ℝ×ℝ, uy w*v w) := by
  change (∫ w : ℝ×ℝ, u w*vy w ∂volume.prod volume)= -(∫ w : ℝ×ℝ, uy w*v w ∂volume.prod volume)
  rw [integral_prod _ h₁,integral_prod _ h₂,← integral_neg]
  apply integral_congr_ae
  filter_upwards [h₁.prod_right_ae,h₂.prod_right_ae,h₀.prod_right_ae] with x hx₁ hx₂ hx₀
  exact integral_mul_deriv_eq_deriv_mul_of_integrable (fun y _ => hu x y) (fun y _ => hv x y) hx₁ hx₂ hx₀

abbrev Static (f : ℝ×ℝ→ℂ) := Growth (fun _ : Unit => f)
noncomputable def Z (t : ℂ) (w : ℝ×ℝ) := G t w.1 w.2
theorem contZ (t : ℂ) : Continuous (Z t) := by unfold Z G B Q;fun_prop
theorem contLy (t : ℂ) : Continuous (fun w : ℝ×ℝ => Ly t w.1 w.2) := by unfold Ly;fun_prop
theorem contLxy (t : ℂ) : Continuous (fun w : ℝ×ℝ => Lxy t w.1 w.2) := by unfold Lxy Lx Ly;fun_prop

theorem integrate (t : ℂ) (ht : ‖t‖<1) {f : ℝ×ℝ→ℂ} (hf : Static f) (hm : Measurable f) :
    Integrable (fun w => Z t w*f w) := by
  obtain ⟨B,hB,h⟩ := majorant hf (norm_nonneg t) ht
  exact hB.mono' ((contZ t).measurable.mul hm).aestronglyMeasurable (Eventually.of_forall (h ⟨t,le_rfl⟩ ()))

theorem gaussian_parts (t : ℂ) (ht : ‖t‖<1) {f fx fxy : ℝ×ℝ→ℂ}
    (h₀ : Static f) (h₁ : Static fx) (h₂ : Static fxy)
    (m₀ : Measurable f) (m₁ : Measurable fx) (m₂ : Measurable fxy)
    (hX : ∀ x y : ℝ,HasDerivAt (fun X => f (X,y)) (fx (x,y)) x)
    (hY : ∀ x y : ℝ,HasDerivAt (fun Y => fx (x,Y)) (fxy (x,y)) y) :
    (∫ w : ℝ×ℝ, Z t w*(Lxy t w.1 w.2*f w)) =
      ∫ w : ℝ×ℝ, Z t w*fxy w := by
  let dy := fun w : ℝ×ℝ => Ly t w.1 w.2
  let dxy := fun w : ℝ×ℝ => Lxy t w.1 w.2
  let selector := fun _ : Unit => (⟨t,le_rfl⟩ : Disc ‖t‖)
  have hy : Static dy := (growth_y (norm_nonneg t) ht).comp selector
  have hxy : Static dxy := (growth_xy (norm_nonneg t) ht).comp selector
  have md : Measurable dy := (contLy t).measurable
  have mxy : Measurable dxy := (contLxy t).measurable
  have iu : Integrable (fun w => (Z t w*dy w)*f w) := by
    simpa only [mul_assoc] using integrate t ht (f:=fun w => dy w*f w) (hy.mul h₀) (md.mul m₀)
  have iv : Integrable (fun w => (Z t w*dy w)*fx w) := by
    simpa only [mul_assoc] using integrate t ht (f:=fun w => dy w*fx w) (hy.mul h₁) (md.mul m₁)
  have ixy : Integrable (fun w => (Z t w*dxy w)*f w) := by
    simpa only [mul_assoc] using integrate t ht (f:=fun w => dxy w*f w) (hxy.mul h₀) (mxy.mul m₀)
  have hx := partsX (fun w => Z t w*dy w) (fun w => Z t w*dxy w) f fx (xyG t ht) hX iv ixy iu
  have hy' := partsY (Z t) (fun w => Z t w*dy w) fx fxy (yG t ht) hY
    (integrate t ht h₂ m₂) iv (integrate t ht h₁ m₁)
  calc
    _ = ∫ w : ℝ×ℝ,(Z t w*dxy w)*f w := by simp only [dxy,mul_assoc]
    _ = -(∫ w : ℝ×ℝ,(Z t w*dy w)*fx w) := by rw [hx,neg_neg]
    _ = _ := hy'.symm

end CQPriceIntegration


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

theorem response (f g : ℂ→ℝ×ℝ→ℂ) (z : ℂ) (hz : ‖z‖<1) (fx fxy : ℝ×ℝ→ℂ)
    (m₀ : ∀ t : ℂ, ‖t‖<1 → Measurable (f t)) (m₁ : ∀ t : ℂ, ‖t‖<1 → Measurable (g t))
    (h₀ : ∀ R : ℝ, 0≤R → R<1 → Growth (fun i : Disc R => f i.val))
    (h₁ : ∀ R : ℝ, 0≤R → R<1 → Growth (fun i : Disc R => g i.val))
    (hd : ∀ (t : ℂ), ‖t‖<1 → ∀ w : ℝ×ℝ, HasDerivAt (fun t => f t w) (g t w) t)
    (hx : Static fx) (hxy : Static fxy) (mx : Measurable fx) (mxy : Measurable fxy)
    (dX : ∀ x y : ℝ,HasDerivAt (fun X => f z (X,y)) (fx (x,y)) x)
    (dY : ∀ x y : ℝ,HasDerivAt (fun Y => fx (x,Y)) (fxy (x,y)) y) :
    HasDerivAt (fun t => ∫ w : ℝ×ℝ, density (-t) w.1 w.2*f t w)
      ((∫ w : ℝ×ℝ, density (-z) w.1 w.2*g z w)-
        ∫ w : ℝ×ℝ, density (-z) w.1 w.2*fxy w) z := by
  have hn : ‖-z‖<1 := by simpa
  have hf : Static (f z) := (h₀ ‖z‖ (norm_nonneg z) hz).comp (fun _ : Unit => (⟨z,le_rfl⟩ : Disc ‖z‖))
  have hp := gaussian_parts (-z) hn hf hx hxy (m₀ z hz) mx mxy dX dY
  have h := under_integral f g z hz m₀ m₁ h₀ h₁ hd
  rw [hp] at h
  apply h.congr_deriv
  simp only [Z,density_eq _ hn]

end CQPriceIntegration


open MeasureTheory GrothendieckLB.Supplement.CQPrice CQPriceGrowth CQPriceIntegration

theorem solution (f g fx fxy : ℂ → ℝ×ℝ → ℂ) (z : ℂ) (hz : ‖z‖<1)
    (hm : ∀ H∈[f,g,fx,fxy], ∀ t : ℂ, ‖t‖<1 → Measurable (H t))
    (hp : ∀ H∈[f,g,fx,fxy], ∀ R : ℝ, 0≤R → R<1 → ∃ C : ℝ, 0≤C ∧ ∃ k : ℕ,
      ∀ t : ℂ, ‖t‖≤R → ∀ w : ℝ×ℝ, ‖H t w‖≤ C*((1+|w.1|)*(1+|w.2|))^k)
    (hd : ∀ t : ℂ, ‖t‖<1 → ∀ w : ℝ×ℝ, HasDerivAt (fun s : ℂ => f s w) (g t w) t)
    (hx : ∀ x y : ℝ, HasDerivAt (fun X : ℝ => f z (X,y)) (fx z (x,y)) x)
    (hy : ∀ x y : ℝ, HasDerivAt (fun Y : ℝ => fx z (x,Y)) (fxy z (x,y)) y) :
    HasDerivAt (fun t : ℂ => ∫ w : ℝ×ℝ, density (-t) w.1 w.2*f t w)
      ((∫ w : ℝ×ℝ, density (-z) w.1 w.2*g z w)-
        ∫ w : ℝ×ℝ, density (-z) w.1 w.2*fxy z w) z := by
  have hG (H) (hH : H∈[f,g,fx,fxy]) (R : ℝ) (hR : 0≤R) (hR' : R<1) : Growth (fun i : Disc R => H i.val) := by
    obtain ⟨C,hC,k,hk⟩ := hp _ hH R hR hR'
    exact ⟨C,hC,k, fun i w => hk _ i.property w⟩
  have hS (H) (hH : H∈[f,g,fx,fxy]) : Static (H z) := (hG H hH _ (norm_nonneg _) hz).comp (fun _ : Unit => (⟨z,le_rfl⟩ : Disc ‖z‖))
  exact response f g z hz (fx z) (fxy z) (hm f (by simp)) (hm g (by simp)) (hG f (by simp)) (hG g (by simp))
    hd (hS fx (by simp)) (hS fxy (by simp)) (hm fx (by simp) z hz) (hm fxy (by simp) z hz) hx hy