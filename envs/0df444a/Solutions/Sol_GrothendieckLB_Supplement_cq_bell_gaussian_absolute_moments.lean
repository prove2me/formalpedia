-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_bell_gaussian_absolute_moments
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:28:19.343444+00:00
-- url     : https://prove2.me/submissions/d3cf8028-8d6f-44ef-81fa-ef4df77ff1c1

import Definitions.Def_GrothendieckLB_Supplement_cqPriceKernels
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.IntervalCases


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


open MeasureTheory Real GrothendieckLB.Supplement.CQPrice CQGaussianMoment
namespace CQBellMoments

private abbrev cap : ℝ := 0.05265

private theorem delta_bounds : 0 ≤ delta ∧ delta ≤ cap := by
  unfold delta
  have hp : 0<(6*(1+0.34101124^2+0.05276111^2):ℝ) := by norm_num
  have hs := Real.sqrt_pos.mpr hp
  refine ⟨by positivity, (div_le_iff₀ hs).mpr ?_⟩
  dsimp [cap]
  nlinarith only [hs, Real.sq_sqrt hp.le, sq_nonneg (0.05265*Real.sqrt (6*(1+0.34101124^2+0.05276111^2))-0.136419125),
    mul_self_nonneg (Real.sqrt (6*(1+0.34101124^2+0.05276111^2)))]

private theorem inverse_pi : 1/Real.sqrt Real.pi ≤ (0.565:ℝ) := by
  rw [div_le_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)]
  nlinarith only [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_pos.mpr Real.pi_pos, Real.pi_gt_d2]

noncomputable def mask : ℕ → ℝ → ℝ
  | 0,_ => 1
  | 1,x => |x|^2+1
  | n+2,x => (|x|^2-1)^2 * mask n x

private theorem mask_bound (x : ℝ) : ∀ l : ℕ, |x^2-1|^l ≤ mask l x
  | 0 => by simp [mask]
  | 1 => by simp only [mask,pow_one,sq_abs];exact abs_le.mpr ⟨by nlinarith [sq_nonneg x],by linarith⟩
  | n+2 => by
    rw [mask,pow_add,sq_abs,sq_abs,mul_comm]
    exact mul_le_mul_of_nonneg_left (mask_bound x n) (sq_nonneg _)

noncomputable def envelope : List Piece → ℝ → ℝ
  | [], _ => 0
  | e::es, x => (e.c:ℝ)*|x|^e.b*mask e.l x+envelope es x

private theorem bound_list (ps : List Piece) (x : ℝ) :
    |(ps.map (fun e => (e.c:ℝ)*x^e.b*(x^2-1)^e.l)).sum| ≤ envelope ps x := by
  induction ps with
  | nil => simp [envelope]
  | cons e es ih =>
    simp only [List.map_cons,List.sum_cons,envelope]
    apply (abs_add_le _ _).trans
    apply add_le_add _ ih
    rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_pow,abs_pow]
    exact mul_le_mul_of_nonneg_left (mask_bound x _) (by positivity)

private theorem continuous_sum (ps : List Piece) :
    Continuous (fun x : ℝ => (ps.map (fun e => (e.c:ℝ)*x^e.b*(x^2-1)^e.l)).sum) := by
  induction ps with
  | nil => simp;fun_prop
  | cons e es ih =>
    simp only [List.map_cons,List.sum_cons]
    apply Continuous.add _ ih
    fun_prop

noncomputable def poly : List (ℕ×ℤ) → ℝ → ℝ
  | [],_ => 0
  | (k,c)::ts,x => (c:ℝ)*(normalTwo x*|x|^k)+poly ts x
noncomputable def values : List (ℕ×ℤ) → ℝ
  | [] => 0
  | (k,c)::ts => (c:ℝ)*normal k+values ts

private theorem poly_int (ts : List (ℕ×ℤ)) :
    Integrable (poly ts) ∧ (∫ x : ℝ, poly ts x)=values ts := by
  induction ts with
  | nil => simp [poly,values,integrable_zero]
  | cons t ts ih =>
    rcases t with ⟨k,c⟩
    have h := (normal_integrable k).const_mul (c:ℝ)
    refine ⟨h.add ih.1,?_⟩
    change (∫ x : ℝ, (c:ℝ)*(normalTwo x*|x|^k)+poly ts x)=_
    rw [integral_add h ih.1,integral_const_mul,ih.2]
    rfl

private theorem from_data (a i : ℕ) (ts : List (ℕ×ℤ))
    (hmodel : ∀ x : ℝ, normalTwo x * envelope (pieces a i) x = poly ts x)
    (hnum : cap^i*values ts ≤ (bellUnits a i:ℝ)/(2:ℝ)^64) :
    Integrable (fun x : ℝ => normalTwo x * |bell a i x|) ∧
    (∫ x : ℝ, normalTwo x * |bell a i x|) ≤ (bellUnits a i:ℝ)/(2:ℝ)^64 := by
  have hn (x : ℝ) : 0 ≤ normalTwo x := by unfold normalTwo;positivity
  have hdom (x : ℝ) : normalTwo x * |bell a i x| ≤ cap^i*poly ts x := by
    rw [bell,abs_mul,abs_pow,abs_of_nonneg delta_bounds.1,← hmodel]
    calc
      _ ≤ normalTwo x * (cap^i * envelope (pieces a i) x) := by
        apply mul_le_mul_of_nonneg_left _ (hn x)
        exact mul_le_mul (pow_le_pow_left₀ delta_bounds.1 delta_bounds.2 i) (bound_list _ x) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have htop := (poly_int ts).1.const_mul (cap^i)
  have hb : Continuous (fun x : ℝ => bell a i x) := continuous_const.mul (continuous_sum _)
  have hmeas : Continuous (fun x : ℝ => normalTwo x * |bell a i x|) := by
    apply Continuous.mul _ hb.abs
    unfold normalTwo
    fun_prop
  have hint : Integrable (fun x : ℝ => normalTwo x * |bell a i x|) :=
    htop.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hn x) (abs_nonneg _))] using hdom x)
  refine ⟨hint,?_⟩
  exact (integral_mono hint htop hdom).trans (by rw [integral_const_mul,(poly_int ts).2];exact hnum)

private theorem v0 : normal 0=1 := by rw [normal_zero]

private theorem v1 : normal 1=2*(1/Real.sqrt Real.pi) := by rw [normal_one];ring

private theorem v2 : normal 2=2 := by rw [show 2=0+2 by decide,normal_step,v0];norm_num <;> ring

private theorem v3 : normal 3=8*(1/Real.sqrt Real.pi) := by rw [show 3=1+2 by decide,normal_step,v1];norm_num <;> ring

private theorem v4 : normal 4=12 := by rw [show 4=2+2 by decide,normal_step,v2];norm_num <;> ring

private theorem v5 : normal 5=64*(1/Real.sqrt Real.pi) := by rw [show 5=3+2 by decide,normal_step,v3];norm_num <;> ring

private theorem v6 : normal 6=120 := by rw [show 6=4+2 by decide,normal_step,v4];norm_num <;> ring

private theorem v7 : normal 7=768*(1/Real.sqrt Real.pi) := by rw [show 7=5+2 by decide,normal_step,v5];norm_num <;> ring

private theorem v8 : normal 8=1680 := by rw [show 8=6+2 by decide,normal_step,v6];norm_num <;> ring

private theorem v9 : normal 9=12288*(1/Real.sqrt Real.pi) := by rw [show 9=7+2 by decide,normal_step,v7];norm_num <;> ring

private theorem v10 : normal 10=30240 := by rw [show 10=8+2 by decide,normal_step,v8];norm_num <;> ring

private theorem case0_0 :
    Integrable (fun x : ℝ => normalTwo x * |bell 0 0 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 0 0 x|) ≤ (bellUnits 0 0:ℝ)/(2:ℝ)^64 := by
  apply from_data 0 0 [(0,1)]
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case1_0 :
    Integrable (fun x : ℝ => normalTwo x * |bell 1 0 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 1 0 x|) ≤ (bellUnits 1 0:ℝ)/(2:ℝ)^64 := by
  apply from_data 1 0 []
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case1_1 :
    Integrable (fun x : ℝ => normalTwo x * |bell 1 1 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 1 1 x|) ≤ (bellUnits 1 1:ℝ)/(2:ℝ)^64 := by
  apply from_data 1 1 [(0,3), (2,3)]
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case2_0 :
    Integrable (fun x : ℝ => normalTwo x * |bell 2 0 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 2 0 x|) ≤ (bellUnits 2 0:ℝ)/(2:ℝ)^64 := by
  apply from_data 2 0 []
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case2_1 :
    Integrable (fun x : ℝ => normalTwo x * |bell 2 1 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 2 1 x|) ≤ (bellUnits 2 1:ℝ)/(2:ℝ)^64 := by
  apply from_data 2 1 [(1,6)]
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case2_2 :
    Integrable (fun x : ℝ => normalTwo x * |bell 2 2 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 2 2 x|) ≤ (bellUnits 2 2:ℝ)/(2:ℝ)^64 := by
  apply from_data 2 2 [(0,9), (2,-18), (4,9)]
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case3_0 :
    Integrable (fun x : ℝ => normalTwo x * |bell 3 0 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 3 0 x|) ≤ (bellUnits 3 0:ℝ)/(2:ℝ)^64 := by
  apply from_data 3 0 []
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case3_1 :
    Integrable (fun x : ℝ => normalTwo x * |bell 3 1 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 3 1 x|) ≤ (bellUnits 3 1:ℝ)/(2:ℝ)^64 := by
  apply from_data 3 1 [(0,6)]
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case3_2 :
    Integrable (fun x : ℝ => normalTwo x * |bell 3 2 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 3 2 x|) ≤ (bellUnits 3 2:ℝ)/(2:ℝ)^64 := by
  apply from_data 3 2 [(1,54), (3,54)]
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case3_3 :
    Integrable (fun x : ℝ => normalTwo x * |bell 3 3 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 3 3 x|) ≤ (bellUnits 3 3:ℝ)/(2:ℝ)^64 := by
  apply from_data 3 3 [(0,27), (2,-27), (4,-27), (6,27)]
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case4_0 :
    Integrable (fun x : ℝ => normalTwo x * |bell 4 0 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 4 0 x|) ≤ (bellUnits 4 0:ℝ)/(2:ℝ)^64 := by
  apply from_data 4 0 []
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case4_1 :
    Integrable (fun x : ℝ => normalTwo x * |bell 4 1 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 4 1 x|) ≤ (bellUnits 4 1:ℝ)/(2:ℝ)^64 := by
  apply from_data 4 1 []
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case4_2 :
    Integrable (fun x : ℝ => normalTwo x * |bell 4 2 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 4 2 x|) ≤ (bellUnits 4 2:ℝ)/(2:ℝ)^64 := by
  apply from_data 4 2 [(0,72), (2,180)]
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case4_3 :
    Integrable (fun x : ℝ => normalTwo x * |bell 4 3 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 4 3 x|) ≤ (bellUnits 4 3:ℝ)/(2:ℝ)^64 := by
  apply from_data 4 3 [(1,324), (3,-648), (5,324)]
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case4_4 :
    Integrable (fun x : ℝ => normalTwo x * |bell 4 4 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 4 4 x|) ≤ (bellUnits 4 4:ℝ)/(2:ℝ)^64 := by
  apply from_data 4 4 [(0,81), (2,-324), (4,486), (6,-324), (8,81)]
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case5_0 :
    Integrable (fun x : ℝ => normalTwo x * |bell 5 0 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 5 0 x|) ≤ (bellUnits 5 0:ℝ)/(2:ℝ)^64 := by
  apply from_data 5 0 []
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case5_1 :
    Integrable (fun x : ℝ => normalTwo x * |bell 5 1 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 5 1 x|) ≤ (bellUnits 5 1:ℝ)/(2:ℝ)^64 := by
  apply from_data 5 1 []
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case5_2 :
    Integrable (fun x : ℝ => normalTwo x * |bell 5 2 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 5 2 x|) ≤ (bellUnits 5 2:ℝ)/(2:ℝ)^64 := by
  apply from_data 5 2 [(1,360)]
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case5_3 :
    Integrable (fun x : ℝ => normalTwo x * |bell 5 3 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 5 3 x|) ≤ (bellUnits 5 3:ℝ)/(2:ℝ)^64 := by
  apply from_data 5 3 [(0,540), (2,540), (4,2160)]
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case5_4 :
    Integrable (fun x : ℝ => normalTwo x * |bell 5 4 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 5 4 x|) ≤ (bellUnits 5 4:ℝ)/(2:ℝ)^64 := by
  apply from_data 5 4 [(1,1620), (3,-1620), (5,-1620), (7,1620)]
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

private theorem case5_5 :
    Integrable (fun x : ℝ => normalTwo x * |bell 5 5 x|) ∧
    (∫ x : ℝ, normalTwo x * |bell 5 5 x|) ≤ (bellUnits 5 5:ℝ)/(2:ℝ)^64 := by
  apply from_data 5 5 [(0,243), (2,-729), (4,486), (6,486), (8,-729), (10,243)]
  · intro x
    norm_num [envelope,mask,pieces,poly]
    all_goals try rw [← sq_abs x]
    all_goals ring
  · have hp := inverse_pi
    norm_num [one_div] at hp
    norm_num [cap,values,bellUnits,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] <;> linarith only [hp]

end CQBellMoments

open CQBellMoments
theorem solution (a i : ℕ) (ha : a≤5) (hi : i≤a) :
    Integrable (fun x : ℝ => normalTwo x * |bell a i x|) ∧
    (∫ x : ℝ, normalTwo x * |bell a i x|) ≤ (bellUnits a i:ℝ)/(2:ℝ)^64 := by
  interval_cases a <;> interval_cases i <;> first
    | exact CQBellMoments.case0_0
    | exact CQBellMoments.case1_0
    | exact CQBellMoments.case1_1
    | exact CQBellMoments.case2_0
    | exact CQBellMoments.case2_1
    | exact CQBellMoments.case2_2
    | exact CQBellMoments.case3_0
    | exact CQBellMoments.case3_1
    | exact CQBellMoments.case3_2
    | exact CQBellMoments.case3_3
    | exact CQBellMoments.case4_0
    | exact CQBellMoments.case4_1
    | exact CQBellMoments.case4_2
    | exact CQBellMoments.case4_3
    | exact CQBellMoments.case4_4
    | exact CQBellMoments.case5_0
    | exact CQBellMoments.case5_1
    | exact CQBellMoments.case5_2
    | exact CQBellMoments.case5_3
    | exact CQBellMoments.case5_4
    | exact CQBellMoments.case5_5
