-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_sextic_initial_integrals
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T17:46:49.07825+00:00
-- url     : https://prove2.me/submissions/8db5f43a-8e74-4c26-81b0-410b1159549f

import Definitions.Def_GrothendieckLB_Supplement_cqSexticHead
import Mathlib

open MeasureTheory Real Set Finset Filter
open GrothendieckLB.Supplement
namespace SexticIntegralCertificate

-- P(9t) = (A t² - B t⁴ + D t⁶)/Q, and H = A - B + D.
private def A : ℤ := 2477493360792183177
private def B : ℤ := 3256036684402353750
private def D : ℤ := 43956495239431775625
private def H : ℤ := 43177951915821605052
private def Q : ℤ := 59683861361854384
private def scale : ℤ := 2^1800

private structure Box where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq

private def plus (x y : Box) : Box := ⟨x.lo+y.lo,x.hi+y.hi⟩
private def minus (x y : Box) : Box := ⟨x.lo-y.hi,x.hi-y.lo⟩
private def times (x : Box) (c : ℤ) : Box := ⟨c*x.lo,c*x.hi⟩
private def quot (x : Box) (c : ℤ) : Box := ⟨x.lo/c,-((-x.hi)/c)⟩

private structure State where
  q : Box
  j0 : Box
  j2 : Box
  j4 : Box
  t0 : Box
  t2 : Box
  t4 : Box
  deriving DecidableEq

private def start : State :=
  let o : Box := ⟨scale,scale⟩
  let z : Box := ⟨0,0⟩
  ⟨o,o,quot o 3,quot o 5,z,z,z⟩

private def high (m k : ℤ) (q x y : Box) : Box :=
  quot (plus (minus (times q H) (times x ((2*m+k+1)*A))) (times y ((4*m+k+1)*B)))
    ((6*m+k+1)*D)

private def nextJ (m : ℤ) (x y z : Box) : Box :=
  quot (plus (minus (times x A) (times y B)) (times z D)) (Q*m)

private def advance (n : ℕ) (st : State) : State :=
  let m : ℤ := n+1
  let j6 := high m 0 st.q st.j2 st.j4
  let j8 := high m 2 st.q st.j4 j6
  let j10 := high m 4 st.q j6 j8
  let acc := if n%2=0 then plus else minus
  ⟨quot (times st.q H) (Q*m),nextJ m st.j2 st.j4 j6,nextJ m st.j4 j6 j8,
    nextJ m j6 j8 j10, acc st.t0 st.j0, acc st.t2 st.j2, acc st.t4 st.j4⟩

private def iterate : ℕ → State
  | 0 => start
  | n+1 => advance n (iterate n)

private def cellOK (q t : Box) (k : ℕ) (lower : ℤ) : Prop :=
  lower * 2^1416 ≤ 2*9^(k+1)*(t.lo-2*q.hi) ∧
    2*9^(k+1)*(t.hi+2*q.hi)+48*2^1200 ≤ (lower+1)*2^1416

private instance (q t : Box) (k : ℕ) (lo : ℤ) : Decidable (cellOK q t k lo) := by
  unfold cellOK
  infer_instance

private def lower0 : ℤ := 98100829642129577717705252461250802877285043994588462406870607474137489297660729170734376455389328977175112900544138
private def lower2 : ℤ := 95020680131779427752407447234488278202461530610309981184152310885588522728819096259031464439548105786990997297548714
private def lower4 : ℤ := 262876500006536681973879627718902500274060155065983995563998798928285304964789315907500644382597812284962670046502317
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem arithmetic : let st := iterate 2400
          cellOK st.q st.t0 0 lower0 ∧ cellOK st.q st.t2 2 lower2 ∧ cellOK st.q st.t4 4 lower4 := by
  decide +kernel

private def contains (b : Box) (x : ℝ) : Prop := (b.lo:ℝ) ≤ x ∧ x ≤ (b.hi:ℝ)

private theorem plus_sound {b c : Box} {x y : ℝ} (hx : contains b x) (hy : contains c y) :
    contains (plus b c) (x+y) := by
  simpa [contains, plus] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

private theorem minus_sound {b c : Box} {x y : ℝ} (hx : contains b x) (hy : contains c y) :
    contains (minus b c) (x-y) := by
  simpa [contains, minus] using And.intro (sub_le_sub hx.1 hy.2) (sub_le_sub hx.2 hy.1)

private theorem times_sound {b : Box} {x : ℝ} (hx : contains b x) {c : ℤ} (hc : 0 ≤ c) :
    contains (times b c) ((c:ℝ)*x) := by
  have hp : 0 ≤ (c:ℝ) := by exact_mod_cast hc
  simpa [contains, times] using And.intro (mul_le_mul_of_nonneg_left hx.1 hp)
    (mul_le_mul_of_nonneg_left hx.2 hp)

private theorem quot_sound {b : Box} {x : ℝ} (hx : contains b x) {c : ℤ} (hc : 0 < c) :
    contains (quot b c) (x/(c:ℝ)) := by
  have hp : 0 < (c:ℝ) := by exact_mod_cast hc
  have hl : (↑(b.lo / c) : ℝ)*(c:ℝ) ≤ (b.lo:ℝ) := by exact_mod_cast Int.ediv_mul_le _ hc.ne'
  have hu : (↑((-b.hi)/c) : ℝ)*(c:ℝ) ≤ -(b.hi:ℝ) := by exact_mod_cast Int.ediv_mul_le _ hc.ne'
  constructor
  · exact (le_div_iff₀ hp).2 (hl.trans hx.1)
  · apply (div_le_iff₀ hp).2
    simp only [quot, Int.cast_neg, neg_mul]
    linarith only [hu,hx.2]

private noncomputable def pot (t : ℝ) : ℝ := ((A:ℝ)*t^2-(B:ℝ)*t^4+(D:ℝ)*t^6)/(Q:ℝ)
private noncomputable def top : ℝ := (H:ℝ)/(Q:ℝ)
private noncomputable def mon (n k : ℕ) (t : ℝ) : ℝ := t^k * pot t^n
private noncomputable def raw (n k : ℕ) := ∫ t : ℝ in 0..1, mon n k t
private noncomputable def weight (n k : ℕ) : ℝ := (scale:ℝ)/(n.factorial:ℝ)*raw n k
private noncomputable def mass (n : ℕ) : ℝ := (scale:ℝ)/(n.factorial:ℝ)*top^n
private noncomputable def accVal (n k : ℕ) : ℝ := ∑ j ∈ Finset.range n, (-1:ℝ)^j*weight j k

private theorem pot_cont : Continuous pot := by unfold pot; fun_prop
private theorem mon_cont (n k : ℕ) : Continuous (mon n k) := (continuous_id.pow k).mul (pot_cont.pow n)
private theorem pot_at_one : pot 1 = top := by norm_num [pot,top,A,B,D,H,Q]
private theorem Q_pos : 0 < (Q:ℝ) := by norm_num [Q]
private theorem D_pos : 0 < (D:ℝ) := by norm_num [D]

private theorem pot_deriv (t : ℝ) :
    HasDerivAt pot ((2*(A:ℝ)*t-4*(B:ℝ)*t^3+6*(D:ℝ)*t^5)/(Q:ℝ)) t := by
  apply (((((hasDerivAt_pow 2 t).const_mul (A:ℝ)).sub
    ((hasDerivAt_pow 4 t).const_mul (B:ℝ))).add
    ((hasDerivAt_pow 6 t).const_mul (D:ℝ))).div_const (Q:ℝ)).congr_deriv
  norm_num
  ring

private theorem linear_integral (n k : ℕ) (a b d : ℝ) :
    (∫ x : ℝ in 0..1, a*mon n (k+2) x - b*mon n (k+4) x + d*mon n (k+6) x) =
      a*raw n (k+2)-b*raw n (k+4)+d*raw n (k+6) := by
  have h (c : ℝ) (j : ℕ) : IntervalIntegrable (fun t => c*mon n j t) volume 0 1 :=
    (continuous_const.mul (mon_cont n j)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add ((h a _).sub (h b _)) (h d _),
    intervalIntegral.integral_sub (h a _) (h b _)]
  simp only [intervalIntegral.integral_const_mul,raw]

private theorem raw_high (n k : ℕ) :
    let m : ℝ := n+1
    ((6*m+(k:ℝ)+1)*(D:ℝ))*raw n (k+6) =
      (H:ℝ)*top^n-((2*m+(k:ℝ)+1)*(A:ℝ))*raw n (k+2)+
      ((4*m+(k:ℝ)+1)*(B:ℝ))*raw n (k+4) := by
  let m : ℝ := n+1
  let a : ℝ := (2*m+(k:ℝ)+1)*(A:ℝ)
  let b : ℝ := (4*m+(k:ℝ)+1)*(B:ℝ)
  let d : ℝ := (6*m+(k:ℝ)+1)*(D:ℝ)
  let f (t : ℝ) := (Q:ℝ)*t^(k+1)*pot t^(n+1)
  let g (t : ℝ) := a*mon n (k+2) t-b*mon n (k+4) t+d*mon n (k+6) t
  have der (t : ℝ) : HasDerivAt f (g t) t := by
    apply (((hasDerivAt_pow (k+1) t).const_mul (Q:ℝ)).mul ((pot_deriv t).pow (n+1))).congr_deriv
    dsimp only [g, a, b, d, m, mon]
    simp only [Nat.cast_succ, Nat.add_sub_cancel, Pi.pow_apply, Pi.mul_apply, pow_succ (pot t)]
    rw [show pot t = ((A:ℝ)*t^2-(B:ℝ)*t^4+(D:ℝ)*t^6)/(Q:ℝ) from rfl]
    simp only [pow_add, pow_one]
    field_simp [Q_pos.ne'] <;> ring
  have hint : IntervalIntegrable g volume 0 1 :=
    (((continuous_const.mul (mon_cont n _)).sub (continuous_const.mul (mon_cont n _))).add
      (continuous_const.mul (mon_cont n _))).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => der t) hint
  change (∫ t : ℝ in 0..1, a*mon n (k+2) t-b*mon n (k+4) t+d*mon n (k+6) t) = f 1-f 0 at he
  rw [linear_integral] at he
  have hc : (Q:ℝ)*top=(H:ℝ) := by unfold top; field_simp [Q_pos.ne']
  simp only [f,one_pow,mul_one,pot_at_one,zero_pow (Nat.succ_ne_zero k),mul_zero,
    zero_mul,sub_zero,pow_succ top] at he
  change d*raw n (k+6) = (H:ℝ)*top^n-a*raw n (k+2)+b*raw n (k+4)
  linear_combination he + top^n*hc

private theorem raw_next (n k : ℕ) :
    (Q:ℝ)*raw (n+1) k = (A:ℝ)*raw n (k+2)-(B:ℝ)*raw n (k+4)+(D:ℝ)*raw n (k+6) := by
  rw [← linear_integral, raw, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [mon, pow_succ (pot x)]
  unfold pot
  simp only [pow_add]
  field_simp [Q_pos.ne'] <;> ring

private theorem weight_high (n k : ℕ) :
    let m : ℝ := n+1
    weight n (k+6) = ((H:ℝ)*mass n - ((2*m+(k:ℝ)+1)*(A:ℝ))*weight n (k+2) +
      ((4*m+(k:ℝ)+1)*(B:ℝ))*weight n (k+4))/((6*m+(k:ℝ)+1)*(D:ℝ)) := by
  dsimp only
  apply (eq_div_iff (mul_pos (by positivity) D_pos).ne').2
  unfold weight mass
  linear_combination ((scale:ℝ)/(n.factorial:ℝ)) * raw_high n k

private theorem weight_next (n k : ℕ) :
    weight (n+1) k = ((A:ℝ)*weight n (k+2)-(B:ℝ)*weight n (k+4)+(D:ℝ)*weight n (k+6)) /
      ((Q:ℝ)*((n:ℝ)+1)) := by
  apply (eq_div_iff (mul_pos Q_pos (by positivity)).ne').2
  unfold weight
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp
  linear_combination (scale:ℝ) * raw_next n k

private theorem mass_next (n : ℕ) :
    mass (n+1) = (H:ℝ)*mass n/((Q:ℝ)*((n:ℝ)+1)) := by
  unfold mass
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
  unfold top
  field_simp [Q_pos.ne'] <;> ring

private theorem high_sound {n k : ℕ} {q x y : Box}
    (hq : contains q (mass n)) (hx : contains x (weight n (k+2))) (hy : contains y (weight n (k+4))) :
    contains (high ((n:ℤ)+1) k q x y) (weight n (k+6)) := by
  have hA : 0 ≤ A := by decide
  have hB : 0 ≤ B := by decide
  have hD : 0 < D := by decide
  have hH : 0 ≤ H := by decide
  let m : ℤ := n+1
  have hm : 0 < m := by dsimp [m]; positivity
  have hz := quot_sound (plus_sound (minus_sound (times_sound hq hH)
      (times_sound hx (c:=(2*m+(k:ℤ)+1)*A) (by positivity)))
      (times_sound hy (c:=(4*m+(k:ℤ)+1)*B) (by positivity)))
      (c:=(6*m+(k:ℤ)+1)*D) (by positivity)
  rw [weight_high]
  simpa only [high,m,Int.cast_mul,Int.cast_add,Int.cast_one,Int.cast_natCast,Int.cast_ofNat] using hz

private theorem next_sound {n k : ℕ} {x y z : Box}
    (hx : contains x (weight n (k+2))) (hy : contains y (weight n (k+4))) (hz : contains z (weight n (k+6))) :
    contains (nextJ ((n:ℤ)+1) x y z) (weight (n+1) k) := by
  have hQ : 0 < Q := by decide
  have hh := quot_sound (plus_sound (minus_sound (times_sound hx (c:=A) (by decide))
      (times_sound hy (c:=B) (by decide))) (times_sound hz (c:=D) (by decide)))
      (c:=Q*((n:ℤ)+1)) (by positivity)
  rw [weight_next]
  simpa only [nextJ,Int.cast_mul,Int.cast_add,Int.cast_one,Int.cast_natCast] using hh

private theorem acc_sound {n k : ℕ} {t j : Box}
    (ht : contains t (accVal n k)) (hj : contains j (weight n k)) :
    contains ((if n%2=0 then plus else minus) t j) (accVal (n+1) k) := by
  rw [accVal,Finset.sum_range_succ]
  by_cases h : Even n
  · simpa only [if_pos (Nat.even_iff.mp h),h.neg_one_pow,one_mul,accVal] using plus_sound ht hj
  · have hn : Odd n := Nat.not_even_iff_odd.mp h
    simpa only [if_neg (fun he => h (Nat.even_iff.mpr he)),hn.neg_one_pow,neg_one_mul,
      ←sub_eq_add_neg,accVal] using minus_sound ht hj

private structure Valid (st : State) (n : ℕ) : Prop where
  q : contains st.q (mass n)
  j0 : contains st.j0 (weight n 0)
  j2 : contains st.j2 (weight n 2)
  j4 : contains st.j4 (weight n 4)
  t0 : contains st.t0 (accVal n 0)
  t2 : contains st.t2 (accVal n 2)
  t4 : contains st.t4 (accVal n 4)

private theorem valid (n : ℕ) : Valid (iterate n) n := by
  induction n with
  | zero =>
    have hz (k : ℕ) : raw 0 k = 1/((k:ℝ)+1) := by
      simp [raw, mon, integral_pow]
    have hw (k : ℕ) : weight 0 k = (scale:ℝ)/((k:ℝ)+1) := by
      simp [weight,hz,div_eq_mul_inv]
    have ho : contains (⟨scale,scale⟩ : Box) (scale:ℝ) := ⟨le_rfl,le_rfl⟩
    constructor
    · simpa [iterate,start,mass] using ho
    · simpa [iterate,start,hw] using ho
    · simpa [iterate,start,hw,show (2:ℝ)+1=3 by norm_num] using quot_sound ho (c:=3) (by decide)
    · simpa [iterate,start,hw,show (4:ℝ)+1=5 by norm_num] using quot_sound ho (c:=5) (by decide)
    all_goals simp [iterate,start,contains,accVal]
  | succ n ih =>
    have h6 := high_sound (k:=0) ih.q ih.j2 ih.j4
    have h8 := high_sound (k:=2) ih.q ih.j4 h6
    have h10 := high_sound (k:=4) ih.q h6 h8
    constructor
    · have hQ : 0 < Q := by decide
      have h := quot_sound (times_sound ih.q (c:=H) (by decide)) (c:=Q*((n:ℤ)+1)) (by positivity)
      rw [mass_next]
      simpa only [iterate,advance,Int.cast_mul,Int.cast_add,Int.cast_one,Int.cast_natCast] using h
    · exact next_sound ih.j2 ih.j4 h6
    · exact next_sound ih.j4 h6 h8
    · exact next_sound h6 h8 h10
    · exact acc_sound ih.t0 ih.j0
    · exact acc_sound ih.t2 ih.j2
    · exact acc_sound ih.t4 ih.j4

private noncomputable def c : ℝ := 744407106630625/268577376128344728
private noncomputable def potential (x : ℝ) : ℝ := (x^2+c*(x^3-3*x)^2)/2
private theorem c_pos : 0 < c := by norm_num [c]
private theorem rescale (t : ℝ) : pot t = potential (9*t) := by
  unfold pot potential c
  norm_num [A,B,D,Q]
  ring

private theorem pot_range (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : 0 ≤ pot t ∧ pot t≤top := by
  set x : ℝ := 9*t
  have hx : 0 ≤ x := mul_nonneg (by norm_num) ht.1
  have hx9 : x ≤ 9 := by dsimp [x]; linarith only [ht.2]
  have hub : x^3-3*x ≤ 702 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hx9) (by positivity : 0 ≤ x^2+9*x+78)]
  have hlb : -(702:ℝ) ≤ x^3-3*x := by linarith only [pow_nonneg hx 3,hx9]
  have hs : (x^3-3*x)^2 ≤ (702:ℝ)^2 := sq_le_sq' hlb hub
  have hd : x^2 ≤ (9:ℝ)^2 := pow_le_pow_left₀ hx hx9 2
  have htop : top = ((9:ℝ)^2+c*702^2)/2 := by norm_num [top,H,Q,c]
  rw [rescale,htop]
  change 0 ≤ potential x ∧ potential x ≤ _
  exact ⟨div_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg c_pos.le (sq_nonneg _))) (by norm_num),
    div_le_div_of_nonneg_right (add_le_add hd (mul_le_mul_of_nonneg_left hs c_pos.le)) (by norm_num)⟩

private theorem exp_error (n : ℕ) (x : ℝ) (hx : 0 ≤ x) (hn : x/((n:ℝ)+1) ≤ 1/2) :
    |exp (-x)- ∑ j ∈ Finset.range n, (-x)^j/(j.factorial:ℝ)| ≤ x^n/(n.factorial:ℝ)*2 := by
  have hz : ‖((-x:ℝ):ℂ)‖ = x := by simp [abs_of_nonneg hx]
  have h := Complex.exp_bound' (x:=((-x:ℝ):ℂ)) (n:=n) (by rwa [hz,Nat.cast_succ])
  rw [hz] at h
  convert h using 1
  rw [← Real.norm_eq_abs,← Complex.norm_real]
  push_cast
  rfl

private noncomputable def interior (k : ℕ) : ℝ := ∫ t : ℝ in 0..1, t^k*exp (-(pot t))

private theorem interior_enclosure (n k : ℕ) (hn : top/((n:ℝ)+1) ≤ 1/2) :
    |(scale:ℝ)*interior k - accVal n k| ≤ 2*mass n := by
  let w (j : ℕ) : ℝ := (-1:ℝ)^j*((scale:ℝ)/(j.factorial:ℝ))
  let T (t : ℝ) := ∑ j ∈ Finset.range n, w j*mon j k t
  let f (t : ℝ) := (scale:ℝ)*(t^k*exp (-(pot t)))
  have hT : Continuous T := by
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul (mon_cont _ _)
  have hf : Continuous f := continuous_const.mul ((continuous_id.pow _).mul (Real.continuous_exp.comp pot_cont.neg))
  have hTint : (∫ t : ℝ in 0..1, T t) = accVal n k := by
    unfold T
    rw [intervalIntegral.integral_finsetSum (f:=fun j t => w j*mon j k t) (fun j _ =>
      (continuous_const.mul (mon_cont j k)).intervalIntegrable 0 1)]
    simp only [intervalIntegral.integral_const_mul,accVal,weight,raw,w,mul_assoc]
  have hfint : (∫ t : ℝ in 0..1, f t) = (scale:ℝ)*interior k := by
    exact intervalIntegral.integral_const_mul _ _
  have harg (t : ℝ) : f t - T t = ((scale:ℝ)*t^k)*
      (exp (-(pot t)) - ∑ j ∈ Finset.range n, (-(pot t))^j/(j.factorial:ℝ)) := by
    dsimp only [f,T]
    rw [mul_sub,Finset.mul_sum,mul_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    unfold w mon
    rw [neg_eq_neg_one_mul (pot t),mul_pow]
    ring
  have hp (t : ℝ) (ht : t ∈ Set.uIoc (0:ℝ) 1) : ‖f t-T t‖ ≤ 2*mass n := by
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have h := pot_range t ⟨ht.1.le,ht.2⟩
    have he := exp_error n (pot t) h.1 ((div_le_div_of_nonneg_right h.2 (by positivity)).trans hn)
    have hsc : 0 ≤ (scale:ℝ) := by unfold scale; positivity
    have htk : t^k ≤ 1 := pow_le_one₀ ht.1.le ht.2
    rw [Real.norm_eq_abs,harg,abs_mul,abs_of_nonneg (mul_nonneg hsc (pow_nonneg ht.1.le _))]
    calc
      _ ≤ (scale:ℝ)*(top^n/(n.factorial:ℝ)*2) := by
        apply mul_le_mul _ (he.trans _) (abs_nonneg _) hsc
        · exact (mul_le_mul_of_nonneg_left htk hsc).trans_eq (mul_one _)
        · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
            (pow_le_pow_left₀ h.1 h.2 n) (Nat.cast_nonneg _)) (by norm_num)
      _ = 2*mass n := by unfold mass; ring
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const hp
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hT.intervalIntegrable _ _),
    hTint,hfint,Real.norm_eq_abs] at hb
  simpa only [sub_zero,abs_one,mul_one] using hb

private noncomputable def phi (k : ℕ) (x : ℝ) : ℝ := x^k*exp (-(potential x))
private noncomputable def exterior (k : ℕ) : ℝ := ∫ x : ℝ in Ioi 9, phi k x

private theorem phi_integrable (k : ℕ) : Integrable (phi k) := by
  have hg : Integrable fun x : ℝ => x^k*exp (-(1/2:ℝ)*x^2) := by
    simpa only [rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq (by norm_num : 0 < (1/2:ℝ))
      (lt_of_lt_of_le (by norm_num : (-1:ℝ)<0) (Nat.cast_nonneg k))
  apply hg.mono (by unfold phi potential; fun_prop)
  filter_upwards with x
  simp only [phi,Real.norm_eq_abs,abs_mul,abs_of_pos (exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply exp_le_exp.mpr
  unfold potential
  linarith only [mul_nonneg c_pos.le (sq_nonneg (x^3-3*x))]

private theorem exterior_bounds (k : ℕ) (hk : k.factorial ≤ 24) :
    0 ≤ exterior k ∧ exterior k ≤ 24/2^600 := by
  have hd : exp (-(600:ℝ)) ≤ 1/2^600 := by
    have he : (2:ℝ)^600 ≤ exp (600:ℝ) := by
      simpa only [← Real.exp_nat_mul,Nat.cast_ofNat,mul_one] using
        pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) (by linarith only [Real.add_one_le_exp (1:ℝ)] : (2:ℝ) ≤ exp 1) 600
    rw [exp_neg,one_div, inv_le_inv₀ (exp_pos _) (by positivity)]
    exact he
  have h (x : ℝ) (hx : x ∈ Ioi (9:ℝ)) : phi k x ≤ (24/2^600)*exp (-x) := by
    have hx9 : 9 ≤ x := hx.le
    have hx0 : 0 ≤ x := le_trans (by norm_num) hx9
    have hcub : (702:ℝ) ≤ x^3-3*x := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hx9) (by positivity : 0 ≤ x^2+9*x+78)]
    have h600 : (600:ℝ) ≤ c*(x^3-3*x)^2/2 := by
      exact (by norm_num [c] : (600:ℝ) ≤ c*702^2/2).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by norm_num) hcub 2) c_pos.le) (by norm_num))
    have hlarge : 2*x+600 ≤ potential x := by
      unfold potential
      nlinarith only [h600, mul_nonneg hx0 (by linarith only [hx9] : 0 ≤ x-4)]
    have hp : x^k ≤ (24:ℝ)*exp x := by
      have h1 := (div_le_iff₀ (by positivity : (0:ℝ)<(k.factorial:ℝ))).mp
        (Real.pow_div_factorial_le_exp x hx0 k)
      have h2 : (k.factorial:ℝ) ≤ 24 := by exact_mod_cast hk
      simpa [mul_comm] using h1.trans (mul_le_mul_of_nonneg_left h2 (exp_nonneg x))
    calc
      phi k x ≤ (24*exp x)*exp (-(potential x)) := mul_le_mul_of_nonneg_right hp (exp_nonneg _)
      _ = 24 * exp (x-potential x) := by rw [mul_assoc,←exp_add,sub_eq_add_neg]
      _ ≤ 24 * exp (-600-x) := by
        apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr _) (by norm_num)
        linarith only [hlarge]
      _ ≤ (24/2^600)*exp (-x) := by
        rw [sub_eq_add_neg,exp_add,←mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (exp_nonneg _)
        calc 24*exp (-600:ℝ) ≤ 24*(1/2^600) := mul_le_mul_of_nonneg_left hd (by norm_num)
             _ = _ := by ring
  constructor
  · apply setIntegral_nonneg measurableSet_Ioi
    intro x hx
    exact mul_nonneg (pow_nonneg (by linarith only [show (9:ℝ)<x from hx]) _) (exp_nonneg _)
  · have hm := setIntegral_mono_on (phi_integrable k).integrableOn
      ((integrableOn_exp_neg_Ioi 9).const_mul (24/2^600)) measurableSet_Ioi h
    change (∫ x : ℝ in Ioi 9, phi k x) ≤ ∫ x : ℝ in Ioi 9, (24/2^600)*exp (-x) at hm
    rw [integral_const_mul, integral_exp_neg_Ioi] at hm
    have he9 : exp (-(9:ℝ)) ≤ 1 := exp_le_one_iff.mpr (by norm_num)
    exact hm.trans ((mul_le_mul_of_nonneg_left he9 (by positivity : 0 ≤ (24:ℝ)/2^600)).trans_eq (mul_one _))

private theorem split_moment (k : ℕ) (hk : Even k) :
    (∫ x : ℝ, phi k x) = 2*9^(k+1)*interior k + 2*exterior k := by
  have heven (x : ℝ) : phi k (-x) = phi k x := by
    unfold phi
    rw [hk.neg_pow]
    have h : potential (-x)=potential x := by unfold potential; ring
    rw [h]
  have href : (∫ x : ℝ in Iic 0, phi k x) = ∫ x : ℝ in Ioi 0, phi k x := by
    simpa only [neg_zero,heven] using (integral_comp_neg_Ioi 0 (phi k)).symm
  have changeVar := intervalIntegral.smul_integral_comp_mul_left (a:=(0:ℝ)) (b:=1) (phi k) (9:ℝ)
  have hscale (t : ℝ) : phi k (9*t) = 9^k*(t^k*exp (-(pot t))) := by
    simp only [phi,rescale,mul_pow,mul_assoc]
  simp only [hscale,intervalIntegral.integral_const_mul,smul_eq_mul,mul_zero,mul_one] at changeVar
  have hsplit := intervalIntegral.integral_interval_add_Ioi (a:=(0:ℝ)) (b:=9)
      (phi_integrable k).integrableOn (phi_integrable k).integrableOn
  rw [← integral_add_compl (s:=Ioi 0) measurableSet_Ioi (phi_integrable k),compl_Ioi,href,←hsplit]
  unfold exterior interior
  rw [← changeVar, pow_succ]
  ring

set_option exponentiation.threshold 2048 in
private theorem certified_cell (k : ℕ) (hk : Even k) (hk24 : k.factorial ≤ 24)
    (q t : Box) (lo : ℤ) (hq : contains q (mass 2400)) (ht : contains t (accVal 2400 k))
    (hcert : cellOK q t k lo) :
    (lo:ℝ) ≤ 2^384*(∫ x : ℝ, phi k x) ∧ 2^384*(∫ x : ℝ, phi k x) ≤ (lo:ℝ)+1 := by
  let C : ℝ := 2*9^(k+1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs : 0 ≤ (scale:ℝ) := by unfold scale; positivity
  have hscale : (scale:ℝ) = 2^1416*2^384 := by norm_num [scale]
  have htailScale : (scale:ℝ)*(48/2^600) = 48*2^1200 := by norm_num [scale]
  have herr := abs_le.mp (interior_enclosure 2400 k (by norm_num [top,H,Q]))
  have hsmall := exterior_bounds k hk24
  have hlow : (t.lo:ℝ)-2*(q.hi:ℝ) ≤ (scale:ℝ)*interior k := by linarith only [herr.1,ht.1,hq.2]
  have hhigh : (scale:ℝ)*interior k ≤ (t.hi:ℝ)+2*(q.hi:ℝ) := by linarith only [herr.2,ht.2,hq.2]
  have hl : (lo:ℝ)*2^1416 ≤ C*((t.lo:ℝ)-2*(q.hi:ℝ)) := by
    dsimp only [C]; exact_mod_cast hcert.1
  have hu : C*((t.hi:ℝ)+2*(q.hi:ℝ))+48*2^1200 ≤ ((lo:ℝ)+1)*2^1416 := by
    dsimp only [C]; exact_mod_cast hcert.2
  have hsplit : (∫ x : ℝ, phi k x) = C*interior k+2*exterior k := split_moment k hk
  have hprod : (2^384*(∫ x : ℝ, phi k x))*2^1416 =
      C*((scale:ℝ)*interior k)+(scale:ℝ)*(2*exterior k) := by
    rw [hsplit,hscale]
    ring
  constructor
  · apply le_of_mul_le_mul_right (a:=(2:ℝ)^1416) _ (by positivity)
    rw [hprod]
    exact (hl.trans (mul_le_mul_of_nonneg_left hlow hC)).trans
      (le_add_of_nonneg_right (mul_nonneg hs (mul_nonneg (by norm_num) hsmall.1)))
  · apply le_of_mul_le_mul_right (a:=(2:ℝ)^1416) _ (by positivity)
    rw [hprod]
    apply le_trans _ hu
    apply add_le_add (mul_le_mul_of_nonneg_left hhigh hC)
    rw [← htailScale]
    apply mul_le_mul_of_nonneg_left _ hs
    calc 2*exterior k ≤ 2*(24/2^600) := mul_le_mul_of_nonneg_left hsmall.2 (by norm_num)
         _ = _ := by ring

end SexticIntegralCertificate

open SexticIntegralCertificate in
theorem solution :
    let s : ℝ := 0.136419125 / Real.sqrt (6*(1+(0.34101124:ℝ)^2+0.05276111^2))
    cqSexticSeedBounds (fun n => ∫ x : ℝ, x^n * Real.exp (-(x^2+(s*(x^3-3*x))^2)/2)) := by
  let s : ℝ := 0.136419125 / Real.sqrt (6*(1+(0.34101124:ℝ)^2+0.05276111^2))
  have hsc : s^2 = c := by
    dsimp only [s]
    rw [div_pow,Real.sq_sqrt (by positivity)]
    norm_num [c]
  have hh (k : ℕ) : (∫ x : ℝ, x^k * Real.exp (-(x^2+(s*(x^3-3*x))^2)/2)) =
      ∫ x : ℝ, phi k x := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [phi,potential,mul_pow,hsc]
    congr 2
    ring
  let st := iterate 2400
  have hv := valid 2400
  obtain ⟨h0,h2,h4⟩ := arithmetic
  have b0 := certified_cell 0 (by decide) (by decide) st.q st.t0 lower0 hv.q hv.t0 h0
  have b2 := certified_cell 2 (by decide) (by decide) st.q st.t2 lower2 hv.q hv.t2 h2
  have b4 := certified_cell 4 (by decide) (by decide) st.q st.t4 lower4 hv.q hv.t4 h4
  change cqSexticSeedBounds (fun n => ∫ x : ℝ, x^n * Real.exp (-(x^2+(s*(x^3-3*x))^2)/2))
  unfold cqSexticSeedBounds
  dsimp only
  rw [hh,hh,hh]
  exact ⟨b0,b2,b4⟩
