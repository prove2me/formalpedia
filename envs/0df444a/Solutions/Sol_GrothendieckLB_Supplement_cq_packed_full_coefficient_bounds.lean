-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_packed_full_coefficient_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:19:08.517985+00:00
-- url     : https://prove2.me/submissions/13e4905a-ed50-4a5f-b1e9-01af97baf8f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_cq_packed_center_products_0_to_63
import Theorems.Thm_GrothendieckLB_Supplement_cq_packed_center_products_64_to_127
import Theorems.Thm_GrothendieckLB_Supplement_cq_packed_center_products_128_to_191
import Theorems.Thm_GrothendieckLB_Supplement_cq_packed_center_products_192_to_251
import Theorems.Thm_GrothendieckLB_Supplement_cq_center_product_terminal_checks
import Definitions.Def_GrothendieckLB_Supplement_cqHeadSumProducts
import Mathlib
open GrothendieckLB.Supplement CQHeadArithmetic CQHeadCertificate CQHeadSum
set_option maxHeartbeats 1500000
namespace CenterBounds
private def err : ℤ := 2^158
private def Near (c e : ℤ) (v : Interval) := c-e ≤ 4*coefficientScale*v.lo ∧ 4*coefficientScale*v.hi ≤ c+e

private theorem endpoints {v : Interval} {A : ℤ} (h0 : 0 ≤ width v) (h : width v ≤ A)
    (x : ℤ) (hx : x=v.lo ∨ x=v.hi) : |2*x-center v| ≤ A := by
  rcases hx with rfl|rfl <;> rw [abs_le] <;> unfold center width at * <;> omega

private theorem mulCenter {x y u v : ℤ} (hx : |2*x-u| ≤ 1) (hy : |2*y-v| ≤ 256)
    (hu : |u| ≤ 2^148) (hv : |v| ≤ 2^146) :
    |4*x*y-u*v| ≤ 2^148*256+2^146+256 := by
  have h1 := mul_le_mul hu hy (abs_nonneg _) (by positivity : (0:ℤ) ≤ 2^148)
  have h2 := mul_le_mul hx hv (abs_nonneg _) (by decide : (0:ℤ) ≤ 1)
  have h3 := mul_le_mul hx hy (abs_nonneg _) (by decide : (0:ℤ) ≤ 1)
  rw [show 4*x*y-u*v=u*(2*y-v)+(2*x-u)*v+(2*x-u)*(2*y-v) by ring]
  apply (abs_add_le _ _).trans
  have ha := abs_add_le (u*(2*y-v)) ((2*x-u)*v)
  simp only [abs_mul,one_mul] at *
  linarith

private theorem prodNear (s t : Interval)
    (hs : |center s| ≤ 2^148 ∧ 0 ≤ width s ∧ width s ≤ 1)
    (ht : |center t| ≤ 2^146 ∧ 0 ≤ width t ∧ width t ≤ 256) :
    Near (center s*center t) err (mulInterval coefficientScale s t) := by
  let C := center s*center t
  let R : ℤ := 2^148*256+2^146+256
  have h (x y : ℤ) (hx : x=s.lo ∨ x=s.hi) (hy : y=t.lo ∨ y=t.hi) :
      C-R ≤ 4*(x*y) ∧ 4*(x*y) ≤ C+R := by
    have h' := abs_le.mp (mulCenter (endpoints hs.2.1 hs.2.2 x hx) (endpoints ht.2.1 ht.2.2 y hy) hs.1 ht.1)
    dsimp only [C,R]
    constructor <;> linarith
  obtain ⟨h1,k1⟩ := h _ _ (Or.inl rfl) (Or.inl rfl)
  obtain ⟨h2,k2⟩ := h _ _ (Or.inl rfl) (Or.inr rfl)
  obtain ⟨h3,k3⟩ := h _ _ (Or.inr rfl) (Or.inl rfl)
  obtain ⟨h4,k4⟩ := h _ _ (Or.inr rfl) (Or.inr rfl)
  let lo := min (min (s.lo*t.lo) (s.lo*t.hi)) (min (s.hi*t.lo) (s.hi*t.hi))
  let hi := max (max (s.lo*t.lo) (s.lo*t.hi)) (max (s.hi*t.lo) (s.hi*t.hi))
  have hl : C-R ≤ 4*lo := by dsimp [lo]; omega
  have hu : 4*hi ≤ C+R := by dsimp [hi]; omega
  have hS : 0 < coefficientScale := by decide +kernel
  have low := Int.emod_lt_of_pos lo hS
  have high := Int.emod_lt_of_pos (-hi) hS
  have lr := Int.mul_ediv_add_emod lo coefficientScale
  have hr := Int.mul_ediv_add_emod (-hi) coefficientScale
  have hE : R+4*coefficientScale ≤ err := by decide +kernel
  change C-err ≤ 4*coefficientScale*(lo/coefficientScale) ∧ 4*coefficientScale*(-((-hi)/coefficientScale)) ≤ C+err
  constructor <;> linarith

private theorem signNear {c e : ℤ} {x : Interval} (h : Near c e x) (b : ℕ) :
    Near ((-1:ℤ)^b*c) e (scaleInterval ((-1:ℤ)^b) x) := by
  rcases neg_one_pow_eq_or ℤ b with hs|hs
  · simpa [hs,scaleInterval] using h
  · simp only [Near] at *
    simp [hs,scaleInterval]
    constructor <;> linarith [h.1,h.2]

private theorem addNear {z e : ℕ → ℤ} {x : ℕ → Interval} (n : ℕ) (h : ∀ k < n, Near (z k) (e k) (x k)) :
    Near (∑ k ∈ Finset.range n,z k) (∑ k ∈ Finset.range n,e k) (sumIntervals x n) := by
  induction n with
  | zero => simp [Near,sumIntervals,zeroInterval]
  | succ n ih =>
    obtain ⟨h1,h2⟩ := ih (fun k hk => h k (by omega))
    obtain ⟨h3,h4⟩ := h n (by omega)
    simp only [Finset.sum_range_succ,sumIntervals,Near,addInterval]
    constructor <;> linarith

private def cm (a m : ℕ) := ∑ b ∈ Finset.range (m+1),wc a b*pc a (m-b)
private def cmAll (m : ℕ) := ∑ a ∈ Finset.range 252, cm a m
private theorem cmTrim (a m : ℕ) (ha : a ≤ m) : cm a m=∑ b ∈ Finset.range (m+1-a),wc a b*pc a (m-b) := by
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : m+1-a ≤ m+1))
  intro b hb hbr
  have h1 := Finset.mem_range.mp hb
  have h2 : ¬b < m+1-a := fun h => hbr (Finset.mem_range.mpr h)
  simp [pc,p,show ¬a ≤ m-b by omega,center,zeroInterval]

private theorem wholeNear {m : ℕ} (hm : m < 252) (hr : ∀ a < 252, rowHolds a) :
    Near (cmAll m) (2^176) (sumIntervals (part m) (m+1)) := by
  have hr' (a j : ℕ) (ha : a < 252) (hj : j < 252) := of_decide_eq_true
    (List.all_eq_true.mp (hr a ha).2 j (List.mem_range.mpr hj))
  have hrow (a : ℕ) (ha : a < m+1) : Near (cm a m) ((m+1-a:ℕ)*err) (part m a) := by
    rw [cmTrim a m (by omega)]
    have h := addNear (z:=fun b => wc a b*pc a (m-b)) (e:=fun _ => err) (x:=term m a) (m+1-a) (by
      intro b hb
      have hg := hr' a b (by omega) (by omega)
      have hh := hr' a (m-b) (by omega) (by omega)
      have h0 := prodNear (w a b) (p a (m-b)) ⟨hg.1,hg.2.1,hg.2.2.1⟩ hh.2.2.2
      have h1 := signNear h0 b
      simpa only [wc,pc,w,p,if_pos (show a+b ≤ 251 by omega),if_pos (show a ≤ m-b by omega),term,mul_assoc] using h1)
    simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,part] using! h
  have h := addNear (m+1) hrow
  have he : ∑ a ∈ Finset.range (m+1),cm a m=cmAll m := by
    apply Finset.sum_subset (Finset.range_mono (by omega : m+1 ≤ 252))
    intro a _ ha
    have hgt : m < a := by by_contra! h;exact ha (Finset.mem_range.mpr (by omega))
    apply Finset.sum_eq_zero
    intro b hb
    simp [pc,p,show ¬a ≤ m-b by omega,center,zeroInterval]
  rw [he] at h
  have hx : (∑ a ∈ Finset.range (m+1),((m+1-a:ℕ):ℤ)*err) ≤ 2^176 := by
    calc
      _ ≤ ∑ _ ∈ Finset.range (m+1), (252:ℤ)*err := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_right _ (by decide +kernel)
        exact_mod_cast (show m+1-a ≤ 252 by omega)
      _ ≤ 252*(252*err) := by
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by decide +kernel)
        exact_mod_cast (show m+1 ≤ 252 by omega)
      _ ≤ _ := by decide +kernel
  exact ⟨by linarith only [h.1,hx],by linarith only [h.2,hx]⟩

private def cv (f g : ℕ → ℤ) (n : ℕ) := ∑ k ∈ Finset.range (n+1), f k*g (n-k)

private theorem cv_succ (f g : ℕ → ℤ) (n : ℕ) :
    cv f g (n+1)=f 0*g (n+1)+cv (fun k => f (k+1)) g n := by
  rw [cv,Finset.sum_range_succ']
  simp only [Nat.sub_zero,Nat.succ_sub_succ_eq_sub]
  rw [add_comm]
  rfl

private theorem pack_add (B : ℤ) (f g : ℕ → ℤ) (n : ℕ) :
    pack B (fun i => f i+g i) n=pack B f n+pack B g n := by
  induction n generalizing f g with
  | zero => simp [pack]
  | succ n ih =>
    simp only [pack]
    rw [ih (fun k => f (k+1)) (fun k => g (k+1))]
    ring

private theorem pack_scale (B c : ℤ) (g : ℕ → ℤ) (n : ℕ) :
    pack B (fun i => c*g i) n=c*pack B g n := by
  induction n generalizing g with
  | zero => simp [pack]
  | succ n ih =>
    simp only [pack]
    rw [ih (fun k => g (k+1))]
    ring

private theorem pack_extra (B : ℤ) (g : ℕ → ℤ) (n : ℕ) :
    pack B g (n+1)=pack B g n+B^n*g n := by
  induction n generalizing g with
  | zero => simp [pack]
  | succ n ih =>
    change g 0+B*pack B (fun i => g (i+1)) (n+1)=g 0+B*pack B (fun i => g (i+1)) n+B^(n+1)*g (n+1)
    rw [ih,pow_succ];ring

private theorem convolutionMod (B : ℤ) (f g : ℕ → ℤ) (n : ℕ) :
    B^n ∣ pack B f n*pack B g n-pack B (cv f g) n := by
  induction n generalizing f g with
  | zero => simp
  | succ n ih =>
    let F k := f (k+1)
    let G k := g (k+1)
    obtain ⟨d,hd⟩ := ih F g
    refine ⟨d+pack B F n*g n,?_⟩
    rw [show pack B f (n+1)=f 0+B*pack B F n from rfl]
    have hc : pack B (cv f g) (n+1)=f 0*g 0+B*(f 0*pack B G n+pack B (cv F g) n) := by
      rw [pack]
      simp only [cv_succ,pack_add,pack_scale]
      simp [cv,F,G]
    rw [hc,pow_succ]
    have hg := pack_extra B g n
    have hbase : pack B g (n+1)=g 0+B*pack B G n := rfl
    linear_combination (f 0)*hbase + B*(pack B F n)*hg + B*hd

private theorem zeroDigits (B : ℤ) (hB : 0 < B) (f : ℕ → ℤ) (n : ℕ)
    (h : B^n ∣ pack B f n) (hb : ∀ k < n, |f k| < B) : ∀ k < n, f k=0 := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    obtain ⟨d,hd⟩ := h
    rw [pack,pow_succ] at hd
    have hdiv : B ∣ f 0 := ⟨B^n*d-pack B (fun k => f (k+1)) n,by linarith only [hd] <;> ring⟩
    have hzero : f 0=0 := Int.eq_zero_of_abs_lt_dvd hdiv (hb 0 (by omega))
    rw [hzero,zero_add] at hd
    have htail : B^n ∣ pack B (fun k => f (k+1)) n := ⟨d,by
      have h' : B*pack B (fun k => f (k+1)) n=B*(B^n*d) := hd.trans (by ring)
      exact mul_left_cancel₀ hB.ne' h'⟩
    intro k hk
    cases k with
    | zero => exact hzero
    | succ k => exact ih _ htail (fun j hj => hb (j+1) (by omega)) k (by omega)


private theorem packSum (B : ℤ) (f : ℕ → ℕ → ℤ) (A N : ℕ) :
    pack B (fun k => ∑ a ∈ Finset.range A, f a k) N=∑ a ∈ Finset.range A,pack B (f a) N := by
  induction A with
  | zero =>
    simp only [Finset.range_zero,Finset.sum_empty]
    induction N with
    | zero => rfl
    | succ N ih => simp [pack,ih]
  | succ a ih => simp only [Finset.sum_range_succ,pack_add,ih]

private theorem packedAll (hr : ∀ a < 252, rowHolds a)
    (ht : base^252 ∣ pack base value 252-∑ a ∈ Finset.range 252,row a)
    (bound : ∀ m < 252, |value m| ≤ 2^320) : ∀ m < 252, value m=cmAll m := by
  have hsum : base^252 ∣ (∑ a ∈ Finset.range 252,row a)-pack base cmAll 252 := by
    change base^252 ∣ (∑ a ∈ Finset.range 252,row a)-pack base (fun k => ∑ a ∈ Finset.range 252,cm a k) 252
    rw [packSum,←Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro a ha
    rw [(hr a (Finset.mem_range.mp ha)).1]
    exact convolutionMod base (wc a) (pc a) 252
  have hdiv : base^252 ∣ pack base (fun k => value k-cmAll k) 252 := by
    have eq' : (fun k => value k-cmAll k) = fun k => value k+(-1)*cmAll k := by ext k;ring
    rw [eq',pack_add,pack_scale]
    rw [show pack base value 252+(-1)*pack base cmAll 252 = (pack base value 252-∑ a ∈ Finset.range 252,row a)+((∑ a ∈ Finset.range 252,row a)-pack base cmAll 252) by ring]
    exact dvd_add ht hsum
  have hb (m : ℕ) (hm : m < 252) : |value m-cmAll m| < base := by
    have hcm (a : ℕ) (ha : a < 252) : |cm a m| ≤ 252*((2:ℤ)^148*2^146) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc
        _ ≤ ∑ _ ∈ Finset.range (m+1),((2:ℤ)^148*2^146) := by
          apply Finset.sum_le_sum
          intro b hbr
          have hb' := Finset.mem_range.mp hbr
          have wh := of_decide_eq_true (List.all_eq_true.mp (hr a ha).2 b (Finset.mem_range.mpr (by omega)))
          have ph := of_decide_eq_true (List.all_eq_true.mp (hr a ha).2 (m-b) (Finset.mem_range.mpr (by omega)))
          simp only [wc,pc,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
          exact mul_le_mul wh.1 ph.2.2.2.1 (abs_nonneg _) (by positivity)
        _ ≤ _ := by
          simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast (show m+1 ≤ 252 by omega)
    have hs : |cmAll m| ≤ 252*(252*((2:ℤ)^148*2^146)) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_ofNat] using
        Finset.sum_le_sum (s:=Finset.range 252) (fun a ha => hcm a (Finset.mem_range.mp ha))
    exact (abs_sub _ _).trans_lt ((add_le_add (bound m hm) hs).trans_lt (by decide +kernel))
  have h := zeroDigits base (by decide +kernel) _ 252 hdiv hb
  exact fun m hm => sub_eq_zero.mp (h m hm)

private theorem allCoefficients (hr : ∀ a < 252, rowHolds a) (cert : base^252 ∣ pack base value 252-
    (∑ a ∈ Finset.range 252, row a) ∧ (∀ m < 252, |value m| ≤ 2^320) ∧
    ∀ j < 125, (|value (2*j+3)|+2^176)*10^40 ≤
      4*coefficientScale^2*2*314159265358979323846*(cqHeadUnits[j]?.getD 0)) :
    ∀ j < 125, let v := sumIntervals (fun a => part (2*j+3) a) (2*j+4)
      max (-v.lo) v.hi*10^40 ≤ coefficientScale*2*314159265358979323846*(cqHeadUnits[j]?.getD 0) := by
  intro j hj
  let m := 2*j+3
  have hm : m < 252 := by dsimp [m];omega
  let v := sumIntervals (part m) (m+1)
  have h := wholeNear hm hr
  rw [←packedAll hr cert.1 cert.2.1 m hm] at h
  change value m-2^176 ≤ 4*coefficientScale*v.lo ∧ 4*coefficientScale*v.hi ≤ value m+2^176 at h
  have hs : 4*coefficientScale > 0 := by decide +kernel
  have hmax : 4*coefficientScale*max (-v.lo) v.hi ≤ |value m|+2^176 := by
    rcases le_total (-v.lo) v.hi with hl|hl
    · rw [max_eq_right hl]
      linarith only [h.2,le_abs_self (value m)]
    · rw [max_eq_left hl]
      linarith only [h.1,neg_le_abs (value m)]
  have hn := cert.2.2 j hj
  change (|value m|+2^176)*10^40 ≤ _ at hn
  change max (-v.lo) v.hi*10^40 ≤ _
  apply le_of_mul_le_mul_left (a:=4*coefficientScale) _ hs
  calc
    _=(4*coefficientScale*max (-v.lo) v.hi)*10^40 := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right hmax (by positivity)).trans hn
    _ = _ := by ring
end CenterBounds

open CenterBounds in
theorem solution :
    ∀ j < 125, let v := sumIntervals (fun a => part (2*j+3) a) (2*j+4)
      max (-v.lo) v.hi * 10^40 ≤ coefficientScale*2*314159265358979323846*(cqHeadUnits[j]?.getD 0) := by
  apply allCoefficients _ cq_center_product_terminal_checks
  intro a ha
  by_cases h1 : a < 64
  · exact cq_packed_center_products_0_to_63 a (by omega) h1
  by_cases h2 : a < 128
  · exact cq_packed_center_products_64_to_127 a (by omega) h2
  by_cases h3 : a < 192
  · exact cq_packed_center_products_128_to_191 a (by omega) h3
  exact cq_packed_center_products_192_to_251 a (by omega) ha
