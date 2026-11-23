-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_degree251_table_comparisons
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:32:55.887107+00:00
-- url     : https://prove2.me/submissions/184effd3-b206-492e-b00e-3a1c3568b0b5

import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GrothendieckLB_Supplement_cqDegree251Tables

set_option maxRecDepth 10000
set_option exponentiation.threshold 50000

open Polynomial
open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQHeadArithmetic
open GrothendieckLB.Supplement.CQDegree251
namespace CQPackedCertificate

private theorem smallConstant (B : ℤ) (hB : 0 < B) (p : ℤ[X])
    (hr : p.eval B = 0) (hb : |p.coeff 0| < B) :
    p.coeff 0=0 ∧ p.divX.eval B=0 := by
  have hrec := congrArg (Polynomial.eval B) (X_mul_divX_add p)
  simp only [eval_add, eval_mul, eval_X, eval_C, hr] at hrec
  have hz : p.coeff 0 = 0 := Int.eq_zero_of_abs_lt_dvd
    ⟨-(p.divX.eval B), by rw [mul_neg]; omega⟩ hb
  rw [hz, add_zero] at hrec
  exact ⟨hz, (mul_eq_zero.mp hrec).resolve_left hB.ne'⟩

/-- An integer polynomial with a root at B and small low-order coefficients
has those coefficients equal to zero, one place at a time. -/
theorem coefficient_unique (B : ℤ) (hB : 0 < B) (p : ℤ[X]) (n : ℕ)
    (hr : p.eval B = 0) (hb : ∀ i, i ≤ n → |p.coeff i| < B) : p.coeff n = 0 := by
  induction n generalizing p with
  | zero => exact (smallConstant B hB p hr (hb 0 (by omega))).1
  | succ n ih =>
    rw [← coeff_divX]
    apply ih p.divX (smallConstant B hB p hr (hb 0 (by omega))).2
    intro i hi
    simpa only [coeff_divX] using hb (i+1) (by omega)

/-- The unconsumed high digits are kept in the highest coefficient. -/
noncomputable def ofWord (B : ℕ) : ℕ → ℕ → ℤ[X]
  | 0, v => C (v:ℤ)
  | k+1, v => C ((v%B:ℕ):ℤ) + X * ofWord B k (v/B)

theorem eval_ofWord (B k v : ℕ) : (ofWord B k v).eval (B:ℤ) = v := by
  induction k generalizing v with
  | zero => simp [ofWord]
  | succ k ih =>
    simp only [ofWord, eval_add, eval_C, eval_mul, eval_X, ih]
    exact_mod_cast Nat.mod_add_div v B

theorem coeff_ofWord (B k v i : ℕ) (hi : i<k) :
    (ofWord B k v).coeff i = (digit B v i : ℤ) := by
  induction k generalizing v i with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => simp [ofWord,digit]
    | succ i =>
      simp only [ofWord, coeff_add, coeff_C_succ, coeff_X_mul, zero_add, ih (v/B) i (by omega)]
      simp [digit, Nat.div_div_eq_div_mul, pow_succ']

noncomputable def ofCoefficients : List ℤ → ℤ[X]
  | [] => 0
  | x :: xs => C x + X * ofCoefficients xs

def horner (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | x :: xs => x + B * horner B xs

theorem eval_ofCoefficients (B : ℤ) (xs : List ℤ) :
    (ofCoefficients xs).eval B = horner B xs := by
  induction xs with
  | nil => simp [ofCoefficients, horner]
  | cons x xs ih => simp [ofCoefficients, horner, ih]

theorem coeff_ofCoefficients (xs : List ℤ) (i : ℕ) :
    (ofCoefficients xs).coeff i = xs[i]?.getD 0 := by
  induction xs generalizing i with
  | nil => simp [ofCoefficients]
  | cons x xs ih => cases i <;> simp only [ofCoefficients,coeff_add,coeff_C_zero,coeff_X_mul_zero,
      add_zero,List.getElem?_cons_zero,Option.getD_some,coeff_C_succ,coeff_X_mul,zero_add,
      List.getElem?_cons_succ,ih]

def mask : ℕ := (radix^252-1)/(radix-1)*(2^147-1)

theorem digit_and_le (v maskVal i : ℕ) (h : v &&& maskVal = v) :
    digit radix v i ≤ digit radix maskVal i := by
  have hs := congrArg (fun n : ℕ => n >>> (320*i)) h
  change (v &&& maskVal) >>> (320*i) = v >>> (320*i) at hs
  rw [Nat.shiftRight_and_distrib] at hs
  unfold digit radix
  rw [← pow_mul, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow,
      ← Nat.and_two_pow_sub_one_eq_mod, ← Nat.and_two_pow_sub_one_eq_mod]
  rw [← hs, Nat.and_assoc]
  exact Nat.and_le_right

theorem digit_vanish {v a j : ℕ} (h : radix^a ∣ v) (hj : j<a) : digit radix v j=0 := by
  obtain ⟨q,hq⟩ := dvd_trans (pow_dvd_pow radix (by omega : j+1≤a)) h
  rw [digit,hq,pow_succ, Nat.mul_assoc, Nat.mul_div_cancel_left _ (pow_pos (by decide : 0<radix) j)]
  exact Nat.mul_mod_right _ _

end CQPackedCertificate

open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQHeadArithmetic
open GrothendieckLB.Supplement.CQDegree251
namespace CQPackedCertificate

set_option maxRecDepth 100000
set_option exponentiation.threshold 50000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def wr (a : ℕ) := entry default wp a
noncomputable def rr (a : ℕ) := entry default rp a

def fits (r : PackedRow) : Prop :=
  (r.pos &&& mask) = r.pos ∧ (r.neg &&& mask) = r.neg
instance (r : PackedRow) : Decidable (fits r) := inferInstanceAs (Decidable (_ ∧ _))

theorem maskDigits : ∀ i : Fin 252, digit radix mask i = 2^147-1 := by decide +kernel
theorem tablesFit : ∀ a : Fin 252, fits (wr a) ∧ fits (rr a) := by decide +kernel
theorem powersSupport : ∀ a : Fin 252, (rr a).pos % radix^a.val = 0 ∧
    (rr a).neg % radix^a.val = 0 := by decide +kernel

def value (r : PackedRow) : ℤ := (r.pos:ℤ)-r.neg
noncomputable def packedSum : ℕ → ℤ
  | 0 => 0
  | n+1 => packedSum n + value (wr n)*value (rr n)

theorem packed_equality : packedSum 252 = horner (radix:ℤ) convolution := by decide +kernel

theorem coefficientsSmall : ∀ i : Fin 252, |convolution[i.val]?.getD 0| ≤ (2:ℤ)^310 := by
  decide +kernel

theorem coefficientMargins : ∀ j : Fin 125,
    (|convolution[2*j.val+3]?.getD 0| + 252^2*4096*coefficientScale)*10^40 ≤
      coefficientScale^2*2*314159265358979323846*(cqHeadUnits[j.val]?.getD 0) := by
  decide +kernel
end CQPackedCertificate

open Polynomial
open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQHeadArithmetic
open GrothendieckLB.Supplement.CQDegree251
namespace CQPackedCertificate

set_option maxRecDepth 10000
set_option exponentiation.threshold 50000
def signedDigit (r : PackedRow) (i : ℕ) : ℤ :=
  (digit radix r.pos i : ℤ) - digit radix r.neg i

noncomputable def rowPoly (r : PackedRow) : ℤ[X] :=
  ofWord radix 252 r.pos - ofWord radix 252 r.neg

theorem rowPoly_eval (r : PackedRow) : (rowPoly r).eval (radix:ℤ) = value r := by
  unfold rowPoly
  rw [eval_sub, eval_ofWord, eval_ofWord]
  rfl

theorem rowPoly_coeff (r : PackedRow) (i : ℕ) (hi : i<252) :
    (rowPoly r).coeff i = signedDigit r i := by
  unfold rowPoly
  rw [coeff_sub, coeff_ofWord _ _ _ _ hi, coeff_ofWord _ _ _ _ hi]
  rfl

theorem digitBound (r : PackedRow) (h : fits r) (i : ℕ) (hi : i<252) :
    |signedDigit r i| ≤ 2^147 := by
  have hp := digit_and_le r.pos mask i h.1
  have hn := digit_and_le r.neg mask i h.2
  have hm : digit radix mask i = 2^147-1 := maskDigits ⟨i,hi⟩
  rw [hm] at hp hn
  unfold signedDigit
  rw [abs_le]
  norm_num at hp hn ⊢
  omega

theorem rhoLowZero {a i : ℕ} (ha : a<252) (hi : i<a) : signedDigit (rr a) i = 0 := by
  obtain ⟨hp,hn⟩ := powersSupport ⟨a,ha⟩
  unfold signedDigit
  rw [digit_vanish (Nat.dvd_of_mod_eq_zero hp) hi, digit_vanish (Nat.dvd_of_mod_eq_zero hn) hi]
  simp

noncomputable def totalPoly : ℤ[X] := ∑ a ∈ Finset.range 252, rowPoly (wr a)*rowPoly (rr a)

private theorem eval_sum (n : ℕ) :
    (∑ a ∈ Finset.range n, value (wr a)*value (rr a)) = packedSum n := by
  induction n with
  | zero => simp [packedSum]
  | succ n ih => simp [Finset.sum_range_succ, ih, packedSum]

theorem total_eval : totalPoly.eval (radix:ℤ) = (ofCoefficients convolution).eval (radix:ℤ) := by
  simp only [totalPoly, eval_finsetSum, eval_mul, rowPoly_eval, eval_sum, eval_ofCoefficients]
  exact packed_equality

noncomputable def term (a b m : ℕ) := signedDigit (wr a) b * signedDigit (rr a) (m-b)

theorem total_coeff (m : ℕ) (hm : m<252) : totalPoly.coeff m =
    ∑ a ∈ Finset.range 252, ∑ b ∈ Finset.range (m+1), term a b m := by
  rw [totalPoly, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro a _
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro b hb
  have hi := Finset.mem_range.mp hb
  simp only [rowPoly_coeff _ b (by omega), rowPoly_coeff _ (m-b) (by omega), term]

theorem abs_range_le (f : ℕ → ℤ) (n : ℕ) (M : ℤ) (hf : ∀ i, i<n → |f i| ≤ M) :
    |∑ i ∈ Finset.range n, f i| ≤ (n:ℤ)*M := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, |f i| := Finset.abs_sum_le_sum_abs .. 
    _ ≤ ∑ _i ∈ Finset.range n, M := Finset.sum_le_sum fun i hi => hf i (Finset.mem_range.mp hi)
    _ = _ := by simp

theorem total_bound (m : ℕ) (hm : m<252) : |totalPoly.coeff m| ≤ 252*(252*((2:ℤ)^147)^2) := by
  rw [total_coeff m hm]
  apply abs_range_le
  intro a ha
  have hw := (tablesFit ⟨a,ha⟩).1
  have hr := (tablesFit ⟨a,ha⟩).2
  calc
    _ ≤ ((m+1:ℕ):ℤ)*((2:ℤ)^147)^2 := by
      apply abs_range_le
      intro b hb
      unfold term
      rw [abs_mul, pow_two]
      exact mul_le_mul (digitBound _ hw _ (by omega)) (digitBound _ hr _ (by omega))
        (abs_nonneg _) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by omega) (by positivity)

theorem agrees (m : ℕ) (hm : m<252) : totalPoly.coeff m = convolution[m]?.getD 0 := by
  rw [← coeff_ofCoefficients]
  apply sub_eq_zero.mp
  rw [← coeff_sub]
  apply coefficient_unique (radix:ℤ) (by norm_num [radix])
  · simp only [eval_sub, total_eval, sub_self]
  · intro i hi
    have hsmall : |convolution[i]?.getD 0| ≤ (2:ℤ)^310 := coefficientsSmall ⟨i,by omega⟩
    rw [coeff_sub, coeff_ofCoefficients, sub_eq_add_neg]
    calc
      _ ≤ |totalPoly.coeff i| + |convolution[i]?.getD 0| := by
        simpa only [abs_neg] using abs_add_le (totalPoly.coeff i) (-(convolution[i]?.getD 0))
      _ ≤ 252*(252*((2:ℤ)^147)^2) + 2^310 := add_le_add (total_bound _ (by omega)) hsmall
      _ < _ := by norm_num [radix]

theorem triangle_coeff (m : ℕ) (hm : m<252) : convolution[m]?.getD 0 =
    ∑ a ∈ Finset.range (m+1), ∑ b ∈ Finset.range (m+1-a), term a b m := by
  rw [← agrees m hm, total_coeff m hm]
  have hz (a b : ℕ) (ha : a<252) (h : m-b<a) : term a b m=0 := by
    rw [term,rhoLowZero ha h,mul_zero]
  calc
    _ = ∑ a ∈ Finset.range (m+1), ∑ b ∈ Finset.range (m+1), term a b m := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro a ha hnot
      apply Finset.sum_eq_zero
      intro b _
      apply hz _ _ (Finset.mem_range.mp ha)
      simp only [Finset.mem_range] at hnot
      omega
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro b hb hnot
      simp only [Finset.mem_range] at ha hb hnot
      exact hz _ _ (by omega) (by omega)

end CQPackedCertificate

open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQHeadArithmetic
open GrothendieckLB.Supplement.CQDegree251
namespace CQPackedCertificate

set_option maxRecDepth 10000
set_option exponentiation.threshold 50000

private def near (D z err : ℤ) (v : Interval) : Prop :=
  z-err ≤ D*v.lo ∧ D*v.hi ≤ z+err

private theorem perturbed_product (D x y u v : ℤ) (hD : 1≤D)
    (hx : |x|≤8*D) (hy : |y|≤8*D) (hu : |u|≤1) (hv : |v|≤255) :
    |(x+u)*(y+v)-x*y| ≤ 3000*D := by
  rw [show (x+u)*(y+v)-x*y = (x*v+y*u)+u*v by ring]
  calc
    _ ≤ |x*v+y*u| + |u*v| := abs_add_le .. 
    _ ≤ (|x*v|+|y*u|) + |u*v| := add_le_add_left (abs_add_le ..) _
    _ = (|x| * |v| + |y| * |u|) + |u| * |v| := by simp only [abs_mul]
    _ ≤ (8*D*255+8*D*1) + 1*255 := by
      exact add_le_add (add_le_add (mul_le_mul hx hv (abs_nonneg _) (by omega))
        (mul_le_mul hy hu (abs_nonneg _) (by omega)))
        (mul_le_mul hu hv (abs_nonneg _) (by decide))
    _ ≤ _ := by omega

private theorem round_product (D x y u v : ℤ) (hD : 1≤D)
    (hx : |x|≤8*D) (hy : |y|≤8*D) (hu : |u|≤1) (hv : |v|≤255) :
    near D (x*y) (4096*D) (mulInterval D ⟨x,x+u⟩ ⟨y,y+v⟩) := by
  have both (s t : ℤ) (hs : |s|≤1) (ht : |t|≤255) :
      x*y-3000*D ≤ (x+s)*(y+t) ∧ (x+s)*(y+t) ≤ x*y+3000*D := by
    have h := abs_le.mp (perturbed_product D x y s t hD hx hy hs ht)
    omega
  have h0 := both 0 0 (by decide) (by decide)
  have h1 := both 0 v (by decide) hv
  have h2 := both u 0 hu (by decide)
  have h3 := both u v hu hv
  simp only [add_zero] at h0 h1 h2
  let l := min (min (x*y) (x*(y+v))) (min ((x+u)*y) ((x+u)*(y+v)))
  let h := max (max (x*y) (x*(y+v))) (max ((x+u)*y) ((x+u)*(y+v)))
  have hl : x*y-3000*D ≤ l := le_min (le_min h0.1 h1.1) (le_min h2.1 h3.1)
  have hh : h ≤ x*y+3000*D := max_le (max_le h0.2 h1.2) (max_le h2.2 h3.2)
  have floor := Int.lt_ediv_mul l (by omega : 0<D)
  have ceil := Int.lt_ediv_mul (-h) (by omega : 0<D)
  rw [mul_comm (l/D) D] at floor
  rw [mul_comm ((-h)/D) D] at ceil
  change x*y-4096*D ≤ D*(l/D) ∧ D*(-((-h)/D)) ≤ x*y+4096*D
  rw [mul_neg]
  omega

private theorem near_mono {D z e e' : ℤ} {v : Interval} (h : near D z e v) (he : e≤e') :
    near D z e' v := by unfold near at *; omega

private theorem near_sum (D e : ℤ) (f : ℕ → Interval) (g : ℕ → ℤ) (n : ℕ)
    (h : ∀ k, k<n → near D (g k) e (f k)) :
    near D (∑ k ∈ Finset.range n, g k) ((n:ℤ)*e) (sumIntervals f n) := by
  induction n with
  | zero => simp [near,sumIntervals,zeroInterval]
  | succ n ih =>
    have ih' := ih (fun k hk => h k (by omega))
    have hlast := h n (by omega)
    unfold near at ih' hlast ⊢
    simp only [Finset.sum_range_succ, sumIntervals, addInterval, Nat.cast_succ, add_mul,
      one_mul, mul_add]
    omega

private theorem tab_entry {α : Type} (d : α) (n : ℕ) (f : ℕ → α) (i : ℕ) (hi : i<n) :
    entry d (tab n f) i = f i := by simp [entry,tab,hi]

private theorem signed_product (m a b : ℕ) (hm : m<252) (ha : a<m+1) (hb : b<m+1-a) :
    near coefficientScale (term a b m) (4096*coefficientScale)
      (scaleInterval ((-1:ℤ)^b) (mulInterval coefficientScale
        (entry zeroInterval (entry #[] weights a) b) (entry zeroInterval (entry #[] powers a) (m-b)))) := by
  have ha' : a<252 := by omega
  have hb' : b<252 := by omega
  have hk : m-b<252 := by omega
  rw [weights,tab_entry _ _ _ _ ha',powers,tab_entry _ _ _ _ ha',wrow,rrow,
    tab_entry _ _ _ _ (by omega : b<252-a),tab_entry _ _ _ _ hk]
  let x := signedDigit (wr a) b
  let y := signedDigit (rr a) (m-b)
  let u : ℤ := digit 2 (wr a).wid b
  let v : ℤ := digit 256 (rr a).wid (m-b)
  have hx : |x| ≤ 8*coefficientScale := by
    exact (digitBound _ (tablesFit ⟨a,ha'⟩).1 b hb').trans (by norm_num [coefficientScale])
  have hy : |y| ≤ 8*coefficientScale := by
    exact (digitBound _ (tablesFit ⟨a,ha'⟩).2 (m-b) hk).trans (by norm_num [coefficientScale])
  have hu : |u|≤1 := by
    change |((digit 2 (wr a).wid b:ℕ):ℤ)| ≤ _
    have h : digit 2 (wr a).wid b < 2 := Nat.mod_lt _ (by decide)
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    omega
  have hv : |v|≤255 := by
    change |((digit 256 (rr a).wid (m-b):ℕ):ℤ)| ≤ _
    have h : digit 256 (rr a).wid (m-b) < 256 := Nat.mod_lt _ (by decide)
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    omega
  change near _ (x*y) _ (scaleInterval ((-1:ℤ)^b) (mulInterval _
    ⟨((-1:ℤ)^b)*x, ((-1:ℤ)^b)*x+u⟩ ⟨1*y,1*y+v⟩))
  rcases neg_one_pow_eq_or ℤ b with hs|hs
  · rw [hs]
    simp only [one_mul]
    have hr := round_product coefficientScale x y u v (by decide) hx hy hu hv
    simpa [scaleInterval] using hr
  · rw [hs]
    simp only [neg_one_mul,one_mul]
    have hr := round_product coefficientScale (-x) y u v (by decide) (by simpa using hx) hy hu hv
    unfold near at hr ⊢
    simp only [scaleInterval,show (-1:ℤ)≠0 by decide,show ¬0≤(-1:ℤ) by decide,
      if_false,one_mul,mul_neg,neg_mul] at *
    omega

private theorem whole (m : ℕ) (hm : m<252) :
    near coefficientScale (convolution[m]?.getD 0) (252^2*4096*coefficientScale)
      (fullSum weights powers m) := by
  rw [triangle_coeff m hm]
  unfold fullSum
  apply near_mono
  · apply near_sum coefficientScale (252*(4096*coefficientScale))
    intro a ha
    apply near_mono (near_sum coefficientScale (4096*coefficientScale) _ _
      (m+1-a) (fun b hb => signed_product m a b hm ha hb))
    exact mul_le_mul_of_nonneg_right (by omega) (by norm_num [coefficientScale])
  · have h : ((m+1:ℕ):ℤ) ≤ 252 := by omega
    calc
      _ ≤ 252*(252*(4096*coefficientScale)) :=
        mul_le_mul_of_nonneg_right h (by norm_num [coefficientScale])
      _ = _ := by ring

end CQPackedCertificate

open CQPackedCertificate
theorem solution : ∀ j : Fin 125,
    let v := CQHeadArithmetic.fullSum CQDegree251.weights CQDegree251.powers (2*j.val+3)
    max (-v.lo) v.hi * 10^40 ≤
      CQHeadArithmetic.coefficientScale*2*314159265358979323846*(cqHeadUnits[j.val]?.getD 0) := by
  intro j
  let m := 2*j.val+3
  let v := fullSum weights powers m
  change max (-v.lo) v.hi * 10^40 ≤ _
  have he : convolution[m]?.getD 0 - 252^2*4096*coefficientScale ≤ coefficientScale*v.lo ∧
      coefficientScale*v.hi ≤ convolution[m]?.getD 0 + 252^2*4096*coefficientScale :=
    whole m (by dsimp [m]; omega)
  have hp : 0<coefficientScale := by decide
  have hh : coefficientScale*max (-v.lo) v.hi ≤ |convolution[m]?.getD 0| + 252^2*4096*coefficientScale := by
    rw [mul_max_of_nonneg _ _ hp.le,mul_neg]
    exact max_le (by have := neg_le_abs (convolution[m]?.getD 0); omega)
      (by have := le_abs_self (convolution[m]?.getD 0); omega)
  have hnum := coefficientMargins j
  change (|convolution[m]?.getD 0|+_)*10^40 ≤ _ at hnum
  apply (le_of_mul_le_mul_left · hp)
  calc
    coefficientScale*(max (-v.lo) v.hi*10^40) =
        (coefficientScale*max (-v.lo) v.hi)*10^40 := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right hh (by norm_num : (0:ℤ)≤10^40)).trans hnum
    _ = _ := by ring
