-- Prove2me | solution 1 for MasulloRH.height_one_theta_gram_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:13:43.352368+00:00
-- url     : https://prove2.me/submissions/30fa901e-2216-4fde-8ad4-2be74630cf09

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Mathlib
import Theorems.Thm_MasulloAudit_window_mellin_evaluation_bounded
import Theorems.Thm_MasulloRH_finite_theta_approximation_excludes_rectangle_zeros


open Set Filter MeasureTheory
open scoped BigOperators
namespace MasulloRH.GaussianApproximation
noncomputable section

private def dyad (t : ℝ) := Real.exp (-Real.pi*t^2) - 3*Real.exp (-Real.pi*(2*t)^2) +
  2*Real.exp (-Real.pi*(4*t)^2)

/-- Dyadic Gaussian theta series at the positive physical scale u. -/
def D (u : ℝ) : ℝ := ∑' n : ℤ, dyad ((n:ℝ)*u)

theorem theta_eq_D (x : ℝ) : theta x = (D (Real.exp x):ℂ) := by
  rw [D, Complex.ofReal_tsum]
  rfl

private def J (u : ℝ) := HurwitzZeta.evenKernel 0 (u^2)

private lemma dyad_hasSum (u : ℝ) (hu : 0<u) :
    HasSum (fun n : ℤ => dyad ((n:ℝ)*u)) (J u-3*J (2*u)+2*J (4*u)) := by
  have ht (a : ℝ) (ha : 0 < a) : HasSum (fun n : ℤ => Real.exp (-Real.pi* (a*((n:ℝ)*u))^2)) (J (a*u)) := by
    convert! HurwitzZeta.hasSum_int_evenKernel 0 (sq_pos_of_pos (mul_pos ha hu)) using 1
    funext n
    congr 1
    ring
  simpa [dyad] using ((ht 1 (by norm_num)).sub ((ht 2 (by norm_num)).mul_left 3)).add ((ht 4 (by norm_num)).mul_left 2)

private lemma J_reflect {u : ℝ} (hu : 0 < u) : J u = J u⁻¹/u := by
  unfold J
  rw [HurwitzZeta.evenKernel_functional_equation,← HurwitzZeta.evenKernel_eq_cosKernel_of_zero,
    ← Real.sqrt_eq_rpow,Real.sqrt_sq hu.le,inv_pow]
  ring

theorem D_reflect {u : ℝ} (hu : 0 < u) : D u = D (1/(4*u))/(2*u) := by
  have hstep : 0 < 1/(4*u) := by positivity
  rw [show D u = _ from (dyad_hasSum u hu).tsum_eq,
      show D (1/(4*u)) = _ from (dyad_hasSum _ hstep).tsum_eq]
  rw [J_reflect hu,J_reflect (mul_pos (by norm_num : (0:ℝ)<2) hu),J_reflect (mul_pos (by norm_num : (0:ℝ)<4) hu)]
  have h1 : 2*(1/(4*u))=(2*u)⁻¹ := by field_simp; norm_num
  have h2 : 4*(1/(4*u))=u⁻¹ := by field_simp
  rw [h1,h2,one_div]
  field_simp
  ring

private def B (q : ℝ) (n : ℕ) := 2*q^(n^2)-6*q^(4*n^2)+4*q^(16*n^2)

private lemma D_series {u q : ℝ} (hu : 0<u) (hq : q=Real.exp (-Real.pi*u^2)) :
    D u = ∑' n : ℕ, B q (n+1) := by
  let F (k : ℤ) := dyad ((k:ℝ)*u)
  have hF : Summable F := (dyad_hasSum u hu).summable
  have hp : Summable (fun n : ℕ => F ((n:ℤ)+1)) := hF.comp_injective (fun n m h => by exact_mod_cast add_right_cancel h)
  have hn : Summable (fun n : ℕ => F (-((n:ℤ)+1))) := hF.comp_injective (fun n m h => by exact_mod_cast add_right_cancel (neg_inj.mp h))
  have h := tsum_of_add_one_of_neg_add_one (f:=F) hp hn
  change (∑' k : ℤ, F k) = _
  rw [h]
  have he (n : ℕ) : F ((n:ℤ)+1) + F (-((n:ℤ)+1)) = B q (n+1) := by
    simp only [F,dyad,B,hq,← Real.exp_nat_mul]
    push_cast
    ring_nf
  have hzero : F 0 = 0 := by norm_num [F,dyad]
  rw [hzero,add_zero,← hp.tsum_add hn]
  exact tsum_congr he

private lemma B_bound {q : ℝ} (hq : 0 ≤ q) (h1 : q ≤ 1) (n : ℕ) : |B q n| ≤ 12*q^(n^2) := by
  have h4 : q^(4*n^2) ≤ q^(n^2) := pow_le_pow_of_le_one hq h1 (by omega)
  have h16 : q^(16*n^2) ≤ q^(n^2) := pow_le_pow_of_le_one hq h1 (by omega)
  rw [abs_le]
  unfold B
  constructor <;> nlinarith [pow_nonneg hq (4*n^2),pow_nonneg hq (16*n^2),pow_nonneg hq (n^2)]

private theorem tail_bound {q : ℝ} (hq : 0 ≤ q) (h1 : q ≤ 1) (k l : ℕ)
    (hr : q^l ≤ 1/2) (hkl : l ≤ 2*k+1) :
    Summable (fun n : ℕ => B q (n+k)) ∧ |∑' n : ℕ, B q (n+k)| ≤ 24*q^(k^2) := by
  have hs : Summable (fun n : ℕ => 12*q^(k^2)*(q^l)^n) :=
    (summable_geometric_of_lt_one (pow_nonneg hq _) (by linarith : q^l<1)).mul_left _
  have hb (n : ℕ) : ‖B q (n+k)‖ ≤ 12*q^(k^2)*(q^l)^n := by
    rw [Real.norm_eq_abs,mul_assoc,← pow_mul,← pow_add]
    apply (B_bound hq h1 _).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply pow_le_pow_of_le_one hq h1
    have hsq : n ≤ n^2 := by nlinarith [Nat.le_mul_self n]
    nlinarith [Nat.mul_le_mul_right n hkl]
  have hsum := hs.of_norm_bounded hb
  refine ⟨hsum,(norm_tsum_le_tsum_norm hsum.norm).trans ((hsum.norm.tsum_le_tsum hb hs).trans ?_)⟩
  rw [tsum_mul_left,tsum_geometric_of_lt_one (pow_nonneg hq _) (by linarith : q^l<1)]
  have hden : 0 < 1-q^l := by linarith
  rw [← div_eq_mul_inv,div_le_iff₀ hden]
  nlinarith [mul_nonneg (pow_nonneg hq (k^2)) (sub_nonneg.mpr hr)]

private lemma gauss_q {u q : ℝ} (hu : 0 < u) (hq : q=Real.exp (-Real.pi*u^2)) : 0<q ∧ q<1 := by
  rw [hq]
  exact ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) (sq_pos_of_pos hu))⟩

theorem D_far_bound {u q : ℝ} (hu : 0<u) (hq : q=Real.exp (-Real.pi*u^2)) (hhalf : q≤1/2) :
    |D u| ≤ 24*q := by
  obtain ⟨h0,h1⟩ := gauss_q hu hq
  rw [D_series hu hq]
  simpa using (tail_bound h0.le h1.le 1 1 (by simpa using hhalf) (by decide)).2

theorem D_two_term {u q : ℝ} (hu : 0<u) (hq : q=Real.exp (-Real.pi*u^2)) (h7 : q^7≤1/2) :
    |D u - (2*q-4*q^4-2*q^16+4*q^64)| ≤ 24*q^9 := by
  obtain ⟨h0,h1⟩ := gauss_q hu hq
  obtain ⟨hs,hh⟩ := tail_bound h0.le h1.le 3 7 h7 (by decide)
  have hs' : Summable (fun n : ℕ => B q ((n+2)+1)) := hs
  have hall := (summable_nat_add_iff 2 (f:=fun n : ℕ => B q (n+1))).mp hs'
  have split := hall.sum_add_tsum_nat_add 2
  rw [D_series hu hq,← split,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_zero]
  have hp : 0+B q (0+1)+B q (1+1) = 2*q-4*q^4-2*q^16+4*q^64 := by norm_num [B]; ring
  rw [hp,add_sub_cancel_left]
  exact hh

end
end MasulloRH.GaussianApproximation

set_option maxHeartbeats 800000
namespace MasulloGram.Cert

abbrev precision : ℚ := 1073741824

def down (q : ℚ) : ℚ := (⌊q*precision⌋ : ℤ) / precision
def up (q : ℚ) : ℚ := (⌈q*precision⌉ : ℤ) / precision

theorem down_le (q : ℚ) : down q ≤ q := by
  unfold down
  exact (div_le_iff₀ (by norm_num : 0 < precision)).mpr (Int.floor_le _)
theorem le_up (q : ℚ) : q ≤ up q := by
  unfold up
  exact (le_div_iff₀ (by norm_num : 0 < precision)).mpr (Int.le_ceil _)

structure Box where
  lo : ℚ
  hi : ℚ
  deriving Repr, Inhabited

namespace Box

def Holds (B : Box) (x : ℝ) := (B.lo : ℝ) ≤ x ∧ x ≤ (B.hi : ℝ)

def const (q : ℚ) : Box := ⟨q,q⟩

def add (A B : Box) : Box := ⟨A.lo+B.lo,A.hi+B.hi⟩
def neg (A : Box) : Box := ⟨-A.hi,-A.lo⟩
def sub (A B : Box) : Box := A.add B.neg

def mul (A B : Box) : Box :=
  ⟨min (min (A.lo*B.lo) (A.lo*B.hi)) (min (A.hi*B.lo) (A.hi*B.hi)),
   max (max (A.lo*B.lo) (A.lo*B.hi)) (max (A.hi*B.lo) (A.hi*B.hi))⟩

def sq (A : Box) : Box :=
  ⟨0, (max (-A.lo) A.hi)^2⟩

def powNonneg (A : Box) (n : ℕ) : Box := ⟨(max 0 A.lo)^n,(max 0 A.hi)^n⟩

def radius (A : Box) : Box := ⟨-A.hi,A.hi⟩

lemma const_holds (q : ℚ) : (const q).Holds (q:ℝ) := ⟨le_rfl,le_rfl⟩
lemma Holds.add {A B : Box} {x y : ℝ} (ha : A.Holds x) (hb : B.Holds y) :
    (A.add B).Holds (x+y) := by
  simpa only [Holds, Box.add, Rat.cast_add] using And.intro (add_le_add ha.1 hb.1) (add_le_add ha.2 hb.2)
lemma Holds.neg {A : Box} {x : ℝ} (ha : A.Holds x) : A.neg.Holds (-x) := by
  simpa only [Holds, Box.neg, Rat.cast_neg] using And.intro (neg_le_neg ha.2) (neg_le_neg ha.1)
lemma Holds.sub {A B : Box} {x y : ℝ} (ha : A.Holds x) (hb : B.Holds y) :
    (A.sub B).Holds (x-y) := by simpa only [Box.sub,sub_eq_add_neg] using ha.add hb.neg

private lemma mul_trap {b y d : ℝ} (a : ℝ) (h : b≤y ∧ y≤d) :
    min (a*b) (a*d) ≤ a*y ∧ a*y ≤ max (a*b) (a*d) := by
  rcases le_total 0 a with ha|ha
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left h.1 ha),
      (mul_le_mul_of_nonneg_left h.2 ha).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left h.2 ha),
      (mul_le_mul_of_nonpos_left h.1 ha).trans (le_max_left _ _)⟩

lemma Holds.mul {A B : Box} {x y : ℝ} (ha : A.Holds x) (hb : B.Holds y) :
    (A.mul B).Holds (x*y) := by
  have h₁ := mul_trap (A.lo:ℝ) hb
  have h₂ := mul_trap (A.hi:ℝ) hb
  have h₃ := mul_trap y ha
  rw [mul_comm y x, mul_comm y (A.lo:ℝ), mul_comm y (A.hi:ℝ)] at h₃
  simp only [Holds,Box.mul,Rat.cast_min,Rat.cast_max,Rat.cast_mul]
  exact ⟨(min_le_min h₁.1 h₂.1).trans h₃.1, h₃.2.trans (max_le_max h₁.2 h₂.2)⟩

lemma Holds.sq {A : Box} {x : ℝ} (ha : A.Holds x) : A.sq.Holds (x^2) := by
  have h : |x| ≤ max (-(A.lo:ℝ)) (A.hi:ℝ) := abs_le.mpr ⟨by linarith [ha.1,le_max_left (-(A.lo:ℝ)) (A.hi:ℝ)],ha.2.trans (le_max_right _ _)⟩
  simpa only [Holds,Box.sq,Rat.cast_zero,Rat.cast_pow,Rat.cast_max,Rat.cast_neg,sq_abs] using
    And.intro (sq_nonneg x) (pow_le_pow_left₀ (abs_nonneg x) h 2)
lemma Holds.powNonneg {A : Box} {x : ℝ} (ha : A.Holds x) (hx : 0≤x) (n : ℕ) :
    (A.powNonneg n).Holds (x^n) := by
  simp only [Holds,Box.powNonneg,Rat.cast_pow,Rat.cast_max,Rat.cast_zero]
  exact ⟨pow_le_pow_left₀ (le_max_left _ _) (max_le hx ha.1) _,pow_le_pow_left₀ hx (ha.2.trans (le_max_right _ _)) _⟩

end Box

private def sqDown (q : ℚ) : ℚ := max 0 (down (q^2))
private def sqUp (q : ℚ) : ℚ := up (q^2)

private lemma sqDown_spec {q : ℚ} {y : ℝ} (hq : 0≤q) (hy : (q:ℝ) ≤ y) :
    0 ≤ sqDown q ∧ ((sqDown q:ℚ):ℝ) ≤ y^2 := by
  constructor
  · exact le_max_left _ _
  · rw [sqDown, Rat.cast_max,Rat.cast_zero]
    refine max_le (sq_nonneg _) ?_
    have h : ((down (q^2):ℚ):ℝ) ≤ (q:ℝ)^2 := by
      simpa only [Rat.cast_pow] using (Rat.cast_le (K:=ℝ)).mpr (down_le (q^(2:ℕ)))
    exact h.trans (pow_le_pow_left₀ (by exact_mod_cast hq) hy _)
private lemma sqUp_spec {q : ℚ} {y : ℝ} (hy : 0≤y) (hq : y ≤ (q:ℝ)) : y^2 ≤ ((sqUp q:ℚ):ℝ) := by
  apply (pow_le_pow_left₀ hy hq 2).trans
  unfold sqUp
  simpa only [Rat.cast_pow] using (Rat.cast_le (K:=ℝ)).mpr (le_up (q^(2:ℕ)))

private def squaredLo : ℕ → ℚ → ℚ
  | 0, q => q
  | n+1, q => sqDown (squaredLo n q)
private def squaredHi : ℕ → ℚ → ℚ
  | 0, q => q
  | n+1, q => sqUp (squaredHi n q)

private theorem squares_lo {q : ℚ} {y : ℝ} (hq : 0≤q) (h : (q:ℝ)≤y) (n : ℕ) :
    0 ≤ squaredLo n q ∧ ((squaredLo n q:ℚ):ℝ) ≤ y^(2^n) := by
  induction n with
  | zero => simpa [squaredLo] using And.intro hq h
  | succ n ih => simpa only [pow_succ 2 n, pow_mul, squaredLo] using sqDown_spec ih.1 ih.2
private theorem squares_hi {q : ℚ} {y : ℝ} (hy : 0≤y) (h : y≤(q:ℝ)) (n : ℕ) :
    y^(2^n) ≤ ((squaredHi n q:ℚ):ℝ) := by
  induction n with
  | zero => simpa [squaredHi] using h
  | succ n ih => simpa only [pow_succ 2 n, pow_mul,squaredHi] using sqUp_spec (pow_nonneg hy (2^n)) ih

private def atom (q : ℚ) : Box :=
  if -1024 ≤ q ∧ q ≤ 1024 then
    ⟨squaredLo 12 (max 0 (down (1+q/4096))),squaredHi 12 (up (1/(1-q/4096)))⟩
  else ⟨0,4^(⌈q⌉₊)⟩

private theorem atom_spec (q : ℚ) : (atom q).Holds (Real.exp (q:ℝ)) := by
  unfold atom
  split_ifs with hq
  · let z := (q:ℝ)/4096
    have hz : z<1 := by
      have hh : (q:ℝ) ≤ 1024 := by exact_mod_cast hq.2
      dsimp [z]; linarith
    have hpos : 0<1-z := by linarith
    have hl : ((max 0 (down (1+q/4096)):ℚ):ℝ) ≤ Real.exp z := by
      rw [Rat.cast_max,Rat.cast_zero]; refine max_le (Real.exp_nonneg _) ?_
      have hh : ((down (1+q/4096):ℚ):ℝ) ≤ 1+z := by dsimp [z]; exact_mod_cast down_le (1+q/4096)
      exact hh.trans (by simpa [add_comm] using Real.add_one_le_exp z)
    have hu : Real.exp z ≤ ((up (1/(1-q/4096)):ℚ):ℝ) := by
      have hneg : 1-z ≤ Real.exp (-z) := by linarith [Real.add_one_le_exp (-z)]
      have hlower : Real.exp z ≤ 1/(1-z) := by
        rw [le_div_iff₀ hpos]; calc
          _ ≤ Real.exp z*Real.exp (-z) := mul_le_mul_of_nonneg_left hneg (Real.exp_nonneg _)
          _ = _ := by rw [← Real.exp_add]; simp
      apply hlower.trans
      dsimp [z]; exact_mod_cast le_up (1/(1-q/4096))
    have hpow : (Real.exp z)^(2^12) = Real.exp (q:ℝ) := by
      rw [← Real.exp_nat_mul]; congr 1; dsimp [z]; norm_num; ring
    exact ⟨hpow ▸ (squares_lo (le_max_left _ _) hl 12).2,hpow ▸ squares_hi (Real.exp_nonneg _) hu 12⟩
  · simp only [Box.Holds,Rat.cast_zero,Rat.cast_pow,Rat.cast_ofNat]
    refine ⟨Real.exp_nonneg _,?_⟩
    have hle : (q:ℝ) ≤ (⌈q⌉₊ : ℕ) := by exact_mod_cast Nat.le_ceil q
    have hh : Real.exp (⌈q⌉₊ : ℕ) = Real.exp 1 ^ ⌈q⌉₊ := by simpa only [mul_one] using Real.exp_nat_mul 1 ⌈q⌉₊
    push_cast
    exact (Real.exp_le_exp.mpr hle).trans (hh.trans_le (pow_le_pow_left₀ (Real.exp_nonneg _) (by linarith [Real.exp_one_lt_three]) _))

def Box.exp (A : Box) : Box := ⟨(atom A.lo).lo,(atom A.hi).hi⟩
lemma Box.Holds.exp {A : Box} {x : ℝ} (h : A.Holds x) : A.exp.Holds (Real.exp x) :=
  ⟨(atom_spec _).1.trans (Real.exp_le_exp.mpr h.1), (Real.exp_le_exp.mpr h.2).trans (atom_spec _).2⟩

end MasulloGram.Cert

namespace MasulloGram.Cert
open Box

/-- Endpoints on the central grid, from −3 to 3. -/
def edge (i : ℕ) : ℚ := ((i:ℚ)-96)/32
def cellX (i : ℕ) : Box := ⟨edge i, edge (i+1)⟩
def cellAbs (i : ℕ) : Box := if i<96 then (cellX i).neg else cellX i

def prefExponent (i : ℕ) := if i<96 then (const (3/4)).sub (cellX i) else (cellX i).sub (const (3/4))
def eScale (i : ℕ) : Box := (prefExponent i).exp
def chosenU (i : ℕ) := if i<96 then (const (1/4)).mul (eScale i) else eScale i
def pref (i : ℕ) := if i<96 then (const (1/2)).mul (eScale i) else const 1

def piBox : Box := ⟨31415/10000,31416/10000⟩
def qBox (i : ℕ) := ((piBox.mul ((chosenU i).powNonneg 2)).neg).exp

def oneTerm (Q : Box) (n : ℕ) :=
  (((const 2).mul (Q.powNonneg (n^2))).sub ((const 6).mul (Q.powNonneg (4*n^2)))).add
    ((const 4).mul (Q.powNonneg (16*n^2)))

def twoDirect (Q : Box) := ((oneTerm Q 1).add (oneTerm Q 2)).add (((const 24).mul (Q.powNonneg 9)).radius)

def pulseBox (i : ℕ) := (⟨1128/1000,1129/1000⟩:Box).mul
    (((const (-4)).mul ((cellAbs i).powNonneg 2)).exp)
def weightBox (i : ℕ) := ((const (if i<96 then (6/5:ℚ) else 9/5)).mul (cellX i)).exp
def energyBox (i : ℕ) := (weightBox i).mul (((pulseBox i).sub
    ((const (3/2)).mul ((pref i).mul (twoDirect (qBox i))))).sq)

def bound (i : ℕ) : ℚ := up (energyBox i).hi

def sumBounds : ℕ → ℚ
  | 0 => 0
  | n+1 => sumBounds n + bound n

end MasulloGram.Cert

namespace MasulloGram.Cert
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem finite_bound : sumBounds 192 / 32 < 21/1000 := by decide +kernel
end MasulloGram.Cert

open MeasureTheory Set
open scoped BigOperators
namespace MasulloGram.Cert

/-- The two theta terms retained before applying the Poisson prefactor. -/
def seriesTerm (q : ℝ) (n : ℕ) : ℝ := 2*q^(n^2) - 6*q^(4*n^2) + 4*q^(16*n^2)
noncomputable def chosenRealU (x : ℝ) := if x<0 then Real.exp (3/4-x)/4 else Real.exp (x-3/4)
noncomputable def realPref (x : ℝ) := if x<0 then Real.exp (3/4-x)/2 else 1
noncomputable def realQ (x : ℝ) := Real.exp (-Real.pi * chosenRealU x^2)

/-- A quantitative form of the two-term Poisson truncation. The prefactor corresponds to the
original theta sum on the right half and its reflected expression on the left half. -/
def TwoTermEnclosure (f : ℝ → ℝ) : Prop := ∀ x ∈ Icc (-3:ℝ) 3,
  ∃ e : ℝ, |e| ≤ 24 * realQ x^9 ∧
    f x = realPref x * (seriesTerm (realQ x) 1 + seriesTerm (realQ x) 2 + e)

noncomputable def centralIntegrand (f : ℝ → ℝ) (x : ℝ) :=
  Real.exp (3/2*x+3/10*|x|) * (2/Real.sqrt Real.pi * Real.exp (-4*x^2) - 3/2*f x)^2

private lemma piBox_spec : piBox.Holds Real.pi := by
  have h₁ := Real.pi_gt_d4
  have h₂ := Real.pi_lt_d4
  norm_num [Box.Holds,piBox] at *; constructor <;> linarith

private lemma normalization_spec : (⟨1128/1000,1129/1000⟩ : Box).Holds (2/Real.sqrt Real.pi) := by
  have h₁ := Real.pi_gt_d4
  have h₂ := Real.pi_lt_d4
  have hs := Real.sq_sqrt Real.pi_pos.le
  have hs' := Real.sqrt_nonneg Real.pi
  have hmin : 1.772 ≤ Real.sqrt Real.pi := by nlinarith
  have hmax : Real.sqrt Real.pi ≤ 1.773 := by nlinarith
  norm_num [Box.Holds]; constructor
  · apply (le_div_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)).mpr; linarith
  · apply (div_le_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)).mpr; linarith

private lemma seriesTerm_spec {Q : Box} {q : ℝ} (hQ : Q.Holds q) (hq : 0 ≤ q) (n : ℕ) :
    (oneTerm Q n).Holds (seriesTerm q n) := by
  simpa only [oneTerm,seriesTerm,Rat.cast_ofNat] using
    (((Box.const_holds 2).mul (hQ.powNonneg hq (n^2))).sub
      ((Box.const_holds 6).mul (hQ.powNonneg hq (4*n^2)))).add
      ((Box.const_holds 4).mul (hQ.powNonneg hq (16*n^2)))

private lemma direct_spec {Q : Box} {q e : ℝ} (hQ : Q.Holds q) (hq : 0 ≤ q) (he : |e|≤24*q^9) :
    (twoDirect Q).Holds (seriesTerm q 1 + seriesTerm q 2 + e) := by
  have hr := (Box.const_holds 24).mul (hQ.powNonneg hq 9)
  have hrad : (((Box.const 24).mul (Q.powNonneg 9)).radius).Holds e := by
    have hmax : |e| ≤ (((Box.const 24).mul (Q.powNonneg 9)).hi:ℝ) :=
      he.trans (by exact_mod_cast hr.2)
    simpa only [Box.radius,Box.Holds,Rat.cast_neg] using abs_le.mp hmax
  exact ((seriesTerm_spec hQ hq 1).add (seriesTerm_spec hQ hq 2)).add hrad

private lemma edge_real (i : ℕ) : (edge i : ℝ) = ((i:ℝ)-96)/32 := by simp [edge]

private lemma cell_sound {f : ℝ → ℝ} (hf : TwoTermEnclosure f) (i : ℕ) (hi : i<192)
    (x : ℝ) (hx : x∈Ioo (edge i:ℝ) (edge (i+1):ℝ)) : centralIntegrand f x ≤ (bound i:ℝ) := by
  have hX : (cellX i).Holds x := ⟨hx.1.le,hx.2.le⟩
  have hxx := hx
  simp only [Set.mem_Ioo,edge_real,Nat.cast_add,Nat.cast_one] at hxx
  have hsg : i<96 ↔ x<0 := by
    constructor
    · intro h
      have : (i:ℝ) ≤ 95 := by exact_mod_cast (show i ≤ 95 by omega)
      linarith [hxx.2]
    · intro h; by_contra hn
      have : (96:ℝ) ≤ i := by exact_mod_cast (show 96 ≤ i by omega)
      linarith [hxx.1]
  have hzero : (0:ℝ) ≤ i := by positivity
  have hi' : (i:ℝ)≤191 := by exact_mod_cast (show i≤191 by omega)
  have hrange : x∈Icc (-3:ℝ) 3 := ⟨by linarith [hxx.1],by linarith [hxx.2]⟩
  have hA : (cellAbs i).Holds |x| := by
    by_cases hs : i<96
    · rw [cellAbs,if_pos hs,abs_of_neg (hsg.mp hs)]; exact hX.neg
    · rw [cellAbs,if_neg hs,abs_of_nonneg (le_of_not_gt (fun h => hs (hsg.mpr h)))]; exact hX
  have hE : (eScale i).Holds (if x<0 then Real.exp (3/4-x) else Real.exp (x-3/4)) := by
    by_cases hs : i<96
    · simpa only [eScale,prefExponent,if_pos hs,if_pos (hsg.mp hs),Rat.cast_div,Rat.cast_ofNat] using
        ((Box.const_holds (3/4)).sub hX).exp
    · simpa only [eScale,prefExponent,if_neg hs,if_neg (fun hh => hs (hsg.mpr hh)),Rat.cast_div,Rat.cast_ofNat] using
        (hX.sub (Box.const_holds (3/4))).exp
  have hU : (chosenU i).Holds (chosenRealU x) := by
    by_cases hs : i<96
    · simp only [if_pos (hsg.mp hs)] at hE
      simpa only [chosenU,chosenRealU,if_pos hs,if_pos (hsg.mp hs),Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,one_div,div_eq_inv_mul,Rat.cast_mul,Rat.cast_inv,mul_one] using
        (Box.const_holds (1/4)).mul hE
    · simpa only [chosenU,chosenRealU,if_neg hs,if_neg (fun hh => hs (hsg.mpr hh))] using hE
  have hP : (pref i).Holds (realPref x) := by
    by_cases hs : i<96
    · simp only [if_pos (hsg.mp hs)] at hE
      simpa only [pref,realPref,if_pos hs,if_pos (hsg.mp hs),Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,one_div,div_eq_inv_mul,Rat.cast_mul,Rat.cast_inv,mul_one] using
        (Box.const_holds (1/2)).mul hE
    · simp only [pref,realPref,if_neg hs,if_neg (fun hh => hs (hsg.mpr hh))]; simpa using Box.const_holds 1
  have hup : 0≤chosenRealU x := by unfold chosenRealU; split <;> positivity
  have hQ : (qBox i).Holds (realQ x) := by
    simpa only [qBox,realQ,neg_mul] using (piBox_spec.mul (hU.powNonneg hup 2)).neg.exp
  obtain ⟨e,he,hef⟩ := hf x hrange
  have htheta : ((pref i).mul (twoDirect (qBox i))).Holds (f x) :=
    hef ▸ hP.mul (direct_spec hQ (Real.exp_nonneg _) he)
  have hpulse : (pulseBox i).Holds (2/Real.sqrt Real.pi*Real.exp (-4*x^2)) := by
    simpa only [pulseBox,Rat.cast_neg,Rat.cast_ofNat,sq_abs] using normalization_spec.mul
      (((Box.const_holds (-4)).mul (hA.powNonneg (abs_nonneg _) 2)).exp)
  have hweight : (weightBox i).Holds (Real.exp (3/2*x+3/10*|x|)) := by
    by_cases hs : i<96
    · rw [abs_of_neg (hsg.mp hs),show 3/2*x+3/10*(-x)=(6/5)*x by ring]
      simpa only [weightBox,if_pos hs,Rat.cast_div,Rat.cast_ofNat] using ((Box.const_holds (6/5)).mul hX).exp
    · rw [abs_of_nonneg (le_of_not_gt fun hh => hs (hsg.mpr hh)),show 3/2*x+3/10*x=(9/5)*x by ring]
      simpa only [weightBox,if_neg hs,Rat.cast_div,Rat.cast_ofNat] using ((Box.const_holds (9/5)).mul hX).exp
  have hb : (energyBox i).Holds (centralIntegrand f x) := by
    simpa only [energyBox,centralIntegrand,Rat.cast_div,Rat.cast_ofNat] using
      hweight.mul ((hpulse.sub ((Box.const_holds (3/2)).mul htheta)).sq)
  exact hb.2.trans ((Rat.cast_le (K:=ℝ)).mpr (le_up _))


private lemma sumBounds_eq (n : ℕ) : sumBounds n = ∑ i ∈ Finset.range n, bound i := by
  induction n with
  | zero => simp [sumBounds]
  | succ n ih => simp [sumBounds,Finset.sum_range_succ,ih]

theorem central_le_computed {f : ℝ → ℝ} (hf : TwoTermEnclosure f)
    (hint : Integrable (centralIntegrand f)) :
    ∫ x in Icc (-3:ℝ) 3, centralIntegrand f x ≤ ((sumBounds 192 / 32:ℚ):ℝ) := by
  let a (i : ℕ) : ℝ := edge i
  have h0 : a 0 = -3 := by norm_num [a,edge]
  have h192 : a 192 = 3 := by norm_num [a,edge]
  have hlen (i : ℕ) : a (i+1) - a i = 1/32 := by dsimp [a]; simp only [edge_real,Nat.cast_add,Nat.cast_one]; ring
  have hf' : ∀ i, IntervalIntegrable (centralIntegrand f) volume (a i) (a (i+1)) :=
    fun i => hint.intervalIntegrable
  have he (i : ℕ) (hi : i<192) : (∫ x in a i..a (i+1), centralIntegrand f x) ≤ (bound i:ℝ)/32 := by
    have hai : a i ≤ a (i+1) := by linarith [hlen i]
    calc
      _ ≤ ∫ _ in a i..a (i+1), (bound i:ℝ) :=
        intervalIntegral.integral_mono_on_of_le_Ioo hai (hf' i) intervalIntegrable_const (cell_sound hf i hi)
      _ = _ := by rw [intervalIntegral.integral_const, hlen, smul_eq_mul]; ring
  have hc : (∫ x in Icc (-3:ℝ) 3, centralIntegrand f x) = ∫ x in a 0..a 192, centralIntegrand f x := by
    rw [h0,h192,intervalIntegral.integral_of_le (by norm_num),integral_Icc_eq_integral_Ioc]
  rw [hc,← intervalIntegral.sum_integral_adjacent_intervals (fun i _ => hf' i)]
  calc
    _ ≤ ∑ i ∈ Finset.range 192, (bound i:ℝ)/32 := Finset.sum_le_sum fun i hi => he i (Finset.mem_range.mp hi)
    _ = _ := by rw [← Finset.sum_div,sumBounds_eq]; norm_cast

end MasulloGram.Cert

open MeasureTheory Set
namespace MasulloGram.Cert

theorem central_lt {f : ℝ → ℝ} (hf : TwoTermEnclosure f)
    (hint : Integrable (centralIntegrand f)) :
    ∫ x in Icc (-3:ℝ) 3, centralIntegrand f x < 21/1000 :=
by
  apply (central_le_computed hf hint).trans_lt
  exact ((Rat.cast_lt (K:=ℝ)).mpr finite_bound).trans_eq (by norm_num)

end MasulloGram.Cert

open Set MeasureTheory
namespace MasulloGram.Cert

private lemma u_third (x : ℝ) : 1/3 ≤ chosenRealU x := by
  unfold chosenRealU
  split_ifs with h
  · have he := Real.add_one_le_exp (3/4-x)
    linarith
  · have hx : 0≤x := le_of_not_gt h
    have h₁ : Real.exp (3/4:ℝ) ≤ 3 :=
      ((Real.exp_le_exp.mpr (by norm_num : (3/4:ℝ) ≤ 1))).trans Real.exp_one_lt_three.le
    have h₂ : (1/3:ℝ) ≤ (Real.exp (3/4:ℝ))⁻¹ := by
      rw [← one_div]; exact one_div_le_one_div_of_le (Real.exp_pos _) h₁
    apply h₂.trans
    rw [← Real.exp_neg,Real.exp_le_exp]; linarith

private lemma q_seventh (x : ℝ) : realQ x^7 ≤ 1/2 := by
  rw [realQ, ← Real.exp_nat_mul]
  have hu := u_third x
  have hn : 0≤chosenRealU x := by linarith
  have hs := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1/3) hu
  have hpi : 3*(chosenRealU x)^2 ≤ Real.pi * (chosenRealU x)^2 :=
    mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg _)
  have he := Real.add_one_le_exp (1:ℝ)
  calc
    _ ≤ Real.exp (-1:ℝ) := Real.exp_le_exp.mpr (by norm_num; nlinarith)
    _ ≤ _ := by rw [Real.exp_neg,← one_div]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)

theorem twoTerm_of_reflection (D : ℝ → ℝ)
    (hr : ∀ {u : ℝ}, 0<u → D u = D (1/(4*u))/(2*u))
    (ht : ∀ {u q : ℝ}, 0<u → q=Real.exp (-Real.pi*u^2) → q^7≤1/2 →
      |D u-(2*q-4*q^4-2*q^16+4*q^64)| ≤ 24*q^9) :
    TwoTermEnclosure (fun x => D (Real.exp (x-3/4))) := by
  intro x _
  let q := realQ x
  have hu : 0<chosenRealU x := by linarith [u_third x]
  have h := ht hu (show q=Real.exp (-Real.pi*chosenRealU x^2) from rfl) (q_seventh x)
  have hp : seriesTerm q 1 + seriesTerm q 2 = 2*q-4*q^4-2*q^16+4*q^64 := by dsimp [seriesTerm]; ring
  refine ⟨D (chosenRealU x) - (seriesTerm q 1 + seriesTerm q 2), ?_, ?_⟩
  · rw [hp]; exact h
  · change D (Real.exp (x-3/4)) = realPref x * (_ + (D (chosenRealU x)-_))
    rw [add_sub_cancel]
    by_cases hx : x<0
    · rw [hr (Real.exp_pos (x-3/4)), realPref, chosenRealU, if_pos hx,
        show (3/4:ℝ)-x = -(x-3/4) by ring, Real.exp_neg]
      have hu' := Real.exp_ne_zero (x-3/4)
      rw [show 1/(4*Real.exp (x-3/4))=(Real.exp (x-3/4))⁻¹/4 by field_simp]
      field_simp; rw [if_pos hx]
    · simp [realPref,chosenRealU,hx]

end MasulloGram.Cert

open MeasureTheory Set MasulloRH.GaussianApproximation
namespace MasulloGram.Cert

noncomputable def concreteEnergyDensity (x : ℝ) : ℝ :=
  Real.exp (2*(3/4)*x+2*(3/20)*|x|) *
    ‖residual 1 (fun _ : Fin 1 => (3/2:ℂ)) (fun _ => (3/4:ℝ)) x‖^2

theorem concreteEnergyDensity_eq (x : ℝ) : concreteEnergyDensity x =
    centralIntegrand (fun t => D (Real.exp (t-3/4))) x := by
  have hp : MasulloRH.GaussianApproximation.pulse 1 x =
      ((2/Real.sqrt Real.pi * Real.exp (-4*x^2):ℝ):ℂ) := by
    unfold MasulloRH.GaussianApproximation.pulse
    norm_num only [one_add_one_eq_two]
    simp only [Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_neg,Complex.ofReal_pow,Complex.ofReal_ofNat]
    congr 2; push_cast; ring
  have hr : residual 1 (fun _ : Fin 1 => (3/2:ℂ)) (fun _ => (3/4:ℝ)) x =
      ((2/Real.sqrt Real.pi * Real.exp (-4*x^2) - 3/2*D (Real.exp (x-3/4)):ℝ):ℂ) := by
    rw [MasulloRH.GaussianApproximation.residual, Fin.sum_univ_one, hp, theta_eq_D]
    push_cast; rfl
  rw [concreteEnergyDensity,hr,Complex.norm_real,Real.norm_eq_abs,sq_abs,centralIntegrand]
  congr 2; ring

theorem actual_central_lt (hint : Integrable concreteEnergyDensity) :
    ∫ x in Icc (-3:ℝ) 3, concreteEnergyDensity x < 21/1000 := by
  have h := twoTerm_of_reflection D D_reflect D_two_term
  have hh := funext concreteEnergyDensity_eq
  rw [hh] at hint ⊢
  exact central_lt h hint

end MasulloGram.Cert



open MeasureTheory Set
namespace MasulloGram.Outer
noncomputable section

private lemma exp_nat_two (n : ℕ) : (2 : ℝ)^n ≤ Real.exp n := by
  have h := Real.exp_one_gt_d9
  have hh : (2:ℝ) ≤ Real.exp 1 := by linarith
  simpa only [←Real.exp_nat_mul,mul_one] using pow_le_pow_left₀ (by positivity) hh n

private lemma exp_quad (t : ℝ) (ht : 3≤t) : 8*t ≤ Real.pi*Real.exp t := by
  have h := Real.sum_le_exp_of_nonneg (show 0≤t by linarith) 3
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.exp_pos t).le
  nlinarith [sq_nonneg (t-3)]

private theorem direct_bound (D : ℝ → ℝ)
    (hf : ∀ u : ℝ, 0 < u → Real.exp (-Real.pi*u^2) ≤ 1/2 →
      |D u| ≤ 24*Real.exp (-Real.pi*u^2))
    {u t : ℝ} (hu : 0<u) (ht : 3≤t) (hbig : Real.exp t ≤ u^2) :
    |D u| ≤ 24*Real.exp (-8*t) := by
  have h := (exp_quad t ht).trans (mul_le_mul_of_nonneg_left hbig Real.pi_pos.le)
  have hq : Real.exp (-Real.pi*u^2) ≤ Real.exp (-8*t) := Real.exp_le_exp.mpr (by linarith)
  have hsmall : Real.exp (-8*t) ≤ 1/2 := by
    rw [show -8*t = -(8*t) by ring,Real.exp_neg]
    simpa only [one_div] using (inv_le_inv₀ (Real.exp_pos (8*t)) (by norm_num : (0:ℝ)<2)).mpr
      (by linarith [Real.add_one_le_exp (8*t)])
  exact (hf u hu (hq.trans hsmall)).trans (by linarith)

theorem shifted_theta_bound (D : ℝ → ℝ)
    (hf : ∀ u : ℝ, 0 < u → Real.exp (-Real.pi*u^2) ≤ 1/2 →
      |D u| ≤ 24*Real.exp (-Real.pi*u^2))
    (hr : ∀ u : ℝ, 0<u → D u = D (1/(4*u))/(2*u))
    {x : ℝ} (hx : 3 ≤ |x|) :
    |D (Real.exp (x-3/4))| ≤ 48 * Real.exp (-7*|x|) := by
  by_cases hs : 0 ≤ x
  · rw [abs_of_nonneg hs] at hx ⊢
    have hbig : Real.exp x ≤ (Real.exp (x-3/4))^2 := by
      rw [←Real.exp_nat_mul]; exact Real.exp_le_exp.mpr (by push_cast; linarith)
    have h := direct_bound D hf (Real.exp_pos _) hx hbig
    have he : Real.exp (-8*x) ≤ Real.exp (-7*x) := Real.exp_le_exp.mpr (by linarith)
    linarith [Real.exp_pos (-7*x)]
  · rw [abs_of_neg (lt_of_not_ge hs)] at hx ⊢
    let u := Real.exp (x-3/4)
    let v := 1/(4*u)
    have hu : 0<u := Real.exp_pos _
    have hv : 0<v := by dsimp [v]; positivity
    have hinv : u⁻¹ = Real.exp (-x+3/4) := by dsimp [u]; rw [←Real.exp_neg]; congr 1; ring
    have hvform : v = Real.exp (-x+3/4)/4 := by dsimp [v]; rw [←hinv]; field_simp
    have h16 : 16 ≤ Real.exp (-x+3/2) := by
      have h₄ := exp_nat_two 4
      norm_num at h₄
      exact h₄.trans (Real.exp_le_exp.mpr (by linarith))
    have hbig : Real.exp (-x) ≤ v^2 := by
      rw [hvform,div_pow,←Real.exp_nat_mul]
      rw [le_div_iff₀ (by norm_num)]
      calc
        _ ≤ Real.exp (-x) * Real.exp (-x+3/2) := by nlinarith [Real.exp_pos (-x)]
        _ = _ := by rw [←Real.exp_add]; congr 1; push_cast; ring
    have hd := direct_bound D hf hv hx hbig
    change |D u| ≤ _
    rw [hr u hu,abs_div,abs_of_pos (by positivity : 0<2*u),div_le_iff₀ (by positivity)]
    change |D v| ≤ _
    have h4 : Real.exp (3/4) ≤ 4 := by
      have h := Real.exp_one_lt_d9
      have h' : Real.exp (3/4) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      linarith
    have hfac : Real.exp (-x+3/4) ≤ 4*Real.exp (-x) := by
      rw [Real.exp_add,mul_comm (4:ℝ)]
      exact mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    have hfac' : 1 ≤ 4 * (Real.exp (-x) * u) := by
      rw [←hinv] at hfac
      have hm := (inv_le_iff_one_le_mul₀ hu).mp hfac
      nlinarith
    apply hd.trans
    have hrewrite : Real.exp (-7* -x) = Real.exp (-8* -x)*Real.exp (-x) := by
      rw [←Real.exp_add]; congr 1; ring
    rw [hrewrite]
    nlinarith [mul_le_mul_of_nonneg_left hfac' (Real.exp_pos (-8* -x)).le]

theorem residual_outer (D : ℝ → ℝ)
    (hd : ∀ x : ℝ, 3≤|x| → |D (Real.exp (x-3/4))| ≤ 48*Real.exp (-7*|x|)) :
    let f (x : ℝ) := Real.exp (3/2*x+3/10*|x|) *
      (2/Real.sqrt Real.pi * Real.exp (-4*x^2) - 3/2*D (Real.exp (x-3/4)))^2
    Integrable f → (∫ x in (Icc (-3:ℝ) 3)ᶜ, f x) < 1/1000 := by
  intro f hi
  have hcoef : 0 ≤ 2/Real.sqrt Real.pi := by positivity
  have hcle : 2/Real.sqrt Real.pi ≤ 2 := by
    have hs : 1 ≤ Real.sqrt Real.pi := (Real.one_le_sqrt).mpr (by linarith [Real.pi_gt_three])
    exact (div_le_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)).mpr (by linarith)
  have hp (x : ℝ) (hx : 3 ≤ |x|) :
      f x ≤ 5500*Real.exp (-30) * Real.exp (-2*|x|) := by
    have hs : -4*x^2 ≤ -7*|x| := by nlinarith [sq_abs x,mul_nonneg (sub_nonneg.mpr hx) (abs_nonneg x)]
    have haha := mul_le_mul hcle (Real.exp_le_exp.mpr hs) (Real.exp_pos _).le (by norm_num)
    have hr := abs_sub (2/Real.sqrt Real.pi*Real.exp (-4*x^2)) (3/2*D (Real.exp (x-3/4)))
    rw [abs_of_nonneg (mul_nonneg hcoef (Real.exp_pos _).le),abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3/2)] at hr
    have h := hd x hx
    have hb : |2/Real.sqrt Real.pi*Real.exp (-4*x^2) -3/2*D (Real.exp (x-3/4))| ≤
        74*Real.exp (-7*|x|) := by linarith
    have hsquare := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs] at hsquare
    have hw : 3/2*x+3/10*|x| ≤ 2*|x| := by linarith [le_abs_self x,abs_nonneg x]
    calc
      f x ≤ Real.exp (2*|x|) * (74*Real.exp (-7*|x|))^2 :=
        mul_le_mul (Real.exp_le_exp.mpr hw) hsquare (sq_nonneg _) (Real.exp_nonneg _)
      _ = 5476 * Real.exp (-12*|x|) := by
        rw [mul_pow,←Real.exp_nat_mul,show -12*|x|=2*|x|+2*(-7*|x|) by ring,Real.exp_add]; ring
      _ ≤ 5500 * Real.exp (-30-2*|x|) := by
        have he := Real.exp_le_exp.mpr (show -12*|x| ≤ -30-2*|x| by linarith)
        linarith [Real.exp_nonneg (-30-2*|x|)]
      _ = _ := by rw [show -30-2*|x| = -30 + (-2*|x|) by ring,Real.exp_add]; ring
  have h0 := MasulloAudit.window_mellin_evaluation_bounded 1 (by norm_num) 0 (by norm_num)
  have hint : Integrable (fun x : ℝ => Real.exp (-2*|x|)) := by simpa using h0.1
  have hval : (∫ x : ℝ, Real.exp (-2*|x|))=1 := by convert h0.2.1 using 1 <;> norm_num
  have hx {x : ℝ} (hx : x ∈ (Icc (-3:ℝ) 3)ᶜ) : 3 ≤ |x| := by
    by_contra! hl
    exact hx ⟨by linarith [(abs_lt.mp hl).1],(abs_lt.mp hl).2.le⟩
  have hbound : (∫ x in (Icc (-3:ℝ) 3)ᶜ, f x) ≤ ∫ x : ℝ, 5500*Real.exp (-30)*Real.exp (-2*|x|) := by
    rw [←integral_indicator measurableSet_Icc.compl]
    apply integral_mono_ae (hi.indicator measurableSet_Icc.compl) (hint.const_mul _)
    filter_upwards with x
    by_cases h : x ∈ (Icc (-3:ℝ) 3)ᶜ
    · simpa only [indicator_of_mem h] using hp x (hx h)
    · rw [indicator_of_notMem h]; positivity
  apply hbound.trans_lt
  rw [integral_const_mul,hval,mul_one,Real.exp_neg]
  have h := exp_nat_two 30
  norm_num at h
  rw [←div_eq_mul_inv,div_lt_iff₀ (Real.exp_pos _)]
  linarith

end
end MasulloGram.Outer


open MeasureTheory Set MasulloRH.GaussianApproximation
open scoped Topology

theorem solution :
    (energy (3/4) (3/20) (residual 1 (fun _ : Fin 1 => (3/2:ℂ)) (fun _ => (3/4:ℝ))) < 22/1000 ∧
       (22/1000:ℝ) < (1/20) * Real.exp (-(1/2:ℝ))) ∧
    ∀ s : ℂ, s.re ∈ Icc (13/20:ℝ) (17/20) → |s.im| ≤ 1 → riemannZeta s ≠ 0 := by
  classical
  let E := energy (3/4) (3/20) (residual 1 (fun _ : Fin 1 => (3/2:ℂ)) (fun _ => (3/4:ℝ)))
  have hbox := (MasulloRH.finite_theta_approximation_excludes_rectangle_zeros).1 1 1 (3/4) (3/20)
    (1/20) (fun _ : Fin 1 => (3/2:ℂ)) (fun _ => (3/4:ℝ)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  let I := MasulloGram.Cert.concreteEnergyDensity
  have hi : Integrable I := hbox.1
  have he : E = ∫ x : ℝ, I x := rfl
  have hmid := MasulloGram.Cert.actual_central_lt hi
  have htail : (∫ x in (Icc (-3:ℝ) 3)ᶜ, I x) < 1/1000 := by
    have hD (x : ℝ) (hx : 3≤|x|) : |D (Real.exp (x-3/4))| ≤ 48*Real.exp (-7*|x|) :=
      MasulloGram.Outer.shifted_theta_bound D (fun u hu hq => D_far_bound hu rfl hq)
        (fun u hu => D_reflect hu) hx
    have hI : I = MasulloGram.Cert.centralIntegrand (fun t => D (Real.exp (t-3/4))) :=
      funext MasulloGram.Cert.concreteEnergyDensity_eq
    rw [hI] at hi ⊢
    exact MasulloGram.Outer.residual_outer D hD hi
  have hE : E < 22/1000 := by
    have hsplit := integral_add_compl (s:=Icc (-3:ℝ) 3) measurableSet_Icc hi
    change (∫ x in Icc (-3:ℝ) 3, I x) + (∫ x in (Icc (-3:ℝ) 3)ᶜ, I x) = ∫ x : ℝ, I x at hsplit
    change (∫ x in Icc (-3:ℝ) 3, I x) < 21/1000 at hmid
    linarith
  have hsmall : (22/1000:ℝ) < 1/20*Real.exp (-(1/2:ℝ)) := by
    have hx := Real.exp_one_lt_d9
    have h' : Real.exp (1/2:ℝ)^2 = Real.exp 1 := by rw [←Real.exp_nat_mul]; norm_num
    have h : Real.exp (1/2:ℝ) < 2 := by nlinarith [Real.exp_pos (1/2)]
    rw [Real.exp_neg,←div_eq_mul_inv,lt_div_iff₀ (Real.exp_pos _)]
    linarith
  refine ⟨⟨hE,hsmall⟩,?_⟩
  intro s hs ht hz
  have habs : |s.re-3/4| ≤ 3/20-1/20 := abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hbad := hbox.2.2.2 s habs ht hz
  exact (hE.trans hsmall).not_ge hbad
