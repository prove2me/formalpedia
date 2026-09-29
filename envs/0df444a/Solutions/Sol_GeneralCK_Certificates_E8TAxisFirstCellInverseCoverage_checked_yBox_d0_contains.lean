-- Prove2me | solution 1 for GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage.checked_yBox_d0_contains
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T22:22:30.857314+00:00
-- url     : https://prove2.me/submissions/dbc9cd2f-687c-4985-b162-bde0c2f4df4b

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_semantic_core

namespace GeneralCK.Certificates.E8TAxisReparamJet5
end GeneralCK.Certificates.E8TAxisReparamJet5
namespace GeneralCK.Certificates.E8InverseJet5Bridge
end GeneralCK.Certificates.E8InverseJet5Bridge
namespace GeneralCK.Certificates.E8TAxisReparamInterval
end GeneralCK.Certificates.E8TAxisReparamInterval
namespace GeneralCK.E8AnalyticGerm
end GeneralCK.E8AnalyticGerm

section
namespace GeneralCK.Certificates



namespace DyadicInterval



theorem scale_pos (p : ℕ) : 0 < scale p := by unfold scale; positivity
theorem scale_cast_pos (p : ℕ) : 0 < (scale p : ℝ) := by exact_mod_cast scale_pos p











theorem floorDiv_mul_le (z : ℤ) {d : ℤ} (hd : 0 < d) : floorDiv z d*d ≤ z :=
  Int.ediv_mul_le z hd.ne'

theorem le_ceilDiv_mul (z : ℤ) {d : ℤ} (hd : 0 < d) : z ≤ ceilDiv z d*d := by
  have h := floorDiv_mul_le (-z) hd
  unfold floorDiv ceilDiv at *
  nlinarith








theorem ofInt_sound (p : ℕ) (z : ℤ) : (ofInt p z).Contains (z : ℝ) := by
  simp [Contains, ofInt]

theorem add_sound {p : ℕ} {a b : DyadicInterval p} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.add b).Contains (x+y) := by
  rcases hx with ⟨hlx, hux⟩
  rcases hy with ⟨hly, huy⟩
  dsimp [Contains, add]
  push_cast
  constructor <;> nlinarith

theorem neg_sound {p : ℕ} {a : DyadicInterval p} {x : ℝ}
    (hx : a.Contains x) : a.neg.Contains (-x) := by
  rcases hx with ⟨hl, hu⟩
  dsimp [Contains, neg]
  push_cast
  constructor <;> nlinarith

theorem sub_sound {p : ℕ} {a b : DyadicInterval p} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.sub b).Contains (x-y) := by
  simpa only [sub, sub_eq_add_neg] using add_sound hx (neg_sound hy)

private theorem linear_bounds {lo hi x c : ℝ} (hl : lo ≤ x) (hh : x ≤ hi) :
    min (lo*c) (hi*c) ≤ x*c ∧ x*c ≤ max (lo*c) (hi*c) := by
  by_cases hc : 0 ≤ c
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hl hc),
      (mul_le_mul_of_nonneg_right hh hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hh (not_le.mp hc).le),
      (mul_le_mul_of_nonpos_right hl (not_le.mp hc).le).trans (le_max_left _ _)⟩

private theorem product_bounds {al ah bl bh x y : ℝ}
    (hx : al ≤ x ∧ x ≤ ah) (hy : bl ≤ y ∧ y ≤ bh) :
    min (min (al*bl) (al*bh)) (min (ah*bl) (ah*bh)) ≤ x*y ∧
      x*y ≤ max (max (al*bl) (al*bh)) (max (ah*bl) (ah*bh)) := by
  have h := linear_bounds (c := y) hx.1 hx.2
  have hl := linear_bounds (c := al) hy.1 hy.2
  have hh := linear_bounds (c := ah) hy.1 hy.2
  simp only [mul_comm y al, mul_comm y ah, mul_comm bl al, mul_comm bh al,
    mul_comm bl ah, mul_comm bh ah] at hl hh
  exact ⟨(min_le_min hl.1 hh.1).trans h.1, h.2.trans (max_le_max hl.2 hh.2)⟩

theorem mul_sound {p : ℕ} {a b : DyadicInterval p} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.mul b).Contains (x*y) := by
  have hp := product_bounds hx hy
  have hlo : (productLo a b : ℝ) ≤ ((scale p : ℝ)*x)*((scale p : ℝ)*y) := by
    simpa [productLo, or_assoc] using hp.1
  have hhi : ((scale p : ℝ)*x)*((scale p : ℝ)*y) ≤ (productHi a b : ℝ) := by
    simpa [productHi, or_assoc] using hp.2
  have hroundL : ((floorDiv (productLo a b) (scale p) : ℤ) : ℝ)*(scale p : ℝ) ≤ (productLo a b : ℝ) := by
    exact_mod_cast floorDiv_mul_le (productLo a b) (scale_pos p)
  have hroundH : (productHi a b : ℝ) ≤ ((ceilDiv (productHi a b) (scale p) : ℤ) : ℝ)*(scale p : ℝ) := by
    exact_mod_cast le_ceilDiv_mul (productHi a b) (scale_pos p)
  have hs := scale_cast_pos p
  constructor
  · change (floorDiv (productLo a b) (scale p) : ℝ) ≤ (scale p : ℝ)*(x*y)
    apply (mul_le_mul_iff_left₀ hs).mp
    nlinarith [hroundL.trans hlo]
  · change (scale p : ℝ)*(x*y) ≤ (ceilDiv (productHi a b) (scale p) : ℝ)
    apply (mul_le_mul_iff_left₀ hs).mp
    nlinarith [hhi.trans hroundH]

theorem recip_sound {p : ℕ} {a : DyadicInterval p} {x : ℝ}
    (ha : 0 < a.lo) (hx : a.Contains x) : a.recip.Contains (x⁻¹) := by
  have hs := scale_cast_pos p
  have hlo : (0:ℝ) < a.lo := by exact_mod_cast ha
  have hxpos : 0 < x := pos_of_mul_pos_right (hlo.trans_le hx.1) hs.le
  have hhi : (0:ℝ) < a.hi := (mul_pos hs hxpos).trans_le hx.2
  have hhiZ : 0 < a.hi := by exact_mod_cast hhi
  have hrL : (floorDiv (scale p*scale p) a.hi : ℝ)*(a.hi : ℝ) ≤ (scale p : ℝ)^2 := by
    have h := floorDiv_mul_le (scale p*scale p) hhiZ
    exact_mod_cast (by simpa only [pow_two] using h : floorDiv (scale p*scale p) a.hi*a.hi ≤ (scale p)^2)
  have hrH : (scale p : ℝ)^2 ≤ (ceilDiv (scale p*scale p) a.lo : ℝ)*(a.lo : ℝ) := by
    have h := le_ceilDiv_mul (scale p*scale p) ha
    exact_mod_cast (by simpa only [pow_two] using h : (scale p)^2 ≤ ceilDiv (scale p*scale p) a.lo*a.lo)
  constructor
  · change (floorDiv (scale p*scale p) a.hi : ℝ) ≤ (scale p : ℝ)*x⁻¹
    rw [← div_eq_mul_inv]
    calc
      _ ≤ (scale p : ℝ)^2/(a.hi : ℝ) := (le_div_iff₀ hhi).mpr hrL
      _ ≤ (scale p : ℝ)/x := by
        apply (div_le_div_iff₀ hhi hxpos).mpr
        nlinarith [mul_le_mul_of_nonneg_left hx.2 hs.le]
  · change (scale p : ℝ)*x⁻¹ ≤ (ceilDiv (scale p*scale p) a.lo : ℝ)
    rw [← div_eq_mul_inv]
    calc
      _ ≤ (scale p : ℝ)^2/(a.lo : ℝ) := by
        apply (div_le_div_iff₀ hxpos hlo).mpr
        nlinarith [mul_le_mul_of_nonneg_left hx.1 hs.le]
      _ ≤ _ := (div_le_iff₀ hlo).mpr hrH




theorem subsetCheck_sound {p : ℕ} {a b : DyadicInterval p}
    (h : a.subsetCheck b=true) {x : ℝ} (hx : a.Contains x) : b.Contains x := by
  have hh : b.lo ≤ a.lo ∧ a.hi ≤ b.hi := by simpa [subsetCheck] using h
  have hl : (b.lo : ℝ) ≤ (a.lo : ℝ) := by exact_mod_cast hh.1
  have hu : (a.hi : ℝ) ≤ (b.hi : ℝ) := by exact_mod_cast hh.2
  exact ⟨hl.trans hx.1, hx.2.trans hu⟩

theorem positiveCheck_sound {p : ℕ} {a : DyadicInterval p}
    (h : a.positiveCheck=true) {x : ℝ} (hx : a.Contains x) : 0 < x := by
  have ha : 0 < a.lo := by simpa [positiveCheck] using h
  have ha' : (0:ℝ) < a.lo := by exact_mod_cast ha
  exact pos_of_mul_pos_right (ha'.trans_le hx.1) (scale_cast_pos p).le









end DyadicInterval
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates.DyadicLogSeries
open scoped BigOperators















theorem state_sound {p : ℕ} {w : DyadicInterval p} {x : ℝ} (hw : w.Contains x) (n : ℕ) :
    (state w n).1.Contains (∑ k ∈ Finset.range n, x^(2*k+1)/(2*k+1)) ∧
      (state w n).2.Contains (x^(2*n+1)) := by
  induction n with
  | zero => simpa [state] using And.intro (DyadicInterval.ofInt_sound p 0) hw
  | succ n ih =>
    have hd : 0 < (DyadicInterval.ofInt p (2*(n:ℤ)+1)).lo := by
      change 0 < DyadicInterval.scale p*(2*(n:ℤ)+1)
      exact mul_pos (DyadicInterval.scale_pos p) (by omega)
    have hr := DyadicInterval.recip_sound hd (DyadicInterval.ofInt_sound p (2*(n:ℤ)+1))
    have ht := DyadicInterval.mul_sound ih.2 hr
    have hs := DyadicInterval.add_sound ih.1 ht
    have hp := DyadicInterval.mul_sound ih.2 (DyadicInterval.mul_sound hw hw)
    constructor
    · simpa only [state,Finset.sum_range_succ,Int.cast_add,Int.cast_mul,Int.cast_ofNat,
        Int.cast_one,Int.cast_natCast,div_eq_mul_inv] using hs
    · convert! hp using 1
      rw [show 2*(n+1)+1=(2*n+1)+2 by omega, pow_add, pow_two]

theorem denominator_sound {p : ℕ} {w : DyadicInterval p} {x : ℝ} (hw : w.Contains x) :
    (denominator w).Contains (1-x^2) := by
  simpa only [denominator,Int.cast_one,pow_two] using
    DyadicInterval.sub_sound (DyadicInterval.ofInt_sound p 1) (DyadicInterval.mul_sound hw hw)

theorem guard_sound {p : ℕ} {w : DyadicInterval p} {x : ℝ}
    (hg : guard w=true) (hw : w.Contains x) : 0 ≤ x ∧ x < 1 := by
  have hh := Bool.and_eq_true_iff.mp hg
  have hl : (0:ℝ) ≤ w.lo := by exact_mod_cast (of_decide_eq_true hh.1 : 0 ≤ w.lo)
  have hx : 0 ≤ x := nonneg_of_mul_nonneg_right (hl.trans hw.1) (DyadicInterval.scale_cast_pos p)
  have hd := DyadicInterval.positiveCheck_sound hh.2 (denominator_sound hw)
  exact ⟨hx, by nlinarith⟩

theorem partial_sound {p : ℕ} {w : DyadicInterval p} {x : ℝ} (hw : w.Contains x) (n : ℕ) :
    (partialSum w n).Contains (2*∑ k ∈ Finset.range n, x^(2*k+1)/(2*k+1)) := by
  simpa only [partialSum,Int.cast_ofNat] using
    DyadicInterval.mul_sound (DyadicInterval.ofInt_sound p 2) (state_sound hw n).1

theorem remainder_sound {p : ℕ} {w : DyadicInterval p} {x : ℝ}
    (hg : guard w=true) (hw : w.Contains x) (n : ℕ) :
    (remainder w n).Contains (2*x^(2*n+1)/(1-x^2)) := by
  have hd : 0 < (denominator w).lo := by
    simpa only [DyadicInterval.positiveCheck,decide_eq_true_eq] using (Bool.and_eq_true_iff.mp hg).2
  have hh := DyadicInterval.mul_sound
    (DyadicInterval.mul_sound (DyadicInterval.ofInt_sound p 2) (state_sound hw n).2)
    (DyadicInterval.recip_sound hd (denominator_sound hw))
  simpa only [remainder,Int.cast_ofNat,div_eq_mul_inv] using hh

/-- The analytic inequalities are proved in mathlib; this bridges them to the
integer-only partialSum-sum and outward remainder computation. -/
theorem enclosure_sound {p : ℕ} {w : DyadicInterval p} {x : ℝ}
    (hg : guard w=true) (hw : w.Contains x) (n : ℕ) :
    (enclosure w n).Contains (Real.log ((1+x)/(1-x))) := by
  have hx := guard_sound hg hw
  have hl := Real.sum_range_le_log_div hx.1 hx.2 n
  have hu := Real.log_div_le_sum_range_add hx.1 hx.2 n
  have hs := partial_sound hw n
  have ht := DyadicInterval.add_sound hs (remainder_sound hg hw n)
  have hrealL : 2*∑ k ∈ Finset.range n, x^(2*k+1)/(2*k+1) ≤ Real.log ((1+x)/(1-x)) := by linarith
  have hrealH : Real.log ((1+x)/(1-x)) ≤
      2*∑ k ∈ Finset.range n, x^(2*k+1)/(2*k+1)+2*x^(2*n+1)/(1-x^2) := by
    rw [mul_div_assoc]
    linarith
  exact ⟨hs.1.trans (mul_le_mul_of_nonneg_left hrealL (DyadicInterval.scale_cast_pos p).le),
    (mul_le_mul_of_nonneg_left hrealH (DyadicInterval.scale_cast_pos p).le).trans ht.2⟩













end GeneralCK.Certificates.DyadicLogSeries
end

section
namespace GeneralCK.Certificates.DyadicFastLog



theorem fraction_sound (p : ℕ) (a : ℤ) {b : ℤ} (hb : 0 < b) :
    (fraction p a b).Contains ((a:ℝ)/b) := by
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  have hl : (DyadicInterval.floorDiv (DyadicInterval.scale p*a) b:ℝ)*b ≤
      (DyadicInterval.scale p:ℝ)*a := by
    exact_mod_cast DyadicInterval.floorDiv_mul_le (DyadicInterval.scale p*a) hb
  have hu : (DyadicInterval.scale p:ℝ)*a ≤
      (DyadicInterval.ceilDiv (DyadicInterval.scale p*a) b:ℝ)*b := by
    exact_mod_cast DyadicInterval.le_ceilDiv_mul (DyadicInterval.scale p*a) hb
  change _ ≤ _ ∧ _ ≤ _
  rw [← mul_div_assoc]
  exact ⟨(le_div_iff₀ hb').mpr hl,(div_le_iff₀ hb').mpr hu⟩







theorem check_sound {p : ℕ} {a b : ℤ} {e n : ℕ} {out : DyadicInterval p}
    (hc : check a b e n out=true) : out.Contains (Real.log ((a:ℝ)/b)) := by
  have h3 := Bool.and_eq_true_iff.mp hc
  have h2 := Bool.and_eq_true_iff.mp h3.1
  have h1 := Bool.and_eq_true_iff.mp h2.1
  have hab : 0<a ∧ 0<b := of_decide_eq_true h1.1
  have ha : (0:ℝ)<a := by exact_mod_cast hab.1
  have hb : (0:ℝ)<b := by exact_mod_cast hab.2
  have ht := DyadicLogSeries.enclosure_sound h1.2 (fraction_sound p 1 (by norm_num : (0:ℤ)<3)) n
  norm_num at ht
  have hd : 0 < b+a*2^e := add_pos hab.2 (mul_pos hab.1 (by positivity))
  have hr := DyadicLogSeries.enclosure_sound h2.2 (fraction_sound p (b-a*2^e) hd) n
  have heq : (1+((b-a*2^e:ℤ):ℝ)/(b+a*2^e:ℤ))/
      (1-((b-a*2^e:ℤ):ℝ)/(b+a*2^e:ℤ)) = (b:ℝ)/(a*2^e) := by
    push_cast
    have hp : (0:ℝ)<2^e := by positivity
    field_simp
    ring
  rw [heq] at hr
  have hs := DyadicInterval.neg_sound (DyadicInterval.add_sound
    (DyadicInterval.mul_sound (DyadicInterval.ofInt_sound p e) ht) hr)
  have hl : -((e:ℝ)*Real.log 2+Real.log ((b:ℝ)/(a*2^e))) = Real.log ((a:ℝ)/b) := by
    rw [Real.log_div hb.ne' (mul_pos ha (by positivity)).ne',
      Real.log_mul ha.ne' (by positivity),Real.log_pow,Real.log_div ha.ne' hb.ne']
    ring
  simp only [Int.cast_natCast] at hs
  rw [hl] at hs
  exact DyadicInterval.subsetCheck_sound h3.2 hs

end GeneralCK.Certificates.DyadicFastLog
end

section
namespace GeneralCK.Certificates.DyadicExp

open DyadicInterval





theorem check_sound {p : ℕ} {input : DyadicInterval p}
    {lowerNum lowerDen upperNum upperDen : ℤ}
    {lowerExponent lowerTerms upperExponent upperTerms : ℕ}
    {logLower logUpper : DyadicInterval p}
    (hc : check input lowerNum lowerDen upperNum upperDen
      lowerExponent lowerTerms upperExponent upperTerms logLower logUpper = true)
    {x : ℝ} (hx : input.Contains x) :
    (enclosure p lowerNum lowerDen upperNum upperDen).Contains (Real.exp x) := by
  have htop := Bool.and_eq_true_iff.mp hc
  have hpair := Bool.and_eq_true_iff.mp htop.1
  have hlogLower := DyadicFastLog.check_sound hpair.1
  have hlogUpper := DyadicFastLog.check_sound hpair.2
  have hcmp : logLower.hi ≤ input.lo ∧ input.hi ≤ logUpper.lo :=
    of_decide_eq_true htop.2
  have hlDen : 0 < lowerDen := (of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp hpair.1).1).1).1).2
  have huDen : 0 < upperDen := (of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp hpair.2).1).1).1).2
  have hlNum : 0 < lowerNum := (of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp hpair.1).1).1).1).1
  have huNum : 0 < upperNum := (of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp hpair.2).1).1).1).1
  have hs : (0 : ℝ) < DyadicInterval.scale p := DyadicInterval.scale_cast_pos p
  have hlogLowerLe : Real.log ((lowerNum : ℝ) / lowerDen) ≤ x := by
    have h1 := hlogLower.2
    have h2 : (logLower.hi : ℝ) ≤ (input.lo : ℝ) := by exact_mod_cast hcmp.1
    have h3 := hx.1
    nlinarith
  have hxLeLogUpper : x ≤ Real.log ((upperNum : ℝ) / upperDen) := by
    have h1 := hx.2
    have h2 : (input.hi : ℝ) ≤ (logUpper.lo : ℝ) := by exact_mod_cast hcmp.2
    have h3 := hlogUpper.1
    nlinarith
  have hlRatPos : (0 : ℝ) < (lowerNum : ℝ) / lowerDen := by
    positivity
  have huRatPos : (0 : ℝ) < (upperNum : ℝ) / upperDen := by
    positivity
  have hlExp : (lowerNum : ℝ) / lowerDen ≤ Real.exp x :=
    (Real.log_le_iff_le_exp hlRatPos).mp hlogLowerLe
  have hExpU : Real.exp x ≤ (upperNum : ℝ) / upperDen :=
    (Real.le_log_iff_exp_le huRatPos).mp hxLeLogUpper
  have hlFrac := DyadicFastLog.fraction_sound p lowerNum hlDen
  have huFrac := DyadicFastLog.fraction_sound p upperNum huDen
  constructor
  · exact hlFrac.1.trans (mul_le_mul_of_nonneg_left hlExp hs.le)
  · exact (mul_le_mul_of_nonneg_left hExpU hs.le).trans huFrac.2

end GeneralCK.Certificates.DyadicExp
end

section
namespace GeneralCK.Certificates

structure Jet5 where
  d0 : ℝ → ℝ
  d1 : ℝ → ℝ
  d2 : ℝ → ℝ
  d3 : ℝ → ℝ
  d4 : ℝ → ℝ
  d5 : ℝ → ℝ

namespace Jet5





def const (c : ℝ) : Jet5 :=
  ⟨fun _ => c, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

def variableJet : Jet5 :=
  ⟨id, fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

def add (a b : Jet5) : Jet5 :=
  ⟨fun t => a.d0 t + b.d0 t, fun t => a.d1 t + b.d1 t,
   fun t => a.d2 t + b.d2 t, fun t => a.d3 t + b.d3 t,
   fun t => a.d4 t + b.d4 t, fun t => a.d5 t + b.d5 t⟩

def neg (a : Jet5) : Jet5 :=
  ⟨fun t => -a.d0 t, fun t => -a.d1 t, fun t => -a.d2 t,
   fun t => -a.d3 t, fun t => -a.d4 t, fun t => -a.d5 t⟩

/-- Raw-derivative Leibniz propagation through order five. -/
def mul (a b : Jet5) : Jet5 :=
  ⟨fun t => a.d0 t * b.d0 t,
   fun t => a.d1 t * b.d0 t + a.d0 t * b.d1 t,
   fun t => a.d2 t * b.d0 t + 2*a.d1 t*b.d1 t + a.d0 t*b.d2 t,
   fun t => a.d3 t*b.d0 t + 3*a.d2 t*b.d1 t + 3*a.d1 t*b.d2 t + a.d0 t*b.d3 t,
   fun t => a.d4 t*b.d0 t + 4*a.d3 t*b.d1 t + 6*a.d2 t*b.d2 t +
     4*a.d1 t*b.d3 t + a.d0 t*b.d4 t,
   fun t => a.d5 t*b.d0 t + 5*a.d4 t*b.d1 t + 10*a.d3 t*b.d2 t +
     10*a.d2 t*b.d3 t + 5*a.d1 t*b.d4 t + a.d0 t*b.d5 t⟩













/-- The order-five jet of `exp (c+m*t)`.  This is the first transcendental
shape needed by the E8 parameterization (`c=0`, `m=-2`). -/
noncomputable def expAffine (c m : ℝ) : Jet5 :=
  ⟨fun t => Real.exp (c+m*t), fun t => Real.exp (c+m*t)*m,
   fun t => Real.exp (c+m*t)*m^2, fun t => Real.exp (c+m*t)*m^3,
   fun t => Real.exp (c+m*t)*m^4, fun t => Real.exp (c+m*t)*m^5⟩






end Jet5
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates



namespace DyadicJet5Enclosure

open DyadicInterval

def Contains {p : ℕ} (b : DyadicJet5Enclosure p) (j : Jet5) (t : ℝ) : Prop :=
  b.d0.Contains (j.d0 t) ∧ b.d1.Contains (j.d1 t) ∧
  b.d2.Contains (j.d2 t) ∧ b.d3.Contains (j.d3 t) ∧
  b.d4.Contains (j.d4 t) ∧ b.d5.Contains (j.d5 t)











theorem contains_const (p : ℕ) (z : ℤ) (t : ℝ) :
    (const p z).Contains (Jet5.const z) t := by
  exact ⟨ofInt_sound p z, by simpa [const, Jet5.const] using ofInt_sound p 0,
    by simpa [const, Jet5.const] using ofInt_sound p 0,
    by simpa [const, Jet5.const] using ofInt_sound p 0,
    by simpa [const, Jet5.const] using ofInt_sound p 0,
    by simpa [const, Jet5.const] using ofInt_sound p 0⟩

theorem contains_variable {p : ℕ} {i : DyadicInterval p} {t : ℝ} (ht : i.Contains t) :
    (variableJet i).Contains Jet5.variableJet t := by
  exact ⟨ht, by simpa [variableJet, Jet5.variableJet] using ofInt_sound p 1,
    by simpa [variableJet, Jet5.variableJet] using ofInt_sound p 0,
    by simpa [variableJet, Jet5.variableJet] using ofInt_sound p 0,
    by simpa [variableJet, Jet5.variableJet] using ofInt_sound p 0,
    by simpa [variableJet, Jet5.variableJet] using ofInt_sound p 0⟩

theorem Contains.add {p : ℕ} {b c : DyadicJet5Enclosure p} {j k : Jet5} {t : ℝ}
    (hb : b.Contains j t) (hc : c.Contains k t) :
    (b.add c).Contains (j.add k) t :=
  ⟨add_sound hb.1 hc.1, add_sound hb.2.1 hc.2.1,
    add_sound hb.2.2.1 hc.2.2.1, add_sound hb.2.2.2.1 hc.2.2.2.1,
    add_sound hb.2.2.2.2.1 hc.2.2.2.2.1, add_sound hb.2.2.2.2.2 hc.2.2.2.2.2⟩





end DyadicJet5Enclosure
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates
namespace Jet5

/-- Raw derivatives of the reciprocal through order five. -/
noncomputable def inv (a : Jet5) : Jet5 :=
  ⟨a.d0⁻¹,
   -a.d1 / a.d0^2,
   (fun y => 2*(a.d1^2) y)/a.d0^3-a.d2/a.d0^2,
   (fun y => -6*(a.d1^3) y)/a.d0^4+
     ((fun y => 6*(a.d1*a.d2) y)/a.d0^3-a.d3/a.d0^2),
   (fun y => 24*(a.d1^4) y)/a.d0^5-(fun y => 36*(a.d1^2*a.d2) y)/a.d0^4+
     (fun y => 6*(a.d2^2) y)/a.d0^3+(fun y => 8*(a.d1*a.d3) y)/a.d0^3-
     a.d4/a.d0^2,
   fun t => -120*a.d1 t^5/a.d0 t^6+240*a.d1 t^3*a.d2 t/a.d0 t^5-
     90*a.d1 t*a.d2 t^2/a.d0 t^4-60*a.d1 t^2*a.d3 t/a.d0 t^4+
     20*a.d2 t*a.d3 t/a.d0 t^3+10*a.d1 t*a.d4 t/a.d0 t^3-
     a.d5 t/a.d0 t^2⟩



/-- Define logarithmic derivatives from `a' * a⁻¹`; this exposes the domain
hypothesis only in the soundness theorem. -/
noncomputable def log (a : Jet5) : Jet5 :=
  let r := a.inv
  ⟨fun t => Real.log (a.d0 t),
   fun t => a.d1 t*r.d0 t,
   fun t => a.d2 t*r.d0 t+a.d1 t*r.d1 t,
   fun t => a.d3 t*r.d0 t+2*a.d2 t*r.d1 t+a.d1 t*r.d2 t,
   fun t => a.d4 t*r.d0 t+3*a.d3 t*r.d1 t+3*a.d2 t*r.d2 t+a.d1 t*r.d3 t,
   fun t => a.d5 t*r.d0 t+4*a.d4 t*r.d1 t+6*a.d3 t*r.d2 t+
     4*a.d2 t*r.d3 t+a.d1 t*r.d4 t⟩



end Jet5
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates
namespace DyadicJet5Enclosure

open DyadicInterval



theorem Contains.inv {p : ℕ} {b : DyadicJet5Enclosure p} {a : Jet5} {t : ℝ}
    (hb : b.Contains a t) (hp : 0 < b.d0.lo) : b.inv.Contains a.inv t := by
  rcases hb with ⟨h0,h1,h2,h3,h4,h5⟩
  have r1 := recip_sound hp h0
  have r2 := mul_sound r1 r1
  have r3 := mul_sound r2 r1
  have r4 := mul_sound r3 r1
  have r5 := mul_sound r4 r1
  have r6 := mul_sound r5 r1
  have c2 := ofInt_sound p 2
  have c6 := ofInt_sound p 6
  have c8 := ofInt_sound p 8
  have c10 := ofInt_sound p 10
  have c20 := ofInt_sound p 20
  have c24 := ofInt_sound p 24
  have c36 := ofInt_sound p 36
  have c60 := ofInt_sound p 60
  have c90 := ofInt_sound p 90
  have c120 := ofInt_sound p 120
  have c240 := ofInt_sound p 240
  dsimp only [Contains, DyadicJet5Enclosure.inv, Jet5.inv]
  refine ⟨r1, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [div_eq_mul_inv, pow_two] using mul_sound (neg_sound h1) r2
  · convert sub_sound (mul_sound (mul_sound c2 (mul_sound h1 h1)) r3)
      (mul_sound h2 r2) using 1 <;>
      simp [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.add_apply, Pi.sub_apply] <;> ring
  · convert sub_sound (add_sound
      (mul_sound (neg_sound (mul_sound c6 (mul_sound (mul_sound h1 h1) h1))) r4)
      (mul_sound (mul_sound c6 (mul_sound h1 h2)) r3)) (mul_sound h3 r2)
      using 1 <;>
      simp [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.add_apply, Pi.sub_apply] <;> ring
  · convert sub_sound (add_sound (add_sound
      (sub_sound (mul_sound (mul_sound c24 (mul_sound (mul_sound (mul_sound h1 h1) h1) h1)) r5)
        (mul_sound (mul_sound c36 (mul_sound (mul_sound h1 h1) h2)) r4))
      (mul_sound (mul_sound c6 (mul_sound h2 h2)) r3))
      (mul_sound (mul_sound c8 (mul_sound h1 h3)) r3)) (mul_sound h4 r2)
      using 1 <;>
      simp [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.add_apply, Pi.sub_apply] <;> ring
  · convert sub_sound (add_sound (add_sound
      (sub_sound (sub_sound (add_sound
        (mul_sound (neg_sound (mul_sound c120
          (mul_sound (mul_sound (mul_sound (mul_sound h1 h1) h1) h1) h1))) r6)
        (mul_sound (mul_sound c240 (mul_sound (mul_sound (mul_sound h1 h1) h1) h2)) r5))
        (mul_sound (mul_sound c90 (mul_sound (mul_sound h1 h2) h2)) r4))
        (mul_sound (mul_sound c60 (mul_sound (mul_sound h1 h1) h3)) r4))
      (mul_sound (mul_sound c20 (mul_sound h2 h3)) r3))
      (mul_sound (mul_sound c10 (mul_sound h1 h4)) r3)) (mul_sound h5 r2)
      using 1 <;>
      simp [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.add_apply, Pi.sub_apply] <;> ring



theorem Contains.log {p : ℕ} {b : DyadicJet5Enclosure p} {l : DyadicInterval p}
    {a : Jet5} {t : ℝ} (hb : b.Contains a t) (hp : 0 < b.d0.lo)
    (hl : l.Contains (Real.log (a.d0 t))) : (b.log l).Contains a.log t := by
  have hr := hb.inv hp
  rcases hb with ⟨h0,h1,h2,h3,h4,h5⟩
  rcases hr with ⟨r0,r1,r2,r3,r4,r5⟩
  have c2 := ofInt_sound p 2
  have c3 := ofInt_sound p 3
  have c4 := ofInt_sound p 4
  have c6 := ofInt_sound p 6
  dsimp only [Contains, DyadicJet5Enclosure.log, Jet5.log]
  exact ⟨hl, mul_sound h1 r0,
    add_sound (mul_sound h2 r0) (mul_sound h1 r1),
    add_sound (add_sound (mul_sound h3 r0) (mul_sound (mul_sound c2 h2) r1))
      (mul_sound h1 r2),
    add_sound (add_sound (add_sound (mul_sound h4 r0) (mul_sound (mul_sound c3 h3) r1))
      (mul_sound (mul_sound c3 h2) r2)) (mul_sound h1 r3),
    add_sound (add_sound (add_sound (add_sound (mul_sound h5 r0)
      (mul_sound (mul_sound c4 h4) r1)) (mul_sound (mul_sound c6 h3) r2))
      (mul_sound (mul_sound c4 h2) r3)) (mul_sound h1 r4)⟩

end DyadicJet5Enclosure
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates
namespace DyadicJet5Enclosure

open DyadicInterval



theorem Contains.mul {p : ℕ} {a b : DyadicJet5Enclosure p} {j k : Jet5} {t : ℝ}
    (ha : a.Contains j t) (hb : b.Contains k t) :
    (a.mul b).Contains (j.mul k) t := by
  rcases ha with ⟨a0,a1,a2,a3,a4,a5⟩
  rcases hb with ⟨b0,b1,b2,b3,b4,b5⟩
  have c2 := ofInt_sound p 2
  have c3 := ofInt_sound p 3
  have c4 := ofInt_sound p 4
  have c5 := ofInt_sound p 5
  have c6 := ofInt_sound p 6
  have c10 := ofInt_sound p 10
  dsimp only [Contains, DyadicJet5Enclosure.mul, Jet5.mul]
  exact ⟨mul_sound a0 b0,
    add_sound (mul_sound a1 b0) (mul_sound a0 b1),
    add_sound (add_sound (mul_sound a2 b0) (mul_sound (mul_sound c2 a1) b1))
      (mul_sound a0 b2),
    add_sound (add_sound (add_sound (mul_sound a3 b0) (mul_sound (mul_sound c3 a2) b1))
      (mul_sound (mul_sound c3 a1) b2)) (mul_sound a0 b3),
    add_sound (add_sound (add_sound (add_sound (mul_sound a4 b0)
      (mul_sound (mul_sound c4 a3) b1)) (mul_sound (mul_sound c6 a2) b2))
      (mul_sound (mul_sound c4 a1) b3)) (mul_sound a0 b4),
    add_sound (add_sound (add_sound (add_sound (add_sound (mul_sound a5 b0)
      (mul_sound (mul_sound c5 a4) b1)) (mul_sound (mul_sound c10 a3) b2))
      (mul_sound (mul_sound c10 a2) b3)) (mul_sound (mul_sound c5 a1) b4))
      (mul_sound a0 b5)⟩



end DyadicJet5Enclosure
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates.E8TAxisStableJet5

open Set E8TAxisReparamJet5 E8InverseJet5Bridge



noncomputable def zJet : Jet5 := Jet5.expAffine 0 (-2)
noncomputable def onePlusZJet : Jet5 := (Jet5.const 1).add zJet
noncomputable def rJet : Jet5 :=
  ((Jet5.const 1).add zJet.neg).mul onePlusZJet.inv
noncomputable def qJet : Jet5 :=
  ((Jet5.const 4).mul zJet).mul (onePlusZJet.mul onePlusZJet).inv
noncomputable def l1Jet : Jet5 := onePlusZJet.log
noncomputable def ellJet : Jet5 := Jet5.variableJet.add l1Jet
noncomputable def hJet : Jet5 :=
  l1Jet.add ((((Jet5.const 2).mul Jet5.variableJet).mul zJet).mul onePlusZJet.inv)
noncomputable def log2Jet : Jet5 := Jet5.const (Real.log 2)
noncomputable def xJet : Jet5 :=
  (log2Jet.mul rJet).mul ((Jet5.const 2).mul hJet).inv
noncomputable def yJet : Jet5 :=
  ((Jet5.const 2).mul log2Jet.inv).mul
    (Jet5.variableJet.add ((rJet.mul hJet).mul (qJet.mul ellJet).inv))

@[simp] theorem zJet_d0 (a : ℝ) : zJet.d0 a = E8TAxisStableScalar.z a := by
  simp [zJet, Jet5.expAffine, E8TAxisStableScalar.z]

@[simp] theorem onePlusZJet_d0 (a : ℝ) : onePlusZJet.d0 a = 1 + E8TAxisStableScalar.z a := by
  simp [onePlusZJet, Jet5.add, Jet5.const]

@[simp] theorem rJet_d0 (a : ℝ) : rJet.d0 a = E8TAxisStableScalar.r a := by
  simp [rJet, Jet5.mul, Jet5.add, Jet5.neg, Jet5.const, Jet5.inv,
    E8TAxisStableScalar.r, sub_eq_add_neg, div_eq_mul_inv]

@[simp] theorem qJet_d0 (a : ℝ) : qJet.d0 a = E8TAxisStableScalar.q a := by
  simp [qJet, Jet5.mul, Jet5.const, Jet5.inv, E8TAxisStableScalar.q, pow_two, div_eq_mul_inv]

@[simp] theorem l1Jet_d0 (a : ℝ) : l1Jet.d0 a = E8TAxisStableScalar.l1 a := by
  simp [l1Jet, Jet5.log, E8TAxisStableScalar.l1]

@[simp] theorem ellJet_d0 (a : ℝ) : ellJet.d0 a = E8TAxisStableScalar.ell a := by
  simp [ellJet, Jet5.add, Jet5.variableJet, E8TAxisStableScalar.ell]

@[simp] theorem hJet_d0 (a : ℝ) : hJet.d0 a = E8TAxisStableScalar.h a := by
  simp [hJet, Jet5.add, Jet5.mul, Jet5.const, Jet5.variableJet, Jet5.inv,
    E8TAxisStableScalar.h, div_eq_mul_inv]

@[simp] theorem log2Jet_d0 (a : ℝ) : log2Jet.d0 a = Real.log 2 := rfl



@[simp] theorem yJet_d0 (a : ℝ) : yJet.d0 a = E8TAxisStableScalar.Y a := by
  simp [yJet, Jet5.mul, Jet5.add, Jet5.const, Jet5.inv, Jet5.variableJet,
    E8TAxisStableScalar.Y, div_eq_mul_inv]

































end GeneralCK.Certificates.E8TAxisStableJet5
end

section
namespace GeneralCK.Certificates.E8TAxisStableInterval

open DyadicInterval E8TAxisStableJet5 E8TAxisReparamInterval



theorem constant_sound {p : ℕ} {v : DyadicInterval p} {r a : ℝ}
    (hv : v.Contains r) : (constant v).Contains (Jet5.const r) a := by
  have hz : (ofInt p 0).Contains (0 : ℝ) := by simpa using ofInt_sound p 0
  exact ⟨hv, hz, hz, hz, hz, hz⟩



theorem negative_sound {p : ℕ} {v : DyadicJet5Enclosure p} {j : Jet5} {a : ℝ}
    (hv : v.Contains j a) : (negative v).Contains j.neg a :=
  ⟨neg_sound hv.1, neg_sound hv.2.1, neg_sound hv.2.2.1,
    neg_sound hv.2.2.2.1, neg_sound hv.2.2.2.2.1, neg_sound hv.2.2.2.2.2⟩





theorem zBox_sound {p : ℕ} {i : Inputs p} {a : ℝ}
    (he : i.expNegTwo.Contains (Real.exp (-2 * a))) :
    (zBox i).Contains zJet a := by
  dsimp only [zBox, zJet, Jet5.expAffine, DyadicJet5Enclosure.Contains]
  simp only [zero_add]
  refine ⟨he, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using mul_sound he (ofInt_sound p (-2))
  · norm_num at *
    exact mul_sound he (ofInt_sound p 4)
  · norm_num at *
    simpa using mul_sound he (ofInt_sound p (-8))
  · norm_num at *
    exact mul_sound he (ofInt_sound p 16)
  · norm_num at *
    simpa using mul_sound he (ofInt_sound p (-32))







def xBox {p : ℕ} (i : Inputs p) :=
  ((constant i.logTwo).mul (rBox i)).mul
    ((DyadicJet5Enclosure.const p 2).mul (hBox i)).inv




theorem xyBox_sound {p : ℕ} {i : Inputs p} {a : ℝ}
    (ha : i.alpha.Contains a)
    (he : i.expNegTwo.Contains (Real.exp (-2 * a)))
    (hl : i.logOnePlusExp.Contains (Real.log (1 + Real.exp (-2 * a))))
    (hL : i.logTwo.Contains (Real.log 2)) (hp : DenominatorsPositive i) :
    (xBox i).Contains xJet a ∧ (yBox i).Contains yJet a := by
  have a0 := DyadicJet5Enclosure.contains_variable ha
  have c1 : (DyadicJet5Enclosure.const p 1).Contains (Jet5.const 1) a := by
    simpa using DyadicJet5Enclosure.contains_const p 1 a
  have c2 : (DyadicJet5Enclosure.const p 2).Contains (Jet5.const 2) a := by
    simpa using DyadicJet5Enclosure.contains_const p 2 a
  have c4 : (DyadicJet5Enclosure.const p 4).Contains (Jet5.const 4) a := by
    simpa using DyadicJet5Enclosure.contains_const p 4 a
  have hz := zBox_sound he
  have ho : (onePlusZBox i).Contains onePlusZJet a := c1.add hz
  have hr : (rBox i).Contains rJet a :=
    (c1.add (negative_sound hz)).mul (ho.inv hp.1)
  have hq : (qBox i).Contains qJet a :=
    (c4.mul hz).mul ((ho.mul ho).inv hp.2.1)
  have hlog : (l1Box i).Contains l1Jet a := by
    apply ho.log hp.1
    simpa [onePlusZJet, zJet, Jet5.add, Jet5.const, Jet5.expAffine] using hl
  have hell : (ellBox i).Contains ellJet a := a0.add hlog
  have hh : (hBox i).Contains hJet a :=
    hlog.add (((c2.mul a0).mul hz).mul (ho.inv hp.1))
  have htwo : (constant i.logTwo).Contains log2Jet a := constant_sound hL
  exact ⟨(htwo.mul hr).mul ((c2.mul hh).inv hp.2.2.1),
    (c2.mul (htwo.inv hp.2.2.2.2)).mul
      (a0.add ((hr.mul hh).mul ((hq.mul hell).inv hp.2.2.2.1)))⟩







theorem logBoxCheck_sound {p : ℕ} {input out : DyadicInterval p} {w : FastLogBoxWitness}
    (hc : logBoxCheck input out w = true) {x : ℝ} (hx : input.Contains x) :
    out.Contains (Real.log x) := by
  have htop := Bool.and_eq_true_iff.mp hc
  have hbot := Bool.and_eq_true_iff.mp htop.1
  have hlo : 0 < input.lo := of_decide_eq_true hbot.1
  have hl0 := DyadicFastLog.check_sound hbot.2
  have hu0 := DyadicFastLog.check_sound htop.2
  have hl : out.Contains (-Real.log ((scale p : ℝ) / input.lo)) := by
    simpa only [DyadicInterval.neg, neg_neg] using neg_sound hl0
  have hu : out.Contains (-Real.log ((scale p : ℝ) / input.hi)) := by
    simpa only [DyadicInterval.neg, neg_neg] using neg_sound hu0
  have hs := scale_cast_pos p
  have hlReal : (0 : ℝ) < input.lo := by exact_mod_cast hlo
  have hiReal : (0 : ℝ) < input.hi := lt_of_lt_of_le hlReal (hx.1.trans hx.2)
  have hscale : (0 : ℝ) < scale p := scale_cast_pos p
  have hlEq : -Real.log ((scale p : ℝ) / input.lo) =
      Real.log ((input.lo : ℝ) / scale p) := by
    rw [Real.log_div hscale.ne' hlReal.ne', Real.log_div hlReal.ne' hscale.ne']
    ring
  have huEq : -Real.log ((scale p : ℝ) / input.hi) =
      Real.log ((input.hi : ℝ) / scale p) := by
    rw [Real.log_div hscale.ne' hiReal.ne', Real.log_div hiReal.ne' hscale.ne']
    ring
  rw [hlEq] at hl
  rw [huEq] at hu
  have hlow : (input.lo : ℝ) / scale p ≤ x := (div_le_iff₀ hs).mpr (by
    simpa only [mul_comm] using hx.1)
  have hupp : x ≤ (input.hi : ℝ) / scale p := (le_div_iff₀ hs).mpr (by
    simpa only [mul_comm] using hx.2)
  have hxpos : 0 < x := (div_pos hlReal hs).trans_le hlow
  exact ⟨hl.1.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (div_pos hlReal hs) hlow) hs.le),
    (mul_le_mul_of_nonneg_left (Real.log_le_log hxpos hupp) hs.le).trans hu.2⟩





theorem expBoxCheck_sound {p : ℕ} {input out : DyadicInterval p} {w : ExpWitness p}
    (hc : expBoxCheck input out w = true) {x : ℝ} (hx : input.Contains x) :
    out.Contains (Real.exp x) := by
  have hh := Bool.and_eq_true_iff.mp hc
  exact subsetCheck_sound hh.2 (DyadicExp.check_sound hh.1 hx)






end GeneralCK.Certificates.E8TAxisStableInterval
end

section
namespace GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage

open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar




















end GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage
end

open GeneralCK GeneralCK.Certificates
open Set GeneralCK.Certificates.DyadicInterval GeneralCK.Certificates.E8TAxisStableInterval
open GeneralCK.Certificates.E8TAxisStableScalar
open GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage
theorem solution {p : ℕ} {i : Inputs p}
    {we : ExpWitness p} {wl wL : FastLogBoxWitness}
    (he : expBoxCheck ((ofInt p (-2)).mul i.alpha) i.expNegTwo we = true)
    (hl : logBoxCheck ((ofInt p 1).add i.expNegTwo) i.logOnePlusExp wl = true)
    (hL : logBoxCheck (ofInt p 2) i.logTwo wL = true)
    (hp : DenominatorsPositive i) {a : ℝ} (ha : i.alpha.Contains a) :
    (yBox i).d0.Contains (Y a) := by
  have hz : i.expNegTwo.Contains (Real.exp (-2 * a)) := by
    simpa using expBoxCheck_sound he (mul_sound (ofInt_sound p (-2)) ha)
  have hc1 : (ofInt p 1).Contains (1 : ℝ) := by simpa using ofInt_sound p 1
  have hc2 : (ofInt p 2).Contains (2 : ℝ) := by simpa using ofInt_sound p 2
  have hlog := logBoxCheck_sound hl (add_sound hc1 hz)
  have htwo := logBoxCheck_sound hL hc2
  simpa only [E8TAxisStableJet5.yJet_d0] using (xyBox_sound ha hz hlog htwo hp).2.1
