-- Prove2me | solution 1 for GeneralCK.Certificates.E8TAxisStableInterval.checked_stable_contains_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T23:37:13.421083+00:00
-- url     : https://prove2.me/submissions/8747b311-be8f-43ff-a5e3-9daf3eb27432

import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_derivative_semantics
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_semantic_core
import Definitions.Def_GeneralCK_MixedBounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_entropy_comparison
import Definitions.Def_GeneralCK_statement
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
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
import Mathlib.Topology.Order.MonotoneContinuity
import Theorems.Thm_GeneralCK_Certificates_E8TAxisReparamJet5_qdata5_eq_canonical
import Theorems.Thm_GeneralCK_Certificates_PilotData_log_two
import Theorems.Thm_GeneralCK_H_pos
import Theorems.Thm_GeneralCK_H_strictMonoOn

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



theorem soundAt_const (c t : ℝ) : (const c).SoundAt t := by
  exact ⟨hasDerivAt_const t c, hasDerivAt_const t 0, hasDerivAt_const t 0,
    hasDerivAt_const t 0, hasDerivAt_const t 0⟩

theorem soundAt_variable (t : ℝ) : variableJet.SoundAt t := by
  exact ⟨hasDerivAt_id t, hasDerivAt_const t 1, hasDerivAt_const t 0,
    hasDerivAt_const t 0, hasDerivAt_const t 0⟩

theorem SoundAt.add {a b : Jet5} {t : ℝ} (ha : a.SoundAt t) (hb : b.SoundAt t) :
    (a.add b).SoundAt t := by
  exact ⟨ha.1.add hb.1, ha.2.1.add hb.2.1, ha.2.2.1.add hb.2.2.1,
    ha.2.2.2.1.add hb.2.2.2.1, ha.2.2.2.2.add hb.2.2.2.2⟩

theorem SoundAt.neg {a : Jet5} {t : ℝ} (ha : a.SoundAt t) : a.neg.SoundAt t := by
  exact ⟨ha.1.neg, ha.2.1.neg, ha.2.2.1.neg, ha.2.2.2.1.neg, ha.2.2.2.2.neg⟩

theorem SoundAt.mul {a b : Jet5} {t : ℝ} (ha : a.SoundAt t) (hb : b.SoundAt t) :
    (a.mul b).SoundAt t := by
  refine ⟨ha.1.mul hb.1, ?_, ?_, ?_, ?_⟩
  · convert! (ha.2.1.mul hb.1).add (ha.1.mul hb.2.1) using 1 <;>
      simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;> first | (funext u; simp <;> ring) | ring
  · have h := ((ha.2.2.1.mul hb.1).add
      ((ha.2.1.mul hb.2.1).const_mul 2)).add (ha.1.mul hb.2.2.1)
    convert! h using 1 <;> simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext u; simp <;> ring) | ring
  · have h := (((ha.2.2.2.1.mul hb.1).add
      ((ha.2.2.1.mul hb.2.1).const_mul 3)).add
      ((ha.2.1.mul hb.2.2.1).const_mul 3)).add (ha.1.mul hb.2.2.2.1)
    convert! h using 1 <;> simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext u; simp <;> ring) | ring
  · have h := ((((ha.2.2.2.2.mul hb.1).add
      ((ha.2.2.2.1.mul hb.2.1).const_mul 4)).add
      ((ha.2.2.1.mul hb.2.2.1).const_mul 6)).add
      ((ha.2.1.mul hb.2.2.2.1).const_mul 4)).add (ha.1.mul hb.2.2.2.2)
    convert! h using 1 <;> simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext u; simp <;> ring) | ring

/-- The order-five jet of `exp (c+m*t)`.  This is the first transcendental
shape needed by the E8 parameterization (`c=0`, `m=-2`). -/
noncomputable def expAffine (c m : ℝ) : Jet5 :=
  ⟨fun t => Real.exp (c+m*t), fun t => Real.exp (c+m*t)*m,
   fun t => Real.exp (c+m*t)*m^2, fun t => Real.exp (c+m*t)*m^3,
   fun t => Real.exp (c+m*t)*m^4, fun t => Real.exp (c+m*t)*m^5⟩

theorem soundAt_expAffine (c m t : ℝ) : (expAffine c m).SoundAt t := by
  have hi : HasDerivAt (fun u : ℝ => c+m*u) m t := by
    convert! (hasDerivAt_const t c).add ((hasDerivAt_id t).mul_const m) using 1
    · funext u
      simp [id_eq, mul_comm]
    · ring
  have he := (Real.hasDerivAt_exp (c+m*t)).comp t hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert! he using 1 <;> simp [expAffine]
  · convert! he.mul_const m using 1 <;> simp [expAffine] <;> ring
  · convert! he.mul_const (m^2) using 1 <;> simp [expAffine] <;> ring
  · convert! he.mul_const (m^3) using 1 <;> simp [expAffine] <;> ring
  · convert! he.mul_const (m^4) using 1 <;> simp [expAffine] <;> ring




end Jet5
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates



namespace DyadicJet5Enclosure

open DyadicInterval













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

theorem SoundAt.inv {a : Jet5} {t : ℝ} (ha : a.SoundAt t) (hn : a.d0 t ≠ 0) :
    a.inv.SoundAt t := by
  have h2 : a.d0 t ^ 2 ≠ 0 := pow_ne_zero 2 hn
  have h3 : a.d0 t ^ 3 ≠ 0 := pow_ne_zero 3 hn
  have h4 : a.d0 t ^ 4 ≠ 0 := pow_ne_zero 4 hn
  have h5 : a.d0 t ^ 5 ≠ 0 := pow_ne_zero 5 hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert! ha.1.inv hn using 1 <;> simp [Jet5.inv]
  · have h := ha.2.1.neg.div (ha.1.pow 2) h2
    convert! h using 1 <;> simp only [Jet5.inv, Pi.neg_apply, Pi.pow_apply,
      Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply] <;>
      field_simp [hn] <;> ring
  · have h := (((ha.2.1.pow 2).const_mul 2).div (ha.1.pow 3) h3).sub
      (ha.2.2.1.div (ha.1.pow 2) h2)
    convert! h using 1 <;> simp only [Jet5.inv, Pi.neg_apply, Pi.pow_apply,
      Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply] <;>
      field_simp [hn] <;> ring
  · have h := (((ha.2.1.pow 3).const_mul (-6)).div (ha.1.pow 4) h4).add
      ((((ha.2.1.mul ha.2.2.1).const_mul 6).div (ha.1.pow 3) h3).sub
        (ha.2.2.2.1.div (ha.1.pow 2) h2))
    convert! h using 1 <;> simp only [Jet5.inv, Pi.neg_apply, Pi.pow_apply,
      Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply] <;>
      field_simp [hn] <;> ring
  · have h1 := ((ha.2.1.pow 4).const_mul 24).div (ha.1.pow 5) h5
    have h2term := (((ha.2.1.pow 2).mul ha.2.2.1).const_mul 36).div (ha.1.pow 4) h4
    have h3' := ((ha.2.2.1.pow 2).const_mul 6).div (ha.1.pow 3) h3
    have h4' := ((ha.2.1.mul ha.2.2.2.1).const_mul 8).div (ha.1.pow 3) h3
    have h5' := ha.2.2.2.2.div (ha.1.pow 2) h2
    have h := (((h1.sub h2term).add h3').add h4').sub h5'
    convert! h using 1 <;> simp only [Jet5.inv, Pi.neg_apply, Pi.pow_apply,
      Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply] <;>
      field_simp [hn] <;> ring

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

theorem SoundAt.log {a : Jet5} {t : ℝ} (ha : a.SoundAt t) (hn : a.d0 t ≠ 0) :
    a.log.SoundAt t := by
  have hr := ha.inv hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert! ha.1.log hn using 1 <;> simp [Jet5.log, Jet5.inv, div_eq_mul_inv]
  · convert! ha.2.1.mul hr.1 using 1 <;>
      simp [Jet5.log] <;> first | (funext u; simp <;> ring) | ring
  · have h := (ha.2.2.1.mul hr.1).add (ha.2.1.mul hr.2.1)
    convert! h using 1 <;> simp [Jet5.log] <;>
      first | (funext u; simp <;> ring) | ring
  · have h := ((ha.2.2.2.1.mul hr.1).add
      ((ha.2.2.1.mul hr.2.1).const_mul 2)).add
      (ha.2.1.mul hr.2.2.1)
    convert! h using 1 <;> simp [Jet5.log] <;>
      first | (funext u; simp <;> ring) | ring
  · have h := (((ha.2.2.2.2.mul hr.1).add
      ((ha.2.2.2.1.mul hr.2.1).const_mul 3)).add
      ((ha.2.2.1.mul hr.2.2.1).const_mul 3)).add
      (ha.2.1.mul hr.2.2.2.1)
    convert! h using 1 <;> simp [Jet5.log] <;>
      first | (funext u; simp <;> ring) | ring

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
namespace GeneralCK
open scoped BigOperators















theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

@[simp] theorem H_zero : H 0 = 0 := by simp [H]
@[simp] theorem H_one : H 1 = 0 := by simp [H]
@[simp] theorem H_half : H (1 / 2) = 1 := by
  have h : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  simpa [H, one_div] using div_self h







theorem H_continuous : Continuous H :=
  Real.binEntropy_continuous.div_const _

end GeneralCK
end

section
namespace GeneralCK.Comparison
open Set









@[simp] theorem noiseParameter_zero (eps : ℝ) : noiseParameter eps 0 = eps := by
  simp [noiseParameter]



theorem hasDerivAt_H {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    HasDerivAt H (J p) p := by
  have hl : Real.log ((1 - p) / p) = Real.log (1 - p) - Real.log p :=
    Real.log_div (by linarith) (ne_of_gt hp)
  simpa [H, J, hl] using!
    (Real.hasDerivAt_binEntropy (ne_of_gt hp) (by linarith)).div_const (Real.log 2)







end GeneralCK.Comparison
end

section
namespace GeneralCK
open Set Filter
open scoped Topology









theorem J_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) : 0 < J v := by
  apply div_pos _ log_two_pos
  apply Real.log_pos
  apply (lt_div_iff₀ hv).2
  linarith



theorem hasDerivAt_J {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    HasDerivAt J (-1 / (Real.log 2 * v * (1 - v))) v := by
  have hv1 : 1 - v ≠ 0 := by linarith
  have hlog : J =ᶠ[𝓝 v] (fun p => (Real.log (1 - p) - Real.log p) / Real.log 2) := by
    filter_upwards [Ioo_mem_nhds hv hv'] with p hp
    simp only [J, Real.log_div (by linarith [hp.2] : 1 - p ≠ 0) (ne_of_gt hp.1)]
  have hd := (((hasDerivAt_id v).const_sub 1).log (by simpa using hv1)).sub
    ((hasDerivAt_id v).log (ne_of_gt hv))
  have hd' := (hd.div_const (Real.log 2)).congr_of_eventuallyEq hlog
  convert! hd' using 1
  simp only [id_eq]
  field_simp [hv1]
  ring









end GeneralCK
end

section
namespace GeneralCK

/-- The contact equation has exactly one solution in the open lower half. -/
theorem existsUnique_radialContact {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    ∃! v : ℝ, 0 < v ∧ v < 1 / 2 ∧ z * H v = h * (1 - 2 * v) := by
  let g : ℝ → ℝ := fun v => z * H v - h * (1 - 2 * v)
  have hg : Continuous g :=
    (H_continuous.const_mul z).sub
      ((continuous_const.sub (continuous_const.mul continuous_id)).const_mul h)
  have hzero : g 0 = -h := by simp [g]
  have hhalf : g (1 / 2) = z := by simp only [g, H_half]; ring
  have himage := intermediate_value_Icc (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    hg.continuousOn
  obtain ⟨v, hv, heq⟩ := himage (show (0 : ℝ) ∈ Set.Icc (g 0) (g (1 / 2)) by
    rw [hzero, hhalf]; exact ⟨by linarith, hz.le⟩)
  have hv0 : 0 < v := by
    apply lt_of_le_of_ne hv.1
    intro he
    rw [← he, hzero] at heq
    linarith
  have hv1 : v < 1 / 2 := by
    apply lt_of_le_of_ne hv.2
    intro he
    rw [he, hhalf] at heq
    linarith
  have hveq : z * H v = h * (1 - 2 * v) := sub_eq_zero.mp heq
  refine ⟨v, ⟨hv0, hv1, hveq⟩, ?_⟩
  rintro u ⟨hu0, hu1, hueq⟩
  rcases lt_trichotomy u v with huv | huv | huv
  · have hH := H_strictMonoOn ⟨hu0.le, hu1.le⟩ ⟨hv0.le, hv1.le⟩ huv
    have hm := mul_lt_mul_of_pos_left hH hz
    nlinarith
  · exact huv
  · have hH := H_strictMonoOn ⟨hv0.le, hv1.le⟩ ⟨hu0.le, hu1.le⟩ huv
    have hm := mul_lt_mul_of_pos_left hH hz
    nlinarith

theorem radialContact_spec {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < radialContact z h ∧ radialContact z h < 1 / 2 ∧
      z * H (radialContact z h) = h * (1 - 2 * radialContact z h) := by
  obtain ⟨v, hv, huniq⟩ := existsUnique_radialContact hz hh
  have hset : {u : ℝ | 0 < u ∧ u < 1 / 2 ∧ z * H u = h * (1 - 2 * u)} = {v} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun hu => huniq u hu, fun he => he ▸ hv⟩
  simpa only [radialContact, hset, csInf_singleton] using hv

theorem radialContact_pos {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < radialContact z h := (radialContact_spec hz hh).1

theorem radialContact_lt_half {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    radialContact z h < 1 / 2 := (radialContact_spec hz hh).2.1

theorem radialContact_equation {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    z * H (radialContact z h) = h * (1 - 2 * radialContact z h) :=
  (radialContact_spec hz hh).2.2

theorem radialContact_eq_of_equation {z h v : ℝ} (hz : 0 < z) (hh : 0 < h)
    (hv : 0 < v) (hv' : v < 1 / 2) (heq : z * H v = h * (1 - 2 * v)) :
    radialContact z h = v := by
  obtain ⟨u, _, huniq⟩ := existsUnique_radialContact hz hh
  exact (huniq _ (radialContact_spec hz hh)).trans (huniq v ⟨hv, hv', heq⟩).symm









theorem radialContact_strictAnti_radius {a b h : ℝ}
    (ha : 0 < a) (hab : a < b) (hh : 0 < h) :
    radialContact b h < radialContact a h := by
  obtain ⟨hu, hu', hequ⟩ := radialContact_spec ha hh
  obtain ⟨hv, hv', heqv⟩ := radialContact_spec (ha.trans hab) hh
  by_contra hn
  have huv : radialContact a h ≤ radialContact b h := le_of_not_gt hn
  have hH := H_strictMonoOn.monotoneOn ⟨hu.le, hu'.le⟩ ⟨hv.le, hv'.le⟩ huv
  have hm := mul_le_mul_of_nonneg_left (show 1 - 2 * radialContact b h ≤
      1 - 2 * radialContact a h by linarith) hh.le
  have hg : a * H (radialContact a h) < b * H (radialContact b h) := by
    calc
      a * H (radialContact a h) ≤ a * H (radialContact b h) :=
        mul_le_mul_of_nonneg_left hH ha.le
      _ < b * H (radialContact b h) :=
        mul_lt_mul_of_pos_right hab (H_pos hv (by linarith))
  linarith















end GeneralCK
end

section
namespace GeneralCK
open Set Filter
open scoped Topology

theorem radialContact_image_radius {h : ℝ} (hh : 0 < h) :
    (fun z => radialContact z h) '' Ioi 0 = Ioo 0 (1 / 2) := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨radialContact_pos hz hh, radialContact_lt_half hz hh⟩
  · intro hv
    have hH : 0 < H v := H_pos hv.1 (by linarith [hv.2])
    have hz : 0 < h * (1 - 2 * v) / H v :=
      div_pos (mul_pos hh (by linarith [hv.2])) hH
    refine ⟨h * (1 - 2 * v) / H v, hz, ?_⟩
    apply radialContact_eq_of_equation hz hh hv.1 hv.2
    exact div_mul_cancel₀ _ hH.ne'

theorem continuousAt_radialContact_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    ContinuousAt (fun r => radialContact r h) z := by
  have hanti : StrictAntiOn (fun r => radialContact r h) (Ioi 0) :=
    fun a ha b _ hab => radialContact_strictAnti_radius ha hab hh
  apply hanti.dual_right.continuousAt_of_image_mem_nhds (Ioi_mem_nhds hz)
  change (fun r => radialContact r h) '' Ioi 0 ∈ 𝓝 (radialContact z h)
  rw [radialContact_image_radius hh]
  exact Ioo_mem_nhds (radialContact_pos hz hh) (radialContact_lt_half hz hh)

theorem radialContact_denominator_pos {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < z * J (radialContact z h) + 2 * h := by
  have hJ := J_pos (radialContact_pos hz hh) (radialContact_lt_half hz hh)
  positivity

theorem hasDerivAt_radialContact_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (fun r => radialContact r h)
      (-H (radialContact z h) / (z * J (radialContact z h) + 2 * h)) z := by
  let v := radialContact z h
  have hv : 0 < v := radialContact_pos hz hh
  have hv' : v < 1 / 2 := radialContact_lt_half hz hh
  have hH : H v ≠ 0 := (H_pos hv (by linarith)).ne'
  have heq : h * (1 - 2 * v) = z * H v := (radialContact_equation hz hh).symm
  have hd : HasDerivAt (fun u => h * (1 - 2 * u) / H u)
      (-(z * J v + 2 * h) / H v) v := by
    have hd := ((((hasDerivAt_id v).const_mul 2).const_sub 1).const_mul h).div
      (Comparison.hasDerivAt_H hv (by linarith)) hH
    convert! hd using 1
    simp only [id_eq, mul_one, heq]
    field_simp
    ring
  have hD : z * J v + 2 * h ≠ 0 := (radialContact_denominator_pos hz hh).ne'
  have hinv := hd.of_local_left_inverse (continuousAt_radialContact_radius hz hh)
    (div_ne_zero (neg_ne_zero.mpr hD) hH) (by
      filter_upwards [Ioi_mem_nhds hz] with r hr
      have hp := H_pos (radialContact_pos hr hh)
        (show radialContact r h < 1 by linarith [radialContact_lt_half hr hh])
      rw [← radialContact_equation hr hh]
      exact mul_div_cancel_right₀ r hp.ne')
  convert! hinv using 1
  change -H v / (z * J v + 2 * h) = (-(z * J v + 2 * h) / H v)⁻¹
  rw [inv_div, div_neg, neg_div]



theorem hasDerivAt_F_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (fun r => F r h)
      (J (radialContact z h) + z * H (radialContact z h) /
        (Real.log 2 * radialContact z h * (1 - radialContact z h) *
          (z * J (radialContact z h) + 2 * h))) z := by
  have hv := radialContact_pos hz hh
  have hv' : radialContact z h < 1 := by linarith [radialContact_lt_half hz hh]
  have hd := (hasDerivAt_id z).mul
    ((hasDerivAt_J hv hv').comp z (hasDerivAt_radialContact_radius hz hh))
  have heq : (fun r => F r h) =ᶠ[𝓝 z] (fun r => r * J (radialContact r h)) := by
    filter_upwards [Ioi_mem_nhds hz] with r hr
    simp only [F, ne_of_gt (show 0 < r from hr), ↓reduceIte]
  have hd' := hd.congr_of_eventuallyEq heq
  convert! hd' using 1
  simp only [id_eq, one_mul, Function.comp_apply, div_eq_mul_inv, mul_inv_rev]
  ring



namespace Certificates.Mixed

theorem hn_eq_H_mul_log (v : ℝ) : hn v = H v * Real.log 2 := by
  unfold hn H Real.binEntropy
  simp only [Real.log_inv]
  rw [div_mul_cancel₀ _ log_two_pos.ne']
  ring

theorem kap_identity {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    2 * kap v = 2 * hn v + (1 - 2 * v) * (Real.log 2 * J v) := by
  unfold kap hn J
  rw [Real.log_mul hv.ne' (by linarith), Real.log_div (by linarith) hv.ne']
  field_simp
  ring

theorem kap_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) : 0 < kap v := by
  have hi := kap_identity hv (show v < 1 by linarith)
  have hhn : 0 < hn v := by
    rw [hn_eq_H_mul_log]
    exact mul_pos (H_pos hv (by linarith)) log_two_pos
  have hj := J_pos hv hv'
  have hr : 0 < (1 - 2 * v) * (Real.log 2 * J v) :=
    mul_pos (by linarith) (mul_pos log_two_pos hj)
  linarith

theorem hasDerivAt_hn {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    HasDerivAt hn (J v * Real.log 2) v := by
  simpa only [← hn_eq_H_mul_log] using
    (Comparison.hasDerivAt_H hv hv').mul_const (Real.log 2)

theorem hasDerivAt_kap {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    HasDerivAt kap (-(1 - 2 * v) / (2 * v * (1 - v))) v := by
  have hd := (((hasDerivAt_id v).mul ((hasDerivAt_id v).const_sub 1)).log
    (mul_ne_zero hv.ne' (by simpa using (show 1 - v ≠ 0 by linarith)))).neg.div_const 2
  convert! hd using 1
  simp only [id_eq, one_mul, Pi.mul_apply]
  field_simp
  ring

end Certificates.Mixed

open Certificates.Mixed



theorem hasDerivAt_radialSlope {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    HasDerivAt radialSlope
      (-hn v * (2 * kap v - (1 - 2 * v)^2) /
        (4 * Real.log 2 * v^2 * (1 - v)^2 * (kap v)^2)) v := by
  have hv1 : v < 1 := by linarith
  have hL : Real.log 2 ≠ 0 := log_two_pos.ne'
  have hvc : 1 - v ≠ 0 := by linarith
  have hr : 1 - 2 * v ≠ 0 := by linarith
  have hk : kap v ≠ 0 := (kap_pos hv hv').ne'
  have hJ : J v = (2 * kap v - 2 * hn v) / ((1 - 2 * v) * Real.log 2) := by
    apply (eq_div_iff (mul_ne_zero hr hL)).2
    nlinarith [kap_identity hv hv1]
  have hdN := (((hasDerivAt_id v).const_mul 2).const_sub 1).mul (hasDerivAt_hn hv hv1)
  have hdD := (((hasDerivAt_id v).const_mul (2 * Real.log 2)).mul
    ((hasDerivAt_id v).const_sub 1)).mul (hasDerivAt_kap hv hv1)
  have hd := (hasDerivAt_J hv hv1).add (hdN.div hdD (by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hL) hv.ne') hvc) hk))
  convert! hd using 1
  simp only [id_eq, mul_one, Pi.mul_apply]
  rw [hJ]
  field_simp
  ring

theorem radialContact_denominator_identity {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    (z * J (radialContact z h) + 2 * h) * (1 - 2 * radialContact z h) * Real.log 2 =
      2 * z * kap (radialContact z h) := by
  have hv := radialContact_pos hz hh
  have hv' : radialContact z h < 1 := by linarith [radialContact_lt_half hz hh]
  have hk := kap_identity hv hv'
  rw [hn_eq_H_mul_log] at hk
  have heq := radialContact_equation hz hh
  linear_combination -z * hk - (2 * Real.log 2) * heq

theorem hasDerivAt_F_radius_slope {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (fun r => F r h) (radialSlope (radialContact z h)) z := by
  have hv := radialContact_pos hz hh
  have hv' := radialContact_lt_half hz hh
  have hD := (radialContact_denominator_pos hz hh).ne'
  have hK := (kap_pos hv hv').ne'
  have hvc : 1 - radialContact z h ≠ 0 := by linarith
  have hL := log_two_pos.ne'
  have hi := radialContact_denominator_identity hz hh
  convert! hasDerivAt_F_radius hz hh using 1
  unfold radialSlope
  rw [hn_eq_H_mul_log]
  field_simp [hD, hK, hvc, hL, hv.ne']
  field_simp [show J (radialContact z h) * z + 2 * h ≠ 0 by
    simpa only [mul_comm] using hD]
  linear_combination H (radialContact z h) * hi

theorem deriv_F_radius_slope {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (fun r => F r h) z = radialSlope (radialContact z h) :=
  (hasDerivAt_F_radius_slope hz hh).deriv

theorem hasDerivAt_deriv_F_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (deriv (fun r => F r h))
      (hn (radialContact z h) * (2 * kap (radialContact z h) -
          (1 - 2 * radialContact z h)^2) * H (radialContact z h) /
        (4 * Real.log 2 * (radialContact z h)^2 * (1 - radialContact z h)^2 *
          (kap (radialContact z h))^2 * (z * J (radialContact z h) + 2 * h))) z := by
  have hd := (hasDerivAt_radialSlope (radialContact_pos hz hh)
    (radialContact_lt_half hz hh)).comp z (hasDerivAt_radialContact_radius hz hh)
  have heq : deriv (fun r => F r h) =ᶠ[𝓝 z] (fun r => radialSlope (radialContact r h)) := by
    filter_upwards [Ioi_mem_nhds hz] with r hr
    exact deriv_F_radius_slope hr hh
  have hd' := hd.congr_of_eventuallyEq heq
  convert! hd' using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem radius_mul_deriv2_F_eq_profile {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    z * deriv (deriv (fun r => F r h)) z = profile (radialContact z h) := by
  rw [(hasDerivAt_deriv_F_radius hz hh).deriv]
  have hv := radialContact_pos hz hh
  have hv' := radialContact_lt_half hz hh
  have hD := (radialContact_denominator_pos hz hh).ne'
  have hK := (kap_pos hv hv').ne'
  have hvc : 1 - radialContact z h ≠ 0 := by linarith
  have hL := log_two_pos.ne'
  have hi := radialContact_denominator_identity hz hh
  unfold profile
  rw [hn_eq_H_mul_log]
  field_simp [hD, hK, hvc, hL, hv.ne']
  linear_combination -2 * (H (radialContact z h))^2 *
    (2 * kap (radialContact z h) - (1 - 2 * radialContact z h)^2) * hi

end GeneralCK
end

section
namespace GeneralCK.Scalar







end GeneralCK.Scalar

namespace GeneralCK
open Certificates.Mixed

theorem kap_ge_log_two {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    Real.log 2 ≤ kap v := by
  have hp : 0 < v*(1-v) := mul_pos hv (by linarith)
  have hu : v*(1-v) ≤ 1/4 := by nlinarith [sq_nonneg (v-1/2)]
  have hh : Real.log (v*(1-v)) ≤ -2*Real.log 2 := by
    calc
      Real.log (v*(1-v)) ≤ Real.log (1/4) := Real.log_le_log hp hu
      _ = -2*Real.log 2 := by
        rw [show (1/4:ℝ) = (2^2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
        norm_num
  unfold kap
  linarith

theorem kap_sq_gap_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) :
    0 < 2*kap v-(1-2*v)^2 := by
  have hk := kap_ge_log_two hv (by linarith)
  have hL := Certificates.PilotData.log_two.1
  norm_num only [div_one] at hL
  have hr : (1-2*v)^2 ≤ 1 := by nlinarith
  linarith

theorem mixed_profile_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) :
    0 < profile v := by
  have hvc : 0 < 1-v := by linarith
  have hr : 0 < 1-2*v := by linarith
  have hn0 : 0 < hn v := by
    rw [hn_eq_H_mul_log]
    exact mul_pos (H_pos hv (by linarith)) log_two_pos
  have hk := kap_pos hv hv'
  have hg := kap_sq_gap_pos hv hv'
  unfold profile
  positivity

theorem deriv2_F_radius_pos {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < deriv (deriv (fun r => F r h)) z := by
  have hp : 0 < z*deriv (deriv (fun r => F r h)) z := by
    rw [radius_mul_deriv2_F_eq_profile hz hh]
    exact mixed_profile_pos (radialContact_pos hz hh) (radialContact_lt_half hz hh)
  exact (mul_pos_iff_of_pos_left hz).mp hp





end GeneralCK
end

section
namespace GeneralCK
open Set

theorem hasDerivAt_e8Theta {x : ℝ} (hx : 0 < x) :
    @HasDerivAt ℝ _ ℝ
      DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup
      (((NormedAlgebra.toNormedSpace ℝ) : NormedSpace ℝ ℝ).toModule) _ _
      e8Theta
      (2 * deriv (deriv (fun r => F r 1)) (2 * x)) x := by
  have hd := (hasDerivAt_deriv_F_radius (show 0 < 2 * x by positivity)
    (by norm_num : (0 : ℝ) < 1)).differentiableAt.hasDerivAt
  have h := hd.comp x ((hasDerivAt_id x).const_mul 2)
  have heq : (deriv (fun r => F r 1)) ∘ (fun y : ℝ => 2 * y) = e8Theta := by
    funext y
    rfl
  rw [← heq]
  convert h using 1 <;> ring

theorem deriv_e8Theta_pos {x : ℝ} (hx : 0 < x) :
    0 < deriv e8Theta x := by
  rw [(hasDerivAt_e8Theta hx).deriv]
  exact mul_pos (by norm_num) (deriv2_F_radius_pos (by positivity) (by norm_num))

theorem continuousOn_e8Theta_pos : ContinuousOn e8Theta (Ioi 0) := by
  intro x hx
  exact (hasDerivAt_e8Theta hx).continuousAt.continuousWithinAt

/-- The normalized slope is strictly increasing on precisely the positive
contact-coordinate domain used in equation (8). -/
theorem strictMonoOn_e8Theta_pos : StrictMonoOn e8Theta (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) continuousOn_e8Theta_pos
  intro x hx
  exact deriv_e8Theta_pos (by simpa using hx)









theorem e8Q_pos {y : ℝ} (hy : y ∈ e8SlopeRange) : 0 < e8Q y := by
  rw [e8Q, dif_pos hy]
  exact (Classical.choose_spec hy).1

theorem e8Theta_e8Q {y : ℝ} (hy : y ∈ e8SlopeRange) :
    e8Theta (e8Q y) = y := by
  rw [e8Q, dif_pos hy]
  exact (Classical.choose_spec hy).2

/-- The constructed inverse is a left inverse at every positive contact
coordinate. -/
theorem e8Q_e8Theta {x : ℝ} (hx : 0 < x) : e8Q (e8Theta x) = x := by
  have hy : e8Theta x ∈ e8SlopeRange := ⟨x, hx, rfl⟩
  apply strictMonoOn_e8Theta_pos.injOn (e8Q_pos hy) hx
  rw [e8Theta_e8Q hy]









end GeneralCK
end

section
namespace GeneralCK.Certificates.E8TAxisReparamInterval

open DyadicInterval E8TAxisReparamJet5



theorem powI_sound {p : ℕ} {x : DyadicInterval p} {r : ℝ}
    (hx : x.Contains r) (n : ℕ) : (powI x n).Contains (r ^ n) := by
  induction n with
  | zero => simpa [powI] using ofInt_sound p 1
  | succ n ih => simpa [powI, pow_succ] using mul_sound ih hx



theorem eval_sound {p : ℕ} {x y : DyadicJet5Enclosure p}
    {jx jy : Jet5} {a : ℝ}
    (hx : x.Contains jx a) (hy : y.Contains jy a) (hp : 0 < y.d1.lo) :
    (eval x y).Contains (qdata5 jx jy) a := by
  rcases hx with ⟨hx0,hx1,hx2,hx3,hx4,hx5⟩
  rcases hy with ⟨hy0,hy1,hy2,hy3,hy4,hy5⟩
  have hr := recip_sound hp hy1
  dsimp only [DyadicJet5Enclosure.Contains, eval, qdata5]
  refine ⟨hx0, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [div_eq_mul_inv, inv_pow, Int.cast_ofNat] using (mul_sound hx1 hr)
  · simpa only [div_eq_mul_inv, inv_pow, Int.cast_ofNat] using (mul_sound (sub_sound (mul_sound hy1 hx2) (mul_sound hy2 hx1)) (powI_sound hr 3))
  · simpa only [div_eq_mul_inv, inv_pow, Int.cast_ofNat] using (mul_sound (add_sound (sub_sound (sub_sound (mul_sound (powI_sound hy1 2) hx3) (mul_sound (mul_sound (mul_sound (ofInt_sound p 3) hy1) hy2) hx2)) (mul_sound (mul_sound hy1 hy3) hx1)) (mul_sound (mul_sound (ofInt_sound p 3) (powI_sound hy2 2)) hx1)) (powI_sound hr 5))
  · simpa only [div_eq_mul_inv, inv_pow, Int.cast_ofNat] using (mul_sound (sub_sound (add_sound (add_sound (sub_sound (sub_sound (sub_sound (mul_sound (powI_sound hy1 3) hx4) (mul_sound (mul_sound (mul_sound (ofInt_sound p 6) (powI_sound hy1 2)) hy2) hx3)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 4) (powI_sound hy1 2)) hy3) hx2)) (mul_sound (mul_sound (powI_sound hy1 2) hy4) hx1)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 15) hy1) (powI_sound hy2 2)) hx2)) (mul_sound (mul_sound (mul_sound (mul_sound (ofInt_sound p 10) hy1) hy2) hy3) hx1)) (mul_sound (mul_sound (ofInt_sound p 15) (powI_sound hy2 3)) hx1)) (powI_sound hr 7))
  · simpa only [div_eq_mul_inv, inv_pow, Int.cast_ofNat] using (mul_sound (add_sound (sub_sound (sub_sound (add_sound (add_sound (add_sound (add_sound (sub_sound (sub_sound (sub_sound (sub_sound (mul_sound (powI_sound hy1 4) hx5) (mul_sound (mul_sound (mul_sound (ofInt_sound p 10) (powI_sound hy1 3)) hy2) hx4)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 10) (powI_sound hy1 3)) hy3) hx3)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 5) (powI_sound hy1 3)) hy4) hx2)) (mul_sound (mul_sound (powI_sound hy1 3) hy5) hx1)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 45) (powI_sound hy1 2)) (powI_sound hy2 2)) hx3)) (mul_sound (mul_sound (mul_sound (mul_sound (ofInt_sound p 60) (powI_sound hy1 2)) hy2) hy3) hx2)) (mul_sound (mul_sound (mul_sound (mul_sound (ofInt_sound p 15) (powI_sound hy1 2)) hy2) hy4) hx1)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 10) (powI_sound hy1 2)) (powI_sound hy3 2)) hx1)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 105) hy1) (powI_sound hy2 3)) hx2)) (mul_sound (mul_sound (mul_sound (mul_sound (ofInt_sound p 105) hy1) (powI_sound hy2 2)) hy3) hx1)) (mul_sound (mul_sound (ofInt_sound p 105) (powI_sound hy2 4)) hx1)) (powI_sound hr 9))

theorem contains_of_eqAt {p : ℕ} {x : DyadicJet5Enclosure p}
    {f g : Jet5} {a : ℝ} (hx : x.Contains f a) (he : f.EqAt g a) :
    x.Contains g a := by
  rcases he with ⟨h0,h1,h2,h3,h4,h5⟩
  simpa only [DyadicJet5Enclosure.Contains, h0,h1,h2,h3,h4,h5] using hx

/-- The remaining parameter assumptions are scalar equality and soundness of
the two stable jets; the full fifth-order inverse recurrence is proved here. -/
theorem eval_contains_canonical {p : ℕ} {x y : DyadicJet5Enclosure p}
    {jx jy : Jet5} {U : Set ℝ} (hU : IsOpen U)
    (hjx : jx.SoundOn U) (hjy : jy.SoundOn U)
    (hrange : ∀ a ∈ U, jy.d0 a ∈ GeneralCK.e8SlopeRange)
    (hvalue : ∀ a ∈ U, jx.d0 a = GeneralCK.e8Q (jy.d0 a))
    {a : ℝ} (ha : a ∈ U)
    (hx : x.Contains jx a) (hy : y.Contains jy a) (hp : 0 < y.d1.lo) :
    (eval x y).Contains
      (E8InverseJet5Bridge.e8QJet5 E8InverseJet5Bridge.e8ThetaCanonicalJet5)
      (jy.d0 a) := by
  have hpReal : jy.d1 a ≠ 0 := by
    have hh := hy.2.1.1
    have hpos : (0 : ℝ) < y.d1.lo := by exact_mod_cast hp
    have hs := scale_cast_pos p
    intro he
    rw [he, mul_zero] at hh
    linarith
  have result := contains_of_eqAt (eval_sound hx hy hp)
    (qdata5_eq_canonical hU hjx hjy hrange hvalue ha hpReal)
  exact result




end GeneralCK.Certificates.E8TAxisReparamInterval
end

section
namespace GeneralCK.Certificates.Reflection

























theorem biasE_eq_binEntropy {c : ℝ} (hc : -1 < c) (hc' : c < 1) :
    biasE c = Real.binEntropy ((1-c)/2) := by
  have hm : 0 < 1-c := by linarith
  have hp : 0 < 1+c := by linarith
  rw [Real.binEntropy]
  rw [Real.log_inv, Real.log_inv]
  rw [show 1-(1-c)/2 = (1+c)/2 by ring]
  rw [Real.log_div hm.ne' (by norm_num : (2:ℝ) ≠ 0),
      Real.log_div hp.ne' (by norm_num : (2:ℝ) ≠ 0)]
  unfold biasE
  ring







end GeneralCK.Certificates.Reflection
end

section
namespace GeneralCK.Reflection
open Certificates.Reflection Set Filter
open scoped Topology






theorem biasE_eq_log_mul_E {c : ℝ} (hc : -1 < c) (hc' : c < 1) :
    biasE c = Real.log 2*E c := by
  rw [biasE_eq_binEntropy hc hc']
  unfold E H
  field_simp

















theorem biasB_pos {c : ℝ} (hc : 0 < c) (hc' : c < 1) : 0 < biasB c := by
  have hlog : Real.log (1-c*c) ≤ 0 := Real.log_nonpos (by nlinarith) (by nlinarith)
  unfold biasB
  linarith [log_two_pos]









end GeneralCK.Reflection
end

section
namespace GeneralCK.Correction.Natural
open Certificates.Mixed Certificates.Reflection Reflection

theorem biasE_probability {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    biasE (1-2*v) = hn v := by
  rw [biasE_eq_log_mul_E (by linarith) (by linarith), hn_eq_H_mul_log]
  unfold Reflection.E
  rw [show (1-(1-2*v))/2=v by ring]
  ring

theorem biasB_probability {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    biasB (1-2*v) = kap v := by
  have hp : 0 < v*(1-v) := mul_pos hv (by linarith)
  unfold biasB kap
  rw [show 1-(1-2*v)*(1-2*v)=2^2*(v*(1-v)) by ring,
    Real.log_mul (by norm_num : (2:ℝ)^2 ≠ 0) hp.ne',Real.log_pow]
  ring

theorem A_probability (v : ℝ) :
    2*SmallMean.A (1-2*v) = Real.log 2*J v := by
  unfold SmallMean.A J
  rw [show (1+(1-2*v))/(1-(1-2*v))=(1-v)/v by ring]
  field_simp





theorem Fs_probability (v : ℝ) (hv : 0 < v) (hv' : v < 1) :
    Fs (1-2*v) = Real.log 2*radialSlope v := by
  unfold Fs
  rw [A_probability, biasE_probability hv hv', biasB_probability hv hv']
  unfold radialSlope
  rw [show (1-(1-2*v)^2)/4=v*(1-v) by ring]
  field_simp

theorem Fs_contact {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    Fs (1-2*radialContact z h) = Real.log 2*deriv (fun r => F r h) z := by
  rw [deriv_F_radius_slope hz hh]
  exact Fs_probability _ (radialContact_pos hz hh)
    (lt_trans (radialContact_lt_half hz hh) (by norm_num))




































end GeneralCK.Correction.Natural
end

section
namespace GeneralCK.Reflection
open Certificates.Reflection Set Filter
open scoped Topology

/-- Signed smooth extension of the contact in the regular radius/entropy coordinate.
Unlike `biasContact (1/τ)`, its value at zero is the physical limit zero. -/
noncomputable def regularContact (τ : ℝ) : ℝ :=
  if τ=0 then 0 else if 0<τ then biasContact τ⁻¹ else -biasContact (-τ)⁻¹

@[simp] theorem regularContact_zero : regularContact 0=0 := by simp [regularContact]









theorem biasE_pos_wide {c : ℝ} (hc : -1<c) (hc' : c<1) : 0<biasE c := by
  rw [biasE_eq_binEntropy hc hc']
  exact Real.binEntropy_pos (by linarith) (by linarith)























noncomputable def regularContactFirst (τ : ℝ) : ℝ :=
  (biasE (regularContact τ))^2/biasB (regularContact τ)

noncomputable def regularContactSecond (τ : ℝ) : ℝ :=
  let c := regularContact τ;
  -2*(biasE c)^3*SmallMean.A c/(biasB c)^2 -
    (biasE c)^4*c/((1-c^2)*(biasB c)^3)





@[simp] theorem regularContactFirst_zero : regularContactFirst 0=Real.log 2 := by
  simp only [regularContactFirst,regularContact_zero,biasE,biasB]
  norm_num
  field_simp

@[simp] theorem regularContactSecond_zero : regularContactSecond 0=0 := by
  simp [regularContactSecond,SmallMean.A]





end GeneralCK.Reflection
end

section
namespace GeneralCK.E8AnalyticGerm

open Set Filter Function
open Reflection Certificates.Reflection

noncomputable def thetaParamReal (c : ℝ) : ℝ :=
  (2 / Real.log 2) *
    (SmallMean.A c + c * biasE c / ((1 - c ^ 2) * biasB c))

noncomputable def xParamReal (c : ℝ) : ℝ :=
  Real.log 2 * c / (2 * biasE c)

theorem radialContact_two_mul_xParamReal {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    radialContact (2 * xParamReal c) 1 = (1 - c) / 2 := by
  have hE : 0 < biasE c := biasE_pos_wide (by linarith) hc1
  have hk : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hH : 0 < H ((1 - c) / 2) := H_pos (by linarith) (by linarith)
  have hz : 0 < 2 * xParamReal c := by
    unfold xParamReal
    positivity
  apply radialContact_eq_of_equation hz (by norm_num)
  · linarith
  · linarith
  have hp := Correction.Natural.biasE_probability
    (v := (1 - c) / 2) (by linarith) (by linarith)
  rw [show 1 - 2 * ((1 - c) / 2) = c by ring] at hp
  unfold xParamReal
  rw [hp, Certificates.Mixed.hn_eq_H_mul_log]
  field_simp [hE.ne', hH.ne']
  ring

/-- Exact stable parametrization of the manuscript slope on `0 < c < 1`. -/
theorem e8Theta_xParamReal {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    e8Theta (xParamReal c) = thetaParamReal c := by
  have hx : 0 < xParamReal c := by
    unfold xParamReal
    have hE : 0 < biasE c := biasE_pos_wide (by linarith) hc1
    have hk : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hFs := Correction.Natural.Fs_contact
    (z := 2 * xParamReal c) (h := 1) (by positivity) (by norm_num)
  rw [radialContact_two_mul_xParamReal hc hc1,
    show 1 - 2 * ((1 - c) / 2) = c by ring] at hFs
  have hk : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hB : biasB c ≠ 0 := (biasB_pos hc hc1).ne'
  have hcden : 1 - c ^ 2 ≠ 0 := by nlinarith
  calc
    e8Theta (xParamReal c) = Correction.Natural.Fs c / Real.log 2 := by
      unfold e8Theta
      rw [hFs]
      field_simp [hk]
    _ = thetaParamReal c := by
      unfold Correction.Natural.Fs thetaParamReal
      field_simp [hk, hB, hcden]
      ring

/-- Therefore the global positive inverse recovers the stable contact coordinate. -/
theorem e8Q_thetaParamReal {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    e8Q (thetaParamReal c) = xParamReal c := by
  rw [← e8Theta_xParamReal hc hc1]
  exact e8Q_e8Theta (by
    unfold xParamReal
    have hE : 0 < biasE c := biasE_pos_wide (by linarith) hc1
    have hk : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity)









end GeneralCK.E8AnalyticGerm
end

section
namespace GeneralCK.Certificates.E8TAxisStableScalar

open GeneralCK.Reflection GeneralCK.Certificates.Reflection
open GeneralCK.E8AnalyticGerm







noncomputable def X (a : ℝ) : ℝ := Real.log 2 * r a / (2 * h a)


theorem z_pos (a : ℝ) : 0 < z a := Real.exp_pos _

theorem one_add_z_pos (a : ℝ) : 0 < 1 + z a := by
  linarith [z_pos a]

theorem z_lt_one {a : ℝ} (ha : 0 < a) : z a < 1 := by
  exact Real.exp_lt_one_iff.mpr (by linarith)

theorem r_pos {a : ℝ} (ha : 0 < a) : 0 < r a := by
  exact div_pos (sub_pos.mpr (z_lt_one ha)) (one_add_z_pos a)

theorem r_lt_one (a : ℝ) : r a < 1 := by
  change (1 - z a) / (1 + z a) < 1
  apply (div_lt_one (one_add_z_pos a)).mpr
  linarith [z_pos a]

theorem one_add_r (a : ℝ) : 1 + r a = 2 / (1 + z a) := by
  unfold r
  field_simp [(one_add_z_pos a).ne'] <;> ring

theorem one_sub_r (a : ℝ) : 1 - r a = 2 * z a / (1 + z a) := by
  unfold r
  field_simp [(one_add_z_pos a).ne'] <;> ring

theorem one_add_r_pos (a : ℝ) : 0 < 1 + r a := by
  rw [one_add_r]
  exact div_pos (by norm_num) (one_add_z_pos a)

theorem one_sub_r_pos (a : ℝ) : 0 < 1 - r a := by
  linarith [r_lt_one a]

theorem q_pos (a : ℝ) : 0 < q a := by
  unfold q
  exact div_pos (mul_pos (by norm_num) (z_pos a)) (pow_pos (one_add_z_pos a) 2)

theorem one_sub_r_sq (a : ℝ) : 1 - r a ^ 2 = q a := by
  unfold r q
  field_simp [(one_add_z_pos a).ne'] <;> ring

theorem log_one_add_r (a : ℝ) :
    Real.log (1 + r a) = Real.log 2 - l1 a := by
  rw [one_add_r]
  exact Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (one_add_z_pos a).ne'

theorem log_one_sub_r (a : ℝ) :
    Real.log (1 - r a) = Real.log 2 - 2 * a - l1 a := by
  rw [one_sub_r, Real.log_div (mul_ne_zero (by norm_num) (z_pos a).ne')
      (one_add_z_pos a).ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (z_pos a).ne']
  simp only [z, Real.log_exp, l1]
  ring

theorem A_r (a : ℝ) : SmallMean.A (r a) = a := by
  unfold SmallMean.A
  rw [Real.log_div (one_add_r_pos a).ne' (one_sub_r_pos a).ne',
    log_one_add_r, log_one_sub_r]
  ring

theorem biasB_r (a : ℝ) : biasB (r a) = ell a := by
  unfold biasB
  rw [show 1 - r a * r a = (1 + r a) * (1 - r a) by ring,
    Real.log_mul (one_add_r_pos a).ne' (one_sub_r_pos a).ne',
    log_one_add_r, log_one_sub_r]
  unfold ell
  ring

theorem biasE_r (a : ℝ) : biasE (r a) = h a := by
  unfold biasE
  rw [log_one_add_r, log_one_sub_r, one_add_r, one_sub_r]
  unfold h
  field_simp [(one_add_z_pos a).ne'] <;> ring

theorem ell_pos {a : ℝ} (ha : 0 < a) : 0 < ell a := by
  rw [← biasB_r]
  exact biasB_pos (r_pos ha) (r_lt_one a)

theorem h_pos {a : ℝ} (ha : 0 < a) : 0 < h a := by
  rw [← biasE_r]
  exact biasE_pos_wide (by linarith [r_pos ha]) (r_lt_one a)

theorem X_eq_xParamReal (a : ℝ) : X a = xParamReal (r a) := by
  unfold X xParamReal
  rw [biasE_r]

theorem Y_eq_thetaParamReal (a : ℝ) : Y a = thetaParamReal (r a) := by
  unfold Y thetaParamReal
  rw [A_r, biasE_r, one_sub_r_sq, biasB_r]

theorem X_pos {a : ℝ} (ha : 0 < a) : 0 < X a := by
  unfold X
  exact div_pos (mul_pos (Real.log_pos (by norm_num)) (r_pos ha))
    (mul_pos (by norm_num) (h_pos ha))



theorem e8Theta_X {a : ℝ} (ha : 0 < a) : e8Theta (X a) = Y a := by
  rw [X_eq_xParamReal, Y_eq_thetaParamReal]
  exact e8Theta_xParamReal (r_pos ha) (r_lt_one a)

theorem e8Q_Y {a : ℝ} (ha : 0 < a) : e8Q (Y a) = X a := by
  rw [X_eq_xParamReal, Y_eq_thetaParamReal]
  exact e8Q_thetaParamReal (r_pos ha) (r_lt_one a)

end GeneralCK.Certificates.E8TAxisStableScalar
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

@[simp] theorem xJet_d0 (a : ℝ) : xJet.d0 a = E8TAxisStableScalar.X a := by
  simp [xJet, Jet5.mul, Jet5.const, Jet5.inv, E8TAxisStableScalar.X, div_eq_mul_inv]

@[simp] theorem yJet_d0 (a : ℝ) : yJet.d0 a = E8TAxisStableScalar.Y a := by
  simp [yJet, Jet5.mul, Jet5.add, Jet5.const, Jet5.inv, Jet5.variableJet,
    E8TAxisStableScalar.Y, div_eq_mul_inv]

theorem zJet_soundAt (a : ℝ) : zJet.SoundAt a := Jet5.soundAt_expAffine 0 (-2) a

theorem onePlusZJet_soundAt (a : ℝ) : onePlusZJet.SoundAt a :=
  (Jet5.soundAt_const 1 a).add (zJet_soundAt a)

theorem rJet_soundAt (a : ℝ) : rJet.SoundAt a := by
  unfold rJet
  exact ((Jet5.soundAt_const 1 a).add (zJet_soundAt a).neg).mul
    ((onePlusZJet_soundAt a).inv (by
      rw [onePlusZJet_d0]
      exact (E8TAxisStableScalar.one_add_z_pos a).ne'))

theorem qJet_soundAt (a : ℝ) : qJet.SoundAt a := by
  unfold qJet
  exact ((Jet5.soundAt_const 4 a).mul (zJet_soundAt a)).mul
    (((onePlusZJet_soundAt a).mul (onePlusZJet_soundAt a)).inv (by
      change onePlusZJet.d0 a * onePlusZJet.d0 a ≠ 0
      rw [onePlusZJet_d0]
      exact mul_ne_zero (E8TAxisStableScalar.one_add_z_pos a).ne' (E8TAxisStableScalar.one_add_z_pos a).ne'))

theorem l1Jet_soundAt (a : ℝ) : l1Jet.SoundAt a := by
  exact (onePlusZJet_soundAt a).log (by
    rw [onePlusZJet_d0]
    exact (E8TAxisStableScalar.one_add_z_pos a).ne')

theorem ellJet_soundAt (a : ℝ) : ellJet.SoundAt a :=
  (Jet5.soundAt_variable a).add (l1Jet_soundAt a)

theorem hJet_soundAt (a : ℝ) : hJet.SoundAt a := by
  unfold hJet
  exact (l1Jet_soundAt a).add
    ((((Jet5.soundAt_const 2 a).mul (Jet5.soundAt_variable a)).mul
      (zJet_soundAt a)).mul ((onePlusZJet_soundAt a).inv (by
        rw [onePlusZJet_d0]
        exact (E8TAxisStableScalar.one_add_z_pos a).ne')))

theorem log2Jet_soundAt (a : ℝ) : log2Jet.SoundAt a :=
  Jet5.soundAt_const (Real.log 2) a

theorem xJet_soundAt {a : ℝ} (ha : 0 < a) : xJet.SoundAt a := by
  unfold xJet
  exact ((log2Jet_soundAt a).mul (rJet_soundAt a)).mul
    (((Jet5.soundAt_const 2 a).mul (hJet_soundAt a)).inv (by
      change (2 : ℝ) * hJet.d0 a ≠ 0
      rw [hJet_d0]
      exact mul_ne_zero (by norm_num) (E8TAxisStableScalar.h_pos ha).ne'))

theorem yJet_soundAt {a : ℝ} (ha : 0 < a) : yJet.SoundAt a := by
  unfold yJet
  exact ((Jet5.soundAt_const 2 a).mul ((log2Jet_soundAt a).inv (by
      rw [log2Jet_d0]
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'))).mul
    ((Jet5.soundAt_variable a).add
      (((rJet_soundAt a).mul (hJet_soundAt a)).mul
        (((qJet_soundAt a).mul (ellJet_soundAt a)).inv (by
          change qJet.d0 a * ellJet.d0 a ≠ 0
          rw [qJet_d0, ellJet_d0]
          exact mul_ne_zero (E8TAxisStableScalar.q_pos a).ne' (E8TAxisStableScalar.ell_pos ha).ne'))))

theorem xJet_soundOn : xJet.SoundOn (Ioi 0) := fun _ ha => xJet_soundAt ha

theorem yJet_soundOn : yJet.SoundOn (Ioi 0) := fun _ ha => yJet_soundAt ha

theorem Y_mem_e8SlopeRange {a : ℝ} (ha : 0 < a) : E8TAxisStableScalar.Y a ∈ e8SlopeRange :=
  ⟨E8TAxisStableScalar.X a, E8TAxisStableScalar.X_pos ha, E8TAxisStableScalar.e8Theta_X ha⟩







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

/-- Stable interval evaluation encloses the concrete inverse derivatives for
every positive parameter in the supplied alpha box. -/
theorem stable_contains_canonical {p : ℕ} {i : Inputs p} {a : ℝ}
    (ha : i.alpha.Contains a) (hapos : 0 < a)
    (he : i.expNegTwo.Contains (Real.exp (-2 * a)))
    (hl : i.logOnePlusExp.Contains (Real.log (1 + Real.exp (-2 * a))))
    (hL : i.logTwo.Contains (Real.log 2)) (hp : DenominatorsPositive i)
    (hyp : 0 < (yBox i).d1.lo) :
    (eval (xBox i) (yBox i)).Contains
      (E8InverseJet5Bridge.e8QJet5 E8InverseJet5Bridge.e8ThetaCanonicalJet5)
      (E8TAxisStableScalar.Y a) := by
  have hxy := xyBox_sound ha he hl hL hp
  have result := eval_contains_canonical isOpen_Ioi xJet_soundOn yJet_soundOn
    (fun b hb => by simpa using Y_mem_e8SlopeRange hb)
    (fun b hb => by simpa using (E8TAxisStableScalar.e8Q_Y hb).symm)
    hapos hxy.1 hxy.2 hyp
  simpa only [yJet_d0] using result





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

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.E8TAxisStableInterval
open DyadicInterval E8TAxisStableJet5 E8TAxisReparamInterval
theorem solution {p : ℕ} {i : Inputs p}
    {we : ExpWitness p} {wl wL : FastLogBoxWitness}
    (he : expBoxCheck ((ofInt p (-2)).mul i.alpha) i.expNegTwo we = true)
    (hl : logBoxCheck ((ofInt p 1).add i.expNegTwo) i.logOnePlusExp wl = true)
    (hL : logBoxCheck (ofInt p 2) i.logTwo wL = true)
    (hp : DenominatorsPositive i) (hyp : 0 < (yBox i).d1.lo)
    {a : ℝ} (ha : i.alpha.Contains a) (hapos : 0 < a) :
    (eval (xBox i) (yBox i)).Contains
      (E8InverseJet5Bridge.e8QJet5 E8InverseJet5Bridge.e8ThetaCanonicalJet5)
      (E8TAxisStableScalar.Y a) := by
  have hz : i.expNegTwo.Contains (Real.exp (-2 * a)) := by
    simpa using expBoxCheck_sound he (mul_sound (ofInt_sound p (-2)) ha)
  have hc1 : (ofInt p 1).Contains (1 : ℝ) := by simpa using ofInt_sound p 1
  have hc2 : (ofInt p 2).Contains (2 : ℝ) := by simpa using ofInt_sound p 2
  exact stable_contains_canonical ha hapos hz
    (logBoxCheck_sound hl (add_sound hc1 hz))
    (logBoxCheck_sound hL hc2) hp hyp
