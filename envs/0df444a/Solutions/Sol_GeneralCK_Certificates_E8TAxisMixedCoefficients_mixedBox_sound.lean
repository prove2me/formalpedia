-- Prove2me | solution 1 for GeneralCK.Certificates.E8TAxisMixedCoefficients.mixedBox_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:15:31.17136+00:00
-- url     : https://prove2.me/submissions/840005e8-2355-4b5d-865f-2ffb892de95a

import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_mixed_polynomial_interface
import Definitions.Def_GeneralCK_E8_semantic_core
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

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


















end DyadicInterval
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates.E8TAxisMixedCoefficients

open DyadicInterval
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000









end GeneralCK.Certificates.E8TAxisMixedCoefficients
end

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.E8TAxisMixedCoefficients
open DyadicInterval
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
theorem solution {p : ℕ} {a b c d : DyadicJet5Enclosure p}
    {q : Jet5} {s t : ℝ}
    (ha : a.Contains q t) (hb : b.Contains q (2 * s + t))
    (hc : c.Contains q (s + t)) (hd : d.Contains q s) (i j : ℕ) :
    (mixedBox a b c d i j).Contains (mixed q s t i j) := by
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4, ha5⟩
  rcases hb with ⟨hb0, hb1, hb2, hb3, hb4, hb5⟩
  rcases hc with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
  rcases i with _ | _ | _ | _ | _ | i <;>
    rcases j with _ | _ | _ | _ | _ | _ | j
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · exact add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (neg_sound (mul_sound (mul_sound (ofInt_sound p 2) ha0) hb1)) (mul_sound ha0 hc1)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 2) ha1) hb0))) (mul_sound ha1 hc0)) (mul_sound ha1 hd0)) (mul_sound hb0 hc1)) (mul_sound hb1 hc0)) (neg_sound (mul_sound hb1 hd0))
  · exact add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (neg_sound (mul_sound (mul_sound (ofInt_sound p 2) ha0) hb2)) (mul_sound ha0 hc2)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 4) ha1) hb1))) (mul_sound (mul_sound (ofInt_sound p 2) ha1) hc1)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 2) ha2) hb0))) (mul_sound ha2 hc0)) (mul_sound ha2 hd0)) (mul_sound hb0 hc2)) (mul_sound (mul_sound (ofInt_sound p 2) hb1) hc1)) (mul_sound hb2 hc0)) (neg_sound (mul_sound hb2 hd0))
  · exact add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (neg_sound (mul_sound (mul_sound (ofInt_sound p 2) ha0) hb3)) (mul_sound ha0 hc3)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 6) ha1) hb2))) (mul_sound (mul_sound (ofInt_sound p 3) ha1) hc2)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 6) ha2) hb1))) (mul_sound (mul_sound (ofInt_sound p 3) ha2) hc1)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 2) ha3) hb0))) (mul_sound ha3 hc0)) (mul_sound ha3 hd0)) (mul_sound hb0 hc3)) (mul_sound (mul_sound (ofInt_sound p 3) hb1) hc2)) (mul_sound (mul_sound (ofInt_sound p 3) hb2) hc1)) (mul_sound hb3 hc0)) (neg_sound (mul_sound hb3 hd0))
  · exact add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (neg_sound (mul_sound (mul_sound (ofInt_sound p 2) ha0) hb4)) (mul_sound ha0 hc4)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 8) ha1) hb3))) (mul_sound (mul_sound (ofInt_sound p 4) ha1) hc3)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 12) ha2) hb2))) (mul_sound (mul_sound (ofInt_sound p 6) ha2) hc2)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 8) ha3) hb1))) (mul_sound (mul_sound (ofInt_sound p 4) ha3) hc1)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 2) ha4) hb0))) (mul_sound ha4 hc0)) (mul_sound ha4 hd0)) (mul_sound hb0 hc4)) (mul_sound (mul_sound (ofInt_sound p 4) hb1) hc3)) (mul_sound (mul_sound (ofInt_sound p 6) hb2) hc2)) (mul_sound (mul_sound (ofInt_sound p 4) hb3) hc1)) (mul_sound hb4 hc0)) (neg_sound (mul_sound hb4 hd0))
  · exact add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (neg_sound (mul_sound (mul_sound (ofInt_sound p 2) ha0) hb5)) (mul_sound ha0 hc5)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 10) ha1) hb4))) (mul_sound (mul_sound (ofInt_sound p 5) ha1) hc4)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 20) ha2) hb3))) (mul_sound (mul_sound (ofInt_sound p 10) ha2) hc3)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 20) ha3) hb2))) (mul_sound (mul_sound (ofInt_sound p 10) ha3) hc2)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 10) ha4) hb1))) (mul_sound (mul_sound (ofInt_sound p 5) ha4) hc1)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 2) ha5) hb0))) (mul_sound ha5 hc0)) (mul_sound ha5 hd0)) (mul_sound hb0 hc5)) (mul_sound (mul_sound (ofInt_sound p 5) hb1) hc4)) (mul_sound (mul_sound (ofInt_sound p 10) hb2) hc3)) (mul_sound (mul_sound (ofInt_sound p 10) hb3) hc2)) (mul_sound (mul_sound (ofInt_sound p 5) hb4) hc1)) (mul_sound hb5 hc0)) (neg_sound (mul_sound hb5 hd0))
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · exact add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (neg_sound (mul_sound (mul_sound (ofInt_sound p 4) ha0) hb2)) (mul_sound ha0 hc2)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 4) ha1) hb1))) (mul_sound ha1 hc1)) (mul_sound ha1 hd1)) (mul_sound hb0 hc2)) (mul_sound (mul_sound (ofInt_sound p 3) hb1) hc1)) (neg_sound (mul_sound hb1 hd1))) (mul_sound (mul_sound (ofInt_sound p 2) hb2) hc0)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 2) hb2) hd0))
  · exact add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (neg_sound (mul_sound (mul_sound (ofInt_sound p 4) ha0) hb3)) (mul_sound ha0 hc3)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 8) ha1) hb2))) (mul_sound (mul_sound (ofInt_sound p 2) ha1) hc2)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 4) ha2) hb1))) (mul_sound ha2 hc1)) (mul_sound ha2 hd1)) (mul_sound hb0 hc3)) (mul_sound (mul_sound (ofInt_sound p 4) hb1) hc2)) (mul_sound (mul_sound (ofInt_sound p 5) hb2) hc1)) (neg_sound (mul_sound hb2 hd1))) (mul_sound (mul_sound (ofInt_sound p 2) hb3) hc0)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 2) hb3) hd0))
  · exact add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (neg_sound (mul_sound (mul_sound (ofInt_sound p 4) ha0) hb4)) (mul_sound ha0 hc4)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 12) ha1) hb3))) (mul_sound (mul_sound (ofInt_sound p 3) ha1) hc3)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 12) ha2) hb2))) (mul_sound (mul_sound (ofInt_sound p 3) ha2) hc2)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 4) ha3) hb1))) (mul_sound ha3 hc1)) (mul_sound ha3 hd1)) (mul_sound hb0 hc4)) (mul_sound (mul_sound (ofInt_sound p 5) hb1) hc3)) (mul_sound (mul_sound (ofInt_sound p 9) hb2) hc2)) (mul_sound (mul_sound (ofInt_sound p 7) hb3) hc1)) (neg_sound (mul_sound hb3 hd1))) (mul_sound (mul_sound (ofInt_sound p 2) hb4) hc0)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 2) hb4) hd0))
  · exact add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (neg_sound (mul_sound (mul_sound (ofInt_sound p 4) ha0) hb5)) (mul_sound ha0 hc5)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 16) ha1) hb4))) (mul_sound (mul_sound (ofInt_sound p 4) ha1) hc4)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 24) ha2) hb3))) (mul_sound (mul_sound (ofInt_sound p 6) ha2) hc3)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 16) ha3) hb2))) (mul_sound (mul_sound (ofInt_sound p 4) ha3) hc2)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 4) ha4) hb1))) (mul_sound ha4 hc1)) (mul_sound ha4 hd1)) (mul_sound hb0 hc5)) (mul_sound (mul_sound (ofInt_sound p 6) hb1) hc4)) (mul_sound (mul_sound (ofInt_sound p 14) hb2) hc3)) (mul_sound (mul_sound (ofInt_sound p 16) hb3) hc2)) (mul_sound (mul_sound (ofInt_sound p 9) hb4) hc1)) (neg_sound (mul_sound hb4 hd1))) (mul_sound (mul_sound (ofInt_sound p 2) hb5) hc0)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 2) hb5) hd0))
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · exact add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (neg_sound (mul_sound (mul_sound (ofInt_sound p 8) ha0) hb3)) (mul_sound ha0 hc3)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 8) ha1) hb2))) (mul_sound ha1 hc2)) (mul_sound ha1 hd2)) (mul_sound hb0 hc3)) (mul_sound (mul_sound (ofInt_sound p 5) hb1) hc2)) (neg_sound (mul_sound hb1 hd2))) (mul_sound (mul_sound (ofInt_sound p 8) hb2) hc1)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 4) hb2) hd1))) (mul_sound (mul_sound (ofInt_sound p 4) hb3) hc0)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 4) hb3) hd0))
  · exact add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (neg_sound (mul_sound (mul_sound (ofInt_sound p 8) ha0) hb4)) (mul_sound ha0 hc4)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 16) ha1) hb3))) (mul_sound (mul_sound (ofInt_sound p 2) ha1) hc3)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 8) ha2) hb2))) (mul_sound ha2 hc2)) (mul_sound ha2 hd2)) (mul_sound hb0 hc4)) (mul_sound (mul_sound (ofInt_sound p 6) hb1) hc3)) (mul_sound (mul_sound (ofInt_sound p 13) hb2) hc2)) (neg_sound (mul_sound hb2 hd2))) (mul_sound (mul_sound (ofInt_sound p 12) hb3) hc1)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 4) hb3) hd1))) (mul_sound (mul_sound (ofInt_sound p 4) hb4) hc0)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 4) hb4) hd0))
  · exact add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (neg_sound (mul_sound (mul_sound (ofInt_sound p 8) ha0) hb5)) (mul_sound ha0 hc5)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 24) ha1) hb4))) (mul_sound (mul_sound (ofInt_sound p 3) ha1) hc4)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 24) ha2) hb3))) (mul_sound (mul_sound (ofInt_sound p 3) ha2) hc3)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 8) ha3) hb2))) (mul_sound ha3 hc2)) (mul_sound ha3 hd2)) (mul_sound hb0 hc5)) (mul_sound (mul_sound (ofInt_sound p 7) hb1) hc4)) (mul_sound (mul_sound (ofInt_sound p 19) hb2) hc3)) (mul_sound (mul_sound (ofInt_sound p 25) hb3) hc2)) (neg_sound (mul_sound hb3 hd2))) (mul_sound (mul_sound (ofInt_sound p 16) hb4) hc1)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 4) hb4) hd1))) (mul_sound (mul_sound (ofInt_sound p 4) hb5) hc0)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 4) hb5) hd0))
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · exact add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (neg_sound (mul_sound (mul_sound (ofInt_sound p 16) ha0) hb4)) (mul_sound ha0 hc4)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 16) ha1) hb3))) (mul_sound ha1 hc3)) (mul_sound ha1 hd3)) (mul_sound hb0 hc4)) (mul_sound (mul_sound (ofInt_sound p 7) hb1) hc3)) (neg_sound (mul_sound hb1 hd3))) (mul_sound (mul_sound (ofInt_sound p 18) hb2) hc2)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 6) hb2) hd2))) (mul_sound (mul_sound (ofInt_sound p 20) hb3) hc1)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 12) hb3) hd1))) (mul_sound (mul_sound (ofInt_sound p 8) hb4) hc0)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 8) hb4) hd0))
  · exact add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (neg_sound (mul_sound (mul_sound (ofInt_sound p 16) ha0) hb5)) (mul_sound ha0 hc5)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 32) ha1) hb4))) (mul_sound (mul_sound (ofInt_sound p 2) ha1) hc4)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 16) ha2) hb3))) (mul_sound ha2 hc3)) (mul_sound ha2 hd3)) (mul_sound hb0 hc5)) (mul_sound (mul_sound (ofInt_sound p 8) hb1) hc4)) (mul_sound (mul_sound (ofInt_sound p 25) hb2) hc3)) (neg_sound (mul_sound hb2 hd3))) (mul_sound (mul_sound (ofInt_sound p 38) hb3) hc2)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 6) hb3) hd2))) (mul_sound (mul_sound (ofInt_sound p 28) hb4) hc1)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 12) hb4) hd1))) (mul_sound (mul_sound (ofInt_sound p 8) hb5) hc0)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 8) hb5) hd0))
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · exact add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (neg_sound (mul_sound (mul_sound (ofInt_sound p 32) ha0) hb5)) (mul_sound ha0 hc5)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 32) ha1) hb4))) (mul_sound ha1 hc4)) (mul_sound ha1 hd4)) (mul_sound hb0 hc5)) (mul_sound (mul_sound (ofInt_sound p 9) hb1) hc4)) (neg_sound (mul_sound hb1 hd4))) (mul_sound (mul_sound (ofInt_sound p 32) hb2) hc3)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 8) hb2) hd3))) (mul_sound (mul_sound (ofInt_sound p 56) hb3) hc2)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 24) hb3) hd2))) (mul_sound (mul_sound (ofInt_sound p 48) hb4) hc1)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 32) hb4) hd1))) (mul_sound (mul_sound (ofInt_sound p 16) hb5) hc0)) (neg_sound (mul_sound (mul_sound (ofInt_sound p 16) hb5) hd0))
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
  · simpa only [mixedBox, mixed, Int.cast_zero] using ofInt_sound p 0
