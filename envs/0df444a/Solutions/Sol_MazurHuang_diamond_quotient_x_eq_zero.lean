-- Prove2me | solution 1 for MazurHuang.diamond_quotient_x_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-07T17:45:30.83844+00:00
-- url     : https://prove2.me/submissions/a0d698d5-59b4-4318-afa3-a80f815afc59

import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_MazurHuang_x19_good_quotient_three_isogeny_preimage

set_option maxHeartbeats 1000000

-- ===== scratch.KeystoneEDS =====
section
/-! Replacement for the Keystone EDS export: the multiplication-by-`n` criterion
`n • P = 0 ↔ ΨSqₙ(x) = 0`, derived from the platform theorem
`WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff`. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace KeystoneLadder

theorem evalEval_ψ_sq {k : Type*} [Field k] (W : WeierstrassCurve k) {x y : k}
    (h : W.toAffine.Equation x y) (n : ℤ) :
    ((W.ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x := by
  have hmk : CoordinateRing.mk W.toAffine (W.ψ n ^ 2) =
      CoordinateRing.mk W.toAffine (C (W.ΨSq n)) := by
    rw [map_pow, CoordinateRing.mk_ψ, CoordinateRing.mk_Ψ_sq]
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_eq_mk.mp hmk
  have he : (W.ψ n ^ 2 - C (W.ΨSq n)).evalEval x y = 0 := by
    rw [hq, evalEval_mul, h, zero_mul]
  rw [evalEval_sub, evalEval_pow, evalEval_C, sub_eq_zero] at he
  exact he

theorem nsmul_eq_zero_iff_ΨSq_eval {k : Type*} [Field k] [DecidableEq k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (_h4 : (4 : k) ≠ 0) (_hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (_hc3 : W.Ψ₃ ≠ 0)
    {n : ℕ} {x y : k} (h : (W⁄k).Nonsingular x y) :
    n • (Point.some x y h : (W⁄k).Point) = 0 ↔ (W.ΨSq (n : ℤ)).eval x = 0 := by
  have key := WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff W h (n : ℤ)
  rw [← evalEval_ψ_sq W h.1 (n : ℤ), pow_eq_zero_iff two_ne_zero, ← key, natCast_zsmul]
  rfl

end KeystoneLadder

end

-- ===== FLT.Assumptions.MazurProof.N19SutherlandModels =====
section
/-!
# Explicit affine models for the order-nineteen Tate equation

This file records Sutherland's raw and optimized affine models of `X₁(19)`.
It also gives the direct algebraic quotient of the optimized model by the
order-three diamond action:

`V² + V = U³ + U² + U`.

All maps are verified by polynomial identities.  No modular interpretation
of the formulas is used below.
-/

namespace MazurProof.N19SutherlandModels

noncomputable section

/-! ## The raw and optimized equations -/

/-! ## The raw-to-optimized chart -/

/-! ## The order-three quotient of the optimized model -/

/-- Residual of the elliptic equation `V²+V=U³+U²+U`. -/
def diamondResidual (u v : ℚ) : ℚ :=
  v ^ 2 + v - u ^ 3 - u ^ 2 - u

/-! ## The zero horizontal fibre -/

end

end MazurProof.N19SutherlandModels

end

-- ===== FLT.Assumptions.MazurProof.RationalPointsX135Descent =====
section
namespace MazurProof.RationalPointsX135

noncomputable section

open scoped NumberField

open UniqueFactorizationMonoid

private theorem nat_isSquare_of_isSquare_cube {n : ℕ} (hn : n ≠ 0)
    (h : IsSquare (n ^ 3)) : IsSquare n := by
  rcases h with ⟨c, hc⟩
  have hdvd : n ^ 2 ∣ c ^ 2 := ⟨n, by rw [sq c, ← hc]; ring⟩
  have hndvdc : n ∣ c := by
    rwa [Nat.dvd_pow_iff_ceilRoot_dvd two_ne_zero,
      Nat.ceilRoot_pow_self two_ne_zero] at hdvd
  obtain ⟨d, rfl⟩ := hndvdc
  exact ⟨d, mul_left_cancel₀ (pow_ne_zero 2 hn)
    (show n ^ 2 * n = n ^ 2 * (d * d) by
      calc
        n ^ 2 * n = n ^ 3 := by ring
        _ = n * d * (n * d) := hc
        _ = n ^ 2 * (d * d) := by ring)⟩

private theorem den_monic_cubic_const (a b c : ℤ) (x : ℚ) :
    ((x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c).den : ℤ) =
      (x.den : ℤ) ^ 3 := by
  set A : ℤ := x.num
  set D : ℤ := (x.den : ℤ)
  have hDpos : (0 : ℤ) < D := by positivity
  have hDne : (D : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hDpos)
  have hred : IsCoprime A D := by
    rw [Int.isCoprime_iff_nat_coprime]
    simp only [A, D, Int.natAbs_natCast]
    exact x.reduced
  set N : ℤ := A ^ 3 + a * A ^ 2 * D + b * A * D ^ 2 + c * D ^ 3
  have hND : IsCoprime N D := by
    have h1 : IsCoprime (A ^ 3) D := hred.pow_left
    have h2 : IsCoprime
        (A ^ 3 + D * (a * A ^ 2 + b * A * D + c * D ^ 2)) D :=
      h1.add_mul_left_left _
    convert h2 using 1 <;> ring
  have hND3 : IsCoprime N (D ^ 3) := hND.pow_right
  have hND3nat : Nat.Coprime N.natAbs (D ^ 3).natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hND3
  have hrepr : x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c =
      (N : ℚ) / (D ^ 3 : ℚ) := by
    have hx : x = (A : ℚ) / (D : ℚ) := by
      simp only [A, D]
      push_cast
      exact (Rat.num_div_den x).symm
    rw [hx]
    field_simp [hDne]
    push_cast [N]
    ring
  rw [hrepr]
  exact_mod_cast Rat.den_div_eq_of_coprime (by positivity) hND3nat

private theorem rat_denom_square_monic_const (a b c : ℤ) (x y : ℚ)
    (h : y ^ 2 = x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c) :
    ∃ A B : ℤ, 0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 := by
  have hsq : IsSquare
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c) :=
    ⟨y, by rw [← h]; ring⟩
  have hdenSq : IsSquare
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c).den :=
    (Rat.isSquare_iff.mp hsq).2
  have hdenEq :
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c).den = x.den ^ 3 := by
    exact_mod_cast den_monic_cubic_const a b c x
  have hden3Sq : IsSquare (x.den ^ 3) := hdenEq ▸ hdenSq
  have hdenSq' : IsSquare x.den :=
    nat_isSquare_of_isSquare_cube x.den_ne_zero hden3Sq
  obtain ⟨B0, hB0⟩ := hdenSq'
  have hB0pos : 0 < B0 := by
    rcases Nat.eq_zero_or_pos B0 with hzero | hpos
    · simp [hzero] at hB0
    · exact hpos
  refine ⟨x.num, (B0 : ℤ), by exact_mod_cast hB0pos, ?_, ?_⟩
  · have hBdvd : B0 ∣ x.den := ⟨B0, hB0⟩
    have := x.reduced.coprime_dvd_right hBdvd
    simpa [Int.gcd, Int.natAbs_natCast] using this
  · calc
      x = (x.num : ℚ) / (x.den : ℚ) := by
        simpa using (Rat.num_div_den x).symm
      _ = (x.num : ℚ) / ((B0 : ℚ) ^ 2) := by
        rw [hB0]
        push_cast
        ring

theorem integral_model_monic_const (a b c : ℤ) (x y : ℚ)
    (h : y ^ 2 = x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 ∧
      y = (C : ℚ) / (B : ℚ) ^ 3 ∧
      C ^ 2 = A ^ 3 + a * A ^ 2 * B ^ 2 + b * A * B ^ 4 + c * B ^ 6 := by
  obtain ⟨A, B, hBpos, hcop, hx⟩ := rat_denom_square_monic_const a b c x y h
  have hBne : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hBpos)
  set N : ℤ := A ^ 3 + a * A ^ 2 * B ^ 2 + b * A * B ^ 4 + c * B ^ 6
  have hrat : (y * (B : ℚ) ^ 3) ^ 2 = (N : ℚ) := by
    rw [hx] at h
    push_cast [N] at h ⊢
    field_simp [hBne] at h ⊢
    nlinarith
  have hNsq : IsSquare (N : ℚ) :=
    ⟨y * (B : ℚ) ^ 3, by rw [← sq]; exact hrat.symm⟩
  rw [Rat.isSquare_intCast_iff] at hNsq
  obtain ⟨C, hC⟩ := hNsq
  have hsquares : (y * (B : ℚ) ^ 3) ^ 2 = (C : ℚ) ^ 2 := by
    rw [hrat]
    exact_mod_cast (show N = C ^ 2 by simpa [pow_two] using hC)
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsquares with heq | heq
  · refine ⟨A, B, C, hBpos, hcop, hx, ?_, ?_⟩
    · apply (eq_div_iff (pow_ne_zero 3 hBne)).2
      simpa using heq
    · simpa [N, pow_two] using hC.symm
  · refine ⟨A, B, -C, hBpos, hcop, hx, ?_, ?_⟩
    · apply (eq_div_iff (pow_ne_zero 3 hBne)).2
      simpa using heq
    · simpa [N, pow_two] using hC.symm

/-! Experimental use of Mathlib's cyclotomic PID and Dirichlet-unit APIs. -/
end

end MazurProof.RationalPointsX135

end

-- ===== FLT.Assumptions.MazurProof.TateOriginDivision =====
section
/-!
# Generic odd-order division condition at the Tate origin

This file factors out the kernel-checked division-polynomial argument shared by
the order-11 and order-18 developments.  If the marked origin on a Tate normal
form has odd additive order `n`, then `preΨ'_n(0) = 0`.  Conversely, a proper
odd multiple below the exact order has nonzero evaluation.

The final theorem combines this with `TateNormalFormBridge`: every rational
point of odd order greater than three produces nonsingular Tate parameters
with a nonzero `b` parameter and the corresponding raw division condition.
No explicit factorization of `preΨ'_n(0)` is asserted here.
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOriginDivision



noncomputable section

theorem psi_ne_zero_rat (W : WeierstrassCurve ℚ) :
    ∀ m : ℤ, m ≠ 0 → W.ψ m ≠ 0 := by
  have hψ₂_ne : W.ψ₂ ≠ 0 := by
    rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
    exact ne_of_apply_ne Polynomial.natDegree (by
      rw [Polynomial.natDegree_linear
        (Polynomial.C_ne_zero.mpr (two_ne_zero (α := ℚ))),
        Polynomial.natDegree_zero]
      omega)
  have hψ₂_deg : W.ψ₂.natDegree ≤ 1 := by
    rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
    exact Polynomial.natDegree_linear_le
  have hPsi_ne : ∀ n : ℕ, n ≠ 0 → W.Ψ (n : ℤ) ≠ 0 := by
    intro n hn
    rw [WeierstrassCurve.Ψ_ofNat]
    have hC : Polynomial.C (W.preΨ' n) ≠ 0 :=
      Polynomial.C_ne_zero.mpr
        (W.preΨ'_ne_zero (Nat.cast_ne_zero.mpr hn))
    by_cases heven : Even n
    · simp only [heven, ↓reduceIte]
      exact mul_ne_zero hC hψ₂_ne
    · simp only [heven, ↓reduceIte, mul_one]
      exact hC
  have hPsi_deg : ∀ n : ℕ, n ≠ 0 →
      (W.Ψ (n : ℤ)).natDegree < W.toAffine.polynomial.natDegree := by
    intro n _
    rw [WeierstrassCurve.Affine.natDegree_polynomial,
      WeierstrassCurve.Ψ_ofNat]
    by_cases heven : Even n
    · simp only [heven, ↓reduceIte]
      calc
        (Polynomial.C (W.preΨ' n) * W.ψ₂).natDegree
            ≤ 0 + 1 := Polynomial.natDegree_mul_le |>.trans
              (Nat.add_le_add (Polynomial.natDegree_C _).le hψ₂_deg)
        _ < 2 := by omega
    · simp only [heven, ↓reduceIte, mul_one]
      have hdeg : (Polynomial.C (W.preΨ' n)).natDegree = 0 :=
        Polynomial.natDegree_C _
      omega
  intro m hm hpsi
  suffices hPsi :
      WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (W.Ψ m) ≠ 0 by
    exact hPsi (by
      rw [← WeierstrassCurve.Affine.CoordinateRing.mk_ψ, hpsi, map_zero])
  rcases m with n | n
  · exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
      WeierstrassCurve.Affine.monic_polynomial
      (hPsi_ne n (by intro h; exact hm (by simp [h])))
      (hPsi_deg n (by intro h; exact hm (by simp [h])))
  · rw [show (Int.negSucc n : ℤ) = -(↑(n + 1) : ℤ) by
        simp [Int.negSucc_eq],
      WeierstrassCurve.Ψ_neg, map_neg, neg_ne_zero]
    exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
      WeierstrassCurve.Affine.monic_polynomial
      (hPsi_ne _ (Nat.succ_ne_zero n))
      (hPsi_deg _ (Nat.succ_ne_zero n))

theorem nsmul_eq_zero_iff_PsiSq_eval
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    {n : ℕ} {x y : ℚ} (h : (W⁄ℚ).Nonsingular x y) :
    n • (WeierstrassCurve.Affine.Point.some x y h : (W⁄ℚ).Point) = 0 ↔
      (W.ΨSq (n : ℤ)).eval x = 0 := by
  have h4 : (4 : ℚ) ≠ 0 := by norm_num
  have hc3 : W.Ψ₃ ≠ 0 :=
    WeierstrassCurve.Ψ₃_ne_zero W (by norm_num)
  have key := KeystoneLadder.nsmul_eq_zero_iff_ΨSq_eval
    W h4 (psi_ne_zero_rat W) hc3 (n := n) h
  exact key

end

end MazurProof.TateOriginDivision

end

-- ===== FLT.Assumptions.MazurProof.XDelta19Model =====
section
/-!
# The elliptic intermediate quotient at level nineteen

The order-three diamond quotient used in the order-nineteen argument has
minimal equation

`v² + v = u³ + u² + u`.

For the arithmetic descent it is convenient to use the integral short model

`Y² = X³ + (2X+4)²`,

obtained from the minimal model by `X=4u` and `Y=8v+4`.  This file records
the two models and the explicit degree-three isogeny pair used below.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.XDelta19Model

open WeierstrassCurve
open WeierstrassCurve.Affine

noncomputable section

/-! ## Minimal and integral short models -/

/-- The affine equation of the minimal genus-one quotient. -/
def OnMinimal (u v : ℚ) : Prop :=
  v ^ 2 + v = u ^ 3 + u ^ 2 + u

/-- The integral short model used for the three-isogeny descent. -/
def shortCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 4
  a₃ := 0
  a₄ := 16
  a₆ := 16

/-- The affine equation of the integral short model. -/
def OnShort (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 3 + (2 * x + 4) ^ 2

/-- The short model has nonzero discriminant. -/
theorem shortCurve_delta : shortCurve.Δ = (-77824 : ℚ) := by
  norm_num [shortCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The integral short model is nonsingular. -/
instance shortCurve_isElliptic : shortCurve.IsElliptic where
  isUnit := by
    rw [shortCurve_delta]
    norm_num

/-- The bundled affine equation is the displayed short equation. -/
@[simp] theorem shortCurve_equation_iff (x y : ℚ) :
    WeierstrassCurve.Affine.Equation shortCurve x y ↔ OnShort x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [shortCurve, OnShort]
  ring_nf

/-- The coordinate change from the minimal model to the short model. -/
theorem minimal_to_short {u v : ℚ} (h : OnMinimal u v) :
    OnShort (4 * u) (8 * v + 4) := by
  unfold OnMinimal at h
  unfold OnShort
  linear_combination 64 * h

/-- Rational-point classification on the short model implies the required
classification on the minimal model. -/
theorem minimal_x_eq_zero_of_short_x_eq_zero
    (hshort : ∀ x y : ℚ, OnShort x y → x = 0)
    {u v : ℚ} (h : OnMinimal u v) :
    u = 0 := by
  have hx : 4 * u = 0 :=
    hshort (4 * u) (8 * v + 4) (minimal_to_short h)
  linarith

/-! ## The first degree-three isogeny -/

/-- The scaled Vélu quotient of the short model. -/
def dualCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -108
  a₃ := 0
  a₄ := -8208
  a₆ := -155952

/-- The affine equation of the scaled Vélu quotient. -/
def OnDual (s t : ℚ) : Prop :=
  t ^ 2 = s ^ 3 - 3 * (6 * s + 228) ^ 2

/-- The scaled Vélu quotient has nonzero discriminant. -/
theorem dualCurve_delta : dualCurve.Δ = (-14930550042624 : ℚ) := by
  norm_num [dualCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The scaled Vélu quotient is nonsingular. -/
instance dualCurve_isElliptic : dualCurve.IsElliptic where
  isUnit := by
    rw [dualCurve_delta]
    norm_num

/-- The bundled affine equation is the displayed dual equation. -/
@[simp] theorem dualCurve_equation_iff (s t : ℚ) :
    WeierstrassCurve.Affine.Equation dualCurve s t ↔ OnDual s t := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [dualCurve, OnDual]
  ring_nf

/-- Horizontal coordinate of the dual degree-three isogeny. -/
def dualThreeIsogenyX (s : ℚ) : ℚ :=
  (s ^ 3 - 144 * s ^ 2 - 16416 * s - 623808) / (81 * s ^ 2)

/-- Vertical coordinate of the dual degree-three isogeny. -/
def dualThreeIsogenyY (s t : ℚ) : ℚ :=
  (s ^ 3 * t + 16416 * s * t + 1247616 * t) / (729 * s ^ 3)

/-- The dual degree-three isogeny carries the scaled quotient back to the
short curve. -/
theorem dualThreeIsogeny_on_curve {s t : ℚ} (hs : s ≠ 0)
    (h : OnDual s t) :
    OnShort (dualThreeIsogenyX s) (dualThreeIsogenyY s t) := by
  unfold OnDual at h
  unfold OnShort dualThreeIsogenyX dualThreeIsogenyY
  field_simp [hs]
  simp_rw [h]
  ring

/-! ## Bundled point maps -/

/-- Rational points on the integral short model. -/
abbrev ShortPoint := Point shortCurve

/-- Rational points on the scaled Vélu quotient. -/
abbrev DualPoint := Point dualCurve

/-- A rational affine point on the scaled quotient cannot have first
coordinate zero. -/
theorem dual_x_ne_zero_of_on_curve {s t : ℚ}
    (h : OnDual s t) : s ≠ 0 := by
  intro hs
  rw [hs] at h
  norm_num [OnDual] at h
  nlinarith [sq_nonneg t]

/-- The bundled dual degree-three isogeny. -/
noncomputable def dualThreeIsogenyPoint : DualPoint → ShortPoint
  | .zero => .zero
  | .some s _t h =>
      if hs : s = 0 then .zero
      else Point.mk
        (shortCurve_equation_iff _ _ |>.2 <|
          dualThreeIsogeny_on_curve hs
            (dualCurve_equation_iff _ _ |>.1 h.1))

/-- The bundled dual isogeny fixes the point at infinity. -/
@[simp] theorem dualThreeIsogenyPoint_zero :
    dualThreeIsogenyPoint 0 = 0 := rfl

/-- The bundled dual isogeny is given by the displayed affine formulas away
from the empty exceptional divisor. -/
theorem dualThreeIsogenyPoint_some_of_x_ne_zero {s t : ℚ}
    (h : Nonsingular dualCurve s t) (hs : s ≠ 0) :
    dualThreeIsogenyPoint (.some s t h) =
      Point.mk
        (shortCurve_equation_iff _ _ |>.2 <|
          dualThreeIsogeny_on_curve hs
            (dualCurve_equation_iff _ _ |>.1 h.1)) := by
  simp [dualThreeIsogenyPoint, hs]

/-! ## Visible rational three-torsion -/

end

end MazurProof.XDelta19Model

end

-- ===== FLT.Assumptions.MazurProof.XDelta19Descent =====
section
/-!
# A rational-flex descent on the level-nineteen quotient

On the short model

`y² = x³ + (2x+4)²`,

the two factors `y-(2x+4)` and `y+(2x+4)` have product `x³`.
After putting a rational point in primitive integral coordinates, an exact
two-adic normalization makes these factors coprime.  Consequently the first
factor is itself a rational cube.

This is the elementary descent input for the dual degree-three isogeny.
-/

namespace MazurProof.XDelta19Descent

open MazurProof.RationalPointsX135
open MazurProof.XDelta19Model

noncomputable section

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- A finite two-adic certificate for the even-numerator branch of the
integral short model. -/
private theorem even_short_model_mod_thirtyTwo :
    ∀ A B C : ZMod 32,
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) A = 0 →
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) B ≠ 0 →
      C ^ 2 = A ^ 3 + 4 * A ^ 2 * B ^ 2 + 16 * A * B ^ 4 +
          16 * B ^ 6 →
      ZMod.castHom (show 4 ∣ 32 by norm_num) (ZMod 4) A = 0 ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C -
            2 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B -
            4 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C +
            2 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B +
            4 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) := by
  decide

/-- The finite certificate lifts to the required integer divisibilities. -/
private theorem even_short_model_divisibility {A B C : ℤ}
    (hA : (2 : ℤ) ∣ A) (hB : ¬(2 : ℤ) ∣ B)
    (hmodel : C ^ 2 = A ^ 3 + 4 * A ^ 2 * B ^ 2 +
      16 * A * B ^ 4 + 16 * B ^ 6) :
    (4 : ℤ) ∣ A ∧
      (8 : ℤ) ∣ C - 2 * A * B - 4 * B ^ 3 ∧
      (8 : ℤ) ∣ C + 2 * A * B + 4 * B ^ 3 := by
  have h32 : (C : ZMod 32) ^ 2 = (A : ZMod 32) ^ 3 +
      4 * (A : ZMod 32) ^ 2 * B ^ 2 + 16 * (A : ZMod 32) * B ^ 4 +
        16 * (B : ZMod 32) ^ 6 := by
    have h' := congrArg (fun n : ℤ => (n : ZMod 32)) hmodel
    push_cast at h'
    exact h'
  have hA2 : ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2)
      (A : ZMod 32) = 0 := by
    have hz : (A : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd A 2).mpr hA
    simpa [ZMod.castHom_apply] using hz
  have hB2 : ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2)
      (B : ZMod 32) ≠ 0 := by
    intro hz
    apply hB
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd B 2).mp
    simpa [ZMod.castHom_apply] using hz
  have hc := even_short_model_mod_thirtyTwo (A : ZMod 32)
    (B : ZMod 32) (C : ZMod 32) hA2 hB2 h32
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd A 4).mp
    simpa [ZMod.castHom_apply] using hc.1
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (C - 2 * A * B - 4 * B ^ 3) 8).mp
    simpa [ZMod.castHom_apply] using hc.2.1
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (C + 2 * A * B + 4 * B ^ 3) 8).mp
    simpa [ZMod.castHom_apply] using hc.2.2

/-- Primitive integral flex coordinates in which the two descent factors are
coprime and have cube product. -/
theorem short_flex_integral_model {x y : ℚ}
    (h : OnShort x y) :
    ∃ M D R S : ℤ,
      0 < D ∧ Int.gcd M D = 1 ∧
      x = 4 * (M : ℚ) / (D : ℚ) ^ 2 ∧
      y - (2 * x + 4) = 8 * (R : ℚ) / (D : ℚ) ^ 3 ∧
      R * S = M ^ 3 ∧
      S = R + 2 * M * D + D ^ 3 := by
  have hcubic : y ^ 2 = x ^ 3 + ((4 : ℤ) : ℚ) * x ^ 2 +
      ((16 : ℤ) : ℚ) * x + (16 : ℤ) := by
    unfold OnShort at h
    norm_num at h ⊢
    nlinarith
  obtain ⟨A, B, C, hBpos, hcop, hx, hy, hmodel⟩ :=
    integral_model_monic_const 4 16 16 x y hcubic
  have hBneZ : B ≠ 0 := ne_of_gt hBpos
  have hBneQ : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hBneZ
  have hcopI : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hprodRaw :
      (C - 2 * A * B - 4 * B ^ 3) *
          (C + 2 * A * B + 4 * B ^ 3) = A ^ 3 := by
    calc
      (C - 2 * A * B - 4 * B ^ 3) *
          (C + 2 * A * B + 4 * B ^ 3) =
          C ^ 2 - (2 * A * B + 4 * B ^ 3) ^ 2 := by ring
      _ = A ^ 3 := by linear_combination hmodel
  rcases A.even_or_odd with hAeven | hAodd
  · have hA2 : (2 : ℤ) ∣ A := hAeven.two_dvd
    have hcop2B : IsCoprime (2 : ℤ) B :=
      hcopI.of_isCoprime_of_dvd_left hA2
    have hBodd : Odd B := Int.isCoprime_two_left.mp hcop2B
    obtain ⟨hA4, hN8, hP8⟩ :=
      even_short_model_divisibility hA2 (by
        rw [← even_iff_two_dvd]
        exact Int.not_even_iff_odd.mpr hBodd) hmodel
    obtain ⟨M, hM⟩ := hA4
    obtain ⟨R, hR⟩ := hN8
    obtain ⟨S, hS⟩ := hP8
    have hcopMD : IsCoprime M B := by
      rw [hM] at hcopI
      exact hcopI.of_mul_left_right
    have hprod : R * S = M ^ 3 := by
      rw [hR, hS, hM] at hprodRaw
      ring_nf at hprodRaw ⊢
      omega
    have hlin : S = R + 2 * M * B + B ^ 3 := by
      have h8 : 8 * S = 8 * (R + 2 * M * B + B ^ 3) := by
        calc
          8 * S = C + 2 * A * B + 4 * B ^ 3 := hS.symm
          _ = (C - 2 * A * B - 4 * B ^ 3) +
              8 * (2 * M * B + B ^ 3) := by rw [hM]; ring
          _ = 8 * R + 8 * (2 * M * B + B ^ 3) := by rw [hR]
          _ = 8 * (R + 2 * M * B + B ^ 3) := by ring
      omega
    refine ⟨M, B, R, S, hBpos,
      Int.isCoprime_iff_gcd_eq_one.mp hcopMD, ?_, ?_, hprod, hlin⟩
    · rw [hx, hM]
      push_cast
      ring
    · rw [hx, hy, hM]
      push_cast
      field_simp [hBneQ]
      have hR' := hR
      rw [hM] at hR'
      have hR'' := congrArg (fun n : ℤ => (n : ℚ)) hR'
      push_cast at hR''
      linear_combination hR''
  · have hcopA2 : IsCoprime A (2 : ℤ) :=
      Int.isCoprime_two_right.mpr hAodd
    have hcopAD : IsCoprime A (2 * B) := hcopA2.mul_right hcopI
    refine ⟨A, 2 * B, C - 2 * A * B - 4 * B ^ 3,
      C + 2 * A * B + 4 * B ^ 3, by positivity,
      Int.isCoprime_iff_gcd_eq_one.mp hcopAD, ?_, ?_, hprodRaw, ?_⟩
    · rw [hx]
      push_cast
      field_simp [hBneQ]
      ring
    · rw [hx, hy]
      push_cast
      field_simp [hBneQ]
      ring
    · ring

/-- No prime can divide both normalized descent factors. -/
private theorem flex_factors_isCoprime
    {M D R S : ℤ} (hcop : Int.gcd M D = 1)
    (hprod : R * S = M ^ 3)
    (hlin : S = R + 2 * M * D + D ^ 3) :
    IsCoprime R S := by
  rw [Int.isCoprime_iff_nat_coprime]
  by_contra hnot
  obtain ⟨p, hp, hpR, hpS⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hpR' : (p : ℤ) ∣ R := Int.natCast_dvd.mpr hpR
  have hpS' : (p : ℤ) ∣ S := Int.natCast_dvd.mpr hpS
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpMpow : (p : ℤ) ∣ M ^ 3 := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left hpR' S
  have hpM : (p : ℤ) ∣ M := hpInt.dvd_of_dvd_pow hpMpow
  have hpDiff : (p : ℤ) ∣ S - R := dvd_sub hpS' hpR'
  have hpSum : (p : ℤ) ∣ 2 * M * D + D ^ 3 := by
    rw [hlin] at hpDiff
    have hdiff :
        (R + 2 * M * D + D ^ 3) - R = 2 * M * D + D ^ 3 := by ring
    rwa [hdiff] at hpDiff
  have hpFirst : (p : ℤ) ∣ 2 * M * D := by
    rcases hpM with ⟨k, hk⟩
    refine ⟨2 * k * D, ?_⟩
    rw [hk]
    ring
  have hpDpow : (p : ℤ) ∣ D ^ 3 := by
    have := dvd_sub hpSum hpFirst
    have hdiff :
        (2 * M * D + D ^ 3) - 2 * M * D = D ^ 3 := by ring
    rwa [hdiff] at this
  have hpD : (p : ℤ) ∣ D := hpInt.dvd_of_dvd_pow hpDpow
  have hcopI : IsCoprime M D := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  exact hpInt.not_unit (hcopI.isUnit_of_dvd' hpM hpD)

/-- The normalized first descent factor is an integral cube. -/
theorem flex_factor_is_cube
    {M D R S : ℤ} (hcop : Int.gcd M D = 1)
    (hprod : R * S = M ^ 3)
    (hlin : S = R + 2 * M * D + D ^ 3) :
    ∃ q : ℤ, R = q ^ 3 := by
  have hcopRS : IsCoprime R S :=
    flex_factors_isCoprime hcop hprod hlin
  exact Int.eq_pow_of_mul_eq_pow_odd_left hcopRS
    (show Odd 3 by decide) hprod

/-- The first rational flex factor on the short model is always a rational
cube. -/
theorem short_alpha_is_cube {x y : ℚ} (h : OnShort x y) :
    ∃ r : ℚ, y - (2 * x + 4) = r ^ 3 := by
  obtain ⟨M, D, R, S, hDpos, hcop, _hx, halpha, hprod, hlin⟩ :=
    short_flex_integral_model h
  obtain ⟨q, hq⟩ := flex_factor_is_cube hcop hprod hlin
  refine ⟨2 * (q : ℚ) / (D : ℚ), ?_⟩
  rw [halpha, hq]
  push_cast
  field_simp [Int.cast_ne_zero.mpr (ne_of_gt hDpos)]
  ring

/-- A nonzero cube value of the flex descent function constructs an explicit
preimage under the dual degree-three isogeny. -/
theorem exists_dualThreeIsogeny_preimage_of_alpha_cube
    {x y r : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular shortCurve x y)
    (hr : r ^ 3 = y - (2 * x + 4)) (hr0 : r ≠ 0) :
    ∃ Q : DualPoint,
      dualThreeIsogenyPoint Q =
        WeierstrassCurve.Affine.Point.some x y h := by
  have hcurve : OnShort x y := (shortCurve_equation_iff x y).mp h.1
  have hy : y = r ^ 3 + 2 * x + 4 := by
    linarith
  have hrel : x ^ 3 = r ^ 3 * (r ^ 3 + 4 * x + 8) := by
    unfold OnShort at hcurve
    rw [hy] at hcurve
    linear_combination -hcurve
  let d : ℚ := 3 * x - 3 * r ^ 2 - 4 * r
  have hd : d ≠ 0 := by
    intro hd
    have hx : x = r ^ 2 + 4 * r / 3 := by
      dsimp [d] at hd
      linarith
    rw [hx] at hrel
    ring_nf at hrel
    apply hr0
    have : r ^ 3 = 0 := by
      linarith
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp this
  let s : ℚ := 456 * r / d
  let t : ℚ := 9 * s * r + 6 * s + 684
  have hs : s ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (by norm_num) hr0) hd
  have hdual : OnDual s t := by
    unfold OnDual
    dsimp only [t, s]
    field_simp [hd]
    dsimp only [d]
    linear_combination 16842816 * hrel
  have hxmap : dualThreeIsogenyX s = x := by
    unfold dualThreeIsogenyX
    dsimp only [s]
    field_simp [hd, hr0]
    dsimp only [d]
    linear_combination -16842816 * hrel
  have hymap : dualThreeIsogenyY s t = y := by
    rw [hy]
    unfold dualThreeIsogenyY
    dsimp only [t, s]
    field_simp [hd, hr0]
    dsimp only [d]
    linear_combination
      69122916864 * (-2 * r ^ 2 + x - 2 * r) * hrel
  have hdualns :
      WeierstrassCurve.Affine.Nonsingular dualCurve s t :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((dualCurve_equation_iff s t).mpr hdual)
  let Q : DualPoint :=
    WeierstrassCurve.Affine.Point.some s t hdualns
  refine ⟨Q, ?_⟩
  rw [dualThreeIsogenyPoint_some_of_x_ne_zero hdualns hs]
  change WeierstrassCurve.Affine.Point.some
      (dualThreeIsogenyX s) (dualThreeIsogenyY s t) _ =
    WeierstrassCurve.Affine.Point.some x y h
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hxmap, hymap⟩

/-- The dual degree-three isogeny is surjective on rational points of the
short model. -/
theorem dualThreeIsogenyPoint_surjective (P : ShortPoint) :
    ∃ Q : DualPoint, dualThreeIsogenyPoint Q = P := by
  cases P with
  | zero =>
      exact ⟨0, dualThreeIsogenyPoint_zero⟩
  | some x y h =>
      have hcurve : OnShort x y := (shortCurve_equation_iff x y).mp h.1
      by_cases hx : x = 0
      · have hySq : y ^ 2 = (4 : ℚ) ^ 2 := by
          rw [hx] at hcurve
          norm_num [OnShort] at hcurve ⊢
          exact hcurve
        rcases eq_or_eq_neg_of_sq_eq_sq y 4 hySq with hy | hy
        · have hdual : OnDual 228 2052 := by
            norm_num [OnDual]
          have hdualns :
              WeierstrassCurve.Affine.Nonsingular dualCurve 228 2052 :=
            WeierstrassCurve.Affine.equation_iff_nonsingular.mp
              ((dualCurve_equation_iff 228 2052).mpr hdual)
          let Q : DualPoint :=
            WeierstrassCurve.Affine.Point.some 228 2052 hdualns
          refine ⟨Q, ?_⟩
          rw [dualThreeIsogenyPoint_some_of_x_ne_zero hdualns (by norm_num)]
          change WeierstrassCurve.Affine.Point.some
              (dualThreeIsogenyX 228) (dualThreeIsogenyY 228 2052) _ =
            WeierstrassCurve.Affine.Point.some x y h
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          constructor
          · norm_num [dualThreeIsogenyX, hx]
          · norm_num [dualThreeIsogenyY, hy]
        · have hdual : OnDual 228 (-2052) := by
            norm_num [OnDual]
          have hdualns :
              WeierstrassCurve.Affine.Nonsingular dualCurve 228 (-2052) :=
            WeierstrassCurve.Affine.equation_iff_nonsingular.mp
              ((dualCurve_equation_iff 228 (-2052)).mpr hdual)
          let Q : DualPoint :=
            WeierstrassCurve.Affine.Point.some 228 (-2052) hdualns
          refine ⟨Q, ?_⟩
          rw [dualThreeIsogenyPoint_some_of_x_ne_zero hdualns (by norm_num)]
          change WeierstrassCurve.Affine.Point.some
              (dualThreeIsogenyX 228) (dualThreeIsogenyY 228 (-2052)) _ =
            WeierstrassCurve.Affine.Point.some x y h
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          constructor
          · norm_num [dualThreeIsogenyX, hx]
          · norm_num [dualThreeIsogenyY, hy]
      · obtain ⟨r, hr⟩ := short_alpha_is_cube hcurve
        have hr0 : r ≠ 0 := by
          intro hr0
          rw [hr0] at hr
          norm_num at hr
          apply hx
          have hx3 : x ^ 3 = 0 := by
            calc
              x ^ 3 = y ^ 2 - (2 * x + 4) ^ 2 := by
                unfold OnShort at hcurve
                linarith
              _ = (y - (2 * x + 4)) * (y + (2 * x + 4)) := by ring
              _ = 0 := by rw [hr]; ring
          exact eq_zero_of_pow_eq_zero hx3
        exact exists_dualThreeIsogeny_preimage_of_alpha_cube
          h hr.symm hr0

end

end MazurProof.XDelta19Descent

end

-- ===== FLT.Assumptions.MazurProof.XDelta19GoodModel =====
section
/-!
# A good integral model in the conductor-nineteen isogeny class

The scaled quotient used in `XDelta19Model` becomes the smaller integral
model

`Y² = X³ + (8X+76)²`

after the change of variables

`s = 9X + 228`, `t = 27Y`.

This model has good reduction at three.  Its visible rational flexes are
the two points `(0, ±76)`, which is the normalization needed for the
complementary three-isogeny descent.
-/

namespace MazurProof.XDelta19GoodModel

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.XDelta19Model

noncomputable section

/-! ## The good integral equation -/

/-- The integral model in the middle of the conductor-nineteen
three-isogeny chain. -/
def goodCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 64
  a₃ := 0
  a₄ := 1216
  a₆ := 5776

/-- The affine equation of the good integral model. -/
def OnGood (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 3 + (8 * x + 76) ^ 2

/-- The good model has discriminant `-2^12 * 19^3`, hence in particular
good reduction at three. -/
theorem goodCurve_delta : goodCurve.Δ = (-28094464 : ℚ) := by
  norm_num [goodCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The good integral model is nonsingular. -/
instance goodCurve_isElliptic : goodCurve.IsElliptic where
  isUnit := by
    rw [goodCurve_delta]
    norm_num

/-- The bundled affine equation is the displayed good equation. -/
@[simp] theorem goodCurve_equation_iff (x y : ℚ) :
    Equation goodCurve x y ↔ OnGood x y := by
  rw [equation_iff]
  simp [goodCurve, OnGood]
  ring_nf

/-! ## Change of variables to the scaled quotient -/

/-- The inverse rational change of variables carries the scaled quotient
back to the good model. -/
theorem dual_to_good {s t : ℚ} (h : OnDual s t) :
    OnGood ((s - 228) / 9) (t / 27) := by
  unfold OnDual at h
  unfold OnGood
  linear_combination h / 729

/-- Rational points on the good integral model. -/
abbrev GoodPoint := Point goodCurve

/-! ## Visible rational flexes -/

/-- Nonsingularity of the positive visible flex. -/
theorem goodT_nonsingular : Nonsingular goodCurve (0 : ℚ) 76 :=
  equation_iff_nonsingular.mp <|
    (goodCurve_equation_iff 0 76).mpr (by norm_num [OnGood])

/-- Nonsingularity of the negative visible flex. -/
theorem goodTNeg_nonsingular : Nonsingular goodCurve (0 : ℚ) (-76) :=
  equation_iff_nonsingular.mp <|
    (goodCurve_equation_iff 0 (-76)).mpr (by norm_num [OnGood])

/-- The positive rational flex on the good model. -/
def goodT : GoodPoint :=
  Point.some 0 76 goodT_nonsingular

/-- The negative rational flex on the good model. -/
def goodTNeg : GoodPoint :=
  Point.some 0 (-76) goodTNeg_nonsingular

end

end MazurProof.XDelta19GoodModel

end

-- ===== FLT.Assumptions.MazurProof.XDelta19GoodIsogeny =====
section
/-!
# The complementary three-isogeny on the good conductor-nineteen model

For the good model

`y² = x³ + (8x+76)²`,

the Vélu quotient has the particularly small flex form

`t² = s³ - 3(24s+12)²`.

The constant term `12` is supported only at two and three.  This is the
arithmetic normalization used by the complementary Eisenstein descent:
the split prime above nineteen no longer occurs in the quotient equation.
-/

namespace MazurProof.XDelta19GoodIsogeny

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.XDelta19GoodModel
open Polynomial

noncomputable section

/-! ## The small quotient model -/

/-- The scaled Vélu quotient of the good integral model. -/
def quotientCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -1728
  a₃ := 0
  a₄ := -1728
  a₆ := -432

/-- The affine equation of the small Vélu quotient. -/
def OnQuotient (s t : ℚ) : Prop :=
  t ^ 2 = s ^ 3 - 3 * (24 * s + 12) ^ 2

/-- The quotient model has nonzero discriminant. -/
theorem quotientCurve_delta :
    quotientCurve.Δ = (-41358864384 : ℚ) := by
  norm_num [quotientCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The quotient model is nonsingular. -/
instance quotientCurve_isElliptic : quotientCurve.IsElliptic where
  isUnit := by
    rw [quotientCurve_delta]
    norm_num

/-- The bundled affine equation is the displayed quotient equation. -/
@[simp] theorem quotientCurve_equation_iff (s t : ℚ) :
    Equation quotientCurve s t ↔ OnQuotient s t := by
  rw [equation_iff]
  simp [quotientCurve, OnQuotient]
  ring_nf

/-! ## Explicit isogeny formulas -/

/-- Horizontal coordinate of the forward degree-three isogeny. -/
def threeIsogenyX (x : ℚ) : ℚ :=
  (9 * x ^ 3 + 768 * x ^ 2 + 21888 * x + 207936) / x ^ 2

/-- Vertical coordinate of the forward degree-three isogeny. -/
def threeIsogenyY (x y : ℚ) : ℚ :=
  (27 * x ^ 3 * y - 65664 * x * y - 1247616 * y) / x ^ 3

/-- The forward formulas carry the good model to its small quotient. -/
theorem threeIsogeny_on_curve {x y : ℚ} (hx : x ≠ 0)
    (h : OnGood x y) :
    OnQuotient (threeIsogenyX x) (threeIsogenyY x y) := by
  unfold OnGood at h
  unfold OnQuotient threeIsogenyX threeIsogenyY
  field_simp [hx]
  simp_rw [h]
  ring

/-- Horizontal coordinate of the dual degree-three isogeny. -/
def dualThreeIsogenyX (s : ℚ) : ℚ :=
  (s ^ 3 - 2304 * s ^ 2 - 3456 * s - 1728) / (81 * s ^ 2)

/-- Vertical coordinate of the dual degree-three isogeny. -/
def dualThreeIsogenyY (s t : ℚ) : ℚ :=
  (s ^ 3 * t + 3456 * s * t + 3456 * t) / (729 * s ^ 3)

/-- The dual formulas carry the small quotient back to the good model. -/
theorem dualThreeIsogeny_on_curve {s t : ℚ} (hs : s ≠ 0)
    (h : OnQuotient s t) :
    OnGood (dualThreeIsogenyX s) (dualThreeIsogenyY s t) := by
  unfold OnQuotient at h
  unfold OnGood dualThreeIsogenyX dualThreeIsogenyY
  field_simp [hs]
  simp_rw [h]
  ring

/-! ## Bundled point maps -/

/-- Rational points on the small quotient. -/
abbrev QuotientPoint := Point quotientCurve

/-- A rational affine point on the quotient cannot have first coordinate
zero. -/
theorem quotient_x_ne_zero_of_on_curve {s t : ℚ}
    (h : OnQuotient s t) :
    s ≠ 0 := by
  intro hs
  rw [hs] at h
  norm_num [OnQuotient] at h
  nlinarith [sq_nonneg t]

/-- Away from the visible kernel, the horizontal coordinate of the
forward isogeny is nonzero. -/
theorem threeIsogenyX_ne_zero {x y : ℚ} (hx : x ≠ 0)
    (h : OnGood x y) :
    threeIsogenyX x ≠ 0 :=
  quotient_x_ne_zero_of_on_curve (threeIsogeny_on_curve hx h)

/-- The bundled forward degree-three isogeny. -/
noncomputable def threeIsogenyPoint : GoodPoint → QuotientPoint
  | .zero => .zero
  | .some _x _y h =>
      if hx : _x = 0 then .zero
      else Point.mk
        (quotientCurve_equation_iff _ _ |>.2 <|
          threeIsogeny_on_curve hx
            (goodCurve_equation_iff _ _ |>.1 h.1))

/-- The bundled dual degree-three isogeny. -/
noncomputable def dualThreeIsogenyPoint : QuotientPoint → GoodPoint
  | .zero => .zero
  | .some _s _t h =>
      if hs : _s = 0 then .zero
      else Point.mk
        (goodCurve_equation_iff _ _ |>.2 <|
          dualThreeIsogeny_on_curve hs
            (quotientCurve_equation_iff _ _ |>.1 h.1))

/-- The forward isogeny fixes the point at infinity. -/
@[simp] theorem threeIsogenyPoint_zero :
    threeIsogenyPoint 0 = 0 := rfl

/-- The dual isogeny fixes the point at infinity. -/
@[simp] theorem dualThreeIsogenyPoint_zero :
    dualThreeIsogenyPoint 0 = 0 := rfl

/-- Away from its kernel, the bundled forward map is given by the
displayed affine formulas. -/
theorem threeIsogenyPoint_some_of_x_ne_zero {x y : ℚ}
    (h : Nonsingular goodCurve x y) (hx : x ≠ 0) :
    threeIsogenyPoint (.some x y h) =
      Point.mk
        (quotientCurve_equation_iff _ _ |>.2 <|
          threeIsogeny_on_curve hx
            (goodCurve_equation_iff _ _ |>.1 h.1)) := by
  simp [threeIsogenyPoint, hx]

/-- The bundled dual map is given by the displayed affine formulas on
every affine rational point of the quotient. -/
theorem dualThreeIsogenyPoint_some_of_x_ne_zero {s t : ℚ}
    (h : Nonsingular quotientCurve s t) (hs : s ≠ 0) :
    dualThreeIsogenyPoint (.some s t h) =
      Point.mk
        (goodCurve_equation_iff _ _ |>.2 <|
          dualThreeIsogeny_on_curve hs
            (quotientCurve_equation_iff _ _ |>.1 h.1)) := by
  simp [dualThreeIsogenyPoint, hs]

/-! ## The visible three-torsion kernel -/

/-- Every affine good-model point with first coordinate zero is killed
by three. -/
theorem three_nsmul_of_x_zero {x y : ℚ}
    (h : Nonsingular goodCurve x y) (hx : x = 0) :
    3 • (Point.some x y h : GoodPoint) = 0 := by
  apply (TateOriginDivision.nsmul_eq_zero_iff_PsiSq_eval
    goodCurve h).mpr
  rw [goodCurve.ΨSq_ofNat 3]
  simp [show ¬ Even (3 : ℕ) by decide,
    WeierstrassCurve.preΨ'_three, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, goodCurve, hx]
  norm_num

/-- The positive visible flex has order dividing three. -/
@[simp] theorem goodT_three_nsmul :
    3 • goodT = 0 :=
  three_nsmul_of_x_zero goodT_nonsingular rfl

/-- The negative visible flex has order dividing three. -/
@[simp] theorem goodTNeg_three_nsmul :
    3 • goodTNeg = 0 :=
  three_nsmul_of_x_zero goodTNeg_nonsingular rfl

/-- The negative visible flex is the group inverse of the positive
visible flex. -/
@[simp] theorem goodTNeg_eq_neg :
    goodTNeg = -goodT := by
  rw [goodTNeg, goodT, Point.neg_some, Point.some.injEq]
  constructor
  · rfl
  · simp [negY, goodCurve]

/-! ## Verification of the dual-forward composition -/

/-- Negation on the good model changes only the sign of the vertical
coordinate. -/
@[simp] theorem goodCurve_negY (x y : ℚ) :
    negY goodCurve x y = -y := by
  simp [negY, goodCurve]

/-- The good Weierstrass cubic has no rational root. -/
private theorem goodCubic_ne_zero (x : ℚ) :
    x ^ 3 + 64 * x ^ 2 + 1216 * x + 5776 ≠ 0 := by
  intro h
  let p : ℤ[X] := X ^ 3 + C 64 * X ^ 2 + C 1216 * X + C 5776
  have hpmonic : p.Monic := by
    dsimp [p]
    monicity!
  have hroot : aeval x p = 0 := by
    simp [p, aeval_def]
    norm_cast
  obtain ⟨z, hx, _hzdiv⟩ :=
    exists_integer_of_is_root_of_monic (A := ℤ) (K := ℚ) hpmonic hroot
  rw [hx] at h
  have hz : z ^ 3 + 64 * z ^ 2 + 1216 * z + 5776 = 0 := by
    have hzcast :
        ((z ^ 3 + 64 * z ^ 2 + 1216 * z + 5776 : ℤ) : ℚ) = 0 := by
      push_cast
      exact h
    exact_mod_cast hzcast
  have hzmod : (z : ZMod 5) ^ 3 + 64 * (z : ZMod 5) ^ 2 +
      1216 * (z : ZMod 5) + 5776 = 0 := by
    have hz' := congrArg (fun n : ℤ => (n : ZMod 5)) hz
    push_cast at hz'
    exact hz'
  exact (by decide : ∀ u : ZMod 5,
    u ^ 3 + 64 * u ^ 2 + 1216 * u + 5776 ≠ 0) (z : ZMod 5) hzmod

/-- An affine rational point on the good model never has zero vertical
coordinate. -/
theorem good_y_ne_zero {x y : ℚ} (h : OnGood x y) :
    y ≠ 0 := by
  intro hy
  apply goodCubic_ne_zero x
  unfold OnGood at h
  rw [hy] at h
  norm_num at h
  linear_combination -h

/-- The tangent slope at an affine point of the good model. -/
private def goodTangent (x y : ℚ) : ℚ :=
  (3 * x ^ 2 + 128 * x + 1216) / (2 * y)

/-- Horizontal coordinate of twice an affine point. -/
private def goodDoubleX (x y : ℚ) : ℚ :=
  goodTangent x y ^ 2 - 64 - 2 * x

/-- Vertical coordinate of twice an affine point. -/
private def goodDoubleY (x y : ℚ) : ℚ :=
  -(goodTangent x y * (goodDoubleX x y - x) + y)

/-- Slope of the line from twice a point to the original point. -/
private def goodTripleSlope (x y : ℚ) : ℚ :=
  (goodDoubleY x y - y) / (goodDoubleX x y - x)

/-- Horizontal coordinate of three times an affine point. -/
private def goodTripleX (x y : ℚ) : ℚ :=
  goodTripleSlope x y ^ 2 - 64 - goodDoubleX x y - x

/-- Vertical coordinate of three times an affine point. -/
private def goodTripleY (x y : ℚ) : ℚ :=
  -(goodTripleSlope x y * (goodTripleX x y - goodDoubleX x y) +
      goodDoubleY x y)

/-- The library tangent slope agrees with the displayed rational
function. -/
private theorem goodCurve_slope_self {x y : ℚ} (hy : y ≠ 0) :
    slope goodCurve x x y y = goodTangent x y := by
  have hneg : y ≠ negY goodCurve x y := by
    rw [goodCurve_negY]
    intro h
    apply hy
    linarith
  rw [slope_of_Y_ne rfl hneg]
  simp [goodCurve, goodTangent, negY]
  ring

/-- The library addition formula gives the displayed doubling
horizontal coordinate. -/
private theorem goodCurve_addX_tangent (x y : ℚ) :
    addX goodCurve x x (goodTangent x y) = goodDoubleX x y := by
  simp [goodCurve, goodDoubleX]
  ring

/-- The library addition formula gives the displayed doubling vertical
coordinate. -/
private theorem goodCurve_addY_tangent (x y : ℚ) :
    addY goodCurve x x y (goodTangent x y) = goodDoubleY x y := by
  unfold addY negAddY negY addX goodCurve goodDoubleY goodDoubleX
  ring

/-- The secant slope used for tripling agrees with the displayed
rational function. -/
private theorem goodCurve_slope_double {x y : ℚ}
    (hxx : goodDoubleX x y ≠ x) :
    slope goodCurve (goodDoubleX x y) x (goodDoubleY x y) y =
      goodTripleSlope x y := by
  rw [slope_of_X_ne hxx]
  rfl

/-- The library secant formula gives the displayed tripling horizontal
coordinate. -/
private theorem goodCurve_addX_double (x y : ℚ) :
    addX goodCurve (goodDoubleX x y) x (goodTripleSlope x y) =
      goodTripleX x y := by
  simp [goodCurve, goodTripleX]

/-- The library secant formula gives the displayed tripling vertical
coordinate. -/
private theorem goodCurve_addY_double (x y : ℚ) :
    addY goodCurve (goodDoubleX x y) x (goodDoubleY x y)
        (goodTripleSlope x y) =
      goodTripleY x y := by
  unfold addY negAddY negY addX goodCurve goodTripleY goodTripleX
  ring

/-- The denominator separating a point from its double is the numerator
of the forward isogeny's horizontal coordinate. -/
private theorem goodDoubleX_sub_identity {x y : ℚ} (hy : y ≠ 0)
    (h : OnGood x y) :
    4 * y ^ 2 * (goodDoubleX x y - x) =
      -x * (3 * x ^ 3 + 256 * x ^ 2 + 7296 * x + 69312) := by
  unfold goodDoubleX goodTangent
  unfold OnGood at h
  field_simp [hy]
  rw [h]
  ring

/-- Away from the visible three-torsion kernel, a point is distinct from
its double. -/
private theorem goodDoubleX_ne_self {x y : ℚ} (hx : x ≠ 0)
    (h : OnGood x y) :
    goodDoubleX x y ≠ x := by
  have hy := good_y_ne_zero h
  have hid := goodDoubleX_sub_identity hy h
  have hphi := threeIsogenyX_ne_zero hx h
  have hnum :
      3 * x ^ 3 + 256 * x ^ 2 + 7296 * x + 69312 ≠ 0 := by
    intro hnum
    apply hphi
    unfold threeIsogenyX
    rw [show 9 * x ^ 3 + 768 * x ^ 2 + 21888 * x + 207936 =
      3 * (3 * x ^ 3 + 256 * x ^ 2 + 7296 * x + 69312) by ring]
    rw [hnum]
    simp
  intro heq
  rw [heq, sub_self, mul_zero] at hid
  exact (mul_ne_zero (neg_ne_zero.mpr hx) hnum) hid.symm

/-- The horizontal coordinate of the dual-forward composition agrees
with chord-and-tangent tripling. -/
private theorem dual_three_comp_x {x y : ℚ} (hx : x ≠ 0)
    (h : OnGood x y) :
    dualThreeIsogenyX (threeIsogenyX x) = goodTripleX x y := by
  have hy := good_y_ne_zero h
  have hxx := goodDoubleX_ne_self hx h
  have hphi := threeIsogenyX_ne_zero hx h
  unfold dualThreeIsogenyX goodTripleX goodTripleSlope
  field_simp [hphi, hxx]
  unfold threeIsogenyX goodDoubleY goodDoubleX goodTangent
  unfold OnGood at h
  field_simp [hx, hy]
  have hy4 : y ^ 4 = (x ^ 3 + (8 * x + 76) ^ 2) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = _ := by rw [h]
  have hy6 : y ^ 6 = (x ^ 3 + (8 * x + 76) ^ 2) ^ 3 := by
    calc
      y ^ 6 = (y ^ 2) ^ 3 := by ring
      _ = _ := by rw [h]
  have hy8 : y ^ 8 = (x ^ 3 + (8 * x + 76) ^ 2) ^ 4 := by
    calc
      y ^ 8 = (y ^ 2) ^ 4 := by ring
      _ = _ := by rw [h]
  ring_nf
  rw [h, hy4, hy6, hy8]
  ring

/-- The vertical coordinate of the dual-forward composition agrees with
chord-and-tangent tripling. -/
private theorem dual_three_comp_y {x y : ℚ} (hx : x ≠ 0)
    (h : OnGood x y) :
    dualThreeIsogenyY (threeIsogenyX x) (threeIsogenyY x y) =
      goodTripleY x y := by
  have hy := good_y_ne_zero h
  have hxx := goodDoubleX_ne_self hx h
  have hphi := threeIsogenyX_ne_zero hx h
  unfold dualThreeIsogenyY goodTripleY goodTripleX goodTripleSlope
  field_simp [hphi, hxx]
  unfold threeIsogenyX threeIsogenyY goodDoubleY goodDoubleX goodTangent
  unfold OnGood at h
  field_simp [hx, hy]
  have hy4 : y ^ 4 = (x ^ 3 + (8 * x + 76) ^ 2) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = _ := by rw [h]
  have hy6 : y ^ 6 = (x ^ 3 + (8 * x + 76) ^ 2) ^ 3 := by
    calc
      y ^ 6 = (y ^ 2) ^ 3 := by ring
      _ = _ := by rw [h]
  have hy8 : y ^ 8 = (x ^ 3 + (8 * x + 76) ^ 2) ^ 4 := by
    calc
      y ^ 8 = (y ^ 2) ^ 4 := by ring
      _ = _ := by rw [h]
  have hy10 : y ^ 10 = (x ^ 3 + (8 * x + 76) ^ 2) ^ 5 := by
    calc
      y ^ 10 = (y ^ 2) ^ 5 := by ring
      _ = _ := by rw [h]
  have hy12 : y ^ 12 = (x ^ 3 + (8 * x + 76) ^ 2) ^ 6 := by
    calc
      y ^ 12 = (y ^ 2) ^ 6 := by ring
      _ = _ := by rw [h]
  ring_nf
  rw [hy4, hy6, hy8, hy10, hy12]
  ring

set_option maxHeartbeats 0 in
/-- The explicit dual isogeny composed with the explicit forward isogeny
is multiplication by three on every rational point of the good model. -/
theorem dual_comp_threeIsogenyPoint (P : GoodPoint) :
    dualThreeIsogenyPoint (threeIsogenyPoint P) = 3 • P := by
  cases P with
  | zero => rfl
  | some x y h =>
      have hcurve : OnGood x y :=
        (goodCurve_equation_iff x y).mp h.1
      by_cases hx : x = 0
      · have hzero :
            threeIsogenyPoint (Point.some x y h : GoodPoint) =
              (0 : QuotientPoint) := by
          simp only [threeIsogenyPoint]
          rw [dif_pos hx]
          change (0 : QuotientPoint) = (0 : QuotientPoint)
          rfl
        rw [hzero, dualThreeIsogenyPoint_zero]
        exact (three_nsmul_of_x_zero h hx).symm
      · rw [threeIsogenyPoint_some_of_x_ne_zero h hx]
        have hphi := threeIsogenyX_ne_zero hx hcurve
        change dualThreeIsogenyPoint
            (.some (threeIsogenyX x) (threeIsogenyY x y) _) = _
        rw [dualThreeIsogenyPoint_some_of_x_ne_zero _ hphi]
        have hy := good_y_ne_zero hcurve
        have hneg : y ≠ negY goodCurve x y := by
          rw [goodCurve_negY]
          intro heq
          apply hy
          linarith
        have hxx := goodDoubleX_ne_self hx hcurve
        rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul,
          two_nsmul]
        rw [Point.add_self_of_Y_ne hneg]
        rw [Point.add_of_X_ne (by
          rw [goodCurve_slope_self hy, goodCurve_addX_tangent]
          exact hxx)]
        change Point.some
            (dualThreeIsogenyX (threeIsogenyX x))
            (dualThreeIsogenyY (threeIsogenyX x) (threeIsogenyY x y)) _ = _
        rw [Point.some.injEq]
        constructor
        · rw [goodCurve_slope_self hy, goodCurve_addX_tangent,
            goodCurve_addY_tangent, goodCurve_slope_double hxx,
            goodCurve_addX_double]
          exact dual_three_comp_x hx hcurve
        · rw [goodCurve_slope_self hy, goodCurve_addX_tangent,
            goodCurve_addY_tangent, goodCurve_slope_double hxx,
            goodCurve_addY_double]
          exact dual_three_comp_y hx hcurve

end

end MazurProof.XDelta19GoodIsogeny

end

-- ===== FLT.Assumptions.MazurProof.XDelta19GoodDescent =====
section
/-!
# The rational-flex cubeclasses on the good level-nineteen model

For

`y² = x³ + (8x+76)²`,

the factors `y-(8x+76)` and `y+(8x+76)` have product `x³`.
After a two-adic integral normalization, their only possible common
prime is nineteen.  It follows that the first factor has one of the
three rational cubeclasses `1`, `19`, and `19²`.
-/

namespace MazurProof.XDelta19GoodDescent

open MazurProof.RationalPointsX135
open MazurProof.XDelta19GoodModel
open MazurProof.XDelta19GoodIsogeny

noncomputable section

/-! ## Two-adic normalization -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- A finite two-adic certificate for the even-numerator branch of the
good model. -/
private theorem even_good_model_mod_thirtyTwo :
    ∀ A B C : ZMod 32,
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) A = 0 →
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) B ≠ 0 →
      C ^ 2 = A ^ 3 + 64 * A ^ 2 * B ^ 2 + 1216 * A * B ^ 4 +
          5776 * B ^ 6 →
      ZMod.castHom (show 4 ∣ 32 by norm_num) (ZMod 4) A = 0 ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C -
            8 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B -
            76 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C +
            8 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B +
            76 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) := by
  decide

/-- The finite two-adic certificate lifts to the required integer
divisibilities. -/
private theorem even_good_model_divisibility {A B C : ℤ}
    (hA : (2 : ℤ) ∣ A) (hB : ¬(2 : ℤ) ∣ B)
    (hmodel : C ^ 2 = A ^ 3 + 64 * A ^ 2 * B ^ 2 +
      1216 * A * B ^ 4 + 5776 * B ^ 6) :
    (4 : ℤ) ∣ A ∧
      (8 : ℤ) ∣ C - 8 * A * B - 76 * B ^ 3 ∧
      (8 : ℤ) ∣ C + 8 * A * B + 76 * B ^ 3 := by
  have h32 : (C : ZMod 32) ^ 2 = (A : ZMod 32) ^ 3 +
      64 * (A : ZMod 32) ^ 2 * B ^ 2 +
      1216 * (A : ZMod 32) * B ^ 4 + 5776 * (B : ZMod 32) ^ 6 := by
    have h' := congrArg (fun n : ℤ => (n : ZMod 32)) hmodel
    push_cast at h'
    exact h'
  have hA2 : ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2)
      (A : ZMod 32) = 0 := by
    have hz : (A : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd A 2).mpr hA
    simpa [ZMod.castHom_apply] using hz
  have hB2 : ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2)
      (B : ZMod 32) ≠ 0 := by
    intro hz
    apply hB
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd B 2).mp
    simpa [ZMod.castHom_apply] using hz
  have hc := even_good_model_mod_thirtyTwo (A : ZMod 32)
    (B : ZMod 32) (C : ZMod 32) hA2 hB2 h32
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd A 4).mp
    simpa [ZMod.castHom_apply] using hc.1
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (C - 8 * A * B - 76 * B ^ 3) 8).mp
    simpa [ZMod.castHom_apply] using hc.2.1
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (C + 8 * A * B + 76 * B ^ 3) 8).mp
    simpa [ZMod.castHom_apply] using hc.2.2

/-- Primitive integral flex coordinates in which the two descent factors
have cube product and can share only the prime nineteen. -/
theorem good_flex_integral_model {x y : ℚ}
    (h : OnGood x y) :
    ∃ M D R S : ℤ,
      0 < D ∧ Int.gcd M D = 1 ∧
      x = 4 * (M : ℚ) / (D : ℚ) ^ 2 ∧
      y - (8 * x + 76) = 8 * (R : ℚ) / (D : ℚ) ^ 3 ∧
      R * S = M ^ 3 ∧
      S = R + 8 * M * D + 19 * D ^ 3 := by
  have hcubic : y ^ 2 = x ^ 3 + ((64 : ℤ) : ℚ) * x ^ 2 +
      ((1216 : ℤ) : ℚ) * x + (5776 : ℤ) := by
    unfold OnGood at h
    norm_num at h ⊢
    nlinarith
  obtain ⟨A, B, C, hBpos, hcop, hx, hy, hmodel⟩ :=
    integral_model_monic_const 64 1216 5776 x y hcubic
  have hBneZ : B ≠ 0 := ne_of_gt hBpos
  have hBneQ : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hBneZ
  have hcopI : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hprodRaw :
      (C - 8 * A * B - 76 * B ^ 3) *
          (C + 8 * A * B + 76 * B ^ 3) = A ^ 3 := by
    calc
      (C - 8 * A * B - 76 * B ^ 3) *
          (C + 8 * A * B + 76 * B ^ 3) =
          C ^ 2 - (8 * A * B + 76 * B ^ 3) ^ 2 := by ring
      _ = A ^ 3 := by linear_combination hmodel
  rcases A.even_or_odd with hAeven | hAodd
  · have hA2 : (2 : ℤ) ∣ A := hAeven.two_dvd
    have hcop2B : IsCoprime (2 : ℤ) B :=
      hcopI.of_isCoprime_of_dvd_left hA2
    have hBodd : Odd B := Int.isCoprime_two_left.mp hcop2B
    obtain ⟨hA4, hN8, hP8⟩ :=
      even_good_model_divisibility hA2 (by
        rw [← even_iff_two_dvd]
        exact Int.not_even_iff_odd.mpr hBodd) hmodel
    obtain ⟨M, hM⟩ := hA4
    obtain ⟨R, hR⟩ := hN8
    obtain ⟨S, hS⟩ := hP8
    have hcopMD : IsCoprime M B := by
      rw [hM] at hcopI
      exact hcopI.of_mul_left_right
    have hprod : R * S = M ^ 3 := by
      rw [hR, hS, hM] at hprodRaw
      ring_nf at hprodRaw ⊢
      omega
    have hlin : S = R + 8 * M * B + 19 * B ^ 3 := by
      have h8 : 8 * S = 8 * (R + 8 * M * B + 19 * B ^ 3) := by
        calc
          8 * S = C + 8 * A * B + 76 * B ^ 3 := hS.symm
          _ = (C - 8 * A * B - 76 * B ^ 3) +
              8 * (8 * M * B + 19 * B ^ 3) := by rw [hM]; ring
          _ = 8 * R + 8 * (8 * M * B + 19 * B ^ 3) := by rw [hR]
          _ = 8 * (R + 8 * M * B + 19 * B ^ 3) := by ring
      omega
    refine ⟨M, B, R, S, hBpos,
      Int.isCoprime_iff_gcd_eq_one.mp hcopMD, ?_, ?_, hprod, hlin⟩
    · rw [hx, hM]
      push_cast
      ring
    · rw [hx, hy, hM]
      push_cast
      field_simp [hBneQ]
      have hR' := hR
      rw [hM] at hR'
      have hR'' := congrArg (fun n : ℤ => (n : ℚ)) hR'
      push_cast at hR''
      linear_combination hR''
  · have hcopA2 : IsCoprime A (2 : ℤ) :=
      Int.isCoprime_two_right.mpr hAodd
    have hcopAD : IsCoprime A (2 * B) := hcopA2.mul_right hcopI
    refine ⟨A, 2 * B, C - 8 * A * B - 76 * B ^ 3,
      C + 8 * A * B + 76 * B ^ 3, by positivity,
      Int.isCoprime_iff_gcd_eq_one.mp hcopAD, ?_, ?_, hprodRaw, ?_⟩
    · rw [hx]
      push_cast
      field_simp [hBneQ]
      ring
    · rw [hx, hy]
      push_cast
      field_simp [hBneQ]
      ring
    · ring

/-! ## The three possible cubeclasses -/

/-- A prime common to both normalized descent factors must be nineteen. -/
private theorem flex_common_prime_eq_nineteen
    {M D R S : ℤ} (hcop : Int.gcd M D = 1)
    (hprod : R * S = M ^ 3)
    (hlin : S = R + 8 * M * D + 19 * D ^ 3)
    {p : ℕ} (hp : p.Prime) (hpR : (p : ℤ) ∣ R)
    (hpS : (p : ℤ) ∣ S) :
    p = 19 := by
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpPow : (p : ℤ) ∣ M ^ 3 := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left hpR S
  have hpM : (p : ℤ) ∣ M := hpInt.dvd_of_dvd_pow hpPow
  have hpDiff : (p : ℤ) ∣ S - R := dvd_sub hpS hpR
  have hpSum : (p : ℤ) ∣ 8 * M * D + 19 * D ^ 3 := by
    rw [hlin] at hpDiff
    have heq :
        (R + 8 * M * D + 19 * D ^ 3) - R =
          8 * M * D + 19 * D ^ 3 := by ring
    rwa [heq] at hpDiff
  have hpFirst : (p : ℤ) ∣ 8 * M * D := by
    rcases hpM with ⟨k, hk⟩
    refine ⟨8 * k * D, ?_⟩
    rw [hk]
    ring
  have hpTail : (p : ℤ) ∣ 19 * D ^ 3 := by
    have := dvd_sub hpSum hpFirst
    rcases this with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    linear_combination hk
  have hcopI : IsCoprime M D := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hpD : ¬(p : ℤ) ∣ D := by
    intro hpD
    exact hpInt.not_unit (hcopI.isUnit_of_dvd' hpM hpD)
  rcases hpInt.dvd_mul.mp hpTail with hp19 | hpD3
  · have hp19Nat : p ∣ 19 := by exact_mod_cast hp19
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 19)).mp hp19Nat with
      hp1 | hp19'
    · exact (hp.ne_one hp1).elim
    · exact hp19'
  · exact (hpD (hpInt.dvd_of_dvd_pow hpD3)).elim

/-- If nineteen is not a common factor, the two normalized descent
factors are coprime. -/
private theorem isCoprime_of_common_prime_eq_nineteen {R S : ℤ}
    (hsupport : ∀ {p : ℕ}, p.Prime → (p : ℤ) ∣ R →
      (p : ℤ) ∣ S → p = 19)
    (hnotBoth : ¬((19 : ℤ) ∣ R ∧ (19 : ℤ) ∣ S)) :
    IsCoprime R S := by
  rw [Int.isCoprime_iff_nat_coprime]
  by_contra hcop
  obtain ⟨p, hp, hpR, hpS⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpR' : (p : ℤ) ∣ R := Int.natCast_dvd.mpr hpR
  have hpS' : (p : ℤ) ∣ S := Int.natCast_dvd.mpr hpS
  have hp19 := hsupport hp hpR' hpS'
  subst p
  exact hnotBoth ⟨hpR', hpS'⟩

/-- The normalized first descent factor has cubeclass `1`, `19`, or
`19²`. -/
theorem flex_factor_cubeclass
    {M D R S : ℤ} (hcop : Int.gcd M D = 1)
    (hprod : R * S = M ^ 3)
    (hlin : S = R + 8 * M * D + 19 * D ^ 3) :
    ∃ q : ℤ, R = q ^ 3 ∨ R = 19 * q ^ 3 ∨ R = 361 * q ^ 3 := by
  have hsupport : ∀ {p : ℕ}, p.Prime → (p : ℤ) ∣ R →
      (p : ℤ) ∣ S → p = 19 :=
    fun {_p} hp hpR hpS =>
      flex_common_prime_eq_nineteen hcop hprod hlin hp hpR hpS
  by_cases h19R : (19 : ℤ) ∣ R
  · have h19Mpow : (19 : ℤ) ∣ M ^ 3 := by
      rw [← hprod]
      exact dvd_mul_of_dvd_left h19R S
    have h19M : (19 : ℤ) ∣ M :=
      Int.Prime.dvd_pow' (by norm_num : Nat.Prime 19) h19Mpow
    have h19S : (19 : ℤ) ∣ S := by
      rw [hlin]
      have hmid : (19 : ℤ) ∣ 8 * M * D := by
        rcases h19M with ⟨m, hm⟩
        refine ⟨8 * m * D, ?_⟩
        rw [hm]
        ring
      exact dvd_add (dvd_add h19R hmid) (dvd_mul_right 19 (D ^ 3))
    obtain ⟨R1, hR1⟩ := h19R
    obtain ⟨S1, hS1⟩ := h19S
    obtain ⟨M1, hM1⟩ := h19M
    have hprod1 : R1 * S1 = 19 * M1 ^ 3 := by
      rw [hR1, hS1, hM1] at hprod
      ring_nf at hprod ⊢
      omega
    have hlin1 : S1 = R1 + 8 * M1 * D + D ^ 3 := by
      rw [hR1, hS1, hM1] at hlin
      ring_nf at hlin ⊢
      omega
    have hnotBoth1 : ¬((19 : ℤ) ∣ R1 ∧ (19 : ℤ) ∣ S1) := by
      rintro ⟨h19R1, h19S1⟩
      obtain ⟨r, hr⟩ := h19R1
      obtain ⟨s, hs⟩ := h19S1
      have hM1cube : M1 ^ 3 = 19 * (r * s) := by
        rw [hr, hs] at hprod1
        ring_nf at hprod1 ⊢
        omega
      have h19M1pow : (19 : ℤ) ∣ M1 ^ 3 := ⟨r * s, hM1cube⟩
      have h19M1 : (19 : ℤ) ∣ M1 :=
        Int.Prime.dvd_pow' (by norm_num : Nat.Prime 19) h19M1pow
      obtain ⟨m, hm⟩ := h19M1
      have hDcube : D ^ 3 = 19 * (s - r - 8 * m * D) := by
        rw [hr, hs, hm] at hlin1
        ring_nf at hlin1 ⊢
        omega
      have h19Dpow : (19 : ℤ) ∣ D ^ 3 :=
        ⟨s - r - 8 * m * D, hDcube⟩
      have h19D : (19 : ℤ) ∣ D :=
        Int.Prime.dvd_pow' (by norm_num : Nat.Prime 19) h19Dpow
      have hcopI : IsCoprime M D := Int.isCoprime_iff_gcd_eq_one.mpr hcop
      have hu : IsUnit (19 : ℤ) :=
        hcopI.isUnit_of_dvd'
          (show (19 : ℤ) ∣ M by exact ⟨M1, hM1⟩) h19D
      rw [Int.isUnit_iff_abs_eq] at hu
      norm_num at hu
    have hcop1 : IsCoprime R1 S1 :=
      isCoprime_of_common_prime_eq_nineteen
        (fun {_p} hp hpR hpS => hsupport hp
          (hR1 ▸ dvd_mul_of_dvd_right hpR 19)
          (hS1 ▸ dvd_mul_of_dvd_right hpS 19)) hnotBoth1
    by_cases h19R1 : (19 : ℤ) ∣ R1
    · obtain ⟨R2, hR2⟩ := h19R1
      have hprod2 : R2 * S1 = M1 ^ 3 := by
        rw [hR2] at hprod1
        ring_nf at hprod1 ⊢
        omega
      have hcop2 : IsCoprime R2 S1 := by
        rw [hR2] at hcop1
        exact hcop1.of_mul_left_right
      obtain ⟨q, hq⟩ :=
        Int.eq_pow_of_mul_eq_pow_odd_left hcop2
          (show Odd 3 by decide) hprod2
      refine ⟨q, Or.inr (Or.inr ?_)⟩
      rw [hR1, hR2, hq]
      ring
    · have h19S1 : (19 : ℤ) ∣ S1 := by
        have h19prod : (19 : ℤ) ∣ R1 * S1 := by
          rw [hprod1]
          exact dvd_mul_right 19 _
        have hor : (19 : ℤ) ∣ R1 ∨ (19 : ℤ) ∣ S1 :=
          (by norm_num : Prime (19 : ℤ)).dvd_mul.mp h19prod
        exact Or.resolve_left hor h19R1
      obtain ⟨S2, hS2⟩ := h19S1
      have hprod2 : R1 * S2 = M1 ^ 3 := by
        rw [hS2] at hprod1
        ring_nf at hprod1 ⊢
        omega
      have hcop2 : IsCoprime R1 S2 := by
        rw [hS2] at hcop1
        exact hcop1.of_mul_right_right
      obtain ⟨q, hq⟩ :=
        Int.eq_pow_of_mul_eq_pow_odd_left hcop2
          (show Odd 3 by decide) hprod2
      refine ⟨q, Or.inr (Or.inl ?_)⟩
      rw [hR1, hq]
  · have hcopRS : IsCoprime R S :=
      isCoprime_of_common_prime_eq_nineteen hsupport
        (fun h => h19R h.1)
    obtain ⟨q, hq⟩ :=
      Int.eq_pow_of_mul_eq_pow_odd_left hcopRS
        (show Odd 3 by decide) hprod
    exact ⟨q, Or.inl hq⟩

/-- The rational flex function on the good model has exactly one of the
three candidate cubeclasses `1`, `19`, and `19²`. -/
theorem good_alpha_cubeclass {x y : ℚ} (h : OnGood x y) :
    ∃ r : ℚ,
      y - (8 * x + 76) = r ^ 3 ∨
      y - (8 * x + 76) = 19 * r ^ 3 ∨
      y - (8 * x + 76) = 361 * r ^ 3 := by
  obtain ⟨M, D, R, S, hDpos, hcop, _hx, halpha, hprod, hlin⟩ :=
    good_flex_integral_model h
  obtain ⟨q, hq | hq | hq⟩ :=
    flex_factor_cubeclass hcop hprod hlin
  all_goals
    refine ⟨2 * (q : ℚ) / (D : ℚ), ?_⟩
  · left
    rw [halpha, hq]
    push_cast
    field_simp [Int.cast_ne_zero.mpr (ne_of_gt hDpos)]
    ring
  · right; left
    rw [halpha, hq]
    push_cast
    field_simp [Int.cast_ne_zero.mpr (ne_of_gt hDpos)]
    ring
  · right; right
    rw [halpha, hq]
    push_cast
    field_simp [Int.cast_ne_zero.mpr (ne_of_gt hDpos)]
    ring

/-! ## Cubes and translation by the visible flexes -/

/-- A nonzero cube value of the flex function constructs an explicit
preimage under the dual degree-three isogeny. -/
theorem exists_dualThreeIsogeny_preimage_of_alpha_cube
    {x y r : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y)
    (hr : r ^ 3 = y - (8 * x + 76)) (hr0 : r ≠ 0) :
    ∃ Q : QuotientPoint,
      dualThreeIsogenyPoint Q =
        WeierstrassCurve.Affine.Point.some x y h := by
  have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
  have hy : y = r ^ 3 + 8 * x + 76 := by
    linarith
  have hrel : x ^ 3 = r ^ 3 * (r ^ 3 + 16 * x + 152) := by
    unfold OnGood at hcurve
    rw [hy] at hcurve
    linear_combination -hcurve
  let d : ℚ := 3 * x - 3 * r ^ 2 - 16 * r
  have hd : d ≠ 0 := by
    intro hd
    have hx : x = r ^ 2 + 16 * r / 3 := by
      dsimp [d] at hd
      linarith
    rw [hx] at hrel
    ring_nf at hrel
    apply hr0
    have : r ^ 3 = 0 := by
      linarith
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp this
  let s : ℚ := 24 * r / d
  let t : ℚ := 9 * s * r + 24 * s + 36
  have hs : s ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) hr0) hd
  have hquotient : OnQuotient s t := by
    unfold OnQuotient
    dsimp only [t, s]
    field_simp [hd]
    dsimp only [d]
    linear_combination 46656 * hrel
  have hxmap : dualThreeIsogenyX s = x := by
    unfold dualThreeIsogenyX
    dsimp only [s]
    field_simp [hd, hr0]
    dsimp only [d]
    linear_combination -46656 * hrel
  have hymap : dualThreeIsogenyY s t = y := by
    rw [hy]
    unfold dualThreeIsogenyY
    dsimp only [t, s]
    field_simp [hd, hr0]
    dsimp only [d]
    linear_combination
      10077696 * (-2 * r ^ 2 - 8 * r + x) * hrel
  have hquotientns :
      WeierstrassCurve.Affine.Nonsingular quotientCurve s t :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((quotientCurve_equation_iff s t).mpr hquotient)
  let Q : QuotientPoint :=
    WeierstrassCurve.Affine.Point.some s t hquotientns
  refine ⟨Q, ?_⟩
  rw [dualThreeIsogenyPoint_some_of_x_ne_zero hquotientns hs]
  change WeierstrassCurve.Affine.Point.some
      (dualThreeIsogenyX s) (dualThreeIsogenyY s t) _ =
    WeierstrassCurve.Affine.Point.some x y h
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hxmap, hymap⟩

/-- Translation by the positive visible flex multiplies the flex
function by the stated rational cube factor. -/
theorem add_goodT_alpha_identity {x y : ℚ} (hx : x ≠ 0)
    (hcurve : OnGood x y) :
    let L := WeierstrassCurve.Affine.slope goodCurve x 0 y 76
    let X := WeierstrassCurve.Affine.addX goodCurve x 0 L
    let Y := WeierstrassCurve.Affine.addY goodCurve x 0 y L
    Y - (8 * X + 76) =
      -23104 * (y - (8 * x + 76)) / x ^ 3 := by
  dsimp
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX goodCurve
  field_simp [hx]
  unfold OnGood at hcurve
  linear_combination -(x ^ 3) * (8 * x + y - 228) * hcurve

/-- Translation by the negative visible flex transforms the conjugate
factor by the stated rational cube factor. -/
theorem add_goodTNeg_alpha_identity {x y : ℚ} (hx : x ≠ 0)
    (hcurve : OnGood x y) :
    let L := WeierstrassCurve.Affine.slope goodCurve x 0 y (-76)
    let X := WeierstrassCurve.Affine.addX goodCurve x 0 L
    let Y := WeierstrassCurve.Affine.addY goodCurve x 0 y L
    Y - (8 * X + 76) =
      -152 * (y + (8 * x + 76)) ^ 2 / x ^ 3 := by
  dsimp
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX goodCurve
  field_simp [hx]
  unfold OnGood at hcurve
  linear_combination -(x ^ 3) * (8 * x + y + 76) * hcurve

end

end MazurProof.XDelta19GoodDescent

end

-- ===== shim: the Eisenstein three-isogeny descent, from the platform node =====
section
open MazurProof.XDelta19GoodModel MazurProof.XDelta19GoodIsogeny in
theorem MazurProof.XDelta19GoodDualDescent.quotient_affine_has_threeIsogeny_preimage {s t : ℚ}
    (hquotient : OnQuotient s t) :
    ∃ x y : ℚ, x ≠ 0 ∧ OnGood x y ∧
      threeIsogenyX x = s ∧ threeIsogenyY x y = t := by
  obtain ⟨x, y, hx, hg, hs, ht⟩ :=
    MazurHuang.x19_good_quotient_three_isogeny_preimage s t hquotient
  exact ⟨x, y, hx, hg, hs, ht⟩
end

-- ===== FLT.Assumptions.MazurProof.XDelta19GoodDualDescent =====
section
/-!
# The complementary Eisenstein descent at level nineteen

The small quotient

`t² = s³ - 3(24s+12)²`

factors over the Eisenstein integers.  Primitive integral coordinates
show that the factor

`n - √(-3) d (24m+12d²)`

is a unit times a cube.  The two nontrivial unit classes are excluded by
finite certificates modulo `27`.  Expanding the remaining cube gives an
explicit preimage under the forward degree-three isogeny.
-/

namespace MazurProof.XDelta19GoodDualDescent

open scoped NumberField

open UniqueFactorizationMonoid
open MazurProof.RationalPointsX135
open MazurProof.XDelta19GoodModel
open MazurProof.XDelta19GoodIsogeny

noncomputable section

/-! ## Primitive integral quotient coordinates -/

/-! ## Separation of conjugate prime factors -/

/-! ## Cube extraction and the unit classes -/

/-! ## Finite exclusion of the two nontrivial unit classes -/

/-! ## Explicit recovery of a preimage -/

/-- The forward degree-three isogeny is surjective on rational points of
the small quotient. -/
theorem threeIsogenyPoint_surjective (Q : QuotientPoint) :
    ∃ P : GoodPoint, threeIsogenyPoint P = Q := by
  cases Q with
  | zero => exact ⟨0, threeIsogenyPoint_zero⟩
  | some s t h =>
      have hquotient : OnQuotient s t :=
        (quotientCurve_equation_iff s t).mp h.1
      obtain ⟨x, y, hx, hgood, hX, hY⟩ :=
        quotient_affine_has_threeIsogeny_preimage hquotient
      have hns : WeierstrassCurve.Affine.Nonsingular goodCurve x y :=
        WeierstrassCurve.Affine.equation_iff_nonsingular.mp
          ((goodCurve_equation_iff x y).mpr hgood)
      refine ⟨WeierstrassCurve.Affine.Point.some x y hns, ?_⟩
      rw [threeIsogenyPoint_some_of_x_ne_zero hns hx]
      change WeierstrassCurve.Affine.Point.some
          (threeIsogenyX x) (threeIsogenyY x y) _ =
        WeierstrassCurve.Affine.Point.some s t h
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hX, hY⟩

end

end MazurProof.XDelta19GoodDualDescent

end

-- ===== FLT.Assumptions.MazurProof.XDelta19GoodWeakDescent =====
section
/-!
# Weak three-descent on the good conductor-nineteen model

The flex function has cubeclass `1`, `19`, or `19²`.  Translation by the
two visible rational flexes converts the latter two cases to the cube
case.  Surjectivity of the complementary isogeny and the verified
dual-forward composition then show that every rational point is a
threefold multiple up to one of the two nonzero visible three-torsion
points.
-/

namespace MazurProof.XDelta19GoodWeakDescent

open MazurProof.XDelta19GoodModel
open MazurProof.XDelta19GoodIsogeny
open MazurProof.XDelta19GoodDescent
open MazurProof.XDelta19GoodDualDescent

noncomputable section

/-- Every rational point on the good model is a threefold multiple up to
one of the two visible rational three-torsion points. -/
theorem weak_three_descent (P : GoodPoint) :
    ∃ Q : GoodPoint,
      P = 3 • Q ∨ P = goodT + 3 • Q ∨ P = goodTNeg + 3 • Q := by
  cases P with
  | zero =>
      exact ⟨0, Or.inl (by rfl)⟩
  | some x y h =>
      have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
      by_cases hx : x = 0
      · have hySq : y ^ 2 = (76 : ℚ) ^ 2 := by
          rw [hx] at hcurve
          norm_num [OnGood] at hcurve ⊢
          exact hcurve
        rcases eq_or_eq_neg_of_sq_eq_sq y 76 hySq with hy | hy
        · refine ⟨0, Or.inr (Or.inl ?_)⟩
          change WeierstrassCurve.Affine.Point.some x y h =
            goodT + 3 • 0
          simp only [nsmul_zero, add_zero]
          rw [goodT, WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨hx, hy⟩
        · refine ⟨0, Or.inr (Or.inr ?_)⟩
          change WeierstrassCurve.Affine.Point.some x y h =
            goodTNeg + 3 • 0
          simp only [nsmul_zero, add_zero]
          rw [goodTNeg, WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨hx, hy⟩
      · have hab :
            (y - (8 * x + 76)) * (y + (8 * x + 76)) = x ^ 3 := by
          calc
            (y - (8 * x + 76)) * (y + (8 * x + 76)) =
                y ^ 2 - (8 * x + 76) ^ 2 := by ring
            _ = x ^ 3 := by rw [hcurve]; ring
        obtain ⟨r, halpha | halpha | halpha⟩ :=
          good_alpha_cubeclass hcurve
        · have hr : r ≠ 0 := by
            intro hr0
            rw [hr0] at halpha
            norm_num at halpha
            apply hx
            have hx3 : x ^ 3 = 0 := by
              rw [← hab, halpha]
              ring
            exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hx3
          obtain ⟨Qd, hQd⟩ :=
            exists_dualThreeIsogeny_preimage_of_alpha_cube
              h halpha.symm hr
          obtain ⟨Q, hQ⟩ := threeIsogenyPoint_surjective Qd
          refine ⟨Q, Or.inl ?_⟩
          calc
            WeierstrassCurve.Affine.Point.some x y h =
                dualThreeIsogenyPoint Qd := hQd.symm
            _ = dualThreeIsogenyPoint (threeIsogenyPoint Q) := by
              rw [hQ]
            _ = 3 • Q := dual_comp_threeIsogenyPoint Q
        · have hr : r ≠ 0 := by
            intro hr0
            rw [hr0] at halpha
            norm_num at halpha
            apply hx
            have hx3 : x ^ 3 = 0 := by
              rw [← hab, halpha]
              ring
            exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hx3
          let L :=
            WeierstrassCurve.Affine.slope goodCurve x 0 y 76
          let X :=
            WeierstrassCurve.Affine.addX goodCurve x 0 L
          let Y :=
            WeierstrassCurve.Affine.addY goodCurve x 0 y L
          let hns :
              WeierstrassCurve.Affine.Nonsingular goodCurve X Y :=
            WeierstrassCurve.Affine.nonsingular_add h goodT_nonsingular
              (fun hxy => hx hxy.1)
          let Pplus : GoodPoint :=
            WeierstrassCurve.Affine.Point.some X Y hns
          have hPplus :
              (WeierstrassCurve.Affine.Point.some x y h : GoodPoint) +
                  goodT = Pplus := by
            rw [goodT]
            exact WeierstrassCurve.Affine.Point.add_of_X_ne hx
          let rp : ℚ := -76 * r / x
          have hrp : rp ≠ 0 :=
            div_ne_zero (mul_ne_zero (by norm_num) hr) hx
          have halphaP : rp ^ 3 = Y - (8 * X + 76) := by
            symm
            have hid := add_goodT_alpha_identity hx hcurve
            change Y - (8 * X + 76) =
              -23104 * (y - (8 * x + 76)) / x ^ 3 at hid
            rw [hid, halpha]
            dsimp [rp]
            field_simp [hx]
            ring
          obtain ⟨Qd, hQd⟩ :=
            exists_dualThreeIsogeny_preimage_of_alpha_cube
              hns halphaP hrp
          obtain ⟨Q, hQ⟩ := threeIsogenyPoint_surjective Qd
          have hthree : Pplus = 3 • Q := by
            calc
              Pplus = dualThreeIsogenyPoint Qd := hQd.symm
              _ = dualThreeIsogenyPoint (threeIsogenyPoint Q) := by
                rw [hQ]
              _ = 3 • Q := dual_comp_threeIsogenyPoint Q
          have hsum :
              (WeierstrassCurve.Affine.Point.some x y h : GoodPoint) +
                  goodT = 3 • Q :=
            hPplus.trans hthree
          refine ⟨Q, Or.inr (Or.inr ?_)⟩
          rw [goodTNeg_eq_neg]
          calc
            WeierstrassCurve.Affine.Point.some x y h =
                -goodT +
                  ((WeierstrassCurve.Affine.Point.some x y h : GoodPoint) +
                    goodT) := by abel
            _ = -goodT + 3 • Q := by rw [hsum]
        · have hr : r ≠ 0 := by
            intro hr0
            rw [hr0] at halpha
            norm_num at halpha
            apply hx
            have hx3 : x ^ 3 = 0 := by
              rw [← hab, halpha]
              ring
            exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hx3
          let L :=
            WeierstrassCurve.Affine.slope goodCurve x 0 y (-76)
          let X :=
            WeierstrassCurve.Affine.addX goodCurve x 0 L
          let Y :=
            WeierstrassCurve.Affine.addY goodCurve x 0 y L
          let hns :
              WeierstrassCurve.Affine.Nonsingular goodCurve X Y :=
            WeierstrassCurve.Affine.nonsingular_add h goodTNeg_nonsingular
              (fun hxy => hx hxy.1)
          let Pplus : GoodPoint :=
            WeierstrassCurve.Affine.Point.some X Y hns
          have hPplus :
              (WeierstrassCurve.Affine.Point.some x y h : GoodPoint) +
                  goodTNeg = Pplus := by
            rw [goodTNeg]
            exact WeierstrassCurve.Affine.Point.add_of_X_ne hx
          let rp : ℚ := -2 * x / (19 * r ^ 2)
          have hrp : rp ≠ 0 := by
            exact div_ne_zero (mul_ne_zero (by norm_num) hx)
              (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr))
          have halphaP : rp ^ 3 = Y - (8 * X + 76) := by
            symm
            have hid := add_goodTNeg_alpha_identity hx hcurve
            change Y - (8 * X + 76) =
              -152 * (y + (8 * x + 76)) ^ 2 / x ^ 3 at hid
            rw [hid]
            have hbeta :
                y + (8 * x + 76) = x ^ 3 / (361 * r ^ 3) := by
              apply (eq_div_iff
                (mul_ne_zero (by norm_num) (pow_ne_zero 3 hr))).2
              rw [← hab, halpha]
              ring
            rw [hbeta]
            dsimp [rp]
            field_simp [hx, hr]
            ring
          obtain ⟨Qd, hQd⟩ :=
            exists_dualThreeIsogeny_preimage_of_alpha_cube
              hns halphaP hrp
          obtain ⟨Q, hQ⟩ := threeIsogenyPoint_surjective Qd
          have hthree : Pplus = 3 • Q := by
            calc
              Pplus = dualThreeIsogenyPoint Qd := hQd.symm
              _ = dualThreeIsogenyPoint (threeIsogenyPoint Q) := by
                rw [hQ]
              _ = 3 • Q := dual_comp_threeIsogenyPoint Q
          have hsum :
              (WeierstrassCurve.Affine.Point.some x y h : GoodPoint) +
                  goodTNeg = 3 • Q :=
            hPplus.trans hthree
          refine ⟨Q, Or.inr (Or.inl ?_)⟩
          rw [goodTNeg_eq_neg] at hsum
          calc
            WeierstrassCurve.Affine.Point.some x y h =
                goodT +
                  ((WeierstrassCurve.Affine.Point.some x y h : GoodPoint) -
                    goodT) := by abel
            _ = goodT + 3 • Q := by
              congr 1

end

end MazurProof.XDelta19GoodWeakDescent

end

-- ===== FLT.PortCompat =====
section
/-! Compatibility shims for porting to the platform Mathlib pin. -/

/-- The former hypothesis-taking form of `padicValRat.pow`. -/
theorem padicValRat.pow_of_ne_zero {p : ℕ} [Fact p.Prime] {q : ℚ} (_hq : q ≠ 0) {k : ℕ} :
    padicValRat p (q ^ k) = k * padicValRat p q :=
  padicValRat.pow q

end

-- ===== FLT.Assumptions.MazurProof.XDelta19GoodFormalCore =====
section
/-!
# The three-adic formal core for the good level-nineteen model

This file defines the formal-kernel filtration at three and proves that
tripling raises its level by one.  The proof uses exact rational
coordinates for the verified dual-forward composition.  It also packages
the separatedness argument and connects it to the weak three-descent.

The only input left to the reduction file is that `6P` belongs to this
formal kernel for every rational point `P`; the factor six is the order of
the good special fibre over `𝔽₃`.
-/

namespace MazurProof.XDelta19GoodFormalCore

open MazurProof.XDelta19GoodModel
open MazurProof.XDelta19GoodIsogeny
open MazurProof.XDelta19GoodWeakDescent

noncomputable section

/-! ## Rational coordinates of tripling -/

/-- The common denominator in the affine tripling formulas. -/
def tripleDen (x : ℚ) : ℚ :=
  x * (3 * x + 76) * (x ^ 2 + 60 * x + 912)

/-- The numerator of the horizontal tripling coordinate. -/
def tripleXNum (x : ℚ) : ℚ :=
  x ^ 9 - 14592 * x ^ 7 - 1177088 * x ^ 6 -
    35487744 * x ^ 5 - 168566784 * x ^ 4 +
    15985750016 * x ^ 3 + 409954418688 * x ^ 2 +
    3894566977536 * x + 12332795428864

/-- The factored numerator of the vertical tripling coordinate. -/
def tripleYNum (x y : ℚ) : ℚ :=
  y * (x ^ 3 - 2432 * x - 46208) *
    (x ^ 3 + 76 * x ^ 2 + 2128 * x + 23104) *
    (x ^ 6 + 180 * x ^ 5 + 13376 * x ^ 4 +
      516800 * x ^ 3 + 10905088 * x ^ 2 +
      119401472 * x + 533794816)

/-- The tripling denominator does not vanish away from the visible
three-torsion kernel. -/
theorem tripleDen_ne_zero {x y : ℚ} (hx : x ≠ 0)
    (h : OnGood x y) :
    tripleDen x ≠ 0 := by
  have hquad : x ^ 2 + 60 * x + 912 ≠ 0 := by
    nlinarith [sq_nonneg (x + 30)]
  have hlin : 3 * x + 76 ≠ 0 := by
    intro hlin
    have hxval : x = -76 / 3 := by
      linarith
    rw [hxval] at h
    norm_num [OnGood] at h
    nlinarith [sq_nonneg y]
  exact mul_ne_zero (mul_ne_zero hx hlin) hquad

/-- The forward horizontal isogeny coordinate is the tripling
denominator in factored form. -/
private theorem threeIsogenyX_eq_den (x : ℚ) (hx : x ≠ 0) :
    threeIsogenyX x = 3 * tripleDen x / x ^ 3 := by
  unfold threeIsogenyX tripleDen
  field_simp [hx]
  ring

/-- The forward vertical isogeny coordinate has the displayed cubic
factor. -/
private theorem threeIsogenyY_eq_factor (x y : ℚ) (hx : x ≠ 0) :
    threeIsogenyY x y =
      27 * y * (x ^ 3 - 2432 * x - 46208) / x ^ 3 := by
  unfold threeIsogenyY
  field_simp [hx]
  ring

set_option maxHeartbeats 0 in
/-- The verified dual-forward composition has the displayed horizontal
rational function. -/
theorem tripleX_formula {x y : ℚ} (hx : x ≠ 0)
    (h : OnGood x y) :
    dualThreeIsogenyX (threeIsogenyX x) =
      tripleXNum x / tripleDen x ^ 2 := by
  have hd := tripleDen_ne_zero hx h
  rw [threeIsogenyX_eq_den x hx]
  unfold dualThreeIsogenyX tripleXNum
  field_simp [hx, hd]
  unfold tripleDen
  ring

set_option maxHeartbeats 0 in
/-- The verified dual-forward composition has the displayed vertical
rational function. -/
theorem tripleY_formula {x y : ℚ} (hx : x ≠ 0)
    (h : OnGood x y) :
    dualThreeIsogenyY (threeIsogenyX x) (threeIsogenyY x y) =
      tripleYNum x y / tripleDen x ^ 3 := by
  have hd := tripleDen_ne_zero hx h
  rw [threeIsogenyX_eq_den x hx, threeIsogenyY_eq_factor x y hx]
  unfold dualThreeIsogenyY tripleYNum
  field_simp [hx, hd]
  unfold tripleDen
  ring

/-! ## Valuation helpers -/

/-- The three-adic valuation of an integer is nonnegative. -/
theorem val_int_nonneg (z : ℤ) :
    0 ≤ padicValRat 3 (z : ℚ) := by
  rw [padicValRat.of_int]
  exact Int.natCast_nonneg _

/-- In a sum of unequal valuations, the term of smaller valuation
controls the sum. -/
theorem val_add_eq_left_of_lt {a b : ℚ} (ha : a ≠ 0)
    (hval : padicValRat 3 a < padicValRat 3 b) :
    padicValRat 3 (a + b) = padicValRat 3 a := by
  by_cases hb : b = 0
  · simp [hb]
  have hab : a + b ≠ 0 := by
    intro hzero
    have hba : b = -a := by
      linarith
    have : padicValRat 3 b = padicValRat 3 a := by
      rw [hba, padicValRat.neg]
    omega
  exact padicValRat.add_eq_of_lt hab ha hb hval

/-- A finite sum of terms of valuation larger than `q` is zero or still
has valuation larger than `q`. -/
theorem val_sum_gt_or_zero {q : ℚ} (l : List ℚ)
    (hgt : ∀ a ∈ l, padicValRat 3 q < padicValRat 3 a) :
    l.sum = 0 ∨ padicValRat 3 q < padicValRat 3 l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : padicValRat 3 q < padicValRat 3 a :=
        hgt a (by simp)
      have htail : ∀ b ∈ l, padicValRat 3 q < padicValRat 3 b := by
        intro b hb
        exact hgt b (by simp [hb])
      rcases ih htail with hzero | htailgt
      · right
        simpa [hzero] using ha
      · by_cases hs : a + l.sum = 0
        · exact Or.inl (by simpa using hs)
        · exact Or.inr (padicValRat.lt_add_of_lt hs ha htailgt)

/-- Adding terms of strictly larger valuation does not change the
valuation of a nonzero leading term. -/
theorem val_add_list_eq {q : ℚ} (l : List ℚ) (hq : q ≠ 0)
    (hgt : ∀ a ∈ l, padicValRat 3 q < padicValRat 3 a) :
    padicValRat 3 (q + l.sum) = padicValRat 3 q := by
  rcases val_sum_gt_or_zero l hgt with hzero | hsum
  · simp [hzero]
  · exact val_add_eq_left_of_lt hq hsum

/-- The valuation of an integral-coefficient monomial is bounded below
by the valuations of its variables. -/
theorem val_monomial_ge
    {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (c : ℤ) (hc : c ≠ 0) (a b : ℕ) :
    (a : ℤ) * padicValRat 3 x + (b : ℤ) * padicValRat 3 y ≤
      padicValRat 3 ((c : ℚ) * x ^ a * y ^ b) := by
  rw [padicValRat.mul
      (mul_ne_zero (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx))
      (pow_ne_zero b hy),
    padicValRat.mul (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx),
    padicValRat.pow_of_ne_zero hx, padicValRat.pow_of_ne_zero hy]
  have hcval := val_int_nonneg c
  omega

/-- A monic polynomial at a negative-valuation argument is controlled by
its highest-degree term when every other degree is smaller. -/
theorem val_leading_poly {x y : ℚ} {k : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hvx : padicValRat 3 x = -2 * k)
    (n : ℕ) (l : List (ℤ × ℕ))
    (hval : ∀ cb ∈ l,
      -2 * (n : ℤ) * k < -2 * (cb.2 : ℤ) * k)
    (hcoeff : ∀ cb ∈ l, cb.1 ≠ 0) :
    padicValRat 3
        (x ^ n +
          (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum) =
      -2 * (n : ℤ) * k := by
  rw [val_add_list_eq (q := x ^ n)]
  · rw [padicValRat.pow_of_ne_zero hx, hvx]
    ring
  · exact pow_ne_zero n hx
  · intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨cb, hcb, rfl⟩ := hz
    have hge := val_monomial_ge hx hy cb.1
      (hcoeff cb hcb) cb.2 0
    rw [hvx] at hge
    have hlead : padicValRat 3 (x ^ n) =
        -2 * (n : ℤ) * k := by
      rw [padicValRat.pow_of_ne_zero hx, hvx]
      ring
    rw [hlead]
    norm_num at hge ⊢
    have hge' : -2 * (cb.2 : ℤ) * k ≤
        padicValRat 3 ((cb.1 : ℚ) * x ^ cb.2) := by
      convert hge using 1
      ring
    rw [show -(2 * (n : ℤ) * k) = -2 * (n : ℤ) * k by ring]
    exact (hval cb hcb).trans_le hge'

/-! ## Valuations of the tripling coordinates -/

/-- The tripling denominator has valuation `1-8k` at formal level `k`. -/
private theorem tripleDen_val {x y : ℚ} {k : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hcurve : OnGood x y)
    (hvx : padicValRat 3 x = -2 * k) :
    padicValRat 3 (tripleDen x) = 1 - 8 * k := by
  have hlin : 3 * x + 76 ≠ 0 := by
    intro hz
    apply tripleDen_ne_zero hx hcurve
    unfold tripleDen
    rw [hz]
    ring
  have hv3x : padicValRat 3 (3 * x) = 1 - 2 * k := by
    have hthree : padicValRat 3 (3 : ℚ) = 1 :=
      padicValRat.self (p := 3) (by norm_num)
    rw [padicValRat.mul (by norm_num) hx, hthree, hvx]
    ring
  have hvlin : padicValRat 3 (3 * x + 76) = 1 - 2 * k := by
    rw [val_add_eq_left_of_lt (a := 3 * x) (b := 76)
      (mul_ne_zero (by norm_num) hx) (by
        rw [hv3x]
        have h76 : 0 ≤ padicValRat 3 (76 : ℚ) := by
          simpa using val_int_nonneg 76
        omega), hv3x]
  have hquad : x ^ 2 + 60 * x + 912 ≠ 0 := by
    nlinarith [sq_nonneg (x + 30)]
  have hvquad :
      padicValRat 3 (x ^ 2 + 60 * x + 912) = -4 * k := by
    have hshape : x ^ 2 + 60 * x + 912 =
        x ^ 2 + [60 * x, (912 : ℚ)].sum := by
      simp
      ring
    rw [hshape, val_add_list_eq (q := x ^ 2)]
    · rw [padicValRat.pow_of_ne_zero hx, hvx]
      ring
    · exact pow_ne_zero 2 hx
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · have hge := val_monomial_ge hx hy 60 (by norm_num) 1 0
        rw [padicValRat.pow_of_ne_zero hx, hvx]
        norm_num at hge ⊢
        omega
      · have hge := val_int_nonneg 912
        rw [padicValRat.pow_of_ne_zero hx, hvx]
        norm_num at hge ⊢
        omega
  unfold tripleDen
  rw [padicValRat.mul (mul_ne_zero hx hlin) hquad,
    padicValRat.mul hx hlin, hvx, hvlin, hvquad]
  ring

/-- The horizontal tripling numerator has valuation `-18k`. -/
private theorem tripleXNum_val {x y : ℚ} {k : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 3 x = -2 * k) :
    padicValRat 3 (tripleXNum x) = -18 * k := by
  let l : List (ℤ × ℕ) :=
    [(-14592, 7), (-1177088, 6), (-35487744, 5),
      (-168566784, 4), (15985750016, 3),
      (409954418688, 2), (3894566977536, 1),
      (12332795428864, 0)]
  have h := val_leading_poly hx hy hvx 9 l
    (by
      intro cb hcb
      simp [l] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num <;> omega)
    (by
      intro cb hcb
      simp [l] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num)
  convert h using 1
  · simp [l, tripleXNum]
    ring
  · ring

/-- The vertical tripling numerator has valuation `-27k`. -/
private theorem tripleYNum_val {x y : ℚ} {k : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 3 x = -2 * k)
    (hvy : padicValRat 3 y = -3 * k) :
    padicValRat 3 (tripleYNum x y) = -27 * k := by
  let l1 : List (ℤ × ℕ) := [(-2432, 1), (-46208, 0)]
  let l2 : List (ℤ × ℕ) := [(76, 2), (2128, 1), (23104, 0)]
  let l3 : List (ℤ × ℕ) :=
    [(180, 5), (13376, 4), (516800, 3), (10905088, 2),
      (119401472, 1), (533794816, 0)]
  have hv1 :
      padicValRat 3 (x ^ 3 - 2432 * x - 46208) = -6 * k := by
    have h := val_leading_poly hx hy hvx 3 l1
      (by
        intro cb hcb
        simp [l1] at hcb
        rcases hcb with rfl | rfl <;> norm_num <;> omega)
      (by
        intro cb hcb
        simp [l1] at hcb
        rcases hcb with rfl | rfl <;> norm_num)
    convert h using 1
    · simp [l1]
      ring
    · ring
  have hv2 :
      padicValRat 3
        (x ^ 3 + 76 * x ^ 2 + 2128 * x + 23104) = -6 * k := by
    have h := val_leading_poly hx hy hvx 3 l2
      (by
        intro cb hcb
        simp [l2] at hcb
        rcases hcb with rfl | rfl | rfl <;> norm_num <;> omega)
      (by
        intro cb hcb
        simp [l2] at hcb
        rcases hcb with rfl | rfl | rfl <;> norm_num)
    convert h using 1
    · simp [l2]
      ring
    · ring
  have hv3 :
      padicValRat 3
        (x ^ 6 + 180 * x ^ 5 + 13376 * x ^ 4 +
          516800 * x ^ 3 + 10905088 * x ^ 2 +
          119401472 * x + 533794816) = -12 * k := by
    have h := val_leading_poly hx hy hvx 6 l3
      (by
        intro cb hcb
        simp [l3] at hcb
        rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl <;>
          norm_num <;> omega)
      (by
        intro cb hcb
        simp [l3] at hcb
        rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl <;>
          norm_num)
    convert h using 1
    · simp [l3]
      ring
    · ring
  have hf1 : x ^ 3 - 2432 * x - 46208 ≠ 0 := by
    intro hz
    rw [hz, padicValRat.zero] at hv1
    omega
  have hf2 : x ^ 3 + 76 * x ^ 2 + 2128 * x + 23104 ≠ 0 := by
    intro hz
    rw [hz, padicValRat.zero] at hv2
    omega
  have hf3 :
      x ^ 6 + 180 * x ^ 5 + 13376 * x ^ 4 +
        516800 * x ^ 3 + 10905088 * x ^ 2 +
        119401472 * x + 533794816 ≠ 0 := by
    intro hz
    rw [hz, padicValRat.zero] at hv3
    omega
  unfold tripleYNum
  rw [padicValRat.mul
      (mul_ne_zero (mul_ne_zero hy hf1) hf2) hf3,
    padicValRat.mul (mul_ne_zero hy hf1) hf2,
    padicValRat.mul hy hf1, hvy, hv1, hv2, hv3]
  ring

/-! ## The formal filtration and tripling -/

/-- Membership in the formal kernel at three, expressed by affine
coordinate valuations. -/
def FormalAtThree : GoodPoint → Prop
  | .zero => True
  | .some x y _ =>
      ∃ k : ℤ, 0 < k ∧
        padicValRat 3 x = -2 * k ∧
        padicValRat 3 y = -3 * k

/-- The exact positive level of a nonzero formal point. -/
def FormalLevel : GoodPoint → ℤ → Prop
  | .zero, _ => False
  | .some x y _, k =>
      0 < k ∧ padicValRat 3 x = -2 * k ∧
        padicValRat 3 y = -3 * k

/-- Formal-kernel membership is zero or membership at a unique positive
level. -/
theorem FormalAtThree_iff (P : GoodPoint) :
    FormalAtThree P ↔ P = 0 ∨ ∃ k : ℤ, FormalLevel P k := by
  cases P with
  | zero =>
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        trivial
  | some x y h =>
      simp only [FormalAtThree, FormalLevel,
        WeierstrassCurve.Affine.Point.some_ne_zero, false_or]

/-- Tripling raises the exact formal level by one. -/
theorem FormalLevel_triple {P : GoodPoint} {k : ℤ}
    (hP : FormalLevel P k) :
    FormalLevel (3 • P) (k + 1) := by
  cases P with
  | zero => simp [FormalLevel] at hP
  | some x y h =>
      rcases hP with ⟨hk, hvx, hvy⟩
      have hcurve : OnGood x y :=
        (goodCurve_equation_iff x y).mp h.1
      have hx : x ≠ 0 := by
        intro hx0
        rw [hx0, padicValRat.zero] at hvx
        omega
      have hy : y ≠ 0 := by
        intro hy0
        rw [hy0, padicValRat.zero] at hvy
        omega
      have hdval := tripleDen_val hx hy hk hcurve hvx
      have hXval := tripleXNum_val hx hy hk hvx
      have hYval := tripleYNum_val hx hy hk hvx hvy
      have hd : tripleDen x ≠ 0 := tripleDen_ne_zero hx hcurve
      have hX : tripleXNum x ≠ 0 := by
        intro hz
        rw [hz, padicValRat.zero] at hXval
        omega
      have hY : tripleYNum x y ≠ 0 := by
        intro hz
        rw [hz, padicValRat.zero] at hYval
        omega
      have hphi := threeIsogenyX_ne_zero hx hcurve
      have hcomp := dual_comp_threeIsogenyPoint
        (WeierstrassCurve.Affine.Point.some x y h : GoodPoint)
      rw [threeIsogenyPoint_some_of_x_ne_zero h hx] at hcomp
      unfold WeierstrassCurve.Affine.Point.mk at hcomp
      rw [dualThreeIsogenyPoint_some_of_x_ne_zero _ hphi] at hcomp
      rw [← hcomp]
      change 0 < k + 1 ∧
        padicValRat 3
          (dualThreeIsogenyX (threeIsogenyX x)) = -2 * (k + 1) ∧
        padicValRat 3
          (dualThreeIsogenyY
            (threeIsogenyX x) (threeIsogenyY x y)) =
              -3 * (k + 1)
      refine ⟨by omega, ?_, ?_⟩
      · rw [tripleX_formula hx hcurve,
          padicValRat.div hX (pow_ne_zero 2 hd), hXval,
          padicValRat.pow_of_ne_zero hd, hdval]
        ring
      · rw [tripleY_formula hx hcurve,
          padicValRat.div hY (pow_ne_zero 3 hd), hYval,
          padicValRat.pow_of_ne_zero hd, hdval]
        ring

/-- Tripling preserves the formal kernel and raises nonzero points one
level. -/
theorem FormalAtThree_triple {P : GoodPoint}
    (hP : FormalAtThree P) :
    FormalAtThree (3 • P) := by
  rw [FormalAtThree_iff] at hP ⊢
  rcases hP with rfl | ⟨k, hk⟩
  · simp
  · exact Or.inr ⟨k + 1, FormalLevel_triple hk⟩

/-! ## Separatedness and weak descent -/

/-- A nonzero point has at most one exact formal level. -/
private theorem FormalLevel_unique {P : GoodPoint} {k l : ℤ}
    (hk : FormalLevel P k) (hl : FormalLevel P l) :
    k = l := by
  cases P with
  | zero => simp [FormalLevel] at hk
  | some x y h =>
      rcases hk with ⟨_, hxk, _⟩
      rcases hl with ⟨_, hxl, _⟩
      omega

/-- Multiplication by `3^n` raises a formal level by exactly `n`. -/
theorem FormalLevel_three_power {P : GoodPoint} {k : ℤ}
    (hP : FormalLevel P k) (n : ℕ) :
    ∃ k' : ℤ, k' = k + (n : ℤ) ∧
      FormalLevel ((3 ^ n : ℕ) • P) k' := by
  induction n with
  | zero =>
      exact ⟨k, by simp, by simpa using hP⟩
  | succ n ih =>
      obtain ⟨l, hl, hlevel⟩ := ih
      have hpow : (3 ^ (n + 1) : ℕ) • P =
          3 • ((3 ^ n : ℕ) • P) := by
        rw [pow_succ, mul_nsmul]
      refine ⟨l + 1, by norm_num at hl ⊢; omega, ?_⟩
      rw [hpow]
      exact FormalLevel_triple hlevel

/-- A formal point divisible through formal points by every power of
three is zero. -/
theorem formal_separated (P : GoodPoint)
    (hP : FormalAtThree P)
    (hdiv : ∀ n : ℕ, ∃ Q : GoodPoint,
      FormalAtThree Q ∧ P = (3 ^ n : ℕ) • Q) :
    P = 0 := by
  by_contra hP0
  have hlevelP : ∃ k : ℤ, FormalLevel P k := by
    rw [FormalAtThree_iff] at hP
    exact hP.resolve_left hP0
  obtain ⟨k, hk⟩ := hlevelP
  have hkpos : 0 < k := by
    cases P with
    | zero => exact (hP0 rfl).elim
    | some x y h => exact hk.1
  let n : ℕ := k.toNat + 1
  obtain ⟨Q, hQformal, hPQ⟩ := hdiv n
  have hQ0 : Q ≠ 0 := by
    intro hzero
    rw [hzero, nsmul_zero] at hPQ
    exact hP0 hPQ
  have hlevelQ : ∃ l : ℤ, FormalLevel Q l := by
    rw [FormalAtThree_iff] at hQformal
    exact hQformal.resolve_left hQ0
  obtain ⟨l, hl⟩ := hlevelQ
  obtain ⟨l', hl', hlevel⟩ := FormalLevel_three_power hl n
  have hlevelP' : FormalLevel P l' := by
    rw [hPQ]
    exact hlevel
  have heq : l' = k := FormalLevel_unique hlevelP' hk
  have hkNat : (k.toNat : ℤ) = k :=
    Int.toNat_of_nonneg (le_of_lt hkpos)
  have hncast : (n : ℤ) = k + 1 := by
    dsimp [n]
    rw [hkNat]
  have hlpos : 0 < l := by
    cases Q with
    | zero => simp [FormalLevel] at hl
    | some x y h => exact hl.1
  omega

/-- Weak three-descent makes `3P` divisible by every power of three. -/
theorem three_nsmul_three_power_divisible
    (P : GoodPoint) (n : ℕ) :
    ∃ Q : GoodPoint,
      3 • P = (3 ^ n : ℕ) • (3 • Q) := by
  induction n with
  | zero =>
      exact ⟨P, by simp⟩
  | succ n ih =>
      obtain ⟨Q, hQ⟩ := ih
      obtain ⟨R, hR | hR | hR⟩ := weak_three_descent Q
      all_goals
        have hthreeQ : 3 • Q = 3 • (3 • R) := by
          subst Q
          simp [nsmul_add]
        refine ⟨R, ?_⟩
        calc
          3 • P = (3 ^ n : ℕ) • (3 • Q) := hQ
          _ = (3 ^ n : ℕ) • (3 • (3 • R)) := by rw [hthreeQ]
          _ = (3 ^ (n + 1) : ℕ) • (3 • R) := by
            have hp : (3 ^ (n + 1) : ℕ) = 3 ^ n * 3 := by
              simp [pow_succ, Nat.mul_comm]
            rw [hp, mul_nsmul']

/-- Weak descent and formal entry of every `6P` imply that every rational
point is killed by six. -/
theorem six_nsmul_eq_zero
    (hentry : ∀ Q : GoodPoint, FormalAtThree (6 • Q))
    (P : GoodPoint) :
    6 • P = 0 := by
  apply formal_separated (6 • P) (hentry P)
  intro n
  obtain ⟨Q, hQ⟩ := three_nsmul_three_power_divisible P n
  refine ⟨6 • Q, hentry Q, ?_⟩
  calc
    6 • P = (2 * 3) • P := by norm_num
    _ = 2 • (3 • P) := mul_nsmul' P 2 3
    _ = 2 • ((3 ^ n : ℕ) • (3 • Q)) := by rw [hQ]
    _ = (2 * 3 ^ n) • (3 • Q) :=
      (mul_nsmul' (3 • Q) 2 (3 ^ n)).symm
    _ = (3 ^ n * 2) • (3 • Q) := by rw [Nat.mul_comm 2]
    _ = (3 ^ n : ℕ) • (2 • (3 • Q)) :=
      mul_nsmul' (3 • Q) (3 ^ n) 2
    _ = (3 ^ n : ℕ) • (6 • Q) := by
      rw [show 6 • Q = 2 • (3 • Q) by
        exact mul_nsmul' Q 2 3]

end

end MazurProof.XDelta19GoodFormalCore

end

-- ===== FLT.Assumptions.MazurProof.XDelta19GoodFormalReduction =====
section
/-!
# Reduction into the three-adic formal kernel at level nineteen

The good model has six points over `𝔽₃`.  An integral rational point
reduces to one of

`(0,±1)`, `(1,±1)`, `(2,0)`.

For the first two pairs, doubling has positive horizontal valuation and
unit vertical valuation, so a further tripling enters the formal kernel.
For `(2,0)`, doubling itself enters the formal kernel.  Points with
negative horizontal valuation are already formal.  Consequently `[6]P`
is formal for every rational point.
-/

namespace MazurProof.XDelta19GoodFormalReduction

open MazurProof.XDelta19GoodModel
open MazurProof.XDelta19GoodIsogeny
open MazurProof.XDelta19GoodFormalCore

noncomputable section

/-! ## Integral-or-formal dichotomy -/

/-- An integral coefficient does not lower the valuation of a monomial
in one rational variable. -/
private theorem val_x_monomial_ge
    {x : ℚ} (hx : x ≠ 0) (c : ℤ) (hc : c ≠ 0) (a : ℕ) :
    (a : ℤ) * padicValRat 3 x ≤
      padicValRat 3 ((c : ℚ) * x ^ a) := by
  rw [padicValRat.mul (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx),
    padicValRat.pow_of_ne_zero hx]
  have hcval := val_int_nonneg c
  omega

/-- Every rational affine point is either three-adically integral or
belongs to the formal kernel. -/
theorem formal_or_integral (P : GoodPoint) :
    FormalAtThree P ∨
      match P with
      | .zero => True
      | .some x y _ =>
          0 ≤ padicValRat 3 x ∧ 0 ≤ padicValRat 3 y := by
  cases P with
  | zero =>
      exact Or.inl trivial
  | some x y h =>
      have hE : OnGood x y := (goodCurve_equation_iff x y).mp h.1
      let vx := padicValRat 3 x
      let vy := padicValRat 3 y
      by_cases hxint : 0 ≤ vx
      · right
        refine ⟨hxint, ?_⟩
        by_contra hyint
        have hvyneg : vy < 0 := lt_of_not_ge hyint
        have hy : y ≠ 0 := by
          intro hy0
          dsimp [vy] at hvyneg
          rw [hy0, padicValRat.zero] at hvyneg
          omega
        let l : List ℚ :=
          [-(x ^ 3), -(64 * x ^ 2), -(1216 * x), (-5776 : ℚ)]
        have hshape : y ^ 2 + l.sum = 0 := by
          simp [l]
          unfold OnGood at hE
          linear_combination hE
        have hlead : padicValRat 3 (y ^ 2) = 2 * vy := by
          rw [padicValRat.pow_of_ne_zero hy]
          rfl
        have hgt : ∀ a ∈ l,
            padicValRat 3 (y ^ 2) < padicValRat 3 a := by
          intro a ha
          simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl
          · by_cases hx0 : x = 0
            · simp [hx0, hlead]
              omega
            · rw [padicValRat.neg, padicValRat.pow_of_ne_zero hx0, hlead]
              dsimp [vx, vy] at hxint hvyneg ⊢
              omega
          · by_cases hx0 : x = 0
            · simp [hx0, hlead]
              omega
            · have hge := val_x_monomial_ge hx0 64 (by norm_num) 2
              rw [padicValRat.neg, hlead]
              dsimp [vx, vy] at hxint hvyneg hge ⊢
              omega
          · by_cases hx0 : x = 0
            · simp [hx0, hlead]
              omega
            · have hge := val_x_monomial_ge hx0 1216 (by norm_num) 1
              rw [padicValRat.neg, hlead]
              dsimp [vx, vy] at hxint hvyneg hge ⊢
              norm_num at hge
              omega
          · have hge := val_int_nonneg (-5776)
            rw [hlead]
            norm_num at hge ⊢
            omega
        have hval := val_add_list_eq l (pow_ne_zero 2 hy) hgt
        rw [hshape, padicValRat.zero, hlead] at hval
        omega
      · have hvxneg : vx < 0 := lt_of_not_ge hxint
        have hx : x ≠ 0 := by
          intro hx0
          dsimp [vx] at hvxneg
          rw [hx0, padicValRat.zero] at hvxneg
          omega
        have hvylt : vy < vx := by
          by_contra hnot
          have hvxley : vx ≤ vy := le_of_not_gt hnot
          let l : List ℚ :=
            [y ^ 2, -(64 * x ^ 2), -(1216 * x), (-5776 : ℚ)]
          have hshape : -(x ^ 3) + l.sum = 0 := by
            simp [l]
            unfold OnGood at hE
            linear_combination hE
          have hlead : padicValRat 3 (-(x ^ 3)) = 3 * vx := by
            rw [padicValRat.neg, padicValRat.pow_of_ne_zero hx]
            rfl
          have hgt : ∀ a ∈ l,
              padicValRat 3 (-(x ^ 3)) < padicValRat 3 a := by
            intro a ha
            simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl | rfl
            · by_cases hy0 : y = 0
              · simp [hy0, hlead]
                omega
              · rw [padicValRat.pow_of_ne_zero hy0, hlead]
                dsimp [vx, vy] at hvxneg hvxley ⊢
                omega
            · have hge := val_x_monomial_ge hx 64 (by norm_num) 2
              simp only [padicValRat.neg]
              rw [padicValRat.pow_of_ne_zero hx]
              dsimp [vx] at hvxneg hge ⊢
              omega
            · have hge := val_x_monomial_ge hx 1216 (by norm_num) 1
              simp only [padicValRat.neg]
              rw [padicValRat.pow_of_ne_zero hx]
              dsimp [vx] at hvxneg hge ⊢
              norm_num at hge
              omega
            · have hge := val_int_nonneg (-5776)
              rw [hlead]
              norm_num at hge ⊢
              omega
          have hval := val_add_list_eq l
            (neg_ne_zero.mpr (pow_ne_zero 3 hx)) hgt
          rw [hshape, padicValRat.zero, hlead] at hval
          omega
        have hy : y ≠ 0 := by
          intro hy0
          dsimp [vx, vy] at hvylt
          rw [hy0, padicValRat.zero] at hvylt
          omega
        let l : List ℚ :=
          [64 * x ^ 2, 1216 * x, (5776 : ℚ)]
        have hshape : x ^ 3 + l.sum =
            x ^ 3 + 64 * x ^ 2 + 1216 * x + 5776 := by
          simp [l]
          ring
        have hgt : ∀ a ∈ l,
            padicValRat 3 (x ^ 3) < padicValRat 3 a := by
          intro a ha
          simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl
          · have hge := val_x_monomial_ge hx 64 (by norm_num) 2
            rw [padicValRat.pow_of_ne_zero hx]
            dsimp [vx] at hvxneg hge ⊢
            omega
          · have hge := val_x_monomial_ge hx 1216 (by norm_num) 1
            rw [padicValRat.pow_of_ne_zero hx]
            dsimp [vx] at hvxneg hge ⊢
            norm_num at hge
            omega
          · have hge := val_int_nonneg 5776
            rw [padicValRat.pow_of_ne_zero hx]
            dsimp [vx] at hvxneg ⊢
            norm_num at hge ⊢
            omega
        have hvright := val_add_list_eq l (pow_ne_zero 3 hx) hgt
        have hvrel : 2 * vy = 3 * vx := by
          calc
            2 * vy = padicValRat 3 (y ^ 2) := by
              rw [padicValRat.pow_of_ne_zero hy]
              dsimp [vy]
            _ = padicValRat 3 (x ^ 3 + (8 * x + 76) ^ 2) := by
              rw [hE]
            _ = padicValRat 3
                (x ^ 3 + 64 * x ^ 2 + 1216 * x + 5776) := by
              congr 1
              ring
            _ = padicValRat 3 (x ^ 3 + l.sum) := by rw [hshape]
            _ = 3 * vx := by
              rw [hvright, padicValRat.pow_of_ne_zero hx]
              dsimp [vx]
        left
        change ∃ k : ℤ, 0 < k ∧
          padicValRat 3 x = -2 * k ∧
          padicValRat 3 y = -3 * k
        refine ⟨vx - vy, by omega, ?_, ?_⟩
        · dsimp [vx]
          omega
        · dsimp [vy]
          omega

/-! ## Reduction of integral rational coordinates -/

/-- A rational number of nonnegative valuation viewed as a three-adic
integer. -/
private noncomputable def ratPadicInt (q : ℚ)
    (hq : 0 ≤ padicValRat 3 q) : ℤ_[3] :=
  ⟨(q : ℚ_[3]), by
    rw [Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast]
    exact_mod_cast hq⟩

/-- Positive rational valuation is equivalent to zero reduction for a
nonzero integral rational number. -/
private theorem ratPadicInt_red_eq_zero_of_val_pos
    {q : ℚ} (hq : q ≠ 0) (hv : 0 < padicValRat 3 q) :
    PadicInt.toZMod (ratPadicInt q (le_of_lt hv)) = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd]
  change ‖(q : ℚ_[3])‖ < 1
  have hqcast : (q : ℚ_[3]) ≠ 0 := by
    exact_mod_cast hq
  rw [Padic.norm_eq_zpow_neg_valuation hqcast,
    Padic.valuation_ratCast, ← zpow_zero (3 : ℝ)]
  exact (zpow_lt_zpow_iff_right₀ (a := (3 : ℝ))
    (by norm_num : (1 : ℝ) < 3)).2 (by omega)

/-- Zero reduction of a nonzero integral rational number forces positive
valuation. -/
private theorem val_pos_of_padicInt_red_zero
    {q : ℚ} (hq : q ≠ 0) (hqi : 0 ≤ padicValRat 3 q)
    (hred : PadicInt.toZMod (ratPadicInt q hqi) = 0) :
    0 < padicValRat 3 q := by
  by_contra hnot
  have hv0 : padicValRat 3 q = 0 := by
    omega
  have hm : ratPadicInt q hqi ∈ IsLocalRing.maximalIdeal ℤ_[3] := by
    rw [← PadicInt.ker_toZMod]
    exact hred
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd] at hm
  change ‖(q : ℚ_[3])‖ < 1 at hm
  have hqcast : (q : ℚ_[3]) ≠ 0 := by
    exact_mod_cast hq
  rw [Padic.norm_eq_zpow_neg_valuation hqcast,
    Padic.valuation_ratCast, hv0] at hm
  norm_num at hm

/-- Nonzero reduction of an integral nonzero rational number forces
valuation zero. -/
private theorem val_zero_of_padicInt_red_nonzero
    {q : ℚ} (hq : q ≠ 0) (hqi : 0 ≤ padicValRat 3 q)
    (hred : PadicInt.toZMod (ratPadicInt q hqi) ≠ 0) :
    padicValRat 3 q = 0 := by
  by_contra hne
  have hvpos : 0 < padicValRat 3 q :=
    lt_of_le_of_ne hqi (Ne.symm hne)
  have hzero := ratPadicInt_red_eq_zero_of_val_pos hq hvpos
  have heq : ratPadicInt q hqi =
      ratPadicInt q (le_of_lt hvpos) := by
    apply Subtype.ext
    rfl
  exact hred (by rw [heq, hzero])

/-- The good equation holds in the three-adic integers for integral
rational coordinates. -/
private theorem padicInt_equation {x y : ℚ}
    (hx : 0 ≤ padicValRat 3 x) (hy : 0 ≤ padicValRat 3 y)
    (hE : OnGood x y) :
    (ratPadicInt y hy) ^ 2 =
      (ratPadicInt x hx) ^ 3 + 64 * (ratPadicInt x hx) ^ 2 +
        1216 * ratPadicInt x hx + 5776 := by
  apply Subtype.ext
  change (y : ℚ_[3]) ^ 2 =
    (x : ℚ_[3]) ^ 3 + 64 * (x : ℚ_[3]) ^ 2 +
      1216 * (x : ℚ_[3]) + 5776
  unfold OnGood at hE
  exact_mod_cast
    (show y ^ 2 = x ^ 3 + 64 * x ^ 2 + 1216 * x + 5776 by
      nlinarith [hE])

set_option maxHeartbeats 0 in
/-- Exhaustive classification of affine points on the good special fibre
over `𝔽₃`. -/
private theorem mod_three_affine_points :
    ∀ X Y : ZMod 3,
      Y ^ 2 = X ^ 3 + 64 * X ^ 2 + 1216 * X + 5776 →
      (X = 0 ∧ Y ≠ 0) ∨ (X = 1 ∧ Y ≠ 0) ∨ (X = 2 ∧ Y = 0) := by
  decide

/-- Integral rational coordinates reduce to one of the three affine
residue types. -/
private theorem integral_reduction {x y : ℚ}
    (hx : 0 ≤ padicValRat 3 x) (hy : 0 ≤ padicValRat 3 y)
    (hE : OnGood x y) :
    let X := PadicInt.toZMod (ratPadicInt x hx)
    let Y := PadicInt.toZMod (ratPadicInt y hy)
    (X = 0 ∧ Y ≠ 0) ∨ (X = 1 ∧ Y ≠ 0) ∨ (X = 2 ∧ Y = 0) := by
  have hpadic := padicInt_equation hx hy hE
  have hred :
      PadicInt.toZMod (ratPadicInt y hy) ^ 2 =
        PadicInt.toZMod (ratPadicInt x hx) ^ 3 +
          64 * PadicInt.toZMod (ratPadicInt x hx) ^ 2 +
          1216 * PadicInt.toZMod (ratPadicInt x hx) + 5776 := by
    simpa only [map_pow, map_add, map_mul, map_ofNat] using
      congrArg PadicInt.toZMod hpadic
  exact mod_three_affine_points _ _ hred

/-! ## Explicit doubling coordinates -/

/-- Horizontal coordinate of twice an affine good-model point. -/
def doubleX (x y : ℚ) : ℚ :=
  x * (x ^ 3 - 2432 * x - 46208) / (4 * y ^ 2)

/-- Vertical coordinate of twice an affine good-model point. -/
def doubleY (x y : ℚ) : ℚ :=
  (x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 + 115520 * x ^ 3 -
      28094464 * x - 266897408) / (8 * y ^ 3)

/-- The library doubling formula has the displayed horizontal
coordinate. -/
private theorem addX_self_eq_doubleX {x y : ℚ}
    (hy : y ≠ 0) (h : OnGood x y) :
    let L := WeierstrassCurve.Affine.slope goodCurve x x y y
    WeierstrassCurve.Affine.addX goodCurve x x L = doubleX x y := by
  dsimp
  have hneg : y ≠ WeierstrassCurve.Affine.negY goodCurve x y := by
    rw [goodCurve_negY]
    intro heq
    apply hy
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  unfold WeierstrassCurve.Affine.negY goodCurve doubleX
  field_simp [hy]
  unfold OnGood at h
  ring_nf at h ⊢
  linear_combination
    -32 * y ^ 2 * (x + 32) * h

/-- The library doubling formula has the displayed vertical
coordinate. -/
private theorem addY_self_eq_doubleY {x y : ℚ}
    (hy : y ≠ 0) (h : OnGood x y) :
    let L := WeierstrassCurve.Affine.slope goodCurve x x y y
    WeierstrassCurve.Affine.addY goodCurve x x y L = doubleY x y := by
  dsimp
  have hneg : y ≠ WeierstrassCurve.Affine.negY goodCurve x y := by
    rw [goodCurve_negY]
    intro heq
    apply hy
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  unfold WeierstrassCurve.Affine.addY
  unfold WeierstrassCurve.Affine.negAddY
  unfold WeierstrassCurve.Affine.negY
  unfold WeierstrassCurve.Affine.addX
  unfold goodCurve doubleY
  field_simp [hy]
  unfold OnGood at h
  ring_nf at h ⊢
  linear_combination
    32 * y ^ 3 *
      (7 * x ^ 3 + 448 * x ^ 2 + 9408 * x -
        2 * y ^ 2 + 66272) * h

/-- The displayed doubling coordinates are nonsingular because they are the
coordinates produced by the affine group law. -/
private theorem double_nonsingular {x y : ℚ}
    (hy : y ≠ 0)
    (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y) :
    WeierstrassCurve.Affine.Nonsingular goodCurve
      (doubleX x y) (doubleY x y) := by
  have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
  have hneg : y ≠ WeierstrassCurve.Affine.negY goodCurve x y := by
    rw [goodCurve_negY]
    intro heq
    apply hy
    linarith
  have hxadd := addX_self_eq_doubleX hy hcurve
  have hyadd := addY_self_eq_doubleY hy hcurve
  rw [← hxadd, ← hyadd]
  exact WeierstrassCurve.Affine.nonsingular_add h h
    (fun hxy => hneg hxy.right)

/-- Doubling a good-model point agrees with the two displayed rational
coordinate functions. -/
private theorem two_nsmul_eq_double_point {x y : ℚ}
    (hy : y ≠ 0)
    (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y) :
    2 • (WeierstrassCurve.Affine.Point.some x y h : GoodPoint) =
      WeierstrassCurve.Affine.Point.some (doubleX x y) (doubleY x y)
        (double_nonsingular hy h) := by
  have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
  have hneg : y ≠ WeierstrassCurve.Affine.negY goodCurve x y := by
    rw [goodCurve_negY]
    intro heq
    apply hy
    linarith
  rw [two_nsmul,
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg,
    WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_self_eq_doubleX hy hcurve,
    addY_self_eq_doubleY hy hcurve⟩

/-- A rational integer prime to three has valuation zero. -/
private theorem val_int_unit (z : ℤ) (hz : ¬(3 : ℤ) ∣ z) :
    padicValRat 3 (z : ℚ) = 0 := by
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hz]
  norm_num

/-- A polynomial with unit constant term and all other terms of positive
valuation is a three-adic unit. -/
private theorem val_unit_constant_poly
    {x : ℚ} (hx : x ≠ 0) (hvx : 0 < padicValRat 3 x)
    (c : ℤ) (hc : ¬(3 : ℤ) ∣ c) (l : List (ℤ × ℕ))
    (hexp : ∀ cb ∈ l, 0 < cb.2)
    (hcoeff : ∀ cb ∈ l, cb.1 ≠ 0) :
    (c : ℚ) +
        (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum ≠ 0 ∧
      padicValRat 3
        ((c : ℚ) +
          (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum) = 0 := by
  have hc0 : (c : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (fun hz => hc (by simp [hz]))
  have hgt : ∀ a ∈
      (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2),
      padicValRat 3 (c : ℚ) < padicValRat 3 a := by
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨cb, hcb, rfl⟩ := ha
    have hge := val_x_monomial_ge hx cb.1
      (hcoeff cb hcb) cb.2
    rw [val_int_unit c hc]
    have hp := hexp cb hcb
    have hpZ : (0 : ℤ) < (cb.2 : ℤ) := by
      exact_mod_cast hp
    exact (mul_pos hpZ hvx).trans_le hge
  have hval := val_add_list_eq
    (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2) hc0 hgt
  have hne :
      (c : ℚ) +
        (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum ≠ 0 := by
    intro hz
    have hsum :
        (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum = -(c : ℚ) := by
      linarith
    rcases val_sum_gt_or_zero
      (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2) hgt with
      hzero | hsumgt
    · rw [hzero] at hsum
      exact hc0 (by linarith)
    · rw [hsum, padicValRat.neg] at hsumgt
      omega
  exact ⟨hne, by rw [hval, val_int_unit c hc]⟩

/-! ## Doubling and tripling inside the formal kernel -/

/-- Doubling preserves every positive formal level. -/
theorem FormalLevel_double {P : GoodPoint} {k : ℤ}
    (hP : FormalLevel P k) :
    FormalLevel (2 • P) k := by
  cases P with
  | zero => simp [FormalLevel] at hP
  | some x y h =>
      rcases hP with ⟨hk, hvx, hvy⟩
      have hcurve : OnGood x y :=
        (goodCurve_equation_iff x y).mp h.1
      have hx : x ≠ 0 := by
        intro hx0
        rw [hx0, padicValRat.zero] at hvx
        omega
      have hy : y ≠ 0 := by
        intro hy0
        rw [hy0, padicValRat.zero] at hvy
        omega
      let l3 : List (ℤ × ℕ) := [(-2432, 1), (-46208, 0)]
      have hv3 :
          padicValRat 3 (x ^ 3 - 2432 * x - 46208) = -6 * k := by
        have hv := val_leading_poly hx hy hvx 3 l3
          (by
            intro cb hcb
            simp [l3] at hcb
            rcases hcb with rfl | rfl <;> norm_num <;> omega)
          (by
            intro cb hcb
            simp [l3] at hcb
            rcases hcb with rfl | rfl <;> norm_num)
        convert hv using 1
        · simp [l3]
          ring
        · ring
      have hf3 : x ^ 3 - 2432 * x - 46208 ≠ 0 := by
        intro hz
        rw [hz, padicValRat.zero] at hv3
        omega
      let l6 : List (ℤ × ℕ) :=
        [(128, 5), (6080, 4), (115520, 3),
          (-28094464, 1), (-266897408, 0)]
      have hv6 :
          padicValRat 3
            (x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
              115520 * x ^ 3 - 28094464 * x - 266897408) =
            -12 * k := by
        have hv := val_leading_poly hx hy hvx 6 l6
          (by
            intro cb hcb
            simp [l6] at hcb
            rcases hcb with rfl | rfl | rfl | rfl | rfl <;>
              norm_num <;> omega)
          (by
            intro cb hcb
            simp [l6] at hcb
            rcases hcb with rfl | rfl | rfl | rfl | rfl <;>
              norm_num)
        convert hv using 1
        · simp [l6]
          ring
        · ring
      have hf6 :
          x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
            115520 * x ^ 3 - 28094464 * x - 266897408 ≠ 0 := by
        intro hz
        rw [hz, padicValRat.zero] at hv6
        omega
      have hdx : doubleX x y ≠ 0 := by
        unfold doubleX
        exact div_ne_zero (mul_ne_zero hx hf3)
          (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
      have hdy : doubleY x y ≠ 0 := by
        unfold doubleY
        exact div_ne_zero hf6
          (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy))
      have hvdx : padicValRat 3 (doubleX x y) = -2 * k := by
        have hv4 : padicValRat 3 (4 : ℚ) = 0 :=
          val_int_unit 4 (by norm_num)
        unfold doubleX
        rw [padicValRat.div (mul_ne_zero hx hf3)
            (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)),
          padicValRat.mul hx hf3, hvx, hv3,
          padicValRat.mul (by norm_num) (pow_ne_zero 2 hy),
          hv4, padicValRat.pow_of_ne_zero hy, hvy]
        ring
      have hvdy : padicValRat 3 (doubleY x y) = -3 * k := by
        have hv8 : padicValRat 3 (8 : ℚ) = 0 :=
          val_int_unit 8 (by norm_num)
        unfold doubleY
        rw [padicValRat.div hf6
            (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy)),
          hv6, padicValRat.mul (by norm_num) (pow_ne_zero 3 hy),
          hv8, padicValRat.pow_of_ne_zero hy, hvy]
        ring
      have hneg : y ≠ WeierstrassCurve.Affine.negY goodCurve x y := by
        rw [goodCurve_negY]
        intro heq
        apply hy
        linarith
      rw [two_nsmul,
        WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
      change 0 < k ∧
        padicValRat 3
          (WeierstrassCurve.Affine.addX goodCurve x x
            (WeierstrassCurve.Affine.slope goodCurve x x y y)) =
              -2 * k ∧
        padicValRat 3
          (WeierstrassCurve.Affine.addY goodCurve x x y
            (WeierstrassCurve.Affine.slope goodCurve x x y y)) =
              -3 * k
      rw [addX_self_eq_doubleX hy hcurve,
        addY_self_eq_doubleY hy hcurve]
      exact ⟨hk, hvdx, hvdy⟩

/-- Doubling preserves the three-adic formal kernel. -/
theorem FormalAtThree_double {P : GoodPoint}
    (hP : FormalAtThree P) :
    FormalAtThree (2 • P) := by
  rw [FormalAtThree_iff] at hP ⊢
  rcases hP with rfl | ⟨k, hk⟩
  · simp
  · exact Or.inr ⟨k, FormalLevel_double hk⟩

/-- A point with positive horizontal valuation and unit vertical
valuation enters the formal kernel after tripling. -/
private theorem triple_formal_of_x_pos
    {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y)
    (hvx : 0 < padicValRat 3 x)
    (hvy : padicValRat 3 y = 0) :
    FormalAtThree
      (3 • (WeierstrassCurve.Affine.Point.some x y h : GoodPoint)) := by
  have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0, padicValRat.zero] at hvx
    omega
  have hy : y ≠ 0 := good_y_ne_zero hcurve
  have hd := tripleDen_ne_zero hx hcurve
  have hlin : 3 * x + 76 ≠ 0 := by
    intro hz
    apply hd
    unfold tripleDen
    rw [hz]
    ring
  have hquad : x ^ 2 + 60 * x + 912 ≠ 0 := by
    nlinarith [sq_nonneg (x + 30)]
  have hv3 : padicValRat 3 (3 : ℚ) = 1 :=
    padicValRat.self (p := 3) (by norm_num)
  have hv76 : padicValRat 3 (76 : ℚ) = 0 :=
    val_int_unit 76 (by norm_num)
  have hv3x : padicValRat 3 (3 * x) =
      1 + padicValRat 3 x := by
    rw [padicValRat.mul (by norm_num) hx, hv3]
  have hvlin : padicValRat 3 (3 * x + 76) = 0 := by
    rw [add_comm, val_add_eq_left_of_lt (a := (76 : ℚ))
      (b := 3 * x) (by norm_num)
      (by rw [hv76, hv3x]; omega), hv76]
  have hv20 : padicValRat 3 (20 : ℚ) = 0 :=
    val_int_unit 20 (by norm_num)
  have hv60 : padicValRat 3 (60 : ℚ) = 1 := by
    rw [show (60 : ℚ) = 3 * 20 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num), hv3, hv20]
    norm_num
  have hv304 : padicValRat 3 (304 : ℚ) = 0 :=
    val_int_unit 304 (by norm_num)
  have hv912 : padicValRat 3 (912 : ℚ) = 1 := by
    rw [show (912 : ℚ) = 3 * 304 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num), hv3, hv304]
    norm_num
  let lq : List ℚ := [x ^ 2, 60 * x]
  have hshape : (912 : ℚ) + lq.sum =
      x ^ 2 + 60 * x + 912 := by
    simp [lq]
    ring
  have hgt : ∀ a ∈ lq,
      padicValRat 3 (912 : ℚ) < padicValRat 3 a := by
    intro a ha
    simp only [lq, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · rw [hv912, padicValRat.pow_of_ne_zero hx]
      omega
    · rw [hv912, padicValRat.mul (by norm_num) hx, hv60]
      omega
  have hvquad := val_add_list_eq lq (by norm_num) hgt
  rw [hshape, hv912] at hvquad
  have hdval : padicValRat 3 (tripleDen x) =
      padicValRat 3 x + 1 := by
    unfold tripleDen
    rw [padicValRat.mul (mul_ne_zero hx hlin) hquad,
      padicValRat.mul hx hlin, hvlin, hvquad]
    ring
  let lx : List (ℤ × ℕ) :=
    [(1, 9), (-14592, 7), (-1177088, 6), (-35487744, 5),
      (-168566784, 4), (15985750016, 3), (409954418688, 2),
      (3894566977536, 1)]
  have hX := val_unit_constant_poly hx hvx 12332795428864
    (by norm_num) lx
    (by
      intro cb hcb
      simp [lx] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num)
    (by
      intro cb hcb
      simp [lx] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num)
  have hXshape : ((12332795428864 : ℤ) : ℚ) +
      (lx.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum =
        tripleXNum x := by
    simp [lx, tripleXNum]
    ring
  rw [hXshape] at hX
  obtain ⟨hXne, hXval⟩ := hX
  let l1 : List (ℤ × ℕ) := [(1, 3), (-2432, 1)]
  let l2 : List (ℤ × ℕ) := [(1, 3), (76, 2), (2128, 1)]
  let l3 : List (ℤ × ℕ) :=
    [(1, 6), (180, 5), (13376, 4), (516800, 3),
      (10905088, 2), (119401472, 1)]
  have h1 := val_unit_constant_poly hx hvx (-46208) (by norm_num) l1
    (by
      intro cb hcb
      simp [l1] at hcb
      rcases hcb with rfl | rfl <;> norm_num)
    (by
      intro cb hcb
      simp [l1] at hcb
      rcases hcb with rfl | rfl <;> norm_num)
  have h2 := val_unit_constant_poly hx hvx 23104 (by norm_num) l2
    (by
      intro cb hcb
      simp [l2] at hcb
      rcases hcb with rfl | rfl | rfl <;> norm_num)
    (by
      intro cb hcb
      simp [l2] at hcb
      rcases hcb with rfl | rfl | rfl <;> norm_num)
  have h3 := val_unit_constant_poly hx hvx 533794816
    (by norm_num) l3
    (by
      intro cb hcb
      simp [l3] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num)
    (by
      intro cb hcb
      simp [l3] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num)
  have hs1 : (((-46208 : ℤ) : ℚ)) +
      (l1.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum =
        x ^ 3 - 2432 * x - 46208 := by
    simp [l1]
    ring
  have hs2 : ((23104 : ℤ) : ℚ) +
      (l2.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum =
        x ^ 3 + 76 * x ^ 2 + 2128 * x + 23104 := by
    simp [l2]
    ring
  have hs3 : ((533794816 : ℤ) : ℚ) +
      (l3.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum =
        x ^ 6 + 180 * x ^ 5 + 13376 * x ^ 4 +
          516800 * x ^ 3 + 10905088 * x ^ 2 +
          119401472 * x + 533794816 := by
    simp [l3]
    ring
  rw [hs1] at h1
  rw [hs2] at h2
  rw [hs3] at h3
  rcases h1 with ⟨hne1, hv1⟩
  rcases h2 with ⟨hne2, hv2⟩
  rcases h3 with ⟨hne3, hv3f⟩
  have hYne : tripleYNum x y ≠ 0 := by
    unfold tripleYNum
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hy hne1) hne2) hne3
  have hYval : padicValRat 3 (tripleYNum x y) = 0 := by
    unfold tripleYNum
    rw [padicValRat.mul
        (mul_ne_zero (mul_ne_zero hy hne1) hne2) hne3,
      padicValRat.mul (mul_ne_zero hy hne1) hne2,
      padicValRat.mul hy hne1, hvy, hv1, hv2, hv3f]
    ring
  have hphi := threeIsogenyX_ne_zero hx hcurve
  have hcomp := dual_comp_threeIsogenyPoint
    (WeierstrassCurve.Affine.Point.some x y h : GoodPoint)
  rw [threeIsogenyPoint_some_of_x_ne_zero h hx] at hcomp
  unfold WeierstrassCurve.Affine.Point.mk at hcomp
  rw [dualThreeIsogenyPoint_some_of_x_ne_zero _ hphi] at hcomp
  rw [← hcomp]
  change ∃ k : ℤ, 0 < k ∧
    padicValRat 3
      (dualThreeIsogenyX (threeIsogenyX x)) = -2 * k ∧
    padicValRat 3
      (dualThreeIsogenyY
        (threeIsogenyX x) (threeIsogenyY x y)) = -3 * k
  refine ⟨padicValRat 3 x + 1, by omega, ?_, ?_⟩
  · rw [tripleX_formula hx hcurve,
      padicValRat.div hXne (pow_ne_zero 2 hd), hXval,
      padicValRat.pow_of_ne_zero hd, hdval]
    ring
  · rw [tripleY_formula hx hcurve,
      padicValRat.div hYne (pow_ne_zero 3 hd), hYval,
      padicValRat.pow_of_ne_zero hd, hdval]
    ring

/-- An affine point with first coordinate zero is killed by three and
therefore is formally trivial after tripling. -/
private theorem triple_formal_of_x_zero
    {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y)
    (hx : x = 0) :
    FormalAtThree
      (3 • (WeierstrassCurve.Affine.Point.some x y h : GoodPoint)) := by
  rw [three_nsmul_of_x_zero h hx]
  trivial

/-! ## Reading valuations from explicit PadicInt models -/

/-- A PadicInt expression whose value is rational certifies nonnegative
rational valuation. -/
private theorem val_nonneg_of_padicInt_model
    {q : ℚ} (qi : ℤ_[3])
    (hcoe : (qi : ℚ_[3]) = (q : ℚ_[3])) :
    0 ≤ padicValRat 3 q := by
  have hp := qi.property
  rw [hcoe, Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_ratCast] at hp
  exact_mod_cast hp

/-- Nonzero reduction of a rational PadicInt model forces rational
valuation zero. -/
private theorem val_zero_of_padicInt_model
    {q : ℚ} (hq : q ≠ 0) (qi : ℤ_[3])
    (hcoe : (qi : ℚ_[3]) = (q : ℚ_[3]))
    (hred : PadicInt.toZMod qi ≠ 0) :
    padicValRat 3 q = 0 := by
  have hqint := val_nonneg_of_padicInt_model qi hcoe
  have heq : ratPadicInt q hqint = qi := by
    apply Subtype.ext
    exact hcoe.symm
  apply val_zero_of_padicInt_red_nonzero hq hqint
  rwa [heq]

/-- Zero reduction of a nonzero rational PadicInt model forces positive
rational valuation. -/
private theorem val_pos_of_padicInt_model
    {q : ℚ} (hq : q ≠ 0) (qi : ℤ_[3])
    (hcoe : (qi : ℚ_[3]) = (q : ℚ_[3]))
    (hred : PadicInt.toZMod qi = 0) :
    0 < padicValRat 3 q := by
  have hqint := val_nonneg_of_padicInt_model qi hcoe
  have heq : ratPadicInt q hqint = qi := by
    apply Subtype.ext
    exact hcoe.symm
  apply val_pos_of_padicInt_red_zero hq hqint
  rwa [heq]

/-! ## Entry after multiplication by six -/

set_option maxHeartbeats 0 in
/-- Every rational point enters the three-adic formal kernel after
multiplication by six. -/
theorem six_nsmul_formal (P : GoodPoint) :
    FormalAtThree (6 • P) := by
  rcases formal_or_integral P with hformal | hintegral
  · have hdouble := FormalAtThree_double hformal
    have htriple := FormalAtThree_triple hdouble
    simpa only [show (6 : ℕ) = 3 * 2 by norm_num, mul_nsmul'] using htriple
  · cases P with
    | zero => trivial
    | some x y h =>
        rcases hintegral with ⟨hxint, hyint⟩
        have hcurve : OnGood x y :=
          (goodCurve_equation_iff x y).mp h.1
        have hy : y ≠ 0 := good_y_ne_zero hcurve
        let xi : ℤ_[3] := ratPadicInt x hxint
        let yi : ℤ_[3] := ratPadicInt y hyint
        obtain hred | hred | hred :=
          integral_reduction hxint hyint hcurve
        · rcases hred with ⟨hxred, hyred⟩
          have hvy : padicValRat 3 y = 0 :=
            val_zero_of_padicInt_red_nonzero hy hyint hyred
          let nxi : ℤ_[3] :=
            xi * (xi ^ 3 - 2432 * xi - 46208)
          let nyi : ℤ_[3] :=
            xi ^ 6 + 128 * xi ^ 5 + 6080 * xi ^ 4 +
              115520 * xi ^ 3 - 28094464 * xi - 266897408
          have hnxcoe :
              (nxi : ℚ_[3]) =
                (x * (x ^ 3 - 2432 * x - 46208) : ℚ) := by
            change
              (x : ℚ_[3]) *
                  ((x : ℚ_[3]) ^ 3 - 2432 * (x : ℚ_[3]) - 46208) =
                ((x * (x ^ 3 - 2432 * x - 46208) : ℚ) : ℚ_[3])
            norm_num
          have hnycoe :
              (nyi : ℚ_[3]) =
                (x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
                  115520 * x ^ 3 - 28094464 * x -
                  266897408 : ℚ) := by
            change
              (x : ℚ_[3]) ^ 6 + 128 * (x : ℚ_[3]) ^ 5 +
                    6080 * (x : ℚ_[3]) ^ 4 +
                    115520 * (x : ℚ_[3]) ^ 3 -
                    28094464 * (x : ℚ_[3]) - 266897408 =
                ((x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
                  115520 * x ^ 3 - 28094464 * x -
                  266897408 : ℚ) : ℚ_[3])
            norm_num
          have hnxred : PadicInt.toZMod nxi = 0 := by
            simp [nxi, xi, hxred]
          have hnyred : PadicInt.toZMod nyi ≠ 0 := by
            simp [nyi, xi, hxred]
            norm_num only [map_ofNat]
            decide
          let nx : ℚ := x * (x ^ 3 - 2432 * x - 46208)
          let ny : ℚ :=
            x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
              115520 * x ^ 3 - 28094464 * x - 266897408
          have hny : ny ≠ 0 := by
            intro hzero
            apply hnyred
            have : nyi = 0 := by
              apply Subtype.ext
              rw [hnycoe]
              change ((ny : ℚ) : ℚ_[3]) = 0
              rw [hzero]
              norm_num
            rw [this, map_zero]
          have hvny : padicValRat 3 ny = 0 :=
            val_zero_of_padicInt_model hny nyi hnycoe hnyred
          by_cases hnx : nx = 0
          · have hdx : doubleX x y = 0 := by
              unfold doubleX
              change nx / (4 * y ^ 2) = 0
              rw [hnx]
              simp
            let hd := double_nonsingular hy h
            have hdouble := two_nsmul_eq_double_point hy h
            rw [show (6 : ℕ) = 3 * 2 by norm_num, mul_nsmul', hdouble]
            exact triple_formal_of_x_zero hd hdx
          · have hvnx : 0 < padicValRat 3 nx :=
              val_pos_of_padicInt_model hnx nxi hnxcoe hnxred
            have hdx : doubleX x y ≠ 0 := by
              unfold doubleX
              change nx / (4 * y ^ 2) ≠ 0
              exact div_ne_zero hnx
                (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
            have hdy : doubleY x y ≠ 0 := by
              unfold doubleY
              change ny / (8 * y ^ 3) ≠ 0
              exact div_ne_zero hny
                (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy))
            have hvdx : 0 < padicValRat 3 (doubleX x y) := by
              have hv4 : padicValRat 3 (4 : ℚ) = 0 :=
                val_int_unit 4 (by norm_num)
              unfold doubleX
              change 0 < padicValRat 3 (nx / (4 * y ^ 2))
              rw [padicValRat.div hnx
                  (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)),
                padicValRat.mul (by norm_num) (pow_ne_zero 2 hy),
                hv4, padicValRat.pow_of_ne_zero hy, hvy]
              omega
            have hvdy : padicValRat 3 (doubleY x y) = 0 := by
              have hv8 : padicValRat 3 (8 : ℚ) = 0 :=
                val_int_unit 8 (by norm_num)
              unfold doubleY
              change padicValRat 3 (ny / (8 * y ^ 3)) = 0
              rw [padicValRat.div hny
                  (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy)),
                hvny, padicValRat.mul (by norm_num) (pow_ne_zero 3 hy),
                hv8, padicValRat.pow_of_ne_zero hy, hvy]
              ring
            let hd := double_nonsingular hy h
            have hdouble := two_nsmul_eq_double_point hy h
            rw [show (6 : ℕ) = 3 * 2 by norm_num, mul_nsmul', hdouble]
            exact triple_formal_of_x_pos hd hvdx hvdy
        · rcases hred with ⟨hxred, hyred⟩
          have hvy : padicValRat 3 y = 0 :=
            val_zero_of_padicInt_red_nonzero hy hyint hyred
          let nxi : ℤ_[3] :=
            xi * (xi ^ 3 - 2432 * xi - 46208)
          let nyi : ℤ_[3] :=
            xi ^ 6 + 128 * xi ^ 5 + 6080 * xi ^ 4 +
              115520 * xi ^ 3 - 28094464 * xi - 266897408
          have hnxcoe :
              (nxi : ℚ_[3]) =
                (x * (x ^ 3 - 2432 * x - 46208) : ℚ) := by
            change
              (x : ℚ_[3]) *
                  ((x : ℚ_[3]) ^ 3 - 2432 * (x : ℚ_[3]) - 46208) =
                ((x * (x ^ 3 - 2432 * x - 46208) : ℚ) : ℚ_[3])
            norm_num
          have hnycoe :
              (nyi : ℚ_[3]) =
                (x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
                  115520 * x ^ 3 - 28094464 * x -
                  266897408 : ℚ) := by
            change
              (x : ℚ_[3]) ^ 6 + 128 * (x : ℚ_[3]) ^ 5 +
                    6080 * (x : ℚ_[3]) ^ 4 +
                    115520 * (x : ℚ_[3]) ^ 3 -
                    28094464 * (x : ℚ_[3]) - 266897408 =
                ((x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
                  115520 * x ^ 3 - 28094464 * x -
                  266897408 : ℚ) : ℚ_[3])
            norm_num
          have hnxred : PadicInt.toZMod nxi = 0 := by
            simp [nxi, xi, hxred]
            norm_num only [map_ofNat]
            decide
          have hnyred : PadicInt.toZMod nyi ≠ 0 := by
            simp [nyi, xi, hxred]
            norm_num only [map_ofNat]
            decide
          let nx : ℚ := x * (x ^ 3 - 2432 * x - 46208)
          let ny : ℚ :=
            x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
              115520 * x ^ 3 - 28094464 * x - 266897408
          have hny : ny ≠ 0 := by
            intro hzero
            apply hnyred
            have : nyi = 0 := by
              apply Subtype.ext
              rw [hnycoe]
              change ((ny : ℚ) : ℚ_[3]) = 0
              rw [hzero]
              norm_num
            rw [this, map_zero]
          have hvny : padicValRat 3 ny = 0 :=
            val_zero_of_padicInt_model hny nyi hnycoe hnyred
          by_cases hnx : nx = 0
          · have hdx : doubleX x y = 0 := by
              unfold doubleX
              change nx / (4 * y ^ 2) = 0
              rw [hnx]
              simp
            let hd := double_nonsingular hy h
            have hdouble := two_nsmul_eq_double_point hy h
            rw [show (6 : ℕ) = 3 * 2 by norm_num, mul_nsmul', hdouble]
            exact triple_formal_of_x_zero hd hdx
          · have hvnx : 0 < padicValRat 3 nx :=
              val_pos_of_padicInt_model hnx nxi hnxcoe hnxred
            have hdx : doubleX x y ≠ 0 := by
              unfold doubleX
              change nx / (4 * y ^ 2) ≠ 0
              exact div_ne_zero hnx
                (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
            have hdy : doubleY x y ≠ 0 := by
              unfold doubleY
              change ny / (8 * y ^ 3) ≠ 0
              exact div_ne_zero hny
                (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy))
            have hvdx : 0 < padicValRat 3 (doubleX x y) := by
              have hv4 : padicValRat 3 (4 : ℚ) = 0 :=
                val_int_unit 4 (by norm_num)
              unfold doubleX
              change 0 < padicValRat 3 (nx / (4 * y ^ 2))
              rw [padicValRat.div hnx
                  (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)),
                padicValRat.mul (by norm_num) (pow_ne_zero 2 hy),
                hv4, padicValRat.pow_of_ne_zero hy, hvy]
              omega
            have hvdy : padicValRat 3 (doubleY x y) = 0 := by
              have hv8 : padicValRat 3 (8 : ℚ) = 0 :=
                val_int_unit 8 (by norm_num)
              unfold doubleY
              change padicValRat 3 (ny / (8 * y ^ 3)) = 0
              rw [padicValRat.div hny
                  (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy)),
                hvny, padicValRat.mul (by norm_num) (pow_ne_zero 3 hy),
                hv8, padicValRat.pow_of_ne_zero hy, hvy]
              ring
            let hd := double_nonsingular hy h
            have hdouble := two_nsmul_eq_double_point hy h
            rw [show (6 : ℕ) = 3 * 2 by norm_num, mul_nsmul', hdouble]
            exact triple_formal_of_x_pos hd hvdx hvdy
        · rcases hred with ⟨hxred, hyred⟩
          have hx : x ≠ 0 := by
            intro hx0
            subst x
            simp [ratPadicInt] at hxred
            exact (by decide : (0 : ZMod 3) ≠ 2) hxred
          have hvx : padicValRat 3 x = 0 :=
            val_zero_of_padicInt_red_nonzero hx hxint (by
              rw [hxred]
              decide)
          have hvypos : 0 < padicValRat 3 y :=
            val_pos_of_padicInt_red_zero hy hyint hyred
          let nxi : ℤ_[3] :=
            xi * (xi ^ 3 - 2432 * xi - 46208)
          let nyi : ℤ_[3] :=
            xi ^ 6 + 128 * xi ^ 5 + 6080 * xi ^ 4 +
              115520 * xi ^ 3 - 28094464 * xi - 266897408
          have hnxcoe :
              (nxi : ℚ_[3]) =
                (x * (x ^ 3 - 2432 * x - 46208) : ℚ) := by
            change
              (x : ℚ_[3]) *
                  ((x : ℚ_[3]) ^ 3 - 2432 * (x : ℚ_[3]) - 46208) =
                ((x * (x ^ 3 - 2432 * x - 46208) : ℚ) : ℚ_[3])
            norm_num
          have hnycoe :
              (nyi : ℚ_[3]) =
                (x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
                  115520 * x ^ 3 - 28094464 * x -
                  266897408 : ℚ) := by
            change
              (x : ℚ_[3]) ^ 6 + 128 * (x : ℚ_[3]) ^ 5 +
                    6080 * (x : ℚ_[3]) ^ 4 +
                    115520 * (x : ℚ_[3]) ^ 3 -
                    28094464 * (x : ℚ_[3]) - 266897408 =
                ((x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
                  115520 * x ^ 3 - 28094464 * x -
                  266897408 : ℚ) : ℚ_[3])
            norm_num
          have hnxred : PadicInt.toZMod nxi ≠ 0 := by
            simp [nxi, xi, hxred]
            norm_num only [map_ofNat]
            decide
          have hnyred : PadicInt.toZMod nyi ≠ 0 := by
            simp [nyi, xi, hxred]
            norm_num only [map_ofNat]
            decide
          let nx : ℚ := x * (x ^ 3 - 2432 * x - 46208)
          let ny : ℚ :=
            x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
              115520 * x ^ 3 - 28094464 * x - 266897408
          have hnx : nx ≠ 0 := by
            intro hzero
            apply hnxred
            have : nxi = 0 := by
              apply Subtype.ext
              rw [hnxcoe]
              change ((nx : ℚ) : ℚ_[3]) = 0
              rw [hzero]
              norm_num
            rw [this, map_zero]
          have hny : ny ≠ 0 := by
            intro hzero
            apply hnyred
            have : nyi = 0 := by
              apply Subtype.ext
              rw [hnycoe]
              change ((ny : ℚ) : ℚ_[3]) = 0
              rw [hzero]
              norm_num
            rw [this, map_zero]
          have hvnx : padicValRat 3 nx = 0 :=
            val_zero_of_padicInt_model hnx nxi hnxcoe hnxred
          have hvny : padicValRat 3 ny = 0 :=
            val_zero_of_padicInt_model hny nyi hnycoe hnyred
          have hdx : doubleX x y ≠ 0 := by
            unfold doubleX
            change nx / (4 * y ^ 2) ≠ 0
            exact div_ne_zero hnx
              (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
          have hdy : doubleY x y ≠ 0 := by
            unfold doubleY
            change ny / (8 * y ^ 3) ≠ 0
            exact div_ne_zero hny
              (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy))
          have hvdx :
              padicValRat 3 (doubleX x y) =
                -2 * padicValRat 3 y := by
            have hv4 : padicValRat 3 (4 : ℚ) = 0 :=
              val_int_unit 4 (by norm_num)
            unfold doubleX
            change padicValRat 3 (nx / (4 * y ^ 2)) =
              -2 * padicValRat 3 y
            rw [padicValRat.div hnx
                (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)),
              hvnx, padicValRat.mul (by norm_num) (pow_ne_zero 2 hy),
              hv4, padicValRat.pow_of_ne_zero hy]
            ring
          have hvdy :
              padicValRat 3 (doubleY x y) =
                -3 * padicValRat 3 y := by
            have hv8 : padicValRat 3 (8 : ℚ) = 0 :=
              val_int_unit 8 (by norm_num)
            unfold doubleY
            change padicValRat 3 (ny / (8 * y ^ 3)) =
              -3 * padicValRat 3 y
            rw [padicValRat.div hny
                (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy)),
              hvny, padicValRat.mul (by norm_num) (pow_ne_zero 3 hy),
              hv8, padicValRat.pow_of_ne_zero hy]
            ring
          let hd := double_nonsingular hy h
          have hdouble := two_nsmul_eq_double_point hy h
          have hlevel :
              FormalLevel
                (WeierstrassCurve.Affine.Point.some
                  (doubleX x y) (doubleY x y) hd)
                (padicValRat 3 y) :=
            ⟨hvypos, hvdx, hvdy⟩
          have hformal2 : FormalAtThree
              (2 • (WeierstrassCurve.Affine.Point.some x y h :
                GoodPoint)) := by
            rw [hdouble, FormalAtThree_iff]
            exact Or.inr ⟨padicValRat 3 y, hlevel⟩
          have hformal6 := FormalAtThree_triple hformal2
          simpa only [show (6 : ℕ) = 3 * 2 by norm_num,
            mul_nsmul'] using hformal6

end

end MazurProof.XDelta19GoodFormalReduction

end

-- ===== FLT.Assumptions.MazurProof.XDelta19GoodRationalPoints =====
section
/-!
# Rational points on the good conductor-nineteen model

The two explicit three-isogeny descents give a three-coset cover of the
rational points on

`y² = x³ + (8x+76)²`.

The three-adic formal filtration then kills six times every rational point.
This curve has no rational two-torsion, so every rational point is already
killed by three.  Finally, the verified dual-forward isogeny composition
shows that an affine three-torsion point must lie in the visible kernel
`x=0`.
-/

namespace MazurProof.XDelta19GoodRationalPoints

open WeierstrassCurve.Affine
open MazurProof.XDelta19GoodModel
open MazurProof.XDelta19GoodIsogeny
open MazurProof.XDelta19GoodFormalCore
open MazurProof.XDelta19GoodFormalReduction

noncomputable section

/-! ## Elimination of rational two-torsion -/

/-- The good model has no nonzero rational point killed by two.  An affine
two-torsion point would equal its inverse, forcing its vertical coordinate
to vanish, while the good cubic has no rational root. -/
theorem eq_zero_of_two_nsmul_eq_zero
    (P : GoodPoint) (hP : 2 • P = 0) :
    P = 0 := by
  cases P with
  | zero => rfl
  | some x y h =>
      exfalso
      rw [two_nsmul] at hP
      have hself :
          (Point.some x y h : GoodPoint) = -Point.some x y h :=
        eq_neg_of_add_eq_zero_left hP
      rw [Point.neg_some, Point.some.injEq] at hself
      have hy : y = 0 := by
        have := hself.2
        simp only [WeierstrassCurve.Affine.negY, goodCurve] at this
        linarith
      have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
      exact good_y_ne_zero hcurve hy

/-! ## Exponent three and the visible kernel -/

/-- Weak three-descent, formal entry after multiplication by six, and the
absence of rational two-torsion force every rational point to be killed by
three. -/
theorem three_nsmul_eq_zero (P : GoodPoint) :
    3 • P = 0 := by
  apply eq_zero_of_two_nsmul_eq_zero (3 • P)
  calc
    2 • (3 • P) = 6 • P := by
      exact (mul_nsmul' P 2 3).symm
    _ = 0 := six_nsmul_eq_zero six_nsmul_formal P

/-- An affine rational point killed by three belongs to the visible kernel
of the forward three-isogeny, hence has first coordinate zero.  Otherwise
both isogeny maps are affine at the point, contradicting that their
composition is the point at infinity. -/
theorem x_eq_zero_of_three_nsmul
    {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y)
    (hthree : 3 • (Point.some x y h : GoodPoint) = 0) :
    x = 0 := by
  by_contra hx
  have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
  have hforward := threeIsogenyPoint_some_of_x_ne_zero h hx
  have hforwardX := threeIsogenyX_ne_zero hx hcurve
  have hcomp := dual_comp_threeIsogenyPoint
    (Point.some x y h : GoodPoint)
  rw [hthree] at hcomp
  rw [hforward] at hcomp
  change dualThreeIsogenyPoint
      (Point.some (threeIsogenyX x) (threeIsogenyY x y) _) = 0 at hcomp
  rw [dualThreeIsogenyPoint_some_of_x_ne_zero _ hforwardX] at hcomp
  exact (Point.some_ne_zero _) hcomp

/-- Every affine rational point on the good integral model has first
coordinate zero. -/
theorem affine_x_eq_zero {x y : ℚ} (h : OnGood x y) :
    x = 0 := by
  have hns : WeierstrassCurve.Affine.Nonsingular goodCurve x y :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((goodCurve_equation_iff x y).mpr h)
  exact x_eq_zero_of_three_nsmul hns
    (three_nsmul_eq_zero (Point.some x y hns : GoodPoint))

end

end MazurProof.XDelta19GoodRationalPoints

end

-- ===== FLT.Assumptions.MazurProof.XDelta19RationalPoints =====
section
/-!
# Rational points on the order-nineteen diamond quotient

The good-model classification is transported first to the scaled
three-isogenous curve, then through the surjective dual isogeny to

`Y² = X³ + (2X+4)²`,

and finally to the minimal diamond quotient

`v² + v = u³ + u² + u`.

The resulting statement supplies the arithmetic input of the explicit
Tate-to-diamond quotient and excludes the order-nineteen Tate residual.
-/

namespace MazurProof.XDelta19RationalPoints

open WeierstrassCurve.Affine
open MazurProof.N19SutherlandModels
open MazurProof.XDelta19Model
open MazurProof.XDelta19Descent
open MazurProof.XDelta19GoodModel

noncomputable section

/-! ## Transport from the good model to the short model -/

/-- Every affine rational point on the original short model has first
coordinate zero.  Surjectivity of the first dual isogeny gives a point on
the scaled quotient; the good-model classification forces that point to
have scaled coordinate `s=228`, whose dual image has `x=0`. -/
theorem short_affine_x_eq_zero {x y : ℚ} (h : OnShort x y) :
    x = 0 := by
  have hns : WeierstrassCurve.Affine.Nonsingular shortCurve x y :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((shortCurve_equation_iff x y).mpr h)
  obtain ⟨Q, hQ⟩ :=
    dualThreeIsogenyPoint_surjective
      (Point.some x y hns : ShortPoint)
  cases Q with
  | zero =>
      have hzero :
          dualThreeIsogenyPoint (0 : DualPoint) = (0 : ShortPoint) :=
        dualThreeIsogenyPoint_zero
      have hQzero :
          (0 : ShortPoint) = Point.some x y hns := by
        exact hzero.symm.trans hQ
      exact False.elim ((Point.some_ne_zero hns) hQzero.symm)
  | some s t hs =>
      have hdual : OnDual s t := (dualCurve_equation_iff s t).mp hs.1
      have hs0 : s ≠ 0 := dual_x_ne_zero_of_on_curve hdual
      have hgood : OnGood ((s - 228) / 9) (t / 27) :=
        dual_to_good hdual
      have hgoodx : (s - 228) / 9 = 0 :=
        XDelta19GoodRationalPoints.affine_x_eq_zero hgood
      have hs228 : s = 228 := by linarith
      rw [dualThreeIsogenyPoint_some_of_x_ne_zero hs hs0] at hQ
      unfold Point.mk at hQ
      rw [Point.some.injEq] at hQ
      have hxmap := hQ.1
      rw [hs228] at hxmap
      norm_num [dualThreeIsogenyX] at hxmap
      linarith

/-! ## Minimal quotient and Tate residual -/

/-- Every affine rational point on the minimal diamond quotient has
horizontal coordinate zero. -/
theorem minimal_affine_x_eq_zero {u v : ℚ} (h : OnMinimal u v) :
    u = 0 :=
  minimal_x_eq_zero_of_short_x_eq_zero
    (fun _x _y hshort => short_affine_x_eq_zero hshort) h

/-- A zero of the diamond residual has horizontal coordinate zero. -/
theorem diamond_x_eq_zero
    (u v : ℚ) (h : diamondResidual u v = 0) :
    u = 0 := by
  apply minimal_affine_x_eq_zero
  unfold diamondResidual at h
  unfold OnMinimal
  nlinarith [h]

end

end MazurProof.XDelta19RationalPoints

end


theorem solution (u v : ℚ)
    (h : v ^ 2 + v = u ^ 3 + u ^ 2 + u) : u = 0 := by
  refine MazurProof.XDelta19RationalPoints.diamond_x_eq_zero u v ?_
  unfold MazurProof.N19SutherlandModels.diamondResidual
  linear_combination h
