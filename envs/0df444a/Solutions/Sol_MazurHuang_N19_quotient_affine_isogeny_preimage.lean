-- Prove2me | solution 1 for MazurHuang.N19.quotient_affine_isogeny_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T18:21:07.993977+00:00
-- url     : https://prove2.me/submissions/f28c6407-e282-4fb4-84bf-d2b34adca6e9

/-
Rational surjectivity of the good-model three-isogeny
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Definitions.Def_MazurHuang_EisensteinDescent35
import Theorems.Thm_MazurHuang_N19_primitive_quotient_eisenstein_factor_is_cube

open MazurHuang.EisensteinDescent35

-- Source FLT/Assumptions/MazurProof/XDelta19GoodModel.lean:30-61; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodModel
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
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

end
end MazurProof.XDelta19GoodModel
end

namespace MazurProof.XDelta19GoodModel
abbrev GoodPoint := WeierstrassCurve.Affine.Point goodCurve
end MazurProof.XDelta19GoodModel

-- Source FLT/Assumptions/MazurProof/XDelta19GoodModel.lean:153-170; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodModel
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
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

-- Source FLT/Assumptions/MazurProof/XDelta19GoodIsogeny.lean:31-170; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodIsogeny
open WeierstrassCurve WeierstrassCurve.Affine Polynomial MazurProof.XDelta19GoodModel
noncomputable section
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
end
end MazurProof.XDelta19GoodIsogeny
end

-- Source FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean:138-250; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.RationalPointsX135
noncomputable section
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
end
end MazurProof.RationalPointsX135
end

-- Source FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean:3-136; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section

namespace MazurProof.RationalPointsX135

noncomputable section

open scoped NumberField

open UniqueFactorizationMonoid

/-- A conjugate product which is a cube has cube exponents factor by factor. -/
theorem n35_unit_mul_cube_of_mul_conj_cube
    {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R]
    (conj : R ≃+* R) (hinv : Function.Involutive conj)
    {A M : R} (hA : A ≠ 0) (hEq : A * conj A = M ^ 3)
    (hsep : ∀ p : R, Irreducible p →
      (Associated p (conj p) ∨ ¬(p ∣ A ∧ conj p ∣ A))) :
    ∃ eps : Rˣ, ∃ B : R, A = (eps : R) * B ^ 3 := by
  classical
  letI : StrongNormalizationMonoid R :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  have hconjA : conj A ≠ 0 := by
    intro h
    apply hA
    apply conj.injective
    simpa using h
  have hM : M ≠ 0 := by
    intro h
    have hz : A * conj A = 0 := by simpa [h] using hEq
    exact (mul_ne_zero hA hconjA) hz
  let fac : R →₀ ℕ := factorization A
  have hfac_dvd : ∀ p : R, 3 ∣ fac p := by
    intro p
    by_cases hp0 : fac p = 0
    · simp [hp0]
    have hpSupp : p ∈ fac.support := Finsupp.mem_support_iff.mpr hp0
    have hpNF : p ∈ normalizedFactors A :=
      Multiset.mem_toFinset.mp (by rw [← support_factorization]; exact hpSupp)
    have hpPrime : Prime p := prime_of_normalized_factor p hpNF
    have hpIrr : Irreducible p := hpPrime.irreducible
    have hpNorm : normalize p = p := normalize_normalized_factor p hpNF
    have hpDivA : p ∣ A := dvd_of_mem_normalizedFactors hpNF
    have hfinProd : FiniteMultiplicity p (A * conj A) :=
      FiniteMultiplicity.of_prime_left hpPrime (mul_ne_zero hA hconjA)
    have hfinM : FiniteMultiplicity p M :=
      FiniteMultiplicity.of_prime_left hpPrime hM
    have hmul : multiplicity p A + multiplicity p (conj A) =
        3 * multiplicity p M := by
      calc
        multiplicity p A + multiplicity p (conj A) =
            multiplicity p (A * conj A) :=
          (multiplicity_mul hpPrime hfinProd).symm
        _ = multiplicity p (M ^ 3) := by rw [hEq]
        _ = 3 * multiplicity p M :=
          FiniteMultiplicity.multiplicity_pow hpPrime hfinM
    have hmap : multiplicity p (conj A) = multiplicity (conj p) A := by
      have h := multiplicity_map_eq conj (a := conj p) (b := A)
      simpa only [hinv p] using h
    have hfacEq : fac p = multiplicity p A := by
      change factorization A p = multiplicity p A
      rw [factorization_eq_count,
        multiplicity_eq_count_normalizedFactors hpIrr hA, hpNorm]
    rw [hfacEq]
    rcases hsep p hpIrr with hpSelf | hpSeparated
    · have hconjMult : multiplicity (conj p) A = multiplicity p A :=
        multiplicity_eq_of_associated_left hpSelf
      rw [hmap, hconjMult] at hmul
      have hthree_two : 3 ∣ 2 * multiplicity p A := by
        refine ⟨multiplicity p M, ?_⟩
        simpa [two_mul] using hmul
      exact (Nat.prime_three.dvd_mul.mp hthree_two).resolve_left (by norm_num)
    · have hnotConj : ¬conj p ∣ A := by
        intro hpConj
        exact hpSeparated ⟨hpDivA, hpConj⟩
      have hzero : multiplicity (conj p) A = 0 :=
        multiplicity_eq_zero.mpr hnotConj
      rw [hmap, hzero, add_zero] at hmul
      exact ⟨multiplicity p M, hmul⟩
  let rootFac : R →₀ ℕ :=
    Finsupp.mapRange (fun n : ℕ => n / 3) (by simp) fac
  have hthree_rootFac : (3 : ℕ) • rootFac = fac := by
    ext p
    simpa only [Finsupp.nsmul_apply, rootFac,
      Finsupp.mapRange_apply, Nat.nsmul_eq_mul] using
      Nat.mul_div_cancel' (hfac_dvd p)
  let s : Multiset R := Finsupp.toMultiset rootFac
  have hroot_support : rootFac.support ⊆ fac.support := by
    dsimp [rootFac]
    exact Finsupp.support_mapRange
  have hsNF : ∀ p ∈ s, p ∈ normalizedFactors A := by
    intro p hp
    have hpRoot : p ∈ rootFac.support := by simpa [s] using hp
    have hpFac : p ∈ fac.support := hroot_support hpRoot
    exact Multiset.mem_toFinset.mp (by rw [← support_factorization]; exact hpFac)
  have hsIrr : ∀ p ∈ s, Irreducible p := by
    intro p hp
    exact irreducible_of_normalized_factor p (hsNF p hp)
  have hsNorm : ∀ p ∈ s, normalize p = p := by
    intro p hp
    exact normalize_normalized_factor p (hsNF p hp)
  let B : R := s.prod
  have hB : B ≠ 0 := by
    dsimp [B]
    apply Multiset.prod_ne_zero
    intro hzero
    exact (hsIrr 0 hzero).ne_zero rfl
  have hnormB : normalizedFactors B = s := by
    calc
      normalizedFactors B = s.map normalize := by
        dsimp [B]
        exact normalizedFactors_prod_eq s hsIrr
      _ = s.map id := by
        apply Multiset.map_congr rfl
        intro p hp
        simpa using hsNorm p hp
      _ = s := by simp
  have hfacB : factorization B = rootFac := by
    change Multiset.toFinsupp (normalizedFactors B) = rootFac
    rw [hnormB]
    change Multiset.toFinsupp (Finsupp.toMultiset rootFac) = rootFac
    exact Finsupp.toMultiset_toFinsupp rootFac
  have hfacCube : factorization (B ^ 3) = factorization A := by
    calc
      factorization (B ^ 3) = (3 : ℕ) • factorization B := factorization_pow
      _ = (3 : ℕ) • rootFac := by rw [hfacB]
      _ = fac := hthree_rootFac
      _ = factorization A := rfl
  have hAssoc : Associated (B ^ 3) A :=
    associated_of_factorization_eq (B ^ 3) A
      (pow_ne_zero 3 hB) hA hfacCube
  rcases hAssoc with ⟨eps, heps⟩
  refine ⟨eps, B, ?_⟩
  calc
    A = B ^ 3 * (eps : R) := heps.symm
    _ = (eps : R) * B ^ 3 := mul_comm _ _
end
end MazurProof.RationalPointsX135
end


-- Source FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean:569-576; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.RationalPointsX135
noncomputable section
open scoped NumberField
open UniqueFactorizationMonoid
open MazurHuang.EisensteinDescent35
local instance n35K3_isCyclotomic :
    IsCyclotomicExtension {3} ℚ N35K3 := by
  change IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ)
  exact CyclotomicField.isCyclotomicExtension 3 ℚ

local instance n35O3_isPrincipalIdealRing :
    IsPrincipalIdealRing N35O3 :=
  IsCyclotomicExtension.Rat.three_pid N35K3
theorem n35O3_exists_coords (x : N35O3) :
    ∃ a b : ℤ, x = (a : N35O3) + (b : N35O3) * n35Omega := by
  let pb := n35Zeta_isPrimitive.integralPowerBasis
  have hdim : pb.dim = 2 := by
    dsimp only [pb]
    rw [IsPrimitiveRoot.integralPowerBasis_dim]
    decide
  let B : Module.Basis (Fin 2) ℤ N35O3 :=
    pb.basis.reindex (finCongr hdim)
  let a : ℤ := B.repr x 0
  let b : ℤ := B.repr x 1
  refine ⟨a, b, ?_⟩
  have hB0 : B 0 = 1 := by
    simp [B, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  have hB1 : B 1 = n35Omega := by
    simp [B, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, pb,
      IsPrimitiveRoot.integralPowerBasis_gen, n35Omega]
  have hsum := B.sum_repr x
  rw [Fin.sum_univ_two] at hsum
  simpa [a, b, hB0, hB1, Algebra.smul_def] using hsum.symm

def n35NormForm (a b : ℤ) : ℤ := a ^ 2 - a * b + b ^ 2

theorem n35_coord_mul_conj (a b : ℤ) :
    ((a : N35O3) + (b : N35O3) * n35Omega) *
        n35ConjO ((a : N35O3) + (b : N35O3) * n35Omega) =
      (n35NormForm a b : N35O3) := by
  have hs : n35Omega ^ 2 = -n35Omega - 1 := by
    linear_combination n35Omega_relation
  simp only [map_add, map_mul, map_intCast, n35ConjO_omega]
  push_cast
  unfold n35NormForm
  ring_nf
  rw [hs, n35Omega_cube]
  push_cast
  ring

private theorem n35NormForm_nonneg (a b : ℤ) : 0 ≤ n35NormForm a b := by
  have hsq1 : 0 ≤ (2 * a - b) ^ 2 := sq_nonneg _
  have hsq2 : 0 ≤ b ^ 2 := sq_nonneg _
  unfold n35NormForm
  nlinarith

private theorem n35NormForm_eq_zero_iff (a b : ℤ) :
    n35NormForm a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hsq1 : 0 ≤ (2 * a - b) ^ 2 := sq_nonneg _
    have hsq2 : 0 ≤ b ^ 2 := sq_nonneg _
    unfold n35NormForm at h
    have hb : b = 0 := by nlinarith
    subst b
    norm_num at h ⊢
    nlinarith
  · rintro ⟨rfl, rfl⟩
    norm_num [n35NormForm]

private theorem n35NormForm_ne_two_mod_three :
    ∀ a b : ZMod 3, a ^ 2 - a * b + b ^ 2 ≠ 2 := by
  decide

theorem n35NormForm_ne_two (a b : ℤ) : n35NormForm a b ≠ 2 := by
  intro h
  apply n35NormForm_ne_two_mod_three (a : ZMod 3) (b : ZMod 3)
  have h' := congrArg (fun z : ℤ => (z : ZMod 3)) h
  simpa [n35NormForm] using h'

theorem n35NormForm_ne_five (a b : ℤ) : n35NormForm a b ≠ 5 := by
  intro h
  apply n35NormForm_ne_two_mod_three (a : ZMod 3) (b : ZMod 3)
  have h' := congrArg (fun z : ℤ => (z : ZMod 3)) h
  norm_num [n35NormForm] at h' ⊢
  exact h'

theorem n35_coord_norm_pos {x : N35O3} {a b : ℤ} (hx : x ≠ 0)
    (hcoord : x = (a : N35O3) + (b : N35O3) * n35Omega) :
    0 < n35NormForm a b := by
  have hn := n35NormForm_nonneg a b
  apply lt_of_le_of_ne hn
  intro hzero
  have hab := (n35NormForm_eq_zero_iff a b).mp hzero.symm
  apply hx
  rw [hcoord, hab.1, hab.2]
  norm_num

theorem n35_isUnit_of_coord_norm_one {x : N35O3} {a b : ℤ}
    (hcoord : x = (a : N35O3) + (b : N35O3) * n35Omega)
    (hnorm : n35NormForm a b = 1) : IsUnit x := by
  apply IsUnit.of_mul_eq_one (n35ConjO x)
  rw [hcoord, n35_coord_mul_conj, hnorm]
  norm_num

theorem n35_coord_norm_mul_eq_sq {x y : N35O3} {a b c d r : ℤ}
    (hx : x = (a : N35O3) + (b : N35O3) * n35Omega)
    (hy : y = (c : N35O3) + (d : N35O3) * n35Omega)
    (hxy : x * y = (r : N35O3)) :
    n35NormForm a b * n35NormForm c d = r ^ 2 := by
  have ho :
      ((n35NormForm a b * n35NormForm c d : ℤ) : N35O3) =
        ((r ^ 2 : ℤ) : N35O3) := by
    push_cast
    rw [← n35_coord_mul_conj a b, ← n35_coord_mul_conj c d,
      ← hx, ← hy]
    calc
      (x * n35ConjO x) * (y * n35ConjO y) =
          (x * y) * n35ConjO (x * y) := by rw [map_mul]; ring
      _ = (r : N35O3) * n35ConjO (r : N35O3) := by rw [hxy]
      _ = (r : N35O3) ^ 2 := by simp; ring
  exact_mod_cast ho

private theorem n35_intCast_not_isUnit {p : ℤ} (hp : 2 ≤ p) :
    ¬IsUnit (p : N35O3) := by
  intro hu
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
  obtain ⟨c, d, hvcoord⟩ := n35O3_exists_coords v
  have hv0 : v ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hv
    exact zero_ne_one hv
  have hnormpos := n35_coord_norm_pos hv0 hvcoord
  have hnorm := n35_coord_norm_mul_eq_sq
    (x := (p : N35O3)) (y := v) (a := p) (b := 0)
    (c := c) (d := d) (r := 1) (by ring) hvcoord hv
  have hpform : n35NormForm p 0 = p ^ 2 := by
    simp [n35NormForm]
  rw [hpform] at hnorm
  have hpSq : 4 ≤ p ^ 2 := by nlinarith [sq_nonneg p]
  have hN : 1 ≤ n35NormForm c d := by omega
  have hle : p ^ 2 ≤ p ^ 2 * n35NormForm c d :=
    by simpa using mul_le_mul_of_nonneg_left hN (sq_nonneg p)
  rw [hnorm] at hle
  omega

theorem n35_two_irreducible : Irreducible (2 : N35O3) := by
  rw [irreducible_iff]
  refine ⟨n35_intCast_not_isUnit (by norm_num), ?_⟩
  intro x y hxy
  by_cases hxU : IsUnit x
  · exact Or.inl hxU
  by_cases hyU : IsUnit y
  · exact Or.inr hyU
  exfalso
  obtain ⟨a, b, hxcoord⟩ := n35O3_exists_coords x
  obtain ⟨c, d, hycoord⟩ := n35O3_exists_coords y
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx, zero_mul] at hxy
    norm_num at hxy
  have hy0 : y ≠ 0 := by
    intro hy
    rw [hy, mul_zero] at hxy
    norm_num at hxy
  have hNxpos := n35_coord_norm_pos hx0 hxcoord
  have hNypos := n35_coord_norm_pos hy0 hycoord
  have hNx1 : n35NormForm a b ≠ 1 := by
    intro h
    exact hxU (n35_isUnit_of_coord_norm_one hxcoord h)
  have hNy1 : n35NormForm c d ≠ 1 := by
    intro h
    exact hyU (n35_isUnit_of_coord_norm_one hycoord h)
  have hprod := n35_coord_norm_mul_eq_sq hxcoord hycoord hxy.symm
  norm_num at hprod
  have hNxlo : 2 ≤ n35NormForm a b := by omega
  have hNylo : 2 ≤ n35NormForm c d := by omega
  have hNx : n35NormForm a b = 2 := by nlinarith
  exact n35NormForm_ne_two a b hNx

theorem n35_five_irreducible : Irreducible (5 : N35O3) := by
  rw [irreducible_iff]
  refine ⟨n35_intCast_not_isUnit (by norm_num), ?_⟩
  intro x y hxy
  by_cases hxU : IsUnit x
  · exact Or.inl hxU
  by_cases hyU : IsUnit y
  · exact Or.inr hyU
  exfalso
  obtain ⟨a, b, hxcoord⟩ := n35O3_exists_coords x
  obtain ⟨c, d, hycoord⟩ := n35O3_exists_coords y
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx, zero_mul] at hxy
    norm_num at hxy
  have hy0 : y ≠ 0 := by
    intro hy
    rw [hy, mul_zero] at hxy
    norm_num at hxy
  have hNxpos := n35_coord_norm_pos hx0 hxcoord
  have hNypos := n35_coord_norm_pos hy0 hycoord
  have hNx1 : n35NormForm a b ≠ 1 := by
    intro h
    exact hxU (n35_isUnit_of_coord_norm_one hxcoord h)
  have hNy1 : n35NormForm c d ≠ 1 := by
    intro h
    exact hyU (n35_isUnit_of_coord_norm_one hycoord h)
  have hprod := n35_coord_norm_mul_eq_sq hxcoord hycoord hxy.symm
  norm_num at hprod
  have hNxlo : 2 ≤ n35NormForm a b := by omega
  have hNylo : 2 ≤ n35NormForm c d := by omega
  have hNxhi : n35NormForm a b ≤ 12 := by nlinarith
  have hNx : n35NormForm a b = 5 := by
    interval_cases hN : n35NormForm a b <;> omega
  exact n35NormForm_ne_five a b hNx


theorem n35Omega_sub_one_prime : Prime (n35Omega - 1) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3 ^ (0 + 1)} ℚ N35K3 := by
    simpa using n35K3_isCyclotomic
  simpa [n35Omega] using
    (IsPrimitiveRoot.zeta_sub_one_prime_of_ne_two
      (p := 3) (k := 0) n35Zeta_isPrimitive (by norm_num))

theorem n35SqrtNegThree_prime : Prime n35SqrtNegThree := by
  have hassoc : Associated (n35Omega - 1) n35SqrtNegThree := by
    refine ⟨-n35ZetaUnit, ?_⟩
    change (n35Omega - 1) * (-n35Omega) = 1 + 2 * n35Omega
    have hs : n35Omega ^ 2 = -n35Omega - 1 := by
      linear_combination n35Omega_relation
    rw [mul_neg]
    change -((n35Omega - 1) * n35Omega) = _
    rw [show (n35Omega - 1) * n35Omega =
      n35Omega ^ 2 - n35Omega by ring, hs]
    ring
  exact (hassoc.prime_iff).mp n35Omega_sub_one_prime

theorem n35K3_unit_mod_cube (u : N35O3ˣ) :
    (∃ v : N35O3ˣ, u = v ^ 3) ∨
      (∃ v : N35O3ˣ, u = n35ZetaUnit * v ^ 3) ∨
      (∃ v : N35O3ˣ, u = n35ZetaUnit ^ 2 * v ^ 3) := by
  have hu := IsCyclotomicExtension.Rat.Three.Units.mem
    n35Zeta_isPrimitive u
  change u ∈ [1, -1, n35ZetaUnit, -n35ZetaUnit,
    n35ZetaUnit ^ 2, -(n35ZetaUnit ^ 2)] at hu
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with h | h | h | h | h | h
  · exact Or.inl ⟨1, by simpa using h⟩
  · exact Or.inl ⟨-1, by rw [h]; ext; simp [pow_succ]⟩
  · exact Or.inr (Or.inl ⟨1, by simpa using h⟩)
  · exact Or.inr (Or.inl ⟨-1, by rw [h]; ext; simp [pow_succ]⟩)
  · exact Or.inr (Or.inr ⟨1, by simpa using h⟩)
  · exact Or.inr (Or.inr ⟨-1, by rw [h]; ext; simp [pow_succ]⟩)


theorem n35_coords_injective {a b c d : ℤ}
    (h : (a : N35O3) + (b : N35O3) * n35Omega =
      (c : N35O3) + (d : N35O3) * n35Omega) :
    a = c ∧ b = d := by
  have hc := congrArg n35ConjO h
  simp only [map_add, map_mul, map_intCast, n35ConjO_omega] at hc
  have hdiff : ((b - d : ℤ) : N35O3) *
      (n35Omega - n35Omega ^ 2) = 0 := by
    push_cast
    linear_combination h - hc
  have homega : n35Omega - n35Omega ^ 2 = n35SqrtNegThree := by
    unfold n35SqrtNegThree
    push_cast
    linear_combination -n35Omega_relation
  rw [homega] at hdiff
  have hq0 : n35SqrtNegThree ≠ 0 := by
    intro hq
    have hs := n35SqrtNegThree_sq
    rw [hq] at hs
    norm_num at hs
  have hbdO : ((b - d : ℤ) : N35O3) = 0 :=
    (mul_eq_zero.mp hdiff).resolve_right hq0
  have hbd : b = d := by
    have : b - d = 0 := by exact_mod_cast hbdO
    omega
  subst d
  have hacO : ((a - c : ℤ) : N35O3) = 0 := by
    push_cast
    linear_combination h
  have hac : a - c = 0 := by exact_mod_cast hacO
  exact ⟨by omega, rfl⟩

theorem n35_coord_cube (a b : ℤ) :
    ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 =
      (a ^ 3 + b ^ 3 - 3 * a * b ^ 2 : ℤ) +
        (3 * a ^ 2 * b - 3 * a * b ^ 2 : ℤ) * n35Omega := by
  have hs : n35Omega ^ 2 = -n35Omega - 1 := by
    linear_combination n35Omega_relation
  push_cast
  ring_nf
  rw [hs, n35Omega_cube]
  push_cast
  ring

@[simp] theorem n35ZetaUnit_val : (n35ZetaUnit : N35O3) = n35Omega := rfl

theorem n35ZetaUnit_norm_one :
    (n35ZetaUnit : N35O3) * n35ConjO (n35ZetaUnit : N35O3) = 1 := by
  rw [n35ZetaUnit_val, n35ConjO_omega]
  rw [show n35Omega * n35Omega ^ 2 = n35Omega ^ 3 by ring,
    n35Omega_cube]

theorem n35ZetaUnit_sq_norm_one :
    (n35ZetaUnit : N35O3) ^ 2 *
        n35ConjO ((n35ZetaUnit : N35O3) ^ 2) = 1 := by
  calc
    (n35ZetaUnit : N35O3) ^ 2 *
        n35ConjO ((n35ZetaUnit : N35O3) ^ 2) =
        ((n35ZetaUnit : N35O3) *
          n35ConjO (n35ZetaUnit : N35O3)) ^ 2 := by rw [map_pow]; ring
    _ = 1 := by rw [n35ZetaUnit_norm_one]; norm_num

end
end MazurProof.RationalPointsX135
end

-- Source FLT/Assumptions/MazurProof/XDelta19GoodDualDescent.lean:30-88; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodDualDescent
open scoped NumberField
open UniqueFactorizationMonoid MazurProof.RationalPointsX135 MazurProof.XDelta19GoodModel MazurProof.XDelta19GoodIsogeny
noncomputable section

local instance goodK3_isCyclotomic :
    IsCyclotomicExtension {3} ℚ N35K3 := by
  change IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ)
  exact CyclotomicField.isCyclotomicExtension 3 ℚ

local instance goodO3_isPrincipalIdealRing :
    IsPrincipalIdealRing N35O3 :=
  IsCyclotomicExtension.Rat.three_pid N35K3

/-! ## Primitive integral quotient coordinates -/

/-- Primitive integral coordinates on the small quotient. -/
theorem quotient_integral_model {s t : ℚ}
    (h : OnQuotient s t) :
    ∃ m n d : ℤ,
      0 < d ∧ Int.gcd m d = 1 ∧
      s = (m : ℚ) / (d : ℚ) ^ 2 ∧
      t = (n : ℚ) / (d : ℚ) ^ 3 ∧
      n ^ 2 = m ^ 3 -
        3 * d ^ 2 * (24 * m + 12 * d ^ 2) ^ 2 := by
  have hcubic : t ^ 2 = s ^ 3 + ((-1728 : ℤ) : ℚ) * s ^ 2 +
      ((-1728 : ℤ) : ℚ) * s + ((-432 : ℤ) : ℚ) := by
    unfold OnQuotient at h
    norm_num at h ⊢
    nlinarith
  obtain ⟨m, d, n, hd, hcop, hs, ht, hmodel⟩ :=
    integral_model_monic_const (-1728) (-1728) (-432) s t hcubic
  refine ⟨m, n, d, hd, hcop, hs, ht, ?_⟩
  linear_combination hmodel

/-- The Eisenstein factor of the primitive quotient equation. -/
noncomputable def dualA (m n d : ℤ) : N35O3 :=
  (n : N35O3) - n35SqrtNegThree *
    (d * (24 * m + 12 * d ^ 2) : ℤ)

/-- Conjugation changes the sign of the square-root term. -/
@[simp] theorem conj_dualA (m n d : ℤ) :
    n35ConjO (dualA m n d) =
      (n : N35O3) + n35SqrtNegThree *
        (d * (24 * m + 12 * d ^ 2) : ℤ) := by
  unfold dualA
  rw [map_sub, map_intCast, map_mul, n35ConjO_sqrtNegThree,
    map_intCast]
  ring

/-- The Eisenstein factor times its conjugate is the cube `m³`. -/
theorem dualA_mul_conj {m n d : ℤ}
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (24 * m + 12 * d ^ 2) ^ 2) :
    dualA m n d * n35ConjO (dualA m n d) =
      (m : N35O3) ^ 3 := by
  rw [conj_dualA]
  unfold dualA
  have hc := congrArg (fun z : ℤ => (z : N35O3)) hcurve
  push_cast at hc ⊢
  ring_nf
  rw [n35SqrtNegThree_sq]
  linear_combination hc
end
end MazurProof.XDelta19GoodDualDescent
end

-- Source FLT/Assumptions/MazurProof/XDelta19GoodDualDescent.lean:267-303; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodDualDescent
open scoped NumberField
open UniqueFactorizationMonoid MazurProof.RationalPointsX135 MazurProof.XDelta19GoodModel MazurProof.XDelta19GoodIsogeny
local instance : IsCyclotomicExtension {3} ℚ N35K3 := CyclotomicField.isCyclotomicExtension 3 ℚ
local instance : IsPrincipalIdealRing N35O3 := IsCyclotomicExtension.Rat.three_pid N35K3
noncomputable section
/-- Taking norms of a unit-times-cube identity recovers the primitive
horizontal numerator as an Eisenstein norm. -/
theorem m_eq_coord_norm_of_unit_cube
    {m n d a b : ℤ} {u : N35O3}
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (24 * m + 12 * d ^ 2) ^ 2)
    (hu : u * n35ConjO u = 1)
    (hclass : dualA m n d =
      u * ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) :
    m = n35NormForm a b := by
  have heqO : (m : N35O3) ^ 3 =
      (n35NormForm a b : N35O3) ^ 3 := by
    calc
      (m : N35O3) ^ 3 =
          dualA m n d * n35ConjO (dualA m n d) :=
        (dualA_mul_conj hcurve).symm
      _ = (u * ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) *
          n35ConjO
            (u * ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) := by
        rw [hclass]
      _ = (n35NormForm a b : N35O3) ^ 3 := by
        rw [map_mul, map_pow]
        rw [show
          (u * ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) *
              (n35ConjO u *
                n35ConjO
                  ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) =
            (u * n35ConjO u) *
              (((a : N35O3) + (b : N35O3) * n35Omega) *
                n35ConjO
                  ((a : N35O3) + (b : N35O3) * n35Omega)) ^ 3 by ring,
          hu, one_mul, n35_coord_mul_conj]
  have heqZ : m ^ 3 = n35NormForm a b ^ 3 := by
    exact_mod_cast heqO
  exact (show Odd 3 by decide).pow_injective heqZ

/-! ## Finite exclusion of the two nontrivial unit classes -/
end
end MazurProof.XDelta19GoodDualDescent
end

namespace MazurProof.XDelta19GoodDualDescent
theorem dualA_is_cube {m n d : ℤ} (hd : 0 < d) (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 - 3 * d ^ 2 * (24 * m + 12 * d ^ 2) ^ 2) :
    ∃ B : MazurHuang.EisensteinDescent35.N35O3,
      dualA m n d = B ^ 3 :=
  MazurHuang.N19.primitive_quotient_eisenstein_factor_is_cube hd hcop hcurve
end MazurProof.XDelta19GoodDualDescent

-- Source FLT/Assumptions/MazurProof/XDelta19GoodDualDescent.lean:528-675; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodDualDescent
open scoped NumberField
open UniqueFactorizationMonoid MazurProof.RationalPointsX135 MazurProof.XDelta19GoodModel MazurProof.XDelta19GoodIsogeny
local instance : IsCyclotomicExtension {3} ℚ N35K3 := CyclotomicField.isCyclotomicExtension 3 ℚ
local instance : IsPrincipalIdealRing N35O3 := IsCyclotomicExtension.Rat.three_pid N35K3
noncomputable section
/-- The recovered cubic-cover coordinates lie on the good model. -/
private theorem inverse_good_identity {u v : ℚ} (hv : v + 8 ≠ 0)
    (hrel : u ^ 2 * v + 8 * u ^ 2 - v ^ 3 +
      24 * v ^ 2 + 4 = 0) :
    (u * (-228 / (v + 8)) / 3) ^ 2 =
      (-228 / (v + 8)) ^ 3 +
        (8 * (-228 / (v + 8)) + 76) ^ 2 := by
  field_simp [hv]
  linear_combination 51984 * hrel

/-- The recovered point has the prescribed forward horizontal
coordinate. -/
private theorem inverse_x_identity {u v s : ℚ} (hv : v + 8 ≠ 0)
    (hs : s = u ^ 2 + 3 * v ^ 2)
    (hrel : u ^ 2 * v + 8 * u ^ 2 - v ^ 3 +
      24 * v ^ 2 + 4 = 0) :
    (9 * (-228 / (v + 8)) ^ 3 +
        768 * (-228 / (v + 8)) ^ 2 +
        21888 * (-228 / (v + 8)) + 207936) /
      (-228 / (v + 8)) ^ 2 = s := by
  rw [hs]
  field_simp [hv]
  linear_combination (-51984) * hrel

/-- The recovered point has the prescribed forward vertical
coordinate. -/
private theorem inverse_y_identity {u v t : ℚ} (hv : v + 8 ≠ 0)
    (ht : t = u ^ 3 - 9 * u * v ^ 2)
    (hrel : u ^ 2 * v + 8 * u ^ 2 - v ^ 3 +
      24 * v ^ 2 + 4 = 0) :
    (27 * (-228 / (v + 8)) ^ 3 *
          (u * (-228 / (v + 8)) / 3) -
        65664 * (-228 / (v + 8)) *
          (u * (-228 / (v + 8)) / 3) -
        1247616 * (u * (-228 / (v + 8)) / 3)) /
      (-228 / (v + 8)) ^ 3 = t := by
  rw [ht]
  field_simp [hv]
  linear_combination (-155952 * u) * hrel

/-- Every affine rational point on the small quotient has an explicit
preimage under the forward degree-three isogeny. -/
theorem quotient_affine_has_threeIsogeny_preimage {s t : ℚ}
    (hquotient : OnQuotient s t) :
    ∃ x y : ℚ, x ≠ 0 ∧ OnGood x y ∧
      threeIsogenyX x = s ∧ threeIsogenyY x y = t := by
  obtain ⟨m, n, d, hd, hcop, hs, ht, hcurve⟩ :=
    quotient_integral_model hquotient
  obtain ⟨B, hBcube⟩ := dualA_is_cube hd hcop hcurve
  obtain ⟨a, b, hBcoord⟩ := n35O3_exists_coords B
  have hclass : dualA m n d =
      ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := by
    simpa [hBcoord] using hBcube
  have hm : m = n35NormForm a b :=
    m_eq_coord_norm_of_unit_cube (u := (1 : N35O3)) hcurve
      (by simp only [map_one, one_mul])
      (by simpa only [one_mul] using hclass)
  let C : ℤ := d * (24 * m + 12 * d ^ 2)
  let R : ℤ := a ^ 3 + b ^ 3 - 3 * a * b ^ 2
  let I : ℤ := 3 * a ^ 2 * b - 3 * a * b ^ 2
  have hcoords :
      ((n - C : ℤ) : N35O3) + ((-2 * C : ℤ) : N35O3) * n35Omega =
        (R : N35O3) + (I : N35O3) * n35Omega := by
    calc
      ((n - C : ℤ) : N35O3) +
          ((-2 * C : ℤ) : N35O3) * n35Omega =
          dualA m n d := by
        unfold dualA n35SqrtNegThree C
        push_cast
        ring
      _ = ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := hclass
      _ = (R : N35O3) + (I : N35O3) * n35Omega := by
        rw [n35_coord_cube]
  have hreal : n - C = R := (n35_coords_injective hcoords).1
  have himag : -2 * C = I := (n35_coords_injective hcoords).2
  have hrealQ : ((n - C : ℤ) : ℚ) = (R : ℚ) := by
    exact_mod_cast hreal
  have himagQ : ((-2 * C : ℤ) : ℚ) = (I : ℚ) := by
    exact_mod_cast himag
  let u : ℚ := (2 * a - b : ℤ) / (2 * d : ℤ)
  let v : ℚ := (b : ℚ) / (2 * d : ℤ)
  have hdQ : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hd)
  have hsuv : s = u ^ 2 + 3 * v ^ 2 := by
    rw [hs, hm]
    unfold u v n35NormForm
    push_cast
    field_simp [hdQ]
    ring
  have htuv : t = u ^ 3 - 9 * u * v ^ 2 := by
    rw [ht]
    unfold u v
    push_cast
    field_simp [hdQ]
    dsimp [C, R] at hrealQ
    dsimp [C, I] at himagQ
    push_cast at hrealQ himagQ
    linear_combination 8 * hrealQ - 4 * himagQ
  have himaguv :
      -(24 * s + 12) = 3 * u ^ 2 * v - 3 * v ^ 3 := by
    rw [hs]
    unfold u v
    push_cast
    field_simp [hdQ]
    dsimp [C, I] at himagQ
    push_cast at himagQ
    linear_combination 4 * himagQ
  have hrel :
      u ^ 2 * v + 8 * u ^ 2 - v ^ 3 + 24 * v ^ 2 + 4 = 0 := by
    rw [hsuv] at himaguv
    linear_combination (-1 / 3 : ℚ) * himaguv
  have hv8 : v + 8 ≠ 0 := by
    intro hv
    have hv' : v = -8 := by
      linarith
    rw [hv'] at hrel
    norm_num at hrel
    nlinarith
  let x : ℚ := -228 / (v + 8)
  let y : ℚ := u * x / 3
  have hx0 : x ≠ 0 := by
    unfold x
    exact div_ne_zero (by norm_num) hv8
  refine ⟨x, y, hx0, ?_, ?_, ?_⟩
  · exact inverse_good_identity hv8 hrel
  · exact inverse_x_identity hv8 hsuv hrel
  · exact inverse_y_identity hv8 htuv hrel

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

theorem solution {s t : ℚ} (h : t ^ 2 = s ^ 3 - 3 * (24 * s + 12) ^ 2) :
    ∃ x y : ℚ, x ≠ 0 ∧ y ^ 2 = x ^ 3 + (8 * x + 76) ^ 2 ∧
      (9 * x ^ 3 + 768 * x ^ 2 + 21888 * x + 207936) / x ^ 2 = s ∧
      (27 * x ^ 3 * y - 65664 * x * y - 1247616 * y) / x ^ 3 = t := by
  exact MazurProof.XDelta19GoodDualDescent.quotient_affine_has_threeIsogeny_preimage h
