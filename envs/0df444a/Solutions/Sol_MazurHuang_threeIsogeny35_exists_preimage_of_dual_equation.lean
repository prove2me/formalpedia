-- Prove2me | solution 1 for MazurHuang.threeIsogeny35_exists_preimage_of_dual_equation
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T21:12:39.264265+00:00
-- url     : https://prove2.me/submissions/01cacd73-514c-41ca-9a51-31c4d5cd6b48

/-
The 3-isogeny onto the dual curve is surjective on affine rational points.

Author: Xiang Huang
License: Apache-2.0
Source: Xiang Huang's FLT fork, https://github.com/xiangyazi24/FLT,
  commit 51bbb4f191ad0d3753b87123635c100a638ae580
  (Lean v4.31.0-rc2), ported to Lean v4.33.1 / Mathlib 0df444a360ea.
Port repairs inside the source ranges are marked `port v4.33.1` or listed in the
port notes of the staging repository; no statement of a non-private declaration
was changed.

Contents, in order (each source range sits in its own `section`):
  * FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean (integral model of the dual curve, coordinates and norms in Z[omega], exclusion of the two
    nontrivial cube classes, n35_dual_affine_has_three_isogeny_preimage; the three cube classes and
    the two congruence facts are taken from published theorems)
  * the published statement
-/
import Mathlib
import Definitions.Def_MazurHuang_EisensteinDescent35
import Theorems.Thm_MazurHuang_three_dvd_of_threeIsogeny35_cover_eq_zero
import Theorems.Thm_MazurHuang_eisensteinDescent35_dualA_cube_class

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean. -/
section

namespace MazurProof.RationalPointsX135

noncomputable section

open scoped NumberField

open UniqueFactorizationMonoid

open MazurHuang.EisensteinDescent35

-- FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean, lines 138-250
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

-- FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean, lines 569-576
local instance n35K3_isCyclotomic :
    IsCyclotomicExtension {3} ℚ N35K3 := by
  change IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ)
  exact CyclotomicField.isCyclotomicExtension 3 ℚ

local instance n35O3_isPrincipalIdealRing :
    IsPrincipalIdealRing N35O3 :=
  IsCyclotomicExtension.Rat.three_pid N35K3

-- FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean, lines 656-764
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

-- FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean, lines 912-926
theorem n35_dual_integral_model {s t : ℚ}
    (h : t ^ 2 = s ^ 3 - 3 * (12 * s + 1500) ^ 2) :
    ∃ m n d : ℤ,
      0 < d ∧ Int.gcd m d = 1 ∧
      s = (m : ℚ) / (d : ℚ) ^ 2 ∧
      t = (n : ℚ) / (d : ℚ) ^ 3 ∧
      n ^ 2 = m ^ 3 - 3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2 := by
  have hcubic : t ^ 2 = s ^ 3 + ((-432 : ℤ) : ℚ) * s ^ 2 +
      ((-108000 : ℤ) : ℚ) * s + ((-6750000 : ℤ) : ℚ) := by
    norm_num at h ⊢
    nlinarith
  obtain ⟨m, d, n, hd, hcop, hs, ht, hmodel⟩ :=
    integral_model_monic_const (-432) (-108000) (-6750000) s t hcubic
  refine ⟨m, n, d, hd, hcop, hs, ht, ?_⟩
  linear_combination hmodel

-- FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean, lines 932-952
@[simp] theorem n35ConjO_dualA (m n d : ℤ) :
    n35ConjO (n35DualA m n d) =
      (n : N35O3) + n35SqrtNegThree *
      (d * (12 * m + 1500 * d ^ 2) : ℤ) := by
  unfold n35DualA
  rw [map_sub, map_intCast, map_mul, n35ConjO_sqrtNegThree,
    map_intCast]
  ring

theorem n35DualA_mul_conj {m n d : ℤ}
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2) :
    n35DualA m n d * n35ConjO (n35DualA m n d) =
      (m : N35O3) ^ 3 := by
  rw [n35ConjO_dualA]
  unfold n35DualA
  have hc := congrArg (fun z : ℤ => (z : N35O3)) hcurve
  push_cast at hc ⊢
  ring_nf
  rw [n35SqrtNegThree_sq]
  linear_combination hc

/-- The three cube classes of the descent element (statement as in
`FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean`), here the published theorem
`MazurHuang.eisensteinDescent35_dualA_cube_class`. -/
theorem n35DualA_three_cubeclasses
    {m n d : ℤ} (hd : 0 < d) (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2) :
    (∃ B : N35O3, n35DualA m n d = B ^ 3) ∨
      (∃ B : N35O3, n35DualA m n d = n35ZetaUnit * B ^ 3) ∨
      (∃ B : N35O3, n35DualA m n d = n35ZetaUnit ^ 2 * B ^ 3) :=
  MazurHuang.eisensteinDescent35_dualA_cube_class hd hcop hcurve

-- FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean, lines 1113-1209
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

theorem n35_m_eq_coord_norm_of_unit_cube
    {m n d a b : ℤ} {u : N35O3}
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2)
    (hu : u * n35ConjO u = 1)
    (hclass : n35DualA m n d =
      u * ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) :
    m = n35NormForm a b := by
  have heqO : (m : N35O3) ^ 3 = (n35NormForm a b : N35O3) ^ 3 := by
    calc
      (m : N35O3) ^ 3 =
          n35DualA m n d * n35ConjO (n35DualA m n d) :=
        (n35DualA_mul_conj hcurve).symm
      _ = (u * ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) *
          n35ConjO (u * ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) := by
        rw [hclass]
      _ = (n35NormForm a b : N35O3) ^ 3 := by
        rw [map_mul, map_pow]
        rw [show (u * ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) *
            (n35ConjO u * n35ConjO
              ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) =
            (u * n35ConjO u) *
              (((a : N35O3) + (b : N35O3) * n35Omega) *
                n35ConjO ((a : N35O3) + (b : N35O3) * n35Omega)) ^ 3 by ring,
          hu, one_mul, n35_coord_mul_conj]
  have heqZ : m ^ 3 = n35NormForm a b ^ 3 := by exact_mod_cast heqO
  exact (show Odd 3 by decide).pow_injective heqZ

def n35CoverRho (X Y Z : ℤ) : ℤ :=
  X ^ 3 - 3 * Y ^ 3 + 3000 * Z ^ 3 + 3 * X ^ 2 * Y -
    9 * X * Y ^ 2 + 24 * X ^ 2 * Z + 72 * Y ^ 2 * Z

def n35CoverRhoSq (X Y Z : ℤ) : ℤ :=
  X ^ 3 + 3 * Y ^ 3 + 3000 * Z ^ 3 - 3 * X ^ 2 * Y -
    9 * X * Y ^ 2 + 24 * X ^ 2 * Z + 72 * Y ^ 2 * Z

/-- A zero of the first cover form is divisible by three in every coordinate (statement as in
`FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean`), here the published theorem
`MazurHuang.three_dvd_of_threeIsogeny35_cover_eq_zero`. -/
theorem n35CoverRho_all_three_dvd {X Y Z : ℤ}
    (h : n35CoverRho X Y Z = 0) : 3 ∣ X ∧ 3 ∣ Y ∧ 3 ∣ Z :=
  MazurHuang.three_dvd_of_threeIsogeny35_cover_eq_zero h

/-- The same for the second cover form (statement as in the source file).  The source checks it
by a second enumeration modulo 27; since `n35CoverRhoSq X Y Z = n35CoverRho X (-Y) Z`, it follows
from the first form. -/
theorem n35CoverRhoSq_all_three_dvd {X Y Z : ℤ}
    (h : n35CoverRhoSq X Y Z = 0) : 3 ∣ X ∧ 3 ∣ Y ∧ 3 ∣ Z := by
  have h' : n35CoverRho X (-Y) Z = 0 := by
    unfold n35CoverRhoSq at h
    unfold n35CoverRho
    linear_combination h
  obtain ⟨hX, hY, hZ⟩ := n35CoverRho_all_three_dvd h'
  exact ⟨hX, (dvd_neg (a := (3 : ℤ)) (b := Y)).mp hY, hZ⟩

-- FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean, lines 1265-1502
private theorem n35_common_three_contradiction {m d a b : ℤ}
    (hcop : Int.gcd m d = 1) (hm : m = n35NormForm a b)
    (h3x : (3 : ℤ) ∣ 2 * a - b) (h3b : (3 : ℤ) ∣ b)
    (h3z : (3 : ℤ) ∣ 2 * d) : False := by
  have h32a : (3 : ℤ) ∣ 2 * a := by
    simpa [sub_eq_add_neg, add_assoc] using dvd_add h3x h3b
  have h3a : (3 : ℤ) ∣ a :=
    ((by norm_num : Prime (3 : ℤ)).dvd_mul.mp h32a).resolve_left (by norm_num)
  have h3d : (3 : ℤ) ∣ d :=
    ((by norm_num : Prime (3 : ℤ)).dvd_mul.mp h3z).resolve_left (by norm_num)
  obtain ⟨ka, hka⟩ := h3a
  obtain ⟨kb, hkb⟩ := h3b
  have h3m : (3 : ℤ) ∣ m := by
    refine ⟨3 * (ka ^ 2 - ka * kb + kb ^ 2), ?_⟩
    rw [hm, hka, hkb]
    unfold n35NormForm
    ring
  have hcopI : IsCoprime m d := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hu : IsUnit (3 : ℤ) := hcopI.isUnit_of_dvd' h3m h3d
  rw [Int.isUnit_iff_abs_eq] at hu
  norm_num at hu

theorem n35DualA_not_zeta_cube
    {m n d : ℤ} (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2)
    {B : N35O3}
    (hclass : n35DualA m n d = (n35ZetaUnit : N35O3) * B ^ 3) : False := by
  obtain ⟨a, b, hB⟩ := n35O3_exists_coords B
  have hclass' : n35DualA m n d = (n35ZetaUnit : N35O3) *
      ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := by
    simpa [hB] using hclass
  have hm := n35_m_eq_coord_norm_of_unit_cube hcurve
    n35ZetaUnit_norm_one hclass'
  let C : ℤ := d * (12 * m + 1500 * d ^ 2)
  let R : ℤ := a ^ 3 + b ^ 3 - 3 * a * b ^ 2
  let I : ℤ := 3 * a ^ 2 * b - 3 * a * b ^ 2
  have hcoords :
      ((n - C : ℤ) : N35O3) + ((-2 * C : ℤ) : N35O3) * n35Omega =
        ((-I : ℤ) : N35O3) + ((R - I : ℤ) : N35O3) * n35Omega := by
    calc
      ((n - C : ℤ) : N35O3) + ((-2 * C : ℤ) : N35O3) * n35Omega =
          n35DualA m n d := by
        unfold n35DualA n35SqrtNegThree C
        push_cast
        ring
      _ = (n35ZetaUnit : N35O3) *
          ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := hclass'
      _ = ((-I : ℤ) : N35O3) + ((R - I : ℤ) : N35O3) * n35Omega := by
        rw [n35_coord_cube, n35ZetaUnit_val]
        have hs : n35Omega ^ 2 = -n35Omega - 1 := by
          linear_combination n35Omega_relation
        unfold R I
        push_cast
        ring_nf
        rw [hs]
        push_cast
        ring
  have hcoeff : -2 * C = R - I := (n35_coords_injective hcoords).2
  have hG : n35CoverRhoSq (2 * a - b) b (2 * d) = 0 := by
    dsimp [C, R, I] at hcoeff
    rw [hm] at hcoeff
    unfold n35NormForm at hcoeff
    unfold n35CoverRhoSq
    linear_combination -8 * hcoeff
  obtain ⟨h3x, h3b, h3z⟩ := n35CoverRhoSq_all_three_dvd hG
  exact n35_common_three_contradiction hcop hm h3x h3b h3z

theorem n35DualA_not_zeta_sq_cube
    {m n d : ℤ} (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2)
    {B : N35O3}
    (hclass : n35DualA m n d = (n35ZetaUnit : N35O3) ^ 2 * B ^ 3) : False := by
  obtain ⟨a, b, hB⟩ := n35O3_exists_coords B
  have hclass' : n35DualA m n d = (n35ZetaUnit : N35O3) ^ 2 *
      ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := by
    simpa [hB] using hclass
  have hm := n35_m_eq_coord_norm_of_unit_cube hcurve
    n35ZetaUnit_sq_norm_one hclass'
  let C : ℤ := d * (12 * m + 1500 * d ^ 2)
  let R : ℤ := a ^ 3 + b ^ 3 - 3 * a * b ^ 2
  let I : ℤ := 3 * a ^ 2 * b - 3 * a * b ^ 2
  have hcoords :
      ((n - C : ℤ) : N35O3) + ((-2 * C : ℤ) : N35O3) * n35Omega =
        ((I - R : ℤ) : N35O3) + ((-R : ℤ) : N35O3) * n35Omega := by
    calc
      ((n - C : ℤ) : N35O3) + ((-2 * C : ℤ) : N35O3) * n35Omega =
          n35DualA m n d := by
        unfold n35DualA n35SqrtNegThree C
        push_cast
        ring
      _ = (n35ZetaUnit : N35O3) ^ 2 *
          ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := hclass'
      _ = ((I - R : ℤ) : N35O3) + ((-R : ℤ) : N35O3) * n35Omega := by
        rw [n35_coord_cube, n35ZetaUnit_val]
        have hs : n35Omega ^ 2 = -n35Omega - 1 := by
          linear_combination n35Omega_relation
        unfold R I
        push_cast
        ring_nf
        rw [hs, n35Omega_cube]
        push_cast
        ring
  have hcoeff : -2 * C = -R := (n35_coords_injective hcoords).2
  have hG : n35CoverRho (-(2 * a - b)) (-b) (2 * d) = 0 := by
    dsimp [C, R] at hcoeff
    rw [hm] at hcoeff
    unfold n35NormForm at hcoeff
    unfold n35CoverRho
    linear_combination -8 * hcoeff
  obtain ⟨h3xneg, h3bneg, h3z⟩ := n35CoverRho_all_three_dvd hG
  have h3x : (3 : ℤ) ∣ 2 * a - b := by
    simpa only [dvd_neg] using h3xneg
  have h3b : (3 : ℤ) ∣ b := by
    simpa only [dvd_neg] using h3bneg
  exact n35_common_three_contradiction hcop hm h3x h3b h3z

theorem n35DualA_is_cube
    {m n d : ℤ} (hd : 0 < d) (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2) :
    ∃ B : N35O3, n35DualA m n d = B ^ 3 := by
  rcases n35DualA_three_cubeclasses hd hcop hcurve with h | h | h
  · exact h
  · obtain ⟨B, hB⟩ := h
    exact (n35DualA_not_zeta_cube hcop hcurve hB).elim
  · obtain ⟨B, hB⟩ := h
    exact (n35DualA_not_zeta_sq_cube hcop hcurve hB).elim

private theorem n35_inverse_short_identity {u v : ℚ} (hv : v + 4 ≠ 0)
    (hrel : u ^ 2 * v + 4 * u ^ 2 - v ^ 3 + 12 * v ^ 2 + 500 = 0) :
    (u * (-84 / (v + 4)) / 3) ^ 2 =
      (-84 / (v + 4)) ^ 3 + (4 * (-84 / (v + 4)) + 28) ^ 2 := by
  field_simp [hv]
  linear_combination 7056 * hrel

private theorem n35_inverse_x_identity {u v s : ℚ} (hv : v + 4 ≠ 0)
    (hs : s = u ^ 2 + 3 * v ^ 2)
    (hrel : u ^ 2 * v + 4 * u ^ 2 - v ^ 3 + 12 * v ^ 2 + 500 = 0) :
    (9 * (-84 / (v + 4)) ^ 3 + 192 * (-84 / (v + 4)) ^ 2 +
        4032 * (-84 / (v + 4)) + 28224) /
      (-84 / (v + 4)) ^ 2 = s := by
  rw [hs]
  field_simp [hv]
  linear_combination (-7056) * hrel

private theorem n35_inverse_y_identity {u v t : ℚ} (hv : v + 4 ≠ 0)
    (ht : t = u ^ 3 - 9 * u * v ^ 2)
    (hrel : u ^ 2 * v + 4 * u ^ 2 - v ^ 3 + 12 * v ^ 2 + 500 = 0) :
    (27 * (-84 / (v + 4)) ^ 3 * (u * (-84 / (v + 4)) / 3) -
        12096 * (-84 / (v + 4)) * (u * (-84 / (v + 4)) / 3) -
        169344 * (u * (-84 / (v + 4)) / 3)) /
      (-84 / (v + 4)) ^ 3 = t := by
  rw [ht]
  field_simp [hv]
  linear_combination (-21168 * u) * hrel

theorem n35_dual_affine_has_three_isogeny_preimage {s t : ℚ}
    (hdual : t ^ 2 = s ^ 3 - 3 * (12 * s + 1500) ^ 2) :
    ∃ x y : ℚ, x ≠ 0 ∧
      y ^ 2 = x ^ 3 + (4 * x + 28) ^ 2 ∧
      (9 * x ^ 3 + 192 * x ^ 2 + 4032 * x + 28224) / x ^ 2 = s ∧
      (27 * x ^ 3 * y - 12096 * x * y - 169344 * y) / x ^ 3 = t := by
  obtain ⟨m, n, d, hd, hcop, hs, ht, hcurve⟩ :=
    n35_dual_integral_model hdual
  obtain ⟨B, hBcube⟩ := n35DualA_is_cube hd hcop hcurve
  obtain ⟨a, b, hBcoord⟩ := n35O3_exists_coords B
  have hclass : n35DualA m n d =
      ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := by
    simpa [hBcoord] using hBcube
  have hm : m = n35NormForm a b :=
    n35_m_eq_coord_norm_of_unit_cube (u := (1 : N35O3)) hcurve
      (by simp only [map_one, one_mul])
      (by simpa only [one_mul] using hclass)
  let C : ℤ := d * (12 * m + 1500 * d ^ 2)
  let R : ℤ := a ^ 3 + b ^ 3 - 3 * a * b ^ 2
  let I : ℤ := 3 * a ^ 2 * b - 3 * a * b ^ 2
  have hcoords :
      ((n - C : ℤ) : N35O3) + ((-2 * C : ℤ) : N35O3) * n35Omega =
        (R : N35O3) + (I : N35O3) * n35Omega := by
    calc
      ((n - C : ℤ) : N35O3) + ((-2 * C : ℤ) : N35O3) * n35Omega =
          n35DualA m n d := by
        unfold n35DualA n35SqrtNegThree C
        push_cast
        ring
      _ = ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := hclass
      _ = (R : N35O3) + (I : N35O3) * n35Omega := by
        rw [n35_coord_cube]
  have hreal : n - C = R := (n35_coords_injective hcoords).1
  have himag : -2 * C = I := (n35_coords_injective hcoords).2
  have hrealQ : ((n - C : ℤ) : ℚ) = (R : ℚ) := by exact_mod_cast hreal
  have himagQ : ((-2 * C : ℤ) : ℚ) = (I : ℚ) := by exact_mod_cast himag
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
  have himaguv : -(12 * s + 1500) = 3 * u ^ 2 * v - 3 * v ^ 3 := by
    rw [hs]
    unfold u v
    push_cast
    field_simp [hdQ]
    dsimp [C, I] at himagQ
    push_cast at himagQ
    linear_combination 4 * himagQ
  have hrel : u ^ 2 * v + 4 * u ^ 2 - v ^ 3 + 12 * v ^ 2 + 500 = 0 := by
    rw [hsuv] at himaguv
    linear_combination (-1 / 3 : ℚ) * himaguv
  have hv4 : v + 4 ≠ 0 := by
    intro hv
    have hv' : v = -4 := by linarith
    rw [hv'] at hrel
    norm_num at hrel
    linarith
  let x : ℚ := -84 / (v + 4)
  let y : ℚ := u * x / 3
  have hx0 : x ≠ 0 := by
    unfold x
    exact div_ne_zero (by norm_num) hv4
  refine ⟨x, y, hx0, ?_, ?_, ?_⟩
  · exact n35_inverse_short_identity hv4 hrel
  · exact n35_inverse_x_identity hv4 hsuv hrel
  · exact n35_inverse_y_identity hv4 htuv hrel


end

end MazurProof.RationalPointsX135

end

theorem solution
    {s t : ℚ}
    (hdual : t ^ 2 = s ^ 3 - 3 * (12 * s + 1500) ^ 2) :
    ∃ x y : ℚ, x ≠ 0 ∧
      y ^ 2 = x ^ 3 + (4 * x + 28) ^ 2 ∧
      (9 * x ^ 3 + 192 * x ^ 2 + 4032 * x + 28224) / x ^ 2 = s ∧
      (27 * x ^ 3 * y - 12096 * x * y - 169344 * y) / x ^ 3 = t :=
  MazurProof.RationalPointsX135.n35_dual_affine_has_three_isogeny_preimage hdual
