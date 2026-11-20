-- Prove2me | solution 1 for NCQuadLB.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-20T01:21:30.232194+00:00
-- url     : https://prove2.me/submissions/a4ef7d6f-ff8f-4e83-8987-81138bafd143

import Mathlib
import Definitions.Def_NCQuadLB_Circuit
import Definitions.Def_NCQuadLB_pal

set_option autoImplicit false

namespace NCQuadLB_Proof

open NCQuadLB

/-! ### Part 1: Elementary `ℕ` Combinatorial Lower Bound -/

lemma four_pow_le_twelve_mul_factorial : ∀ k : ℕ, 4 ^ k ≤ 12 * k.factorial
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | k + 4 => by
    have ih := four_pow_le_twelve_mul_factorial (k + 3)
    have h4 : 4 ≤ k + 4 := by omega
    calc
      4 ^ (k + 4) = 4 * 4 ^ (k + 3) := by ring
      _ ≤ 4 * (12 * (k + 3).factorial) := Nat.mul_le_mul_left 4 ih
      _ ≤ (k + 4) * (12 * (k + 3).factorial) := Nat.mul_le_mul_right _ h4
      _ = 12 * ((k + 3 + 1) * (k + 3).factorial) := by ring
      _ = 12 * (k + 3 + 1).factorial := by rw [← Nat.factorial_succ]

lemma sum_two_pow_lt : ∀ m : ℕ, (∑ k ∈ Finset.range m, 2 ^ k) < 2 ^ m
  | 0 => by simp
  | m + 1 => by
    have ih := sum_two_pow_lt m
    rw [Finset.sum_range_succ, pow_succ]
    omega

lemma sum_two_pow_sub_lt (n : ℕ) : (∑ k ∈ Finset.range (n + 1), 2 ^ (n - k)) < 2 * 2 ^ n := by
  have h := Finset.sum_range_reflect (fun k => 2 ^ k) (n + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [h]
  calc
    (∑ k ∈ Finset.range (n + 1), 2 ^ k) < 2 ^ (n + 1) := sum_two_pow_lt (n + 1)
    _ = 2 * 2 ^ n := by ring

lemma add_two_pow_lt (n : ℕ) (hn : 1 ≤ n) : (n + 2) ^ n < 64 * n ^ n := by
  have hterm : ∀ k ∈ Finset.range (n + 1),
      2 ^ n * (2 ^ k * n ^ (n - k) * n.choose k) ≤ 2 ^ (n - k) * (12 * n ^ n) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hpow2 : 2 ^ n * 2 ^ k = 2 ^ (n - k) * 4 ^ k := by
      have h1 : 2 ^ n = 2 ^ (n - k) * 2 ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hkn]
      have h2 : 2 ^ k * 2 ^ k = 4 ^ k := by
        rw [← mul_pow]
        norm_num
      calc
        2 ^ n * 2 ^ k = 2 ^ (n - k) * (2 ^ k * 2 ^ k) := by rw [h1, mul_assoc]
        _ = 2 ^ (n - k) * 4 ^ k := by rw [h2]
    have hchoose : 4 ^ k * n.choose k ≤ 12 * n ^ k := by
      calc
        4 ^ k * n.choose k ≤ (12 * k.factorial) * n.choose k :=
          Nat.mul_le_mul_right _ (four_pow_le_twelve_mul_factorial k)
        _ = 12 * (n.choose k * k.factorial) := by ring
        _ = 12 * n.descFactorial k := by rw [Nat.descFactorial_eq_factorial_mul_choose]; ring
        _ ≤ 12 * n ^ k := Nat.mul_le_mul_left 12 (Nat.descFactorial_le_pow n k)
    have hpow_n : n ^ k * n ^ (n - k) = n ^ n := by
      rw [← pow_add, Nat.add_sub_of_le hkn]
    calc
      2 ^ n * (2 ^ k * n ^ (n - k) * n.choose k)
          = (2 ^ n * 2 ^ k) * (n.choose k * n ^ (n - k)) := by ring
      _ = 2 ^ (n - k) * ((4 ^ k * n.choose k) * n ^ (n - k)) := by rw [hpow2]; ring
      _ ≤ 2 ^ (n - k) * ((12 * n ^ k) * n ^ (n - k)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hchoose)
      _ = 2 ^ (n - k) * (12 * (n ^ k * n ^ (n - k))) := by ring
      _ = 2 ^ (n - k) * (12 * n ^ n) := by rw [hpow_n]
  have hsum : 2 ^ n * (n + 2) ^ n ≤ (∑ k ∈ Finset.range (n + 1), 2 ^ (n - k)) * (12 * n ^ n) := by
    have hcomm : n + 2 = 2 + n := by omega
    have hpow := add_pow 2 n n
    simp only [Nat.cast_id] at hpow
    calc
      2 ^ n * (n + 2) ^ n
          = 2 ^ n * ∑ k ∈ Finset.range (n + 1), 2 ^ k * n ^ (n - k) * n.choose k := by
              rw [hcomm, hpow]
      _ = ∑ k ∈ Finset.range (n + 1), 2 ^ n * (2 ^ k * n ^ (n - k) * n.choose k) := by
            rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.range (n + 1), 2 ^ (n - k) * (12 * n ^ n) := Finset.sum_le_sum hterm
      _ = (∑ k ∈ Finset.range (n + 1), 2 ^ (n - k)) * (12 * n ^ n) := by rw [← Finset.sum_mul]
  have hnn_pos : 0 < 12 * n ^ n := Nat.mul_pos (by decide) (Nat.pow_pos (by omega))
  have hlt : 2 ^ n * (n + 2) ^ n < 2 ^ n * (64 * n ^ n) := by
    calc
      2 ^ n * (n + 2) ^ n ≤ (∑ k ∈ Finset.range (n + 1), 2 ^ (n - k)) * (12 * n ^ n) := hsum
      _ < (2 * 2 ^ n) * (12 * n ^ n) :=
          (Nat.mul_lt_mul_right hnn_pos).mpr (sum_two_pow_sub_lt n)
      _ = 2 ^ n * (24 * n ^ n) := by ring
      _ ≤ 2 ^ n * (64 * n ^ n) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by decide))
  exact Nat.lt_of_mul_lt_mul_left hlt

lemma bernstein_nat (n d S : ℕ) (hn : 2 ≤ n) :
    2 ^ d * n ^ S * (∑ k ∈ Finset.range (d + 1), S.choose k) ≤ n ^ d * (n + 2) ^ S := by
  have htrunc : (∑ k ∈ Finset.range (d + 1), S.choose k) =
      ∑ k ∈ Finset.range (min d S + 1), S.choose k := by
    symm
    apply Finset.sum_subset
    · exact Finset.range_mono (by omega)
    · intro k hk hnot
      rw [Finset.mem_range] at hk hnot
      exact Nat.choose_eq_zero_of_lt (by omega)
  rw [htrunc, Finset.mul_sum]
  have hterm : ∀ k ∈ Finset.range (min d S + 1),
      2 ^ d * n ^ S * S.choose k ≤ n ^ d * (2 ^ k * n ^ (S - k) * S.choose k) := by
    intro k hk
    have hk_min : k ≤ min d S := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hkd : k ≤ d := le_trans hk_min (min_le_left d S)
    have hkS : k ≤ S := le_trans hk_min (min_le_right d S)
    have h2 : 2 ^ d = 2 ^ (d - k) * 2 ^ k := by rw [← pow_add, Nat.sub_add_cancel hkd]
    have hnS : n ^ S = n ^ k * n ^ (S - k) := by rw [← pow_add, Nat.add_sub_of_le hkS]
    have hnd : n ^ (d - k) * n ^ k = n ^ d := by rw [← pow_add, Nat.sub_add_cancel hkd]
    calc
      2 ^ d * n ^ S * S.choose k
          = 2 ^ (d - k) * (2 ^ k * (n ^ k * n ^ (S - k)) * S.choose k) := by
              rw [h2, hnS]; ring
      _ ≤ n ^ (d - k) * (2 ^ k * (n ^ k * n ^ (S - k)) * S.choose k) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hn (d - k))
      _ = (n ^ (d - k) * n ^ k) * (2 ^ k * n ^ (S - k) * S.choose k) := by ring
      _ = n ^ d * (2 ^ k * n ^ (S - k) * S.choose k) := by rw [hnd]
  have hpow := add_pow 2 n S
  simp only [Nat.cast_id] at hpow
  calc
    (∑ k ∈ Finset.range (min d S + 1), 2 ^ d * n ^ S * S.choose k)
        ≤ ∑ k ∈ Finset.range (min d S + 1), n ^ d * (2 ^ k * n ^ (S - k) * S.choose k) :=
          Finset.sum_le_sum hterm
    _ = n ^ d * ∑ k ∈ Finset.range (min d S + 1), 2 ^ k * n ^ (S - k) * S.choose k := by
          rw [← Finset.mul_sum]
    _ ≤ n ^ d * ∑ k ∈ Finset.range (S + 1), 2 ^ k * n ^ (S - k) * S.choose k := by
          apply Nat.mul_le_mul_left
          exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    _ = n ^ d * (2 + n) ^ S := by rw [← hpow]
    _ = n ^ d * (n + 2) ^ S := by rw [Nat.add_comm 2 n]

lemma nat_lower_bound (n d S : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (h : n ^ d ≤ ∑ k ∈ Finset.range (d + 1), S.choose k) : n * d ≤ 6 * S := by
  have h1 : n ^ d * (2 ^ d * n ^ S) ≤ n ^ d * (n + 2) ^ S := by
    calc
      n ^ d * (2 ^ d * n ^ S) = 2 ^ d * n ^ S * n ^ d := by ring
      _ ≤ 2 ^ d * n ^ S * (∑ k ∈ Finset.range (d + 1), S.choose k) := Nat.mul_le_mul_left _ h
      _ ≤ n ^ d * (n + 2) ^ S := bernstein_nat n d S hn
  have hnd_pos : 0 < n ^ d := Nat.pow_pos (by omega)
  have h2 : 2 ^ d * n ^ S ≤ (n + 2) ^ S := Nat.le_of_mul_le_mul_left h1 hnd_pos
  have h6 : 64 ^ d * n ^ (6 * S) ≤ (n + 2) ^ (6 * S) := by
    have hp := Nat.pow_le_pow_left h2 6
    have hlhs : (2 ^ d * n ^ S) ^ 6 = 64 ^ d * n ^ (6 * S) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm d 6, pow_mul]
      norm_num [Nat.mul_comm S 6]
    have hrhs : ((n + 2) ^ S) ^ 6 = (n + 2) ^ (6 * S) := by
      rw [← pow_mul, Nat.mul_comm S 6]
    rwa [hlhs, hrhs] at hp
  by_contra hnot
  have hle : 6 * S ≤ n * d := by omega
  have hbig : (64 * n ^ n) ^ d ≤ ((n + 2) ^ n) ^ d := by
    calc
      (64 * n ^ n) ^ d = 64 ^ d * n ^ (n * d) := by rw [mul_pow, ← pow_mul]
      _ = 64 ^ d * (n ^ (6 * S) * n ^ (n * d - 6 * S)) := by
          rw [← pow_add, Nat.add_sub_of_le hle]
      _ = (64 ^ d * n ^ (6 * S)) * n ^ (n * d - 6 * S) := by ring
      _ ≤ (n + 2) ^ (6 * S) * n ^ (n * d - 6 * S) := Nat.mul_le_mul_right _ h6
      _ ≤ (n + 2) ^ (6 * S) * (n + 2) ^ (n * d - 6 * S) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = (n + 2) ^ (n * d) := by rw [← pow_add, Nat.add_sub_of_le hle]
      _ = ((n + 2) ^ n) ^ d := by rw [← pow_mul]
  have hstrict : ((n + 2) ^ n) ^ d < (64 * n ^ n) ^ d :=
    Nat.pow_lt_pow_left (add_two_pow_lt n (by omega)) (by omega)
  exact absurd hbig (not_le_of_gt hstrict)

/-! ### Part 2: Noncommutative Polynomials in `X` and Minimum Degree -/

abbrev AX (F : Type*) [CommSemiring F] (n : ℕ) : Type _ :=
  MonoidAlgebra F (FreeMonoid (Fin n))

section AXProps

variable {F : Type*} [CommRing F] {n : ℕ}

noncomputable def constMap : AX F n →ₗ[F] F where
  toFun p := p.coeff 1
  map_add' p q := by simp
  map_smul' c p := by simp

@[simp]
lemma constMap_apply (p : AX F n) : constMap p = p.coeff 1 := rfl

lemma constMap_mul (p q : AX F n) : constMap (p * q) = constMap p * constMap q := by
  have h := MonoidAlgebra.coeff_mul_antidiag p q 1 {(1, 1)} (by
    rintro ⟨x₁, x₂⟩
    simp only [Finset.mem_singleton, Prod.ext_iff]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact mul_one 1
    · intro hmul
      have hlen : (x₁ * x₂).length = 0 := by rw [hmul, FreeMonoid.length_one]
      rw [FreeMonoid.length_mul, Nat.add_eq_zero_iff] at hlen
      exact ⟨FreeMonoid.length_eq_zero.mp hlen.1, FreeMonoid.length_eq_zero.mp hlen.2⟩)
  simpa only [constMap_apply, Finset.sum_singleton] using h

@[simp]
lemma constMap_one : constMap (1 : AX F n) = 1 := by
  simp [MonoidAlgebra.one_def]

@[simp]
lemma constMap_algebraMap (c : F) : constMap (algebraMap F (AX F n) c) = c := by
  simp [Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def]

noncomputable def nonConst (p : AX F n) : AX F n :=
  p - algebraMap F (AX F n) (constMap p)

lemma eq_nonConst_add_const (p : AX F n) : p = nonConst p + (constMap p) • 1 := by
  simp [nonConst, Algebra.algebraMap_eq_smul_one]

def MinDeg (k : ℕ) (p : AX F n) : Prop :=
  ∀ w : FreeMonoid (Fin n), w.length < k → p.coeff w = 0

lemma minDeg_zero (p : AX F n) : MinDeg 0 p := by
  intro w hw
  omega

lemma minDeg_nonConst (p : AX F n) : MinDeg 1 (nonConst p) := by
  intro w hw
  have hw1 : w = 1 := FreeMonoid.length_eq_zero.mp (by omega)
  subst hw1
  simp [nonConst, Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def]

lemma minDeg_mul {a b : ℕ} {p q : AX F n} (hp : MinDeg a p) (hq : MinDeg b q) :
    MinDeg (a + b) (p * q) := by
  classical
  intro w hw
  rw [MonoidAlgebra.coeff_mul, Finsupp.sum]
  refine Finset.sum_eq_zero fun w₁ _ => ?_
  rw [Finsupp.sum]
  refine Finset.sum_eq_zero fun w₂ _ => ?_
  split_ifs with hmul
  · have hlen : w₁.length + w₂.length < a + b := by
      rwa [← FreeMonoid.length_mul, hmul]
    by_cases h1 : w₁.length < a
    · change p.coeff w₁ * q.coeff w₂ = 0
      rw [hp w₁ h1, zero_mul]
    · have h2 : w₂.length < b := by omega
      change p.coeff w₁ * q.coeff w₂ = 0
      rw [hq w₂ h2, mul_zero]
  · rfl

end AXProps

/-! ### Part 3: `(X, Y)`-Separated Endomorphism Representation of `FreeAlgebra` -/

abbrev ModXY (F : Type*) [CommRing F] (n : ℕ) : Type _ :=
  List (Fin n) → AX F n

section Representation

variable {F : Type*} [CommRing F] {n : ℕ}

noncomputable def xGen (i : Fin n) : AX F n :=
  MonoidAlgebra.single (FreeMonoid.of i) 1

noncomputable def Lx (i : Fin n) : Module.End F (ModXY F n) where
  toFun f m := xGen i * f m
  map_add' f g := by ext m; simp [mul_add]
  map_smul' c f := by ext m; simp [Algebra.mul_smul_comm]

noncomputable def Ly (j : Fin n) : Module.End F (ModXY F n) where
  toFun f m :=
    match m with
    | [] => 0
    | k :: m' => if k = j then algebraMap F (AX F n) (constMap (f m')) else 0
  map_add' f g := by
    ext m
    cases m with
    | nil => simp
    | cons k m' =>
      by_cases h : k = j <;> simp [h]
  map_smul' c f := by
    ext m
    cases m with
    | nil => simp
    | cons k m' =>
      by_cases h : k = j <;> simp [h, Algebra.algebraMap_eq_smul_one, smul_smul]

noncomputable def Phi : FreeAlgebra F (Fin n ⊕ Fin n) →ₐ[F] Module.End F (ModXY F n) :=
  FreeAlgebra.lift F (Sum.elim Lx Ly)

noncomputable def v0 : ModXY F n
  | [] => 1
  | _ :: _ => 0

def Good (T : Module.End F (ModXY F n)) : Prop :=
  ∀ (f : ModXY F n) (m : List (Fin n)),
    T f m = T v0 [] * f m +
      ∑ k : Fin m.length, constMap (f (m.drop (k.1 + 1))) • T v0 (m.take (k.1 + 1))

lemma good_one : Good (1 : Module.End F (ModXY F n)) := by
  intro f m
  have hsum : (∑ k : Fin m.length,
      constMap (f (m.drop (k.1 + 1))) • (1 : Module.End F (ModXY F n)) v0 (m.take (k.1 + 1))) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    cases m with
    | nil => exact Fin.elim0 k
    | cons a m' => simp [v0]
  rw [hsum]
  simp [v0]

lemma good_add {T₁ T₂ : Module.End F (ModXY F n)} (h₁ : Good T₁) (h₂ : Good T₂) :
    Good (T₁ + T₂) := by
  intro f m
  simp only [LinearMap.add_apply, Pi.add_apply]
  calc
    T₁ f m + T₂ f m
        = (T₁ v0 [] * f m + ∑ k : Fin m.length, constMap (f (m.drop (k.1 + 1))) • T₁ v0 (m.take (k.1 + 1))) +
          (T₂ v0 [] * f m + ∑ k : Fin m.length, constMap (f (m.drop (k.1 + 1))) • T₂ v0 (m.take (k.1 + 1))) := by
            rw [h₁ f m, h₂ f m]
    _ = (T₁ v0 [] * f m + T₂ v0 [] * f m) +
          ((∑ k : Fin m.length, constMap (f (m.drop (k.1 + 1))) • T₁ v0 (m.take (k.1 + 1))) +
           (∑ k : Fin m.length, constMap (f (m.drop (k.1 + 1))) • T₂ v0 (m.take (k.1 + 1)))) := by
            abel
    _ = (T₁ v0 [] + T₂ v0 []) * f m +
          ∑ k : Fin m.length,
            constMap (f (m.drop (k.1 + 1))) • (T₁ v0 (m.take (k.1 + 1)) + T₂ v0 (m.take (k.1 + 1))) := by
            rw [← add_mul, ← Finset.sum_add_distrib]
            simp only [smul_add]

lemma good_smul (c : F) {T : Module.End F (ModXY F n)} (h : Good T) :
    Good (c • T) := by
  intro f m
  simp only [LinearMap.smul_apply, Pi.smul_apply]
  rw [h f m, smul_add, Algebra.smul_mul_assoc, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_comm]

lemma good_Lx (i : Fin n) {T : Module.End F (ModXY F n)} (h : Good T) :
    Good (Lx i * T) := by
  intro f m
  simp only [Module.End.mul_apply, Lx, LinearMap.coe_mk, AddHom.coe_mk]
  rw [h f m, mul_add, mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.mul_smul_comm]

lemma good_Ly (j : Fin n) {T : Module.End F (ModXY F n)} (h : Good T) :
    Good (Ly j * T) := by
  intro f m
  let S : Module.End F (ModXY F n) := Ly j * T
  change S f m = S v0 [] * f m +
    ∑ idx : Fin m.length, constMap (f (m.drop (idx.1 + 1))) • S v0 (m.take (idx.1 + 1))
  cases m with
  | nil =>
    simp [S, Module.End.mul_apply, Ly]
  | cons k m' =>
    by_cases hkj : k = j
    · subst hkj
      have hlhs : S f (k :: m') =
          (f m').coeff 1 • algebraMap F (AX F n) ((T v0 []).coeff 1) +
            ∑ r : Fin m'.length,
              (f (m'.drop (r.1 + 1))).coeff 1 •
                algebraMap F (AX F n) ((T v0 (m'.take (r.1 + 1))).coeff 1) := by
        simp only [S, Module.End.mul_apply, Ly, LinearMap.coe_mk, AddHom.coe_mk, ↓reduceIte]
        rw [h f m', map_add, constMap_mul, map_sum, map_add, map_sum]
        simp only [map_smul, smul_eq_mul, constMap_apply, Algebra.algebraMap_eq_smul_one, smul_smul]
        congr 1
        · rw [mul_comm]
      have hrhs : S v0 [] * f (k :: m') +
          (∑ idx : Fin (k :: m').length,
            constMap (f ((k :: m').drop (idx.1 + 1))) • S v0 ((k :: m').take (idx.1 + 1))) =
          (f m').coeff 1 • algebraMap F (AX F n) ((T v0 []).coeff 1) +
            ∑ r : Fin m'.length,
              (f (m'.drop (r.1 + 1))).coeff 1 •
                algebraMap F (AX F n) ((T v0 (m'.take (r.1 + 1))).coeff 1) := by
        have hzero : S v0 [] * f (k :: m') = 0 := by
          simp [S, Module.End.mul_apply, Ly]
        rw [hzero, zero_add]
        change (∑ idx : Fin (m'.length + 1),
            constMap (f ((k :: m').drop (idx.1 + 1))) • S v0 ((k :: m').take (idx.1 + 1))) = _
        rw [Fin.sum_univ_succ]
        simp [S, Module.End.mul_apply, Ly]
      exact hlhs.trans hrhs.symm
    · simp [S, Module.End.mul_apply, Ly, hkj]

lemma good_Phi (P : FreeAlgebra F (Fin n ⊕ Fin n)) : Good (Phi P) := by
  let S : Subalgebra F (Module.End F (ModXY F n)) :=
    { carrier := { A | ∀ T, Good T → Good (A * T) }
      mul_mem' := fun {A B} hA hB T hT => by
        rw [mul_assoc]
        exact hA (B * T) (hB T hT)
      add_mem' := fun {A B} hA hB T hT => by
        rw [add_mul]
        exact good_add (hA T hT) (hB T hT)
      algebraMap_mem' := fun c T hT => by
        rw [Algebra.algebraMap_eq_smul_one, smul_one_mul]
        exact good_smul c hT }
  have hmem : Phi P ∈ S := by
    induction P using FreeAlgebra.induction with
    | grade0 c =>
      rw [AlgHom.commutes]
      exact S.algebraMap_mem c
    | grade1 v =>
      simp only [Phi, FreeAlgebra.lift_ι_apply]
      cases v with
      | inl i => exact fun T hT => good_Lx i hT
      | inr j => exact fun T hT => good_Ly j hT
    | mul a b ha hb =>
      rw [map_mul]
      exact S.mul_mem ha hb
    | add a b ha hb =>
      rw [map_add]
      exact S.add_mem ha hb
  simpa using hmem 1 good_one

noncomputable def coeffY (P : FreeAlgebra F (Fin n ⊕ Fin n)) (m : List (Fin n)) : AX F n :=
  Phi P v0 m

noncomputable def xPart (P : FreeAlgebra F (Fin n ⊕ Fin n)) : AX F n :=
  Phi P v0 []

lemma coeffY_mul (P Q : FreeAlgebra F (Fin n ⊕ Fin n)) (m : List (Fin n)) :
    coeffY (P * Q) m = xPart P * coeffY Q m +
      ∑ k : Fin m.length, constMap (coeffY Q (m.drop (k.1 + 1))) • coeffY P (m.take (k.1 + 1)) := by
  unfold coeffY xPart
  rw [map_mul, Module.End.mul_apply]
  exact good_Phi P (Phi Q v0) m

end Representation

/-! ### Part 4: Circuit Spanning Set Construction and Degree Truncation -/

def mulSetLe {F V : Type*} (C : Circuit F V) (m : ℕ) : Finset ℕ :=
  (Finset.range m).filter fun j =>
    if h : j < C.size then (C.node ⟨j, h⟩).isMul = true else false

lemma mulSetLe_mono {F V : Type*} (C : Circuit F V) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    mulSetLe C m₁ ⊆ mulSetLe C m₂ :=
  Finset.filter_subset_filter _ (Finset.range_mono h)

lemma mulSetLe_subset_range {F V : Type*} (C : Circuit F V) (m : ℕ) :
    mulSetLe C m ⊆ Finset.range m :=
  Finset.filter_subset _ _

section CircuitSpan

variable {F : Type*} [CommRing F] {n : ℕ}

noncomputable def wPlusAux (u : ℕ → AX F n) (s : Finset ℕ) : ℕ → AX F n
  | 0 => 1
  | m + 1 => if m ∈ s then u m * wPlusAux u s m else wPlusAux u s m

lemma wPlusAux_congr (u : ℕ → AX F n) {s₁ s₂ : Finset ℕ} :
    ∀ m : ℕ, (∀ j < m, (j ∈ s₁ ↔ j ∈ s₂)) → wPlusAux u s₁ m = wPlusAux u s₂ m
  | 0, _ => rfl
  | m + 1, h => by
    have ih := wPlusAux_congr u m (fun j hj => h j (by omega))
    have hm := h m (by omega)
    simp only [wPlusAux, ih]
    by_cases h1 : m ∈ s₁
    · have h2 : m ∈ s₂ := hm.mp h1
      simp [h1, h2]
    · have h2 : m ∉ s₂ := fun hc => h1 (hm.mpr hc)
      simp [h1, h2]

lemma wPlusAux_const_above (u : ℕ → AX F n) (s : Finset ℕ) (m : ℕ) (hs : ∀ j ∈ s, j < m) :
    ∀ M : ℕ, m ≤ M → wPlusAux u s M = wPlusAux u s m
  | 0, hm => by
    have hm0 : m = 0 := by omega
    subst hm0; rfl
  | M + 1, hm => by
    rcases Nat.eq_or_lt_of_le hm with rfl | hlt
    · rfl
    · have hmM : m ≤ M := by omega
      have hnot : M ∉ s := fun hMs => by have := hs M hMs; omega
      simp [wPlusAux, hnot, wPlusAux_const_above u s m hs M hmM]

noncomputable def uRaw (C : Circuit F (Fin n ⊕ Fin n)) (j : ℕ) : AX F n :=
  if h : j < C.size then
    match C.node ⟨j, h⟩ with
    | .mul a _ _ _ => xPart (C.value (C.child a))
    | _ => 0
  else 0

noncomputable def uPlus (C : Circuit F (Fin n ⊕ Fin n)) (j : ℕ) : AX F n :=
  nonConst (uRaw C j)

noncomputable def wPlus (C : Circuit F (Fin n ⊕ Fin n)) (s : Finset ℕ) : AX F n :=
  wPlusAux (uPlus C) s C.size

lemma wPlus_empty (C : Circuit F (Fin n ⊕ Fin n)) : wPlus C ∅ = 1 :=
  wPlusAux_const_above (uPlus C) ∅ 0 (by simp) C.size (Nat.zero_le _)

lemma wPlus_insert (C : Circuit F (Fin n ⊕ Fin n)) (k : ℕ) (hk : k < C.size)
    (s : Finset ℕ) (hs : s ⊆ Finset.range k) :
    wPlus C (insert k s) = uPlus C k * wPlus C s := by
  have hins : ∀ j ∈ insert k s, j < k + 1 := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · omega
    · have := Finset.mem_range.mp (hs hjs); omega
  have h1 : wPlus C (insert k s) = wPlusAux (uPlus C) (insert k s) (k + 1) :=
    wPlusAux_const_above (uPlus C) (insert k s) (k + 1) hins C.size (by omega)
  have h2 : wPlusAux (uPlus C) (insert k s) k = wPlusAux (uPlus C) s k :=
    wPlusAux_congr (uPlus C) k fun j hj => by
      have hjk : j ≠ k := by omega
      simp [hjk]
  have h3 : wPlusAux (uPlus C) s k = wPlus C s :=
    (wPlusAux_const_above (uPlus C) s k (fun j hj => Finset.mem_range.mp (hs hj)) C.size
      (by omega)).symm
  rw [h1]
  simp [wPlusAux, h2, h3]

lemma minDeg_wPlusAux (C : Circuit F (Fin n ⊕ Fin n)) (s : Finset ℕ) :
    ∀ m : ℕ, MinDeg (s.filter (· < m)).card (wPlusAux (uPlus C) s m)
  | 0 => by
    have hempty : s.filter (· < 0) = ∅ := by ext x; simp
    rw [hempty]
    exact minDeg_zero _
  | m + 1 => by
    have ih := minDeg_wPlusAux C s m
    by_cases hm : m ∈ s
    · have hfilt : s.filter (· < m + 1) = insert m (s.filter (· < m)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hxs, hlt⟩
          rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hlt) with rfl | hxlt
          · exact Or.inl rfl
          · exact Or.inr ⟨hxs, hxlt⟩
        · rintro (rfl | ⟨hxs, hxlt⟩)
          · exact ⟨hm, by omega⟩
          · exact ⟨hxs, by omega⟩
      have hnot : m ∉ s.filter (· < m) := by simp
      rw [hfilt, Finset.card_insert_of_notMem hnot, Nat.add_comm]
      simp only [wPlusAux, hm, ↓reduceIte]
      exact minDeg_mul (minDeg_nonConst _) ih
    · have hfilt : s.filter (· < m + 1) = s.filter (· < m) := by
        ext x
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hxs, hlt⟩
          refine ⟨hxs, ?_⟩
          have hxm : x ≠ m := fun h => hm (h ▸ hxs)
          omega
        · rintro ⟨hxs, hxlt⟩
          exact ⟨hxs, by omega⟩
      rw [hfilt]
      simpa [wPlusAux, hm] using ih

lemma minDeg_wPlus (C : Circuit F (Fin n ⊕ Fin n)) (s : Finset ℕ)
    (hs : s ⊆ Finset.range C.size) : MinDeg s.card (wPlus C s) := by
  have hfilt : s.filter (· < C.size) = s := by
    ext x
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    exact fun hx => Finset.mem_range.mp (hs hx)
  have h := minDeg_wPlusAux C s C.size
  rwa [hfilt] at h

lemma circuit_coeffY_mem_span (C : Circuit F (Fin n ⊕ Fin n)) :
    ∀ (k : Fin C.size) (m : List (Fin n)), m ≠ [] →
      coeffY (C.value k) m ∈
        Submodule.span F ((wPlus C) '' (↑(mulSetLe C (k.1 + 1)).powerset : Set (Finset ℕ))) := by
  intro k
  induction hval : k.1 using Nat.strongRecOn generalizing k with
  | ind idx ih =>
    subst hval
    intro m hm
    have h1_mem : (1 : AX F n) ∈
        Submodule.span F ((wPlus C) '' (↑(mulSetLe C (k.1 + 1)).powerset : Set (Finset ℕ))) := by
      apply Submodule.subset_span
      refine ⟨∅, ?_, wPlus_empty C⟩
      simp
    rw [Circuit.value]
    rcases hnode : C.node k with c | v | ⟨a, b, α, β⟩ | ⟨a, b, α, β⟩
    · simp only
      have hc : coeffY (algebraMap F (FreeAlgebra F (Fin n ⊕ Fin n)) c) m = 0 := by
        cases m with
        | nil => contradiction
        | cons x m' =>
          unfold coeffY
          rw [AlgHom.commutes]
          simp [Algebra.algebraMap_eq_smul_one, v0]
      rw [hc]
      exact Submodule.zero_mem _
    · simp only
      cases v with
      | inl i =>
        have hi : coeffY (FreeAlgebra.ι F (Sum.inl i : Fin n ⊕ Fin n)) m = 0 := by
          cases m with
          | nil => contradiction
          | cons x m' =>
            unfold coeffY
            simp [Phi, Lx, v0]
        rw [hi]
        exact Submodule.zero_mem _
      | inr j =>
        cases m with
        | nil => contradiction
        | cons x m' =>
          unfold coeffY
          simp only [Phi, FreeAlgebra.lift_ι_apply, Sum.elim_inr]
          cases m' with
          | nil =>
            by_cases hxj : x = j
            · simp [Ly, hxj, v0, MonoidAlgebra.one_def]
              simpa [MonoidAlgebra.one_def] using h1_mem
            · simp [Ly, hxj]
          | cons y m'' =>
            by_cases hxj : x = j <;> simp [Ly, hxj, v0]
    · simp only
      have hlin : coeffY (α • C.value (C.child a) + β • C.value (C.child b)) m =
          α • coeffY (C.value (C.child a)) m + β • coeffY (C.value (C.child b)) m := by
        simp [coeffY, map_add, map_smul]
      rw [hlin]
      have ha_sub : (wPlus C) '' (↑(mulSetLe C ((C.child a).1 + 1)).powerset : Set (Finset ℕ)) ⊆
          (wPlus C) '' (↑(mulSetLe C (k.1 + 1)).powerset : Set (Finset ℕ)) := by
        apply Set.image_mono
        intro s hs
        simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
          Finset.coe_subset] at hs ⊢
        exact hs.trans (mulSetLe_mono C (by simp [Circuit.child]))
      have hb_sub : (wPlus C) '' (↑(mulSetLe C ((C.child b).1 + 1)).powerset : Set (Finset ℕ)) ⊆
          (wPlus C) '' (↑(mulSetLe C (k.1 + 1)).powerset : Set (Finset ℕ)) := by
        apply Set.image_mono
        intro s hs
        simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
          Finset.coe_subset] at hs ⊢
        exact hs.trans (mulSetLe_mono C (by simp [Circuit.child]))
      have ha_mem := Submodule.span_mono ha_sub
        (ih (C.child a).1 (by simp [Circuit.child]) (C.child a) rfl m hm)
      have hb_mem := Submodule.span_mono hb_sub
        (ih (C.child b).1 (by simp [Circuit.child]) (C.child b) rfl m hm)
      exact Submodule.add_mem _ (Submodule.smul_mem _ α ha_mem) (Submodule.smul_mem _ β hb_mem)
    · simp only
      have hsmul : (α • C.value (C.child a)) * (β • C.value (C.child b)) =
          (α * β) • (C.value (C.child a) * C.value (C.child b)) := by
        rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
      have hcoeff_smul : coeffY ((α * β) • (C.value (C.child a) * C.value (C.child b))) m =
          (α * β) • coeffY (C.value (C.child a) * C.value (C.child b)) m := by
        simp [coeffY, map_smul]
      rw [hsmul, hcoeff_smul]
      refine Submodule.smul_mem _ (α * β) ?_
      rw [coeffY_mul]
      set target :=
        Submodule.span F ((wPlus C) '' (↑(mulSetLe C (k.1 + 1)).powerset : Set (Finset ℕ)))
      refine Submodule.add_mem target ?_ ?_
      · have huRaw : uRaw C k.1 = xPart (C.value (C.child a)) := by
          simp [uRaw, k.isLt, hnode]
        have hb_ih := ih (C.child b).1 (by simp [Circuit.child]) (C.child b) rfl m hm
        have hmul_span :
            Submodule.span F
              ((wPlus C) '' (↑(mulSetLe C ((C.child b).1 + 1)).powerset : Set (Finset ℕ))) ≤
            target.comap (LinearMap.mulLeft F (xPart (C.value (C.child a)))) := by
          rw [Submodule.span_le]
          rintro _ ⟨s, hs, rfl⟩
          simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
            Finset.coe_subset] at hs
          simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
          rw [← huRaw, eq_nonConst_add_const (uRaw C k.1), add_mul, smul_one_mul]
          refine Submodule.add_mem target ?_ ?_
          · have hs_range : s ⊆ Finset.range k.1 := by
              refine hs.trans ((mulSetLe_subset_range C _).trans (Finset.range_mono ?_))
              simp [Circuit.child]
            change uPlus C k.1 * wPlus C s ∈ target
            rw [← wPlus_insert C k.1 k.isLt s hs_range]
            apply Submodule.subset_span
            refine ⟨insert k.1 s, ?_, rfl⟩
            simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
              Finset.coe_subset]
            intro j hj
            rcases Finset.mem_insert.mp hj with rfl | hjs
            · simp [mulSetLe, k.isLt, hnode, Node.isMul]
            · exact mulSetLe_mono C (by simp [Circuit.child]) (hs hjs)
          · refine Submodule.smul_mem target _ (Submodule.subset_span ⟨s, ?_, rfl⟩)
            simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
              Finset.coe_subset]
            exact hs.trans (mulSetLe_mono C (by simp [Circuit.child]))
        exact hmul_span hb_ih
      · refine Submodule.sum_mem target fun r _ => Submodule.smul_mem target _ ?_
        have htake_ne : m.take (r.1 + 1) ≠ [] := by
          cases m with
          | nil => exact Fin.elim0 r
          | cons _ _ => simp
        have ha_sub : (wPlus C) '' (↑(mulSetLe C ((C.child a).1 + 1)).powerset : Set (Finset ℕ)) ⊆
            (wPlus C) '' (↑(mulSetLe C (k.1 + 1)).powerset : Set (Finset ℕ)) := by
          apply Set.image_mono
          intro s hs
          simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
            Finset.coe_subset] at hs ⊢
          exact hs.trans (mulSetLe_mono C (by simp [Circuit.child]))
        exact Submodule.span_mono ha_sub
          (ih (C.child a).1 (by simp [Circuit.child]) (C.child a) rfl (m.take (r.1 + 1)) htake_ne)

end CircuitSpan

/-! ### Part 5: Evaluation on `pal F n d`, Homogeneous Projection, and Final Proof -/

section PalAndProjection

variable {F : Type*} [Field F] {n d : ℕ}

noncomputable def pi_d (n d : ℕ) : AX F n →ₗ[F] ((Fin d → Fin n) → F) where
  toFun p i := p.coeff (FreeMonoid.ofList (List.ofFn i))
  map_add' p q := by ext i; simp
  map_smul' c p := by ext i; simp

lemma pi_d_wPlus_eq_zero_of_lt (C : Circuit F (Fin n ⊕ Fin n)) (s : Finset ℕ)
    (hs : s ⊆ Finset.range C.size) (hcard : d < s.card) :
    pi_d (F := F) n d (wPlus C s) = 0 := by
  ext i
  have hmin := minDeg_wPlus C s hs
  have hlen : (FreeMonoid.ofList (List.ofFn i)).length < s.card := by
    simpa [FreeMonoid.length] using hcard
  exact hmin _ hlen

lemma Phi_list_inl (L : List (Fin n)) (f : ModXY F n) (m : List (Fin n)) :
    Phi ((L.map fun x => FreeAlgebra.ι F (Sum.inl x : Fin n ⊕ Fin n)).prod) f m =
      MonoidAlgebra.single (FreeMonoid.ofList L) 1 * f m := by
  induction L with
  | nil =>
    simp [← MonoidAlgebra.one_def]
  | cons a L' ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, Phi,
      FreeAlgebra.lift_ι_apply, Sum.elim_inl]
    change xGen a * (Phi ((L'.map fun x => FreeAlgebra.ι F (Sum.inl x)).prod) f m) = _
    rw [ih, xGen, ← mul_assoc, MonoidAlgebra.single_mul_single, mul_one, FreeMonoid.ofList_cons]

lemma Phi_list_inr_v0 (L : List (Fin n)) (m : List (Fin n)) :
    Phi ((L.map fun y => FreeAlgebra.ι F (Sum.inr y : Fin n ⊕ Fin n)).prod) v0 m =
      if m = L then (1 : AX F n) else 0 := by
  induction L generalizing m with
  | nil =>
    cases m <;> simp [v0]
  | cons b L' ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, Phi,
      FreeAlgebra.lift_ι_apply, Sum.elim_inr]
    change Ly b (Phi ((L'.map fun y => FreeAlgebra.ι F (Sum.inr y)).prod) v0) m = _
    cases m with
    | nil => simp [Ly]
    | cons k m' =>
      simp only [Ly, LinearMap.coe_mk, AddHom.coe_mk, List.cons.injEq]
      rw [ih m']
      by_cases hkb : k = b
      · subst hkb
        by_cases hmL : m' = L'
        · subst hmL
          simp [← constMap_apply, ← MonoidAlgebra.one_def]
        · simp [hmL]
      · simp [hkb]

def revWord {n d : ℕ} (i : Fin d → Fin n) : List (Fin n) :=
  List.ofFn fun j => i (Fin.rev j)

lemma revWord_injective {n d : ℕ} : Function.Injective (@revWord n d) := by
  intro i₁ i₂ h
  have hfn := List.ofFn_inj.mp h
  funext j
  have := congr_fun hfn (Fin.rev j)
  simpa [Fin.rev_rev] using this

lemma coeffY_pal (n d : ℕ) (i₀ : Fin d → Fin n) :
    coeffY (pal F n d) (revWord i₀) =
      MonoidAlgebra.single (FreeMonoid.ofList (List.ofFn i₀)) 1 := by
  classical
  simp only [coeffY, pal, map_sum, LinearMap.sum_apply, Finset.sum_apply]
  have hterm : ∀ i : Fin d → Fin n,
      Phi (xMonomial F i * yMonomialRev F i) v0 (revWord i₀) =
        if i = i₀ then MonoidAlgebra.single (FreeMonoid.ofList (List.ofFn i)) 1 else 0 := by
    intro i
    rw [map_mul, Module.End.mul_apply]
    have hx : xMonomial F i =
        ((List.ofFn i).map fun x => FreeAlgebra.ι F (Sum.inl x : Fin n ⊕ Fin n)).prod := by
      simp [xMonomial, List.ofFn_eq_map, Function.comp_def]
    have hy : yMonomialRev F i =
        ((revWord i).map fun y => FreeAlgebra.ι F (Sum.inr y : Fin n ⊕ Fin n)).prod := by
      simp [yMonomialRev, revWord, List.ofFn_eq_map, Function.comp_def]
    rw [hx, hy, Phi_list_inl, Phi_list_inr_v0]
    by_cases hii : i = i₀
    · subst hii
      simp
    · have hne : revWord i₀ ≠ revWord i := fun heq => hii (revWord_injective heq.symm)
      simp [hii, hne]
  simp_rw [hterm]
  simp

lemma pi_d_coeffY_pal (n d : ℕ) (i₀ : Fin d → Fin n) :
    pi_d (F := F) n d (coeffY (pal F n d) (revWord i₀)) = Pi.single i₀ 1 := by
  classical
  rw [coeffY_pal]
  ext i
  simp only [pi_d, LinearMap.coe_mk, AddHom.coe_mk, MonoidAlgebra.coeff_single,
    Finsupp.single_apply, Pi.single_apply]
  by_cases h : i = i₀
  · subst h; simp
  · have hne : FreeMonoid.ofList (List.ofFn i₀) ≠ FreeMonoid.ofList (List.ofFn i) := by
      intro heq
      apply h
      exact (List.ofFn_inj.mp (FreeMonoid.ofList.injective heq)).symm
    simp [h, hne]

lemma card_mulSetLe_eq_numMul {V : Type*} (C : Circuit F V) :
    (mulSetLe C C.size).card = C.numMul := by
  unfold mulSetLe Circuit.numMul
  refine Finset.card_bij (fun (j : ℕ) (hj : j ∈ _) => ⟨j, Finset.mem_range.mp (Finset.mem_filter.mp hj).1⟩)
    ?_ ?_ ?_
  · intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hr, hmul⟩
    have hlt : j < C.size := Finset.mem_range.mp hr
    simp only [hlt, ↓reduceDIte] at hmul
    simp [hmul]
  · intro j₁ _ j₂ _ h
    exact congr_arg Fin.val h
  · intro k hk
    have hmul : (C.node k).isMul = true := (Finset.mem_filter.mp hk).2
    refine ⟨k.1, ?_, rfl⟩
    simp [k.isLt, hmul]

theorem theorem_4_2_proof (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (C : Circuit F (Fin n ⊕ Fin n)) (hC : C.Computes (pal F n d)) :
    n * d ≤ 6 * C.numMul ∧ n * d ≤ 6 * C.size := by
  classical
  let G : Finset (Finset ℕ) :=
    (mulSetLe C C.size).powerset.filter fun s => s.card ≤ d
  let img : Finset ((Fin d → Fin n) → F) :=
    G.image fun s => pi_d (F := F) n d (wPlus C s)
  have htop : (⊤ : Submodule F ((Fin d → Fin n) → F)) ≤ Submodule.span F (img : Set _) := by
    intro v _
    have hv : v = ∑ i₀ : Fin d → Fin n, v i₀ • Pi.single i₀ (1 : F) := by
      ext i
      simp [Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun i₀ _ => Submodule.smul_mem _ (v i₀) ?_
    rw [← pi_d_coeffY_pal (F := F) n d i₀, ← hC]
    have hne : revWord i₀ ≠ [] := by
      intro hemp
      have hlen := congr_arg List.length hemp
      simp [revWord] at hlen
      omega
    have hout_mem := circuit_coeffY_mem_span C C.output (revWord i₀) hne
    have hmap_mem : pi_d (F := F) n d (coeffY (C.value C.output) (revWord i₀)) ∈
        (Submodule.span F ((wPlus C) '' (↑(mulSetLe C (C.output.1 + 1)).powerset : Set (Finset ℕ)))).map
          (pi_d (F := F) n d) :=
      Submodule.mem_map_of_mem hout_mem
    rw [Submodule.map_span, ← Set.image_comp] at hmap_mem
    have hspan_le :
        Submodule.span F
          (((pi_d (F := F) n d) ∘ (wPlus C)) ''
            (↑(mulSetLe C (C.output.1 + 1)).powerset : Set (Finset ℕ))) ≤
          Submodule.span F (img : Set _) := by
      rw [Submodule.span_le]
      rintro _ ⟨s, hs, rfl⟩
      simp only [Function.comp_apply]
      simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
        Finset.coe_subset] at hs
      have hs_all : s ⊆ mulSetLe C C.size :=
        hs.trans (mulSetLe_mono C (by omega))
      have hs_range : s ⊆ Finset.range C.size :=
        hs_all.trans (mulSetLe_subset_range C C.size)
      by_cases hcard : s.card ≤ d
      · apply Submodule.subset_span
        simp only [img, G, Finset.coe_image, Set.mem_image, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_powerset]
        exact ⟨s, ⟨hs_all, hcard⟩, rfl⟩
      · rw [pi_d_wPlus_eq_zero_of_lt C s hs_range (by omega)]
        exact Submodule.zero_mem _
    exact hspan_le hmap_mem
  have hspan_eq : Submodule.span F (img : Set ((Fin d → Fin n) → F)) = ⊤ :=
    top_unique htop
  have hdim_le : n ^ d ≤ G.card := by
    have hcard := finrank_span_finset_le_card (R := F) img
    change Module.finrank F (Submodule.span F (img : Set ((Fin d → Fin n) → F))) ≤ img.card at hcard
    rw [hspan_eq] at hcard
    simp at hcard
    exact le_trans hcard Finset.card_image_le
  have hG_sub : G ⊆ (Finset.range (d + 1)).biUnion
      (fun k => (mulSetLe C C.size).powersetCard k) := by
    intro s hs
    simp only [G, Finset.mem_filter, Finset.mem_powerset] at hs
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
    exact ⟨s.card, by omega, hs.1, rfl⟩
  have hG_card : G.card ≤ ∑ k ∈ Finset.range (d + 1), C.numMul.choose k := by
    calc
      G.card ≤ ((Finset.range (d + 1)).biUnion
          (fun k => (mulSetLe C C.size).powersetCard k)).card := Finset.card_le_card hG_sub
      _ ≤ ∑ k ∈ Finset.range (d + 1), ((mulSetLe C C.size).powersetCard k).card :=
          Finset.card_biUnion_le
      _ = ∑ k ∈ Finset.range (d + 1), C.numMul.choose k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.card_powersetCard, card_mulSetLe_eq_numMul (F := F)]
  have hbound : n ^ d ≤ ∑ k ∈ Finset.range (d + 1), C.numMul.choose k :=
    le_trans hdim_le hG_card
  have hmul_lb : n * d ≤ 6 * C.numMul :=
    nat_lower_bound n d C.numMul hn hd hbound
  have hnum_le_size : C.numMul ≤ C.size := by
    unfold Circuit.numMul
    calc
      (Finset.univ.filter fun k : Fin C.size => (C.node k).isMul = true).card
          ≤ (Finset.univ : Finset (Fin C.size)).card := Finset.card_filter_le _ _
      _ = C.size := by simp
  exact ⟨hmul_lb, le_trans hmul_lb (Nat.mul_le_mul_left 6 hnum_le_size)⟩

end PalAndProjection

end NCQuadLB_Proof

open NCQuadLB

theorem solution {F : Type*} [Field F] (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (C : Circuit F (Fin n ⊕ Fin n)) (hC : C.Computes (pal F n d)) :
    n * d ≤ 6 * C.numMul ∧ n * d ≤ 6 * C.size :=
  NCQuadLB_Proof.theorem_4_2_proof n d hn hd C hC
