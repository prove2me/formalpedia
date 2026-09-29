-- Prove2me | solution 1 for LocalGL2.mem_doubleCoset_diagPi_zpow_mul_localRepInf_zpow_iff_of_upperTriangular
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/bcbffa0d-2e57-562c-a448-326dab383451

import Mathlib
import Definitions.Def_LocalLanglands_CartanDecomposition
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import Theorems.Thm_LocalGL2_exists_cartanRel_cartanDiag
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalGL2_mem_doubleCoset_diagPi_zpow_mul_localRepInf_zpow_iff_of_upperTriangular

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Matrix LocalGL2 HeckePair

namespace KcCartanUpperK

section Integral

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

def gU (u₁ u₂ : Rˣ) (ϖ : R) (a b : ℕ) (y : R) : Matrix (Fin 2) (Fin 2) R :=
  !![(u₁ : R) * ϖ ^ a, y; 0, (u₂ : R) * ϖ ^ b]

theorem gU_det (u₁ u₂ : Rˣ) (ϖ : R) (a b : ℕ) (y : R) :
    (gU u₁ u₂ ϖ a b y).det = (u₁ : R) * (u₂ : R) * ϖ ^ (a + b) := by
  rw [gU, Matrix.det_fin_two_of]; ring

theorem gU_det_ne_zero (u₁ u₂ : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (a b : ℕ) (y : R) :
    (gU u₁ u₂ ϖ a b y).det ≠ 0 := by
  rw [gU_det]
  exact mul_ne_zero (mul_ne_zero u₁.ne_zero u₂.ne_zero) (pow_ne_zero _ hϖ.ne_zero)

theorem entryIdeal_gU_le_iff (u₁ u₂ : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (a b : ℕ) (y : R) (c : ℕ) :
    entryIdeal (gU u₁ u₂ ϖ a b y) ≤ Ideal.span {ϖ ^ c} ↔ c ≤ a ∧ c ≤ b ∧ ϖ ^ c ∣ y := by
  rw [entryIdeal_le_iff]
  simp only [Fin.forall_fin_two, gU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Ideal.mem_span_singleton]
  rw [Units.dvd_mul_left, Units.dvd_mul_left, pow_irreducible_dvd_pow_iff hϖ, pow_irreducible_dvd_pow_iff hϖ]
  constructor
  · rintro ⟨⟨ha, hy⟩, -, hb⟩
    exact ⟨ha, hb, hy⟩
  · rintro ⟨ha, hb, hy⟩
    exact ⟨⟨ha, hy⟩, dvd_zero _, hb⟩

theorem invariants_of_cartanRel (u₁ u₂ : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (a b : ℕ) (y : R)
    {c d : ℕ} (hcd : c ≤ d) (h : CartanRel (gU u₁ u₂ ϖ a b y) (cartanDiag ϖ c d)) :
    c + d = a + b ∧ c ≤ min a b ∧ ϖ ^ c ∣ y ∧ (c < min a b → ¬ ϖ ^ (c + 1) ∣ y) := by
  have hE : entryIdeal (gU u₁ u₂ ϖ a b y) = Ideal.span {ϖ ^ c} := by
    rw [h.entryIdeal_eq, entryIdeal_cartanDiag ϖ hcd]
  have hdet : Associated ((u₁ : R) * (u₂ : R) * ϖ ^ (a + b)) (ϖ ^ (c + d)) := by
    rw [← gU_det, ← cartanDiag_det]
    exact h.det_associated
  have hab : c + d = a + b := by
    have h1 : Associated (ϖ ^ (a + b)) (ϖ ^ (c + d)) := by
      have hu : IsUnit ((u₁ : R) * (u₂ : R)) := u₁.isUnit.mul u₂.isUnit
      exact ((associated_isUnit_mul_left_iff hu).1 hdet)
    exact ((pow_irreducible_associated_iff hϖ).1 h1).symm
  obtain ⟨ha, hb, hy⟩ := (entryIdeal_gU_le_iff u₁ u₂ hϖ a b y c).1 hE.le
  refine ⟨hab, le_min ha hb, hy, fun hlt hdvd => ?_⟩
  have hle : entryIdeal (gU u₁ u₂ ϖ a b y) ≤ Ideal.span {ϖ ^ (c + 1)} :=
    (entryIdeal_gU_le_iff u₁ u₂ hϖ a b y (c + 1)).2
      ⟨Nat.succ_le_of_lt (lt_of_lt_of_le hlt (min_le_left a b)),
        Nat.succ_le_of_lt (lt_of_lt_of_le hlt (min_le_right a b)), hdvd⟩
  rw [hE, Ideal.span_singleton_le_span_singleton, pow_irreducible_dvd_pow_iff hϖ] at hle
  omega

theorem integral_iff (u₁ u₂ : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (a b : ℕ) (y : R) {c d : ℕ} (hcd : c ≤ d) :
    CartanRel (gU u₁ u₂ ϖ a b y) (cartanDiag ϖ c d) ↔
      c + d = a + b ∧ c ≤ min a b ∧ ϖ ^ c ∣ y ∧ (c < min a b → ¬ ϖ ^ (c + 1) ∣ y) := by
  refine ⟨invariants_of_cartanRel u₁ u₂ hϖ a b y hcd, ?_⟩
  rintro ⟨hab, hcm, hy, hsharp⟩
  obtain ⟨c', d', hc'd', hrel⟩ :=
    LocalGL2.exists_cartanRel_cartanDiag hϖ (gU u₁ u₂ ϖ a b y) (gU_det_ne_zero u₁ u₂ hϖ a b y)
  obtain ⟨hab', hcm', hy', hsharp'⟩ := invariants_of_cartanRel u₁ u₂ hϖ a b y hc'd' hrel
  have hE : entryIdeal (gU u₁ u₂ ϖ a b y) = Ideal.span {ϖ ^ c'} := by
    rw [hrel.entryIdeal_eq, entryIdeal_cartanDiag ϖ hc'd']
  have hcc' : c ≤ c' := by
    have hle : entryIdeal (gU u₁ u₂ ϖ a b y) ≤ Ideal.span {ϖ ^ c} :=
      (entryIdeal_gU_le_iff u₁ u₂ hϖ a b y c).2 ⟨hcm.trans (min_le_left a b), hcm.trans (min_le_right a b), hy⟩
    rw [hE, Ideal.span_singleton_le_span_singleton, pow_irreducible_dvd_pow_iff hϖ] at hle
    exact hle
  have hc'c : c' ≤ c := by
    by_contra hlt
    rw [not_le] at hlt
    have hcmin : c < min a b := lt_of_lt_of_le hlt hcm'
    exact hsharp hcmin ((pow_dvd_pow ϖ (Nat.succ_le_of_lt hlt)).trans hy')
  have hc : c' = c := le_antisymm hc'c hcc'
  have hd : d' = d := by omega
  rw [hc, hd] at hrel
  exact hrel

end Integral

section Fraction

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

local notation "π" => algebraMap R K ϖ
local notation "P" => LocalGL2.diagPi ϖ hϖ0
local notation "Q" => LocalGL2.localRepInf ϖ hϖ0
local notation "U" => LocalGL2.integralSubgroup R K

theorem coe_z :
    ((P * Q : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = π • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Units.val_mul, coe_diagPi, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_z_pow (n : ℕ) :
    (((P * Q) ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = π ^ n • (1 : Matrix (Fin 2) (Fin 2) K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ih, coe_z, smul_mul_smul_comm, one_mul, ← pow_succ]

theorem coe_diagPi_pow (n : ℕ) :
    ((P ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![π ^ n, 0; 0, 1] := by
  induction n with
  | zero => simp [Matrix.one_fin_two]
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ih, coe_diagPi]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

theorem coe_localRepInf_pow (n : ℕ) :
    ((Q ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 0, π ^ n] := by
  induction n with
  | zero => simp [Matrix.one_fin_two]
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ih, coe_localRepInf]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

theorem coe_D_nat (c d : ℕ) :
    ((P ^ c * Q ^ d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = (cartanDiag ϖ c d).map (algebraMap R K) := by
  rw [Units.val_mul, coe_diagPi_pow, coe_localRepInf_pow, cartanDiag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem z_central (g : GL (Fin 2) K) : (P * Q) * g = g * (P * Q) := by
  apply Units.ext
  have h := coe_z ϖ hϖ0
  rw [Units.val_mul] at h
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, h, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]

theorem commute_PQ : Commute (P) (Q : GL (Fin 2) K) := by
  show P * Q = Q * P
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, coe_diagPi, coe_localRepInf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem D_eq_z_zpow_mul (m n s : ℤ) :
    (P ^ m * Q ^ n : GL (Fin 2) K) = (P * Q) ^ s * (P ^ (m - s) * Q ^ (n - s)) := by
  rw [(commute_PQ ϖ hϖ0).mul_zpow]
  have hc : Commute (Q ^ s : GL (Fin 2) K) (P ^ (m - s)) := ((commute_PQ ϖ hϖ0).symm).zpow_zpow s (m - s)
  calc (P ^ m * Q ^ n : GL (Fin 2) K)
      = P ^ s * P ^ (m - s) * (Q ^ s * Q ^ (n - s)) := by
        rw [← _root_.zpow_add, ← _root_.zpow_add]; congr 2 <;> ring
    _ = P ^ s * (P ^ (m - s) * Q ^ s) * Q ^ (n - s) := by group
    _ = P ^ s * (Q ^ s * P ^ (m - s)) * Q ^ (n - s) := by rw [hc.eq]
    _ = P ^ s * Q ^ s * (P ^ (m - s) * Q ^ (n - s)) := by group

theorem mem_doubleCoset_central_mul_iff {G : Type*} [Group G] {V : Subgroup G} {c g x : G}
    (hc : ∀ y : G, c * y = y * c) :
    x ∈ doubleCoset V (c * g) ↔ c⁻¹ * x ∈ doubleCoset V g := by
  rw [mem_doubleCoset_iff, mem_doubleCoset_iff]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    refine ⟨u, hu, v, hv, ?_⟩
    rw [show u * (c * g) * v = c * (u * g * v) by rw [← mul_assoc, ← hc u]; group]
    rw [inv_mul_cancel_left]
  · rintro ⟨u, hu, v, hv, huv⟩
    refine ⟨u, hu, v, hv, ?_⟩
    rw [show u * (c * g) * v = c * (u * g * v) by rw [← mul_assoc, ← hc u]; group, huv,
      mul_inv_cancel_left]

noncomputable def iota (M : Matrix (Fin 2) (Fin 2) R) (hM : M.det ≠ 0) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (M.map (algebraMap R K)) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun h => hM (IsFractionRing.injective R K (by rw [h, map_zero])))

theorem coe_iota (M : Matrix (Fin 2) (Fin 2) R) (hM : M.det ≠ 0) :
    ((iota (K := K) M hM : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = M.map (algebraMap R K) := rfl

theorem map_injective : Function.Injective fun M : Matrix (Fin 2) (Fin 2) R => M.map (algebraMap R K) := by
  intro M N h
  ext i j
  have := congrFun (congrFun h i) j
  exact IsFractionRing.injective R K this

theorem coe_mapGL (k : GL (Fin 2) R) :
    ((Matrix.GeneralLinearGroup.map (algebraMap R K) k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (k : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K) := rfl

theorem iota_mem_doubleCoset_iff (M : Matrix (Fin 2) (Fin 2) R) (hM : M.det ≠ 0) (c d : ℕ) :
    iota (K := K) M hM ∈ doubleCoset U (P ^ (c : ℤ) * Q ^ (d : ℤ)) ↔ CartanRel M (cartanDiag ϖ c d) := by
  rw [zpow_natCast, zpow_natCast, mem_doubleCoset_iff]
  constructor
  · rintro ⟨u, ⟨k₁, rfl⟩, v, ⟨k₂, rfl⟩, huv⟩
    refine ⟨k₁, k₂, ?_⟩
    apply map_injective (K := K)
    have h := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) huv
    rw [Units.val_mul, Units.val_mul, coe_D_nat, coe_iota, coe_mapGL, coe_mapGL] at h
    show M.map (algebraMap R K) = (k₁.val * cartanDiag ϖ c d * k₂.val).map (algebraMap R K)
    rw [← h, Matrix.map_mul, Matrix.map_mul]
  · rintro ⟨k₁, k₂, hM'⟩
    refine ⟨Matrix.GeneralLinearGroup.map (algebraMap R K) k₁, ⟨k₁, rfl⟩,
      Matrix.GeneralLinearGroup.map (algebraMap R K) k₂, ⟨k₂, rfl⟩, ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_D_nat, coe_iota, coe_mapGL, coe_mapGL]
    conv_rhs => rw [hM']
    rw [Matrix.map_mul, Matrix.map_mul]

end Fraction

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem main {ϖ : R} (hϖ : Irreducible ϖ) (hϖ0 : algebraMap R K ϖ ≠ 0)
    (g : GL (Fin 2) K) (u₁ u₂ : Rˣ) (a b : ℤ)
    (h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = algebraMap R K u₁ * algebraMap R K ϖ ^ a)
    (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = algebraMap R K u₂ * algebraMap R K ϖ ^ b)
    {m n : ℤ} (hmn : m ≤ n) :
    g ∈ doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n) ↔
      m + n = a + b ∧ m ≤ min a b ∧
        (∃ r : R, (g : Matrix (Fin 2) (Fin 2) K) 0 1 = algebraMap R K ϖ ^ m * algebraMap R K r) ∧
        (m < min a b →
          ¬ ∃ r : R, (g : Matrix (Fin 2) (Fin 2) K) 0 1 = algebraMap R K ϖ ^ (m + 1) * algebraMap R K r) := by

  set y : K := (g : Matrix (Fin 2) (Fin 2) K) 0 1 with hy
  obtain ⟨r₀, d₀, hd₀, hyd⟩ := IsFractionRing.div_surjective (A := R) y
  have hd₀0 : d₀ ≠ 0 := nonZeroDivisors.ne_zero hd₀
  obtain ⟨N, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd₀0 hϖ

  have hπ0 : algebraMap R K ϖ ≠ 0 := hϖ0
  have hwK0 : algebraMap R K w ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero w.ne_zero)
  have hwinv : algebraMap R K ((w⁻¹ : Rˣ) : R) = (algebraMap R K w)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← map_mul, Units.mul_inv, map_one]
  have hyN : algebraMap R K ϖ ^ N * y = algebraMap R K (r₀ * ((w⁻¹ : Rˣ) : R)) := by
    have hd : algebraMap R K d₀ = algebraMap R K w * algebraMap R K ϖ ^ N := by
      rw [hw, map_mul, map_pow]
    rw [← hyd, hd, map_mul, hwinv]
    field_simp

  set N' : ℕ := N + a.natAbs + b.natAbs + m.natAbs with hN'
  have hN'N : N ≤ N' := by omega
  have ha' : 0 ≤ a + N' := by have := Int.le_natAbs (a := -a); simp at this; omega
  have hb' : 0 ≤ b + N' := by have := Int.le_natAbs (a := -b); simp at this; omega
  have hm' : 0 ≤ m + N' := by have := Int.le_natAbs (a := -m); simp at this; omega
  have hn' : 0 ≤ n + N' := le_trans hm' (by omega)

  set a' : ℕ := (a + N').toNat with ha'def
  set b' : ℕ := (b + N').toNat with hb'def
  set c : ℕ := (m + N').toNat with hcdef
  set d : ℕ := (n + N').toNat with hddef
  have ha'z : (a' : ℤ) = a + N' := Int.toNat_of_nonneg ha'
  have hb'z : (b' : ℤ) = b + N' := Int.toNat_of_nonneg hb'
  have hcz : (c : ℤ) = m + N' := Int.toNat_of_nonneg hm'
  have hdz : (d : ℤ) = n + N' := Int.toNat_of_nonneg hn'
  have hcd : c ≤ d := by omega

  set y' : R := r₀ * ((w⁻¹ : Rˣ) : R) * ϖ ^ (N' - N) with hy'def
  have hyN' : algebraMap R K ϖ ^ (N' : ℤ) * y = algebraMap R K y' := by
    rw [hy'def, map_mul, ← hyN, map_pow, zpow_natCast]
    have hsplit : algebraMap R K ϖ ^ N' = algebraMap R K ϖ ^ (N' - N) * algebraMap R K ϖ ^ N := by
      rw [← pow_add, Nat.sub_add_cancel hN'N]
    rw [hsplit]; ring

  have hpow : ∀ (e : ℤ) (e' : ℕ), (e' : ℤ) = e + N' →
      algebraMap R K ϖ ^ (N' : ℤ) * algebraMap R K ϖ ^ e = algebraMap R K (ϖ ^ e') := by
    intro e e' he
    rw [map_pow, ← zpow_natCast (algebraMap R K ϖ) e', he, ← zpow_add₀ hπ0, add_comm]

  have hM : (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (N' : ℤ) * g = iota (K := K) (gU u₁ u₂ ϖ a' b' y')
      (gU_det_ne_zero u₁ u₂ hϖ a' b' y') := by
    apply Units.ext
    rw [Units.val_mul, zpow_natCast, coe_z_pow, coe_iota, Matrix.smul_mul, Matrix.one_mul]
    ext i j
    fin_cases i <;> fin_cases j
    · show algebraMap R K ϖ ^ N' * (g : Matrix (Fin 2) (Fin 2) K) 0 0 = algebraMap R K ((u₁ : R) * ϖ ^ a')
      rw [h00, map_mul, ← hpow a a' ha'z, zpow_natCast]; ring
    · show algebraMap R K ϖ ^ N' * (g : Matrix (Fin 2) (Fin 2) K) 0 1 = algebraMap R K y'
      rw [← hyN', zpow_natCast]
    · show algebraMap R K ϖ ^ N' * (g : Matrix (Fin 2) (Fin 2) K) 1 0 = algebraMap R K 0
      rw [h10, mul_zero, map_zero]
    · show algebraMap R K ϖ ^ N' * (g : Matrix (Fin 2) (Fin 2) K) 1 1 = algebraMap R K ((u₂ : R) * ϖ ^ b')
      rw [h11, map_mul, ← hpow b b' hb'z, zpow_natCast]; ring

  have hcentral : ∀ x : GL (Fin 2) K, (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (-(N' : ℤ)) * x =
      x * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (-(N' : ℤ)) := fun x =>
    (Commute.zpow_left (show Commute (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) x from z_central ϖ hϖ0 x) _).eq
  have hshift : g ∈ doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n) ↔
      CartanRel (gU u₁ u₂ ϖ a' b' y') (cartanDiag ϖ c d) := by
    rw [D_eq_z_zpow_mul ϖ hϖ0 m n (-(N' : ℤ)), mem_doubleCoset_central_mul_iff hcentral, _root_.zpow_neg, inv_inv, hM,
      show m - -(N' : ℤ) = (c : ℤ) by omega, show n - -(N' : ℤ) = (d : ℤ) by omega]
    exact iota_mem_doubleCoset_iff ϖ hϖ0 _ _ c d
  rw [hshift, integral_iff u₁ u₂ hϖ a' b' y' hcd]

  have hdvd : ∀ (e : ℤ) (e' : ℕ), (e' : ℤ) = e + N' →
      (ϖ ^ e' ∣ y' ↔ ∃ r : R, y = algebraMap R K ϖ ^ e * algebraMap R K r) := by
    intro e e' he
    constructor
    · rintro ⟨r, hr⟩
      refine ⟨r, ?_⟩
      have h1 : algebraMap R K ϖ ^ (N' : ℤ) * y = algebraMap R K ϖ ^ (N' : ℤ) * (algebraMap R K ϖ ^ e * algebraMap R K r) := by
        rw [hyN', hr, map_mul, ← hpow e e' he, mul_assoc]
      exact mul_left_cancel₀ (zpow_ne_zero _ hπ0) h1
    · rintro ⟨r, hr⟩
      refine ⟨r, IsFractionRing.injective R K ?_⟩
      rw [← hyN', hr, ← mul_assoc, hpow e e' he, ← map_mul]
  have hdvd0 := hdvd m c hcz
  have hdvd1 := hdvd (m + 1) (c + 1) (by push_cast; omega)
  have hmin : c ≤ min a' b' ↔ m ≤ min a b := by
    rw [le_min_iff, le_min_iff]; omega
  have hlt : c < min a' b' ↔ m < min a b := by
    rw [lt_min_iff, lt_min_iff]; omega
  rw [hdvd0, hmin]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by omega, h2, h3, fun h => (hdvd1.not).1 (h4 (hlt.2 h))⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by omega, h2, h3, fun h => (hdvd1.not).2 (h4 (hlt.1 h))⟩

end Main

end KcCartanUpperK

open KcCartanUpperK in
theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) (hϖ0 : algebraMap R K ϖ ≠ 0)
    (g : GL (Fin 2) K) (u₁ u₂ : Rˣ) (a b : ℤ)
    (h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = algebraMap R K u₁ * algebraMap R K ϖ ^ a)
    (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = algebraMap R K u₂ * algebraMap R K ϖ ^ b)
    {m n : ℤ} (hmn : m ≤ n) :
    g ∈ doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n) ↔
      m + n = a + b ∧ m ≤ min a b ∧
        (∃ r : R, (g : Matrix (Fin 2) (Fin 2) K) 0 1 = algebraMap R K ϖ ^ m * algebraMap R K r) ∧
        (m < min a b →
          ¬ ∃ r : R, (g : Matrix (Fin 2) (Fin 2) K) 0 1 = algebraMap R K ϖ ^ (m + 1) * algebraMap R K r) :=
  main hϖ hϖ0 g u₁ u₂ a b h00 h10 h11 hmn

end S_LocalGL2_mem_doubleCoset_diagPi_zpow_mul_localRepInf_zpow_iff_of_upperTriangular
end P2MW
export P2MW.S_LocalGL2_mem_doubleCoset_diagPi_zpow_mul_localRepInf_zpow_iff_of_upperTriangular (solution)
