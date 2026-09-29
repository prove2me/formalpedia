-- Prove2me | solution 1 for LocalGL2.exists_basis_heckeIndicator_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d0f41b8e-3dc2-5fbc-b37a-a1b3b00a929a

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_LocalLanglands_CartanDecomposition
import Theorems.Thm_LocalGL2_exists_cartanRel_cartanDiag
import Theorems.Thm_LocalGL2_cartanDiag_cartanRel_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalGL2_exists_basis_heckeIndicator_zpow

set_option autoImplicit false

open scoped Pointwise
open Matrix

namespace LocalGL2
p2m_export "LocalGL2" "diagPi coe_diagPi localRepInf coe_localRepInf integralSubgroup det_map_algebraMap cartanDiag CartanRel exists_cartanRel_cartanDiag cartanDiag_cartanRel_iff"
p2m_open "LocalGL2"

noncomputable section

section Basic

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

theorem diag_two_pow (x y : K) (n : ℕ) :
    (!![x, 0; 0, y] : Matrix (Fin 2) (Fin 2) K) ^ n = !![x ^ n, 0; 0, y ^ n] := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, pow_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

theorem commute_diagPi_localRepInf : Commute (diagPi ϖ hϖ0) (localRepInf ϖ hϖ0) := by
  apply Units.ext
  change (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K) * (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K)
    = (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K) * (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K)
  rw [coe_diagPi, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_diagPi_zpow_mul_localRepInf_zpow (a b : ℕ) :
    ((diagPi ϖ hϖ0 ^ (a : ℤ) * localRepInf ϖ hϖ0 ^ (b : ℤ) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)
      = (cartanDiag ϖ a b).map (algebraMap R K) := by
  rw [zpow_natCast, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, coe_diagPi, coe_localRepInf, diag_two_pow, diag_two_pow,
    one_pow, one_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, cartanDiag, map_pow]

theorem coe_map_algebraMap (k : GL (Fin 2) R) :
    ((Matrix.GeneralLinearGroup.map (algebraMap R K) k : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)
      = (k : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K) := rfl

theorem coe_diagPi_mul_coe_localRepInf'' :
    (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K) * (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K)
      = algebraMap R K ϖ • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [coe_diagPi, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagPi_mul_localRepInf_mem_center'' :
    diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ∈ Subgroup.center (GL (Fin 2) K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  simp only [Units.val_mul]
  rw [coe_diagPi_mul_coe_localRepInf'', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]

theorem diagPi_mul_localRepInf_pow_mul_apply (N : ℕ) (m : GL (Fin 2) K) (i j : Fin 2) :
    (((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ N * m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
      = algebraMap R K ϖ ^ N * (m : Matrix (Fin 2) (Fin 2) K) i j := by
  induction N generalizing m with
  | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
  | succ N ih =>
    rw [pow_succ, mul_assoc, ih, Units.val_mul, Units.val_mul, coe_diagPi_mul_coe_localRepInf'',
      Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul, pow_succ, mul_assoc]

theorem diagPi_mul_localRepInf_zpow_mul (N m n : ℤ) :
    (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ N * (diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n)
      = diagPi ϖ hϖ0 ^ (N + m) * localRepInf ϖ hϖ0 ^ (N + n) := by
  have htl := commute_diagPi_localRepInf ϖ hϖ0
  have hc : localRepInf ϖ hϖ0 ^ N * diagPi ϖ hϖ0 ^ m = diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ N :=
    (htl.symm.zpow_zpow N m).eq
  rw [htl.mul_zpow, mul_assoc, ← mul_assoc (localRepInf ϖ hϖ0 ^ N), hc, mul_assoc, ← _root_.zpow_add,
    ← mul_assoc, ← _root_.zpow_add]

end Basic

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

include hϖ0 in

theorem exists_pow_mul_mem_range (hϖ : Irreducible ϖ) (x : K) :
    ∃ n : ℕ, algebraMap R K ϖ ^ n * x ∈ Set.range (algebraMap R K) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, u, hbu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hu : algebraMap R K u * algebraMap R K ↑u⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  refine ⟨n, a * ↑u⁻¹, ?_⟩
  rw [hbu, map_mul, map_mul, map_pow, mul_div_assoc', mul_comm (algebraMap R K ϖ ^ n),
    mul_div_mul_right _ _ (pow_ne_zero n hϖ0), div_eq_mul_inv, inv_eq_of_mul_eq_one_right hu]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem pow_mul_mem_range_of_le {x : K} {n N : ℕ} (hnN : n ≤ N)
    (hx : algebraMap R K ϖ ^ n * x ∈ Set.range (algebraMap R K)) :
    algebraMap R K ϖ ^ N * x ∈ Set.range (algebraMap R K) := by
  obtain ⟨r, hr⟩ := hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnN
  refine ⟨ϖ ^ k * r, ?_⟩
  rw [map_mul, map_pow, hr, pow_add]
  ring

theorem exists_mem_doubleCoset_zpow (hϖ : Irreducible ϖ) (g : GL (Fin 2) K) :
    ∃ m n : ℤ, m ≤ n ∧ g ∈ HeckePair.doubleCoset (integralSubgroup R K)
      (diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n) := by

  choose nf hnf using fun i j => exists_pow_mul_mem_range ϖ hϖ0 hϖ ((g : Matrix (Fin 2) (Fin 2) K) i j)
  set N : ℕ := ∑ p : Fin 2 × Fin 2, nf p.1 p.2
  have hle : ∀ i j, nf i j ≤ N := fun i j =>
    Finset.single_le_sum (f := fun p : Fin 2 × Fin 2 => nf p.1 p.2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (i, j))
  have hint : ∀ i j, ∃ r : R, algebraMap R K r =
      (((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ N * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j := by
    intro i j
    obtain ⟨r, hr⟩ := pow_mul_mem_range_of_le ϖ (hle i j) (hnf i j)
    exact ⟨r, by rw [diagPi_mul_localRepInf_pow_mul_apply, hr]⟩
  choose e he using hint
  have hinj := IsFractionRing.injective R K

  have hemap : (Matrix.of e : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K)
      = (((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ N * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    exact he i j
  have hdet : (Matrix.of e : Matrix (Fin 2) (Fin 2) R).det ≠ 0 := by
    intro h0
    apply Matrix.GeneralLinearGroup.det_ne_zero ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ N * g)
    rw [← hemap, det_map_algebraMap, h0, map_zero]

  obtain ⟨a, b, hab, k₁, k₂, hk⟩ := LocalGL2.exists_cartanRel_cartanDiag hϖ (Matrix.of e) hdet

  have hGL : (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ N * g
      = Matrix.GeneralLinearGroup.map (algebraMap R K) k₁
          * (diagPi ϖ hϖ0 ^ (a : ℤ) * localRepInf ϖ hϖ0 ^ (b : ℤ))
          * Matrix.GeneralLinearGroup.map (algebraMap R K) k₂ := by
    apply Units.ext
    rw [← hemap, hk, Units.val_mul, Units.val_mul, coe_map_algebraMap, coe_map_algebraMap,
      coe_diagPi_zpow_mul_localRepInf_zpow, Matrix.map_mul, Matrix.map_mul]
  refine ⟨(a : ℤ) - N, (b : ℤ) - N, by omega, ?_⟩
  refine HeckePair.mem_doubleCoset_iff.mpr
    ⟨Matrix.GeneralLinearGroup.map (algebraMap R K) k₁, ⟨k₁, rfl⟩,
      Matrix.GeneralLinearGroup.map (algebraMap R K) k₂, ⟨k₂, rfl⟩, ?_⟩

  have hzc : ∀ x : GL (Fin 2) K, x * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (N : ℤ)
      = (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (N : ℤ) * x := fun x =>
    Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ (diagPi_mul_localRepInf_mem_center'' ϖ hϖ0) N) x
  have hGL' : (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (N : ℤ) * g
      = Matrix.GeneralLinearGroup.map (algebraMap R K) k₁
          * (diagPi ϖ hϖ0 ^ (a : ℤ) * localRepInf ϖ hϖ0 ^ (b : ℤ))
          * Matrix.GeneralLinearGroup.map (algebraMap R K) k₂ := by
    rw [zpow_natCast]; exact hGL
  apply mul_left_cancel (a := (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (N : ℤ))
  rw [hGL', ← mul_assoc, ← mul_assoc, ← hzc,
    mul_assoc _ ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (N : ℤ)),
    diagPi_mul_localRepInf_zpow_mul, add_sub_cancel, add_sub_cancel]

theorem zpow_pair_unique (hϖ : Irreducible ϖ) {m n m' n' : ℤ} (hmn : m ≤ n) (hmn' : m' ≤ n')
    (h : diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n ∈ HeckePair.doubleCoset (integralSubgroup R K)
      (diagPi ϖ hϖ0 ^ m' * localRepInf ϖ hϖ0 ^ n')) :
    m = m' ∧ n = n' := by
  obtain ⟨u, hu, v, hv, huv⟩ := HeckePair.mem_doubleCoset_iff.mp h
  obtain ⟨k₁, rfl⟩ := hu
  obtain ⟨k₂, rfl⟩ := hv

  set M : ℕ := (-m).toNat + (-m').toNat with hM
  have hm0 : 0 ≤ m + M := by omega
  have hn0 : 0 ≤ n + M := by omega
  have hm0' : 0 ≤ m' + M := by omega
  have hn0' : 0 ≤ n' + M := by omega
  have hzc : ∀ x : GL (Fin 2) K, x * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (M : ℤ)
      = (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (M : ℤ) * x := fun x =>
    Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ (diagPi_mul_localRepInf_mem_center'' ϖ hϖ0) M) x
  have huv' := congrArg ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (M : ℤ) * ·) huv
  rw [← mul_assoc, ← mul_assoc, ← hzc,
    mul_assoc _ ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (M : ℤ)),
    diagPi_mul_localRepInf_zpow_mul, diagPi_mul_localRepInf_zpow_mul, add_comm (M : ℤ) m',
    add_comm (M : ℤ) n', add_comm (M : ℤ) m, add_comm (M : ℤ) n,
    ← Int.toNat_of_nonneg hm0, ← Int.toNat_of_nonneg hn0, ← Int.toNat_of_nonneg hm0',
    ← Int.toNat_of_nonneg hn0'] at huv'

  have hmat := congrArg (fun x : GL (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K)) huv'
  rw [Units.val_mul, Units.val_mul, coe_map_algebraMap, coe_map_algebraMap,
    coe_diagPi_zpow_mul_localRepInf_zpow, coe_diagPi_zpow_mul_localRepInf_zpow,
    ← Matrix.map_mul, ← Matrix.map_mul] at hmat
  have hR : (k₁ : Matrix (Fin 2) (Fin 2) R) * cartanDiag ϖ (m' + ↑M).toNat (n' + ↑M).toNat
        * (k₂ : Matrix (Fin 2) (Fin 2) R)
      = cartanDiag ϖ (m + ↑M).toNat (n + ↑M).toNat :=
    Matrix.map_injective (f := algebraMap R K) (IsFractionRing.injective R K) hmat
  have hrel : CartanRel (cartanDiag ϖ (m + ↑M).toNat (n + ↑M).toNat)
      (cartanDiag ϖ (m' + ↑M).toNat (n' + ↑M).toNat) := ⟨k₁, k₂, hR.symm⟩
  have hiff := (LocalGL2.cartanDiag_cartanRel_iff hϖ (by omega) (by omega)).mp hrel
  omega

end DVR

end

end LocalGL2

namespace HeckePair
p2m_export "HeckePair" "HeckeAlgebra apply_left_mul apply_mul_right finite_cosets ext coe_apply_add coe_apply_smul mul_apply one_mul mul_one smul_mul mul_assoc doubleCoset mem_doubleCoset_iff self_mem_doubleCoset doubleCoset_mul_mem heckeIndicator heckeIndicator_apply_of_mem heckeIndicator_apply_of_notMem"
p2m_open "HeckePair"

noncomputable section

variable {G : Type*} [Group G] {U : Subgroup G} {R₀ : Type*} [CommRing R₀]

theorem apply_eq_of_mem_doubleCoset'' (f : HeckeAlgebra U R₀) {g x : G}
    (hx : x ∈ doubleCoset U g) : (f : G → R₀) x = (f : G → R₀) g := by
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp hx
  rw [apply_mul_right f hv, apply_left_mul f hu]

theorem coe_apply_sum {ι : Type*} (s : Finset ι) (F : ι → HeckeAlgebra U R₀) (x : G) :
    ((∑ i ∈ s, F i : HeckeAlgebra U R₀) : G → R₀) x = ∑ i ∈ s, (F i : G → R₀) x := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, coe_apply_add, ih]

end

end HeckePair

namespace LocalGL2
p2m_export "LocalGL2" "diagPi coe_diagPi localRepInf coe_localRepInf integralSubgroup det_map_algebraMap cartanDiag CartanRel exists_cartanRel_cartanDiag cartanDiag_cartanRel_iff"
p2m_open "LocalGL2"

noncomputable section

section S2b

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

theorem zpow_pair_eq_of_mem_of_mem (hϖ : Irreducible ϖ) {m n m' n' : ℤ} (hmn : m ≤ n)
    (hmn' : m' ≤ n') {x : GL (Fin 2) K}
    (hx : x ∈ HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n))
    (hx' : x ∈ HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 ^ m' * localRepInf ϖ hϖ0 ^ n')) :
    m = m' ∧ n = n' := by
  refine zpow_pair_unique ϖ hϖ0 hϖ hmn hmn' ?_
  obtain ⟨u, hu, v, hv, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  obtain ⟨u', hu', v', hv', h'⟩ := HeckePair.mem_doubleCoset_iff.mp hx'
  refine HeckePair.mem_doubleCoset_iff.mpr ⟨u⁻¹ * u', mul_mem (inv_mem hu) hu', v' * v⁻¹,
    mul_mem hv' (inv_mem hv), ?_⟩
  have h'' : u⁻¹ * (u' * (diagPi ϖ hϖ0 ^ m' * localRepInf ϖ hϖ0 ^ n') * v') * v⁻¹
      = diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n := by
    rw [h']; group
  simpa only [mul_assoc] using h''

theorem exists_basis_heckeIndicator_zpow_impl
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ)
    {R₀ : Type*} [CommRing R₀]
    (hfin : ∀ g : GL (Fin 2) K,
      (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K)) * {g}) :
        Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    ∃ b : Module.Basis {p : ℤ × ℤ // p.1 ≤ p.2} R₀ (HeckePair.HeckeAlgebra (integralSubgroup R K) R₀),
      ∀ p, b p = HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0 ^ p.1.1 * localRepInf ϖ hϖ0 ^ p.1.2) (hfin _) := by
  classical

  set d : {p : ℤ × ℤ // p.1 ≤ p.2} → GL (Fin 2) K :=
    fun p => diagPi ϖ hϖ0 ^ p.1.1 * localRepInf ϖ hϖ0 ^ p.1.2 with hd
  set v : {p : ℤ × ℤ // p.1 ≤ p.2} → HeckePair.HeckeAlgebra (integralSubgroup R K) R₀ :=
    fun p => HeckePair.heckeIndicator R₀ (d p) (hfin _) with hv

  choose κm κn hκle hκmem using fun x : GL (Fin 2) K => exists_mem_doubleCoset_zpow ϖ hϖ0 hϖ x
  let κ : GL (Fin 2) K → {p : ℤ × ℤ // p.1 ≤ p.2} := fun x => ⟨(κm x, κn x), hκle x⟩
  have hκ : ∀ x, x ∈ HeckePair.doubleCoset (integralSubgroup R K) (d (κ x)) := fun x => hκmem x

  have hmem_iff : ∀ (x : GL (Fin 2) K) (p : {p : ℤ × ℤ // p.1 ≤ p.2}),
      x ∈ HeckePair.doubleCoset (integralSubgroup R K) (d p) ↔ p = κ x := by
    intro x p
    constructor
    · intro hx
      obtain ⟨h1, h2⟩ := zpow_pair_eq_of_mem_of_mem ϖ hϖ0 hϖ p.2 (hκle x) hx (hκ x)
      exact Subtype.ext (Prod.ext h1 h2)
    · rintro rfl
      exact hκ x

  have hval : ∀ (p : {p : ℤ × ℤ // p.1 ≤ p.2}) (x : GL (Fin 2) K),
      (v p : GL (Fin 2) K → R₀) x = if p = κ x then 1 else 0 := by
    intro p x
    by_cases h : p = κ x
    · rw [if_pos h]
      exact HeckePair.heckeIndicator_apply_of_mem _ ((hmem_iff x p).mpr h)
    · rw [if_neg h]
      exact HeckePair.heckeIndicator_apply_of_notMem _ (fun hx => h ((hmem_iff x p).mp hx))

  have hli : LinearIndependent R₀ v := by
    rw [linearIndependent_iff']
    intro s c hsum i hi
    have h := congrArg
      (fun f : HeckePair.HeckeAlgebra (integralSubgroup R K) R₀ => (f : GL (Fin 2) K → R₀) (d i)) hsum
    rw [HeckePair.coe_apply_sum] at h
    simp only [HeckePair.coe_apply_smul, hval, mul_boole, Finset.sum_ite_eq'] at h
    have hκi : κ (d i) = i := ((hmem_iff (d i) i).mp (HeckePair.self_mem_doubleCoset _)).symm
    rw [hκi, if_pos hi] at h
    exact h

  have hsp : ⊤ ≤ Submodule.span R₀ (Set.range v) := by
    intro f _
    set P : Finset {p : ℤ × ℤ // p.1 ≤ p.2} :=
      f.2.finite_cosets.toFinset.image (fun q => κ q.out) with hP
    have hf : f = ∑ p ∈ P, ((f : GL (Fin 2) K → R₀) (d p)) • v p := by
      apply HeckePair.ext
      intro x
      rw [HeckePair.coe_apply_sum]
      simp only [HeckePair.coe_apply_smul, hval, mul_boole, Finset.sum_ite_eq']
      by_cases hxP : κ x ∈ P
      · rw [if_pos hxP]
        exact HeckePair.apply_eq_of_mem_doubleCoset'' f (hκ x)
      · rw [if_neg hxP]
        by_contra hfx
        apply hxP

        have hq : (QuotientGroup.mk x : GL (Fin 2) K ⧸ integralSubgroup R K)
            ∈ f.2.finite_cosets.toFinset :=
          (Set.Finite.mem_toFinset _).mpr ⟨x, hfx, rfl⟩
        refine Finset.mem_image.mpr ⟨QuotientGroup.mk x, hq, ?_⟩

        have hu : x⁻¹ * (QuotientGroup.mk x : GL (Fin 2) K ⧸ integralSubgroup R K).out
            ∈ integralSubgroup R K :=
          QuotientGroup.eq.mp ((QuotientGroup.mk x : GL (Fin 2) K ⧸ integralSubgroup R K).out_eq').symm
        have hout : (QuotientGroup.mk x : GL (Fin 2) K ⧸ integralSubgroup R K).out
            ∈ HeckePair.doubleCoset (integralSubgroup R K) (d (κ x)) := by
          have := HeckePair.doubleCoset_mul_mem (hκ x) hu
          rwa [mul_inv_cancel_left] at this
        exact ((hmem_iff _ _).mp hout).symm
    rw [hf]
    exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun p => Module.Basis.mk_apply hli hsp p⟩

end S2b

end

end LocalGL2

open scoped Pointwise
p2m_open "LocalGL2 P2MW.S_LocalGL2_exists_basis_heckeIndicator_zpow.LocalGL2 HeckePair P2MW.S_LocalGL2_exists_basis_heckeIndicator_zpow.HeckePair"

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ)
    {R₀ : Type*} [CommRing R₀]
    (hfin : ∀ g : GL (Fin 2) K,
      (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K)) * {g}) :
        Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    ∃ b : Module.Basis {p : ℤ × ℤ // p.1 ≤ p.2} R₀ (HeckeAlgebra (integralSubgroup R K) R₀),
      ∀ p, b p = heckeIndicator R₀ (diagPi ϖ hϖ0 ^ p.1.1 * localRepInf ϖ hϖ0 ^ p.1.2) (hfin _) := by
  apply LocalGL2.exists_basis_heckeIndicator_zpow_impl <;> assumption

end S_LocalGL2_exists_basis_heckeIndicator_zpow
end P2MW
export P2MW.S_LocalGL2_exists_basis_heckeIndicator_zpow (solution)
