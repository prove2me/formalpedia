-- Prove2me | solution 1 for LocalGL2.finite_image_integralSubgroup_mul_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/08314e66-adb3-57ea-871d-7de9f24f324f

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_LocalLanglands_CartanDecomposition
import Theorems.Thm_LocalGL2_exists_cartanRel_cartanDiag
import Theorems.Thm_LocalGL2_cartanDiag_cartanRel_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalGL2_finite_image_integralSubgroup_mul_singleton

set_option autoImplicit false

open scoped Pointwise
open Matrix

namespace LocalGL2
p2m_export "LocalGL2" "weylInt weylInt_mem diagPi coe_diagPi localRepInf coe_localRepInf finite_image_mul_diagPi integralSubgroup det_map_algebraMap cartanDiag CartanRel exists_cartanRel_cartanDiag cartanDiag_cartanRel_iff"
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

section Finite

variable {G : Type*} [Group G] {U : Subgroup G}

theorem finite_image_mk_mul {A B : Set G}
    (hA : (QuotientGroup.mk '' A : Set (G ⧸ U)).Finite)
    (hB : (QuotientGroup.mk '' B : Set (G ⧸ U)).Finite)
    (hUB : ∀ u ∈ U, ∀ b ∈ B, u * b ∈ B) :
    (QuotientGroup.mk '' (A * B) : Set (G ⧸ U)).Finite := by
  have hsub : (QuotientGroup.mk '' (A * B) : Set (G ⧸ U))
      ⊆ ⋃ q ∈ (QuotientGroup.mk '' A : Set (G ⧸ U)),
          (fun c : G ⧸ U => (q.out : G) • c) '' (QuotientGroup.mk '' B : Set (G ⧸ U)) := by
    rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    refine Set.mem_iUnion₂.mpr ⟨QuotientGroup.mk a, ⟨a, ha, rfl⟩, ?_⟩
    have hu : ((QuotientGroup.mk a : G ⧸ U).out)⁻¹ * a ∈ U :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk a : G ⧸ U))
    refine ⟨QuotientGroup.mk (((QuotientGroup.mk a : G ⧸ U).out)⁻¹ * a * b),
      ⟨_, hUB _ hu b hb, rfl⟩, ?_⟩
    show ((QuotientGroup.mk a : G ⧸ U).out : G) • (QuotientGroup.mk _ : G ⧸ U) = QuotientGroup.mk (a * b)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  exact Set.Finite.subset (Set.Finite.biUnion hA fun q _ => hB.image _) hsub

theorem finite_image_mk_coe : (QuotientGroup.mk '' (U : Set G) : Set (G ⧸ U)).Finite := by
  refine Set.Finite.subset (Set.finite_singleton (QuotientGroup.mk 1)) ?_
  rintro _ ⟨u, hu, rfl⟩
  rw [Set.mem_singleton_iff]
  refine QuotientGroup.eq.mpr ?_
  rw [mul_one]
  exact inv_mem hu

theorem image_mk_mul_singleton_subset_of_mem_doubleCoset {g d : G}
    (hg : g ∈ HeckePair.doubleCoset U d) :
    (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ U))
      ⊆ QuotientGroup.mk '' ((U : Set G) * {d}) := by
  rw [← HeckePair.image_mk_doubleCoset, ← HeckePair.image_mk_doubleCoset]
  refine Set.image_mono fun x hx => ?_
  obtain ⟨u, hu, v, hv, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hg
  obtain ⟨u', hu', v', hv', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  exact HeckePair.mem_doubleCoset_iff.mpr ⟨u' * u, mul_mem hu' hu, v * v', mul_mem hv hv', by group⟩

theorem image_mk_mul_singleton_center_mul_subset {z h : G} (hz : z ∈ Subgroup.center G) :
    (QuotientGroup.mk '' ((U : Set G) * {z * h}) : Set (G ⧸ U))
      ⊆ (fun c : G ⧸ U => z • c) '' (QuotientGroup.mk '' ((U : Set G) * {h}) : Set (G ⧸ U)) := by
  rintro _ ⟨_, ⟨u, hu, _, rfl, rfl⟩, rfl⟩
  refine ⟨QuotientGroup.mk (u * h), ⟨u * h, ⟨u, hu, h, rfl, rfl⟩, rfl⟩, ?_⟩
  show z • (QuotientGroup.mk (u * h) : G ⧸ U) = QuotientGroup.mk (u * (z * h))
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc, ← mul_assoc,
    (Subgroup.mem_center_iff.mp hz) u]

end Finite

section S0

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

omit [IsFractionRing R K] in

theorem finite_image_mk_integralSubgroup_mul_doubleCoset_pow (hϖ : Irreducible ϖ)
    [Finite (R ⧸ Ideal.span {ϖ})] (r : ℕ) :
    (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0) ^ r) :
      Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite := by
  induction r with
  | zero =>
    rw [pow_zero, mul_one]
    exact finite_image_mk_coe
  | succ r ih =>
    rw [pow_succ, ← mul_assoc]
    refine finite_image_mk_mul ih ?_ fun u hu b hb => HeckePair.mul_mem_doubleCoset hb hu
    rw [HeckePair.image_mk_doubleCoset]
    exact finite_image_mul_diagPi ϖ hϖ0 hϖ

theorem finite_image_integralSubgroup_mul_singleton_impl
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] (g : GL (Fin 2) K) :
    (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K)) * {g}) :
      Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite := by
  have hϖ0 : algebraMap R K ϖ ≠ 0 := fun h =>
    hϖ.ne_zero (IsFractionRing.injective R K (by rw [h, map_zero]))

  obtain ⟨m, n, hmn, hg⟩ := exists_mem_doubleCoset_zpow ϖ hϖ0 hϖ g
  refine Set.Finite.subset ?_ (image_mk_mul_singleton_subset_of_mem_doubleCoset hg)

  have htl := commute_diagPi_localRepInf ϖ hϖ0
  have hz : (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ m ∈ Subgroup.center (GL (Fin 2) K) :=
    Subgroup.zpow_mem _ (diagPi_mul_localRepInf_mem_center'' ϖ hϖ0) m
  have hd : diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n
      = (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ m * localRepInf ϖ hϖ0 ^ (n - m).toNat := by
    rw [htl.mul_zpow, mul_assoc, ← zpow_natCast, Int.toNat_of_nonneg (by omega),
      ← _root_.zpow_add, add_sub_cancel]
  rw [hd]
  refine Set.Finite.subset (Set.Finite.image _ ?_) (image_mk_mul_singleton_center_mul_subset hz)

  have hl : localRepInf ϖ hϖ0 ∈ HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0) :=
    HeckePair.mem_doubleCoset_iff.mpr ⟨weylInt R K, weylInt_mem, weylInt R K, weylInt_mem, rfl⟩
  refine Set.Finite.subset (finite_image_mk_integralSubgroup_mul_doubleCoset_pow ϖ hϖ0 hϖ _)
    (Set.image_mono (Set.mul_subset_mul_left (Set.singleton_subset_iff.mpr (Set.pow_mem_pow hl))))

end S0

end

end LocalGL2

open scoped Pointwise
p2m_open "LocalGL2 P2MW.S_LocalGL2_finite_image_integralSubgroup_mul_singleton.LocalGL2"

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] (g : GL (Fin 2) K) :
    (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K)) * {g}) :
      Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite := by
  exact LocalGL2.finite_image_integralSubgroup_mul_singleton_impl hϖ g

end S_LocalGL2_finite_image_integralSubgroup_mul_singleton
end P2MW
export P2MW.S_LocalGL2_finite_image_integralSubgroup_mul_singleton (solution)
