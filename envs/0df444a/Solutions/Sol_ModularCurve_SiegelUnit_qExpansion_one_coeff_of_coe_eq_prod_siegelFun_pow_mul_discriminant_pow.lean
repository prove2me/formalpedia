-- Prove2me | solution 1 for ModularCurve.SiegelUnit.qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a98dee19-02dd-5ab7-9528-ef5621f8f85a

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow
import Theorems.Thm_UpperHalfPlane_qExpansion_coeff_mul_width
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow

set_option autoImplicit false

noncomputable section

namespace DeltaQExpInt

open UpperHalfPlane ModularForm EisensteinSeries PowerSeries
open scoped MatrixGroups ArithmeticFunction.sigma

def sigmaSeries (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (σ k n : ℤ)

theorem coeff_sigmaSeries (k n : ℕ) :
    coeff n (sigmaSeries k) = if n = 0 then 0 else (σ k n : ℤ) := by
  simp [sigmaSeries]

def E4Z : PowerSeries ℤ := 1 + C 240 * sigmaSeries 3

def E6Z : PowerSeries ℤ := 1 - C 504 * sigmaSeries 5

theorem qExpansion_E₄_eq_map : qExpansion 1 E₄ = map (Int.castRingHom ℂ) E4Z := by
  ext m
  rw [E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel, E4Z,
    map_add, map_one, map_mul, PowerSeries.map_C, map_add, coeff_C_mul, coeff_map, coeff_one,
    coeff_sigmaSeries, eq_intCast, eq_intCast]
  split_ifs <;> push_cast <;> ring

theorem qExpansion_E₆_eq_map : qExpansion 1 E₆ = map (Int.castRingHom ℂ) E6Z := by
  ext m
  rw [E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel, E6Z,
    map_sub, map_one, map_mul, PowerSeries.map_C, map_sub, coeff_C_mul, coeff_map, coeff_one,
    coeff_sigmaSeries, eq_intCast, eq_intCast]
  split_ifs <;> push_cast <;> ring

def P144 : PowerSeries ℤ := C 5 * sigmaSeries 3 + C 7 * sigmaSeries 5

def P1728 : PowerSeries ℤ :=
  C 100 * sigmaSeries 3 ^ 2 + C 8000 * sigmaSeries 3 ^ 3 - C 147 * sigmaSeries 5 ^ 2

theorem E4Z_cube_sub_E6Z_sq : E4Z ^ 3 - E6Z ^ 2 = C 144 * P144 + C 1728 * P1728 := by
  simp only [E4Z, E6Z, P144, P1728]
  have h : ∀ a : ℤ, (C a : PowerSeries ℤ) = (a : PowerSeries ℤ) := fun a => by
    simp
  simp only [h]
  push_cast
  ring

theorem twelve_dvd (d : ℕ) : (12 : ℤ) ∣ 5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5 := by
  have h : ∀ e : ZMod 12, 5 * e ^ 3 + 7 * e ^ 5 = 0 := by decide
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) 12).mp
  push_cast
  exact h _

theorem twelve_dvd_coeff_P144 (n : ℕ) : (12 : ℤ) ∣ coeff n P144 := by
  simp only [P144, map_add, coeff_C_mul, coeff_sigmaSeries]
  split_ifs with hn
  · simp
  · rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.dvd_sum fun d _ => twelve_dvd d

def deltaZ : PowerSeries ℤ :=
  PowerSeries.mk fun n => coeff n P144 / 12 + coeff n P1728

theorem C_mul_deltaZ : C 1728 * deltaZ = E4Z ^ 3 - E6Z ^ 2 := by
  rw [E4Z_cube_sub_E6Z_sq]
  ext n
  simp only [deltaZ, coeff_C_mul, coeff_mk, map_add]
  have h := Int.mul_ediv_cancel' (twelve_dvd_coeff_P144 n)
  linear_combination (144 : ℤ) * h

theorem qExpansion_discriminant_eq :
    qExpansion 1 ModularForm.discriminant =
      (1728 : ℂ)⁻¹ • (qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2) := by
  set G : ModularForm 𝒮ℒ 12 :=
    ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2) with hG
  have hGq : qExpansion 1 G = qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2 := by
    simp only [hG, ModularForm.coe_sub, coe_mcast,
      ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have hcoe : (ModularForm.discriminant : UpperHalfPlane → ℂ) = (1728 : ℂ)⁻¹ • (⇑G) := by
    ext z
    simp only [hG, Pi.smul_apply, ModularForm.coe_sub, ModularForm.coe_mcast, ModularForm.coe_pow,
      Pi.sub_apply, Pi.pow_apply, smul_eq_mul, discriminant_eq_E₄_cube_sub_E₆_sq z]
    ring
  rw [hcoe, UpperHalfPlane.qExpansion_smul
    (ModularFormClass.analyticAt_cuspFunction_zero G one_pos one_mem_strictPeriods_SL), hGq]

theorem discriminant_qExpansion_coeff_eq_intCast (n : ℕ) :
    (qExpansion 1 ModularForm.discriminant).coeff n = ((coeff n deltaZ : ℤ) : ℂ) := by
  rw [qExpansion_discriminant_eq, qExpansion_E₄_eq_map, qExpansion_E₆_eq_map, ← map_pow, ← map_pow,
    ← map_sub, ← C_mul_deltaZ, map_mul, PowerSeries.map_C, map_smul, coeff_C_mul, coeff_map,
    smul_eq_mul, eq_intCast, eq_intCast]
  push_cast
  ring

theorem exists_int_discriminant_qExpansion_coeff (n : ℕ) :
    ∃ z : ℤ, (qExpansion 1 ModularForm.discriminant).coeff n = (z : ℂ) :=
  ⟨_, discriminant_qExpansion_coeff_eq_intCast n⟩

theorem discriminant_qExpansion_coeff_zero : (qExpansion 1 ModularForm.discriminant).coeff 0 = 0 := by
  simpa using CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL

theorem coeff_zero_deltaZ : coeff 0 deltaZ = 0 := by
  have h := discriminant_qExpansion_coeff_eq_intCast 0
  rw [discriminant_qExpansion_coeff_zero] at h
  exact_mod_cast h.symm

theorem coeff_one_deltaZ : coeff 1 deltaZ = 1 := by
  have h := discriminant_qExpansion_coeff_eq_intCast 1
  rw [discriminant_qExpansion_coeff_one] at h
  exact_mod_cast h.symm

end DeltaQExpInt

namespace INTINF

open Complex UpperHalfPlane PowerSeries Filter Topology

local notation "𝕢" => Function.Periodic.qParam

def EvA (S : PowerSeries ℂ) (q v : ℂ) : Prop :=
  HasSum (fun n : ℕ => coeff n S * q ^ n) v ∧ Summable fun n : ℕ => ‖coeff n S * q ^ n‖

theorem EvA.mul {S T : PowerSeries ℂ} {q v w : ℂ} (hS : EvA S q v) (hT : EvA T q w) :
    EvA (S * T) q (v * w) := by
  have key : ∀ n : ℕ, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (coeff kl.1 S * q ^ kl.1) * (coeff kl.2 T * q ^ kl.2) = coeff n (S * T) * q ^ n := by
    intro n
    rw [coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    rw [← hkl, pow_add]
    ring
  have hsum := summable_norm_sum_mul_antidiagonal_of_summable_norm hS.2 hT.2
  refine ⟨?_, by simpa only [key] using hsum⟩
  have h1 := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hS.2 hT.2
  rw [hS.1.tsum_eq, hT.1.tsum_eq] at h1
  have h3 := hsum.of_norm.hasSum
  rw [← h1] at h3
  simpa only [key] using h3

theorem EvA_X_pow (q : ℂ) (k : ℕ) : EvA (X ^ k) q (q ^ k) := by
  have hf : (fun n : ℕ => coeff n ((X : PowerSeries ℂ) ^ k) * q ^ n) =
      fun n => if n = k then q ^ k else 0 := by
    funext n
    rw [coeff_X_pow]
    split_ifs with h
    · rw [h, one_mul]
    · rw [zero_mul]
  have hg : (fun n : ℕ => ‖coeff n ((X : PowerSeries ℂ) ^ k) * q ^ n‖) =
      fun n => if n = k then ‖q ^ k‖ else 0 := by
    funext n
    rw [congrFun hf n]
    split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · rw [hf]; exact hasSum_ite_eq k (q ^ k)
  · rw [hg]; exact (hasSum_ite_eq k ‖q ^ k‖).summable

theorem EvA_one (q : ℂ) : EvA 1 q 1 := by
  simpa using EvA_X_pow q 0

theorem EvA.pow {S : PowerSeries ℂ} {q v : ℂ} (hS : EvA S q v) : ∀ n : ℕ, EvA (S ^ n) q (v ^ n)
  | 0 => by simpa using EvA_one q
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact (EvA.pow hS n).mul hS

theorem EvA.smul {S : PowerSeries ℂ} {q v : ℂ} (hS : EvA S q v) (c : ℂ) :
    EvA (c • S) q (c * v) := by
  refine ⟨?_, ?_⟩
  · have := hS.1.mul_left c
    simpa only [coeff_smul, smul_eq_mul, mul_assoc] using this
  · have := hS.2.mul_left ‖c‖
    refine this.congr fun n => ?_
    simp only [coeff_smul, smul_eq_mul, norm_mul, mul_assoc]

theorem EvA_of_forall_hasSum {S : PowerSeries ℂ} {F : ℍ → ℂ} {h : ℝ} (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun n : ℕ => coeff n S * 𝕢 h τ ^ n) (F τ)) (τ : ℍ) :
    EvA S (𝕢 h τ) (F τ) := by
  refine ⟨hF τ, ?_⟩

  let τ' : ℍ := ⟨(τ : ℂ) / 2, by rw [Complex.div_ofNat_im]; exact half_pos τ.im_pos⟩
  have hq : 𝕢 h τ = 𝕢 h τ' ^ 2 := by
    simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    change 2 * ↑Real.pi * Complex.I * (τ : ℂ) / h =
      ((2 : ℕ) : ℂ) * (2 * ↑Real.pi * Complex.I * ((τ : ℂ) / 2) / h)
    push_cast
    ring
  obtain ⟨M, hM⟩ := (hF τ').summable.tendsto_atTop_zero.norm.bddAbove_range
  have hM' : ∀ n, ‖coeff n S * 𝕢 h τ' ^ n‖ ≤ M := fun n => hM ⟨n, rfl⟩
  have hr : ‖𝕢 h τ'‖ < 1 := by
    rw [Function.Periodic.norm_qParam, Real.exp_lt_one_iff]
    have : 0 < 2 * Real.pi * (τ' : ℂ).im / h := by
      have := τ'.im_pos
      rw [UpperHalfPlane.im] at this
      positivity
    have e : -2 * Real.pi * (τ' : ℂ).im / h = -(2 * Real.pi * (τ' : ℂ).im / h) := by ring
    rw [e]
    linarith
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg _) hr).mul_left M)
  rw [hq, ← pow_mul, mul_comm 2 n, pow_mul, sq, ← mul_assoc, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hM' n) (pow_nonneg (norm_nonneg _) n)

theorem qParam_natCast_pow (N : ℕ) (τ : ℍ) (n : ℕ) :
    𝕢 (N : ℝ) τ ^ n = cexp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ) / (N : ℂ)) := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem qParam_natCast_zpow (N : ℕ) (τ : ℍ) (z : ℤ) :
    𝕢 (N : ℝ) τ ^ z = cexp (2 * Real.pi * Complex.I * (z : ℂ) * (τ : ℂ) / (N : ℂ)) := by
  rw [Function.Periodic.qParam, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := by
  simp [CongruenceSubgroup.Gamma1_mem, ModularGroup.T]

theorem strictPeriods_Gamma1 (N : ℕ) :
    ((CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ))).strictPeriods =
      AddSubgroup.zmultiples 1 :=
  Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 N)

theorem one_mem_strictPeriods_Gamma1 (N : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

theorem natCast_mem_strictPeriods_Gamma1 (N n : ℕ) :
    (n : ℝ) ∈ ((CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [strictPeriods_Gamma1]
  exact ⟨n, by simp⟩

def deltaN (N : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun i => if N ∣ i then ((coeff (i / N + 1) DeltaQExpInt.deltaZ : ℤ) : ℂ) else 0

theorem coeff_deltaN (N i : ℕ) :
    coeff i (deltaN N) = if N ∣ i then ((coeff (i / N + 1) DeltaQExpInt.deltaZ : ℤ) : ℂ) else 0 := by
  rw [deltaN, coeff_mk]

theorem constantCoeff_deltaN (N : ℕ) : constantCoeff (deltaN N) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_deltaN, if_pos (dvd_zero N), Nat.zero_div, zero_add,
    DeltaQExpInt.coeff_one_deltaZ, Int.cast_one]

theorem qParam_one_eq_pow (N : ℕ) [NeZero N] (τ : ℍ) : 𝕢 1 τ = 𝕢 (N : ℝ) τ ^ N := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  push_cast
  field_simp

theorem hasSum_discriminant (τ : ℍ) :
    HasSum (fun n : ℕ => ((coeff n DeltaQExpInt.deltaZ : ℤ) : ℂ) * 𝕢 1 τ ^ n)
      (ModularForm.discriminant τ) := by
  have h := UpperHalfPlane.hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex (f := CuspForm.discriminant)
      one_mem_strictPeriods_SL)
    (ModularFormClass.holo CuspForm.discriminant) (ModularFormClass.bdd_at_infty CuspForm.discriminant) τ
  refine (h.congr_fun fun n => ?_ :)
  · rw [CuspForm.coe_discriminant, DeltaQExpInt.discriminant_qExpansion_coeff_eq_intCast, smul_eq_mul]

theorem EvA_deltaN (N : ℕ) [NeZero N] (τ : ℍ) :
    EvA (deltaN N) (𝕢 (N : ℝ) τ) (ModularForm.discriminant τ / 𝕢 (N : ℝ) τ ^ N) := by
  have hN : 0 < N := NeZero.pos N
  refine EvA_of_forall_hasSum (F := fun τ : ℍ => ModularForm.discriminant τ / 𝕢 (N : ℝ) τ ^ N)
    (Nat.cast_pos.mpr hN) (fun τ => ?_) τ
  set q := 𝕢 (N : ℝ) τ with hqdef
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _

  have h1 := hasSum_discriminant τ
  rw [qParam_one_eq_pow N τ, ← hqdef] at h1
  have h2 := (hasSum_nat_add_iff' 1).mpr h1
  rw [Finset.sum_range_one, pow_zero, mul_one, DeltaQExpInt.coeff_zero_deltaZ, Int.cast_zero,
    sub_zero] at h2
  have h3 : HasSum (fun j : ℕ => ((coeff (j + 1) DeltaQExpInt.deltaZ : ℤ) : ℂ) * q ^ (N * j))
      (ModularForm.discriminant τ / q ^ N) := by
    have e : (fun j : ℕ => ((coeff (j + 1) DeltaQExpInt.deltaZ : ℤ) : ℂ) * q ^ (N * j)) =
        fun j : ℕ => ((coeff (j + 1) DeltaQExpInt.deltaZ : ℤ) : ℂ) * (q ^ N) ^ (j + 1) / q ^ N := by
      funext j
      rw [pow_succ, ← mul_assoc, mul_div_assoc, div_self (pow_ne_zero _ hq0), mul_one, ← pow_mul]
    rw [e]
    exact h2.div_const (q ^ N)

  have hinj : Function.Injective fun j : ℕ => N * j := fun a b hab => Nat.eq_of_mul_eq_mul_left hN hab
  refine (hinj.hasSum_iff ?_).mp ?_
  · intro i hi
    rw [coeff_deltaN, if_neg, zero_mul]
    rintro ⟨j, rfl⟩
    exact hi ⟨j, rfl⟩
  · have e : ((fun i : ℕ => coeff i (deltaN N) * q ^ i) ∘ fun j : ℕ => N * j) =
        fun j : ℕ => ((coeff (j + 1) DeltaQExpInt.deltaZ : ℤ) : ℂ) * q ^ (N * j) := by
      funext j
      simp only [Function.comp_apply, coeff_deltaN, if_pos (dvd_mul_right N j),
        Nat.mul_div_cancel_left j hN]
    rw [e]
    exact h3

def CoeffMem (A : Subalgebra ℤ ℂ) (S : PowerSeries ℂ) : Prop := ∀ n : ℕ, coeff n S ∈ A

theorem CoeffMem.mul {A : Subalgebra ℤ ℂ} {S T : PowerSeries ℂ} (hS : CoeffMem A S)
    (hT : CoeffMem A T) : CoeffMem A (S * T) := fun n => by
  rw [coeff_mul]
  exact Subalgebra.sum_mem _ fun kl _ => Subalgebra.mul_mem _ (hS _) (hT _)

theorem CoeffMem_X_pow (A : Subalgebra ℤ ℂ) (k : ℕ) : CoeffMem A (X ^ k) := fun n => by
  rw [coeff_X_pow]
  split_ifs
  exacts [one_mem _, zero_mem _]

theorem CoeffMem.pow {A : Subalgebra ℤ ℂ} {S : PowerSeries ℂ} (hS : CoeffMem A S) :
    ∀ n : ℕ, CoeffMem A (S ^ n)
  | 0 => by simpa using CoeffMem_X_pow A 0
  | n + 1 => by
    rw [pow_succ]
    exact (CoeffMem.pow hS n).mul hS

theorem CoeffMem.smul {A : Subalgebra ℤ ℂ} {S : PowerSeries ℂ} (hS : CoeffMem A S) {c : ℂ}
    (hc : c ∈ A) : CoeffMem A (c • S) := fun n => by
  rw [coeff_smul, smul_eq_mul]
  exact mul_mem hc (hS n)

theorem isIntegral_natCast (n : ℕ) : IsIntegral ℤ (n : ℂ) := by
  have := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (n : ℤ))
  simpa using this

end INTINF

open scoped MatrixGroups ModularForm in
theorem solution
    (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (hm0 : m 0 0 = 0) (t : ℕ)
    (ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 * (t : ℤ)))
    (hϑ : ∀ τ : UpperHalfPlane, ϑ τ =
      (∏ r : ZMod N, ∏ s : ZMod N,
          ModularCurve.siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)) *
        ModularForm.discriminant τ ^ t)
    (m₀ : ℕ)
    (hm₀ : (N : ℤ) * m₀ =
      (∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
        (6 * (r.val : ℤ) ^ 2
          - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) + (N : ℤ) * t) :
    ∃ a : ℕ,
      (∀ n : ℕ, n < m₀ → (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n = 0) ∧
      (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀ ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ a *
        ((UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀)⁻¹) ∧
      ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a *
        (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n) := by
  classical

  obtain ⟨C, d, hCN, hdint, -, hd0ne, hd0inv, hsum, -⟩ :=
    ModularCurve.SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow N m hm0
  set Ord : ℤ := ∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
      (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2) with hOrd
  have hNpos : 0 < N := NeZero.pos N
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hC0 : C ≠ 0 := by
    rintro rfl
    rw [zero_pow hNpos.ne'] at hCN
    exact zero_ne_one hCN
  have hCint : IsIntegral ℤ C := IsIntegral.of_pow hNpos (by rw [hCN]; exact isIntegral_one)

  let D : PowerSeries ℂ := PowerSeries.mk d
  let T : PowerSeries ℂ := C • (PowerSeries.X ^ (N * m₀) * (D * INTINF.deltaN N ^ t))
  have hT : ∀ τ : UpperHalfPlane,
      HasSum (fun k : ℕ => PowerSeries.coeff k T • Function.Periodic.qParam (N : ℝ) τ ^ k) (ϑ τ) := by
    intro τ
    set q := Function.Periodic.qParam (N : ℝ) τ with hqdef
    have hq0 : q ≠ 0 := Complex.exp_ne_zero _
    set u : UpperHalfPlane → ℂ := fun τ => ∏ r : ZMod N, ∏ s : ZMod N,
        ModularCurve.siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s) with hu
    set e : UpperHalfPlane → ℂ := fun τ =>
        Complex.exp (2 * Real.pi * Complex.I * (Ord : ℂ) * (τ : ℂ) / (N : ℂ)) with he
    have hD : INTINF.EvA D q (u τ / (C * e τ)) := by
      refine INTINF.EvA_of_forall_hasSum (S := D) (F := fun τ => u τ / (C * e τ)) hNR (fun τ' => ?_) τ
      have h' := hsum τ'
      simp only [D, PowerSeries.coeff_mk, INTINF.qParam_natCast_pow]
      convert h' using 3
      simp only [he, hOrd]
      push_cast
      ring
    have hall := ((INTINF.EvA_X_pow q (N * m₀)).mul (hD.mul ((INTINF.EvA_deltaN N τ).pow t))).smul C
    have he' : e τ * q ^ (N * t) = q ^ (N * m₀) := by
      have h1 : e τ = q ^ Ord := by
        rw [he, hqdef, INTINF.qParam_natCast_zpow]
      have h2 : (Ord : ℤ) + ((N * t : ℕ) : ℤ) = ((N * m₀ : ℕ) : ℤ) := by push_cast; linarith
      rw [h1, ← zpow_natCast, ← zpow_add₀ hq0, h2, zpow_natCast]
    have he0 : e τ ≠ 0 := Complex.exp_ne_zero _
    have hval : C * (q ^ (N * m₀) * (u τ / (C * e τ) * (ModularForm.discriminant τ / q ^ N) ^ t)) =
        ϑ τ := by
      rw [hϑ τ]
      change _ = u τ * ModularForm.discriminant τ ^ t
      rw [div_pow, ← pow_mul, ← he']
      field_simp
    rw [← hval]
    simpa only [smul_eq_mul] using hall.1

  have hcoefN : ∀ k : ℕ, PowerSeries.coeff k T =
      (UpperHalfPlane.qExpansion (N : ℝ) (⇑ϑ : UpperHalfPlane → ℂ)).coeff k := fun k =>
    ModularFormClass.qExpansion_coeff_unique hNR (INTINF.natCast_mem_strictPeriods_Gamma1 N N) hT k
  have hper : Function.Periodic ((⇑ϑ : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex (f := ϑ) (INTINF.one_mem_strictPeriods_Gamma1 N)
  haveI : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (INTINF.one_mem_strictPeriods_Gamma1 N)⟩
  have hcoef1 : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n =
      PowerSeries.coeff (N * n) T := fun n => by
    have h := UpperHalfPlane.qExpansion_coeff_mul_width (⇑ϑ) 1 one_pos hper (ModularFormClass.holo ϑ)
      (ModularFormClass.bdd_at_infty ϑ) N hNpos (N * n)
    rw [mul_one, if_pos (dvd_mul_right N n), Nat.mul_div_cancel_left n hNpos] at h
    rw [← h, hcoefN]

  have hTcoef : ∀ k : ℕ, PowerSeries.coeff k T =
      C * if N * m₀ ≤ k then PowerSeries.coeff (k - N * m₀) (D * INTINF.deltaN N ^ t) else 0 := by
    intro k
    simp only [T, PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_X_pow_mul']
  have hT0 : PowerSeries.coeff (N * m₀) T = C * d 0 := by
    rw [hTcoef, if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      map_pow, INTINF.constantCoeff_deltaN, one_pow, mul_one,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  have hTmem : INTINF.CoeffMem (integralClosure ℤ ℂ) T := by
    refine INTINF.CoeffMem.smul ((INTINF.CoeffMem_X_pow _ _).mul
      (INTINF.CoeffMem.mul (fun n => ?_) (INTINF.CoeffMem.pow (fun i => ?_) t)))
      ((mem_integralClosure_iff ℤ ℂ).mpr hCint)
    · rw [PowerSeries.coeff_mk]
      exact (mem_integralClosure_iff ℤ ℂ).mpr (hdint n)
    · rw [INTINF.coeff_deltaN]
      split_ifs
      exacts [intCast_mem _ _, zero_mem _]
  refine ⟨12 * N * ∑ r : ZMod N, ∑ s : ZMod N, m r s, fun n hn => ?_, ?_, ?_, fun n => ?_⟩
  · rw [hcoef1, hTcoef, if_neg (not_le.mpr (Nat.mul_lt_mul_left hNpos |>.mpr hn)), mul_zero]
  · rw [hcoef1, hT0]
    exact mul_ne_zero hC0 hd0ne
  · rw [hcoef1, hT0]
    have hCinv : C⁻¹ = C ^ (N - 1) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', Nat.sub_add_cancel hNpos, hCN]
    rw [mul_inv, hCinv, show (N : ℂ) ^ (12 * N * ∑ r : ZMod N, ∑ s : ZMod N, m r s) *
        (C ^ (N - 1) * (d 0)⁻¹) = C ^ (N - 1) *
        ((N : ℂ) ^ (12 * N * ∑ r : ZMod N, ∑ s : ZMod N, m r s) * (d 0)⁻¹) by ring]
    exact (hCint.pow _).mul hd0inv
  · rw [hcoef1]
    exact ((INTINF.isIntegral_natCast N).pow _).mul ((mem_integralClosure_iff ℤ ℂ).mp (hTmem _))

end

end S_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
end P2MW
export P2MW.S_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow (solution)
