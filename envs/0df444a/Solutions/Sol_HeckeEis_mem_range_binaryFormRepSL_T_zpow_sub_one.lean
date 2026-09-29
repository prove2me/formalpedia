-- Prove2me | solution 1 for HeckeEis.mem_range_binaryFormRepSL_T_zpow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/048befd3-7b83-5bd2-b092-84834929790f

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one

set_option autoImplicit false

open scoped MatrixGroups

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binarySubst_X binaryFormRepSL binaryFormRepSL_apply_coe"
namespace RangeTzpowSol
p2m_open "HeckeEis"

open MvPolynomial
open scoped MatrixGroups

variable (K : Type*) [CommRing K] (n : ℕ)

theorem X_pow_mul_X_pow_mem {a b : ℕ} (h : a + b = n) :
    (X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 2) K) ∈ BinaryForm K n := by
  rw [mem_homogeneousSubmodule]
  have := ((isHomogeneous_X K (0 : Fin 2)).pow a).mul ((isHomogeneous_X K (1 : Fin 2)).pow b)
  convert this using 1
  omega

noncomputable def mono (b : ℕ) : ↥(BinaryForm K n) :=
  if hb : b ≤ n then ⟨X 0 ^ (n - b) * X 1 ^ b, X_pow_mul_X_pow_mem K n (by omega)⟩ else 0

theorem coe_mono {b : ℕ} (hb : b ≤ n) : (mono K n b : MvPolynomial (Fin 2) K) = X 0 ^ (n - b) * X 1 ^ b := by
  rw [mono, dif_pos hb]

theorem binaryFormRepSL_T_zpow_mono (h : ℤ) {b : ℕ} (hb : b ≤ n) :
    binaryFormRepSL K n (ModularGroup.T ^ h) (mono K n b)
      = ∑ i ∈ Finset.range (b + 1), ((b.choose i : K) * (h : K) ^ (b - i)) • mono K n i := by
  apply Subtype.ext
  rw [binaryFormRepSL_apply_coe, coe_mono K n hb, Submodule.coe_sum, map_mul, map_pow, map_pow, binarySubst_X,
    binarySubst_X, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [ModularGroup.coe_T_zpow, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val', Int.cast_one, Int.cast_zero, map_one, map_zero, one_mul, zero_mul,
    add_zero]
  rw [add_comm (C (h : K) * X 0) (X 1), add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Submodule.coe_smul, coe_mono K n (by omega : i ≤ n), smul_eq_C_mul, mul_pow, ← C_pow,
    show n - i = (n - b) + (b - i) by omega, pow_add, map_mul, map_natCast]
  ring

variable {K : Type*} [Field K] [CharZero K]

theorem mono_mem_range_T_zpow_sub_one (n : ℕ) {h : ℤ} (hh : h ≠ 0) :
    ∀ b < n, mono K n b ∈ LinearMap.range (binaryFormRepSL K n (ModularGroup.T ^ h) - 1) := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb
    have hexp := binaryFormRepSL_T_zpow_mono K n h (b := b + 1) (by omega)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, one_mul,
      one_smul, Nat.choose_succ_self_right, Nat.add_sub_cancel_left, pow_one] at hexp
    have hmem : (binaryFormRepSL K n (ModularGroup.T ^ h) - 1) (mono K n (b + 1))
        ∈ LinearMap.range (binaryFormRepSL K n (ModularGroup.T ^ h) - 1) := LinearMap.mem_range_self _ _
    rw [LinearMap.sub_apply, Module.End.one_apply, hexp, add_sub_cancel_right] at hmem
    have hsum : ∑ i ∈ Finset.range b, (((b + 1).choose i : K) * (h : K) ^ (b + 1 - i)) • mono K n i
        ∈ LinearMap.range (binaryFormRepSL K n (ModularGroup.T ^ h) - 1) :=
      Submodule.sum_mem _ fun i hi => by
        have hib := Finset.mem_range.mp hi
        exact Submodule.smul_mem _ _ (ih i hib (by omega))
    have hcb : (((b + 1 : ℕ) : K) * (h : K)) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero b)) (Int.cast_ne_zero.mpr hh)
    have key := Submodule.sub_mem _ hmem hsum
    rw [add_sub_cancel_left] at key
    exact (Submodule.smul_mem_iff _ hcb).mp key

end HeckeEis.RangeTzpowSol

open _root_.HeckeEis _root_.P2MW.S_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one.HeckeEis HeckeEis.RangeTzpowSol MvPolynomial in
theorem solution {K : Type*} [Field K] [CharZero K] (n : ℕ) {h : ℤ}
    (hh : h ≠ 0) (P : ↥(HeckeEis.BinaryForm K n))
    (hP : MvPolynomial.coeff (Finsupp.single 1 n) (P : MvPolynomial (Fin 2) K) = 0) :
    P ∈ LinearMap.range (HeckeEis.binaryFormRepSL K n (ModularGroup.T ^ h) - 1) := by
  classical
  have hhom : (P : MvPolynomial (Fin 2) K).IsHomogeneous n := (mem_homogeneousSubmodule n _).mp P.2
  have hdeg : ∀ d ∈ (P : MvPolynomial (Fin 2) K).support, d 0 + d 1 = n ∧ d 1 < n := by
    intro d hd
    have hne := mem_support_iff.mp hd
    have hdn : d.degree = n := by
      by_contra hc
      exact hne (hhom.coeff_eq_zero hc)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdn
    refine ⟨hdn, lt_of_le_of_ne (by omega) fun h1 => hne ?_⟩
    have : d = Finsupp.single 1 n := by
      ext i
      fin_cases i
      · simp
        omega
      · simpa using h1
    rw [this]
    exact hP
  have hrepr : P = ∑ d ∈ (P : MvPolynomial (Fin 2) K).support,
      MvPolynomial.coeff d (P : MvPolynomial (Fin 2) K) • mono K n (d 1) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    conv_lhs => rw [(P : MvPolynomial (Fin 2) K).as_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    obtain ⟨hdn, hd1⟩ := hdeg d hd
    rw [Submodule.coe_smul, coe_mono K n hd1.le, monomial_eq, smul_eq_C_mul,
      Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two, show n - d 1 = d 0 by omega]
  rw [hrepr]
  exact Submodule.sum_mem _ fun d hd => Submodule.smul_mem _ _ (mono_mem_range_T_zpow_sub_one n hh _ (hdeg d hd).2)

end

end S_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one
end P2MW
export P2MW.S_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one (solution)
