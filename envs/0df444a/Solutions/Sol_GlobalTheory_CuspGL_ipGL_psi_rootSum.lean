-- Prove2me | solution 1 for GlobalTheory.CuspGL.ipGL_psi_rootSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:13:19.345906+00:00
-- url     : https://prove2.me/submissions/5691a951-b5a0-4c9e-b47c-072765652cd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumEqTorusSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMobiusInverseMonicEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharacterAdditiveAndXSubOnePowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusMinpolyDegreeRootPowerSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusCharacterOrthogonalityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumMobius
import Theorems.Thm_GlobalTheory_CuspGL_IsAdditive_map_pow_monic
import Theorems.Thm_GlobalTheory_T_additive_eq_polynomialVonMangoldt_convolution_one
import Theorems.Thm_GlobalTheory_T_endomorphismMass_mobiusInverse_monic_eq
import Theorems.Thm_GlobalTheory_T_frobeniusTorus_character_orthogonality
import Theorems.Thm_GlobalTheory_T_frobeniusTorus_minpoly_degree_rootPowerSum
import Theorems.Thm_GlobalTheory_T_invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj
import Theorems.Thm_GlobalTheory_T_invertibleEndInnerProduct_rootPowerSum_eq_torusSum
import Theorems.Thm_GlobalTheory_T_isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse
import Theorems.Thm_GlobalTheory_T_rootPowerSumCharacter_additive_and_X_sub_one_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (hn : 0 < Module.finrank F V)
    (k l : ℕ) :
    ipGL (psi (rootSum θ k) V) (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) =
      glCard F (Module.finrank F V) * (((Finset.range (Module.finrank F V)).filter
        (fun i => k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ Module.finrank F V - 1)])).card : ℂ) := by
  classical
  set n := Module.finrank F V with hn_def
  set q := Nat.card F with hq_def
  have hq : 1 < q := Finite.one_lt_card
  have hN : 0 < q ^ n - 1 := by
    have : 1 < q ^ n := Nat.one_lt_pow hn.ne' hq
    omega
  obtain ⟨hadd, -⟩ := GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k
  have hclass : IsClassFn (psi (rootSum θ k) V) := fun e g => GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj F _ V V e g
  have hprim := GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V _ hadd
  rw [GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_eq_torusSum F V θ _ hclass hprim hn l]

  have hS : {α : AlgebraicClosure F | α ^ (q ^ n - 1) = 1} =
      ↑((nthRoots (q ^ n - 1) (1 : AlgebraicClosure F)).toFinset) := by
    ext α
    simp [Polynomial.mem_nthRoots hN]
  rw [hS, finsum_mem_coe_finset]

  have key : ∀ α ∈ (nthRoots (q ^ n - 1) (1 : AlgebraicClosure F)).toFinset,
      ((n / (minpoly F α).natDegree : ℕ) : ℂ) *
          mass (psi (rootSum θ k) V) (minpoly F α ^ (n / (minpoly F α).natDegree)) * star (θ α ^ l) =
        glCard F n / ((q : ℂ) ^ n - 1) * ∑ i ∈ Finset.range n, θ α ^ (k * q ^ i) * star (θ α ^ l) := by
    intro α hα
    have hα' : α ∈ {α : AlgebraicClosure F | α ^ (q ^ n - 1) = 1} := by
      rw [hS]; exact hα
    obtain ⟨hdvd, -, hroot⟩ := GlobalTheory.T.frobeniusTorus_minpoly_degree_rootPowerSum F θ n hn α hα'
    have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
    have hmon : (minpoly F α).Monic := minpoly.monic hint
    have hirr : Irreducible (minpoly F α) := minpoly.irreducible hint
    have hd : 0 < (minpoly F α).natDegree := minpoly.natDegree_pos hint
    have hm : 0 < n / (minpoly F α).natDegree := Nat.div_pos (Nat.le_of_dvd hn hdvd) hd
    have hdeg : (minpoly F α ^ (n / (minpoly F α).natDegree)).natDegree = n := by
      rw [hmon.natDegree_pow]
      exact Nat.div_mul_cancel hdvd
    rw [GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq F V _ hadd _ (hmon.pow _) hdeg, hdeg,
      (GlobalTheory.T.additive_eq_polynomialVonMangoldt_convolution_one F _ hadd).2.1 _ _ hmon hirr hm]
    have h1 : ((n / (minpoly F α).natDegree : ℕ) : ℂ) * rootSum θ k (minpoly F α) =
        ∑ i ∈ Finset.range n, θ α ^ (k * q ^ i) := by
      rw [← IsAdditive.map_pow_monic hadd hmon, hroot]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_pow, ← pow_mul, Nat.mul_comm]
    rw [← Finset.sum_mul, ← h1]
    ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, Finset.sum_comm]

  have h2 : ∀ i, ∑ α ∈ (nthRoots (q ^ n - 1) (1 : AlgebraicClosure F)).toFinset,
      θ α ^ (k * q ^ i) * star (θ α ^ l) =
        if k * q ^ i ≡ l [MOD q ^ n - 1] then ((q ^ n - 1 : ℕ) : ℂ) else 0 := by
    intro i
    rw [← finsum_mem_coe_finset, ← hS]
    exact (GlobalTheory.T.frobeniusTorus_character_orthogonality F θ hθ n hn).2 _ _
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  have hc : ((q ^ n - 1 : ℕ) : ℂ) = (q : ℂ) ^ n - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hne : (q : ℂ) ^ n - 1 ≠ 0 := by
    rw [← hc]
    exact_mod_cast hN.ne'
  rw [hc]
  field_simp
end GlobalTheory.CuspGL
