-- Prove2me | solution 1 for GlobalTheory.CuspGL.eq_zero_of_ipGL_rootSum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:19:48.251126+00:00
-- url     : https://prove2.me/submissions/a42b4058-cfb9-4a34-835a-7513a0068d8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumMobiusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumEqTorusSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveEndClassFunctionZeroOfCharpolyMassZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharacterAdditiveAndXSubOnePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfFinsumMulStarPowEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveClassFunctionExpansionRootSums
import Theorems.Thm_GlobalTheory_CuspGL_exists_minpoly_eq_of_irreducible
import Theorems.Thm_GlobalTheory_CuspGL_torus_fourier_injective
import Theorems.Thm_GlobalTheory_T_classFn_eq_zero_of_charpoly_not_irreducible_pow
import Theorems.Thm_GlobalTheory_T_invertibleEndInnerProduct_rootPowerSum_eq_torusSum
import Theorems.Thm_GlobalTheory_T_primitiveEndClassFunction_zero_of_charpoly_mass_zero


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
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (φ : Module.End F V → ℂ)
    (hc : IsClassFn φ) (hp : IsPrimitive φ) (hn : 0 < Module.finrank F V)
    (h : ∀ l, ipGL φ (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) = 0)
    (g : Module.End F V) (hg : IsUnit g) : φ g = 0 := by
  have hc0 := torus_fourier_injective F θ hθ (Module.finrank F V) hn
    (fun α => ((Module.finrank F V / (minpoly F α).natDegree : ℕ) : ℂ) *
      mass φ (minpoly F α ^ (Module.finrank F V / (minpoly F α).natDegree)))
    (fun l => by rw [← GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_eq_torusSum F V θ φ hc hp hn l]; exact h l)
  by_cases hex : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ LinearMap.charpoly g = f ^ m
  swap
  · exact GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow F V φ hc hp hn g hex
  obtain ⟨f, m, hfm, hfi, hm, hcp⟩ := hex
  apply GlobalTheory.T.primitiveEndClassFunction_zero_of_charpoly_mass_zero F V φ hc hp g
  have hdeg : f.natDegree * m = Module.finrank F V := by
    have := LinearMap.charpoly_natDegree g
    rw [hcp, natDegree_pow] at this
    rw [mul_comm]; exact this
  have hfdeg : 0 < f.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hfi)
  have h0 : f.coeff 0 ≠ 0 := by
    intro h0
    have hc0' : (LinearMap.charpoly g).coeff 0 = 0 := by
      rw [hcp, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, h0, zero_pow hm.ne']
    have hdet := LinearMap.det_eq_sign_charpoly_coeff g
    rw [hc0', mul_zero] at hdet
    have hu : IsUnit (LinearMap.det g) := LinearMap.isUnit_iff_isUnit_det g |>.mp hg
    rw [hdet] at hu
    exact not_isUnit_zero hu
  obtain ⟨α, hα1, hαmin⟩ := exists_minpoly_eq_of_irreducible F f hfm hfi h0 m
  rw [hdeg] at hα1
  have hcα := hc0 α hα1
  simp only [hαmin] at hcα
  have hdiv : Module.finrank F V / f.natDegree = m := by
    rw [← hdeg]; exact Nat.mul_div_cancel_left m hfdeg
  rw [hdiv] at hcα
  rw [hcp]
  exact (mul_eq_zero.mp hcα).resolve_left (Nat.cast_ne_zero.mpr hm.ne')
end GlobalTheory.CuspGL
