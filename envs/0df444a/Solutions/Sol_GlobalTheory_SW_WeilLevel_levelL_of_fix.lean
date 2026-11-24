-- Prove2me | solution 1 for GlobalTheory.SW.WeilLevel.levelL_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:01:39.10522+00:00
-- url     : https://prove2.me/submissions/16a494b5-6e3a-462f-b161-f1211defca9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Theorems.Thm_GlobalTheory_SW_WeilLevel_discr_mul_integral
import Theorems.Thm_GlobalTheory_SW_WeilLevel_cc_mul
import Theorems.Thm_GlobalTheory_SW_WeilLevel_cc_nat
import Theorems.Thm_GlobalTheory_SW_WeilLevel_cc_zero
import Theorems.Thm_GlobalTheory_SW_WeilLevel_cc_sum
import Theorems.Thm_GlobalTheory_SW_WeilLevel_colsIn_smul
import Theorems.Thm_GlobalTheory_SW_Base_herm_one
import Theorems.Thm_GlobalTheory_SW_Model_cc_cc
import Theorems.Thm_GlobalTheory_SW_Model_cc_integral
import Theorems.Thm_GlobalTheory_SW_Model_herm_one
import Theorems.Thm_GlobalTheory_SW_TransComp_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.WeilLevel
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ} {Λ : Lt E n}
namespace GlobalTheory.SW.WeilLevel
theorem _root_.solution (hΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) {S : ℕ}
    {ψ : Matrix (Fin n) (Fin N) E → ℂ}
    (h : ∀ d b, ColsIn Λ d → ColsIn Λ b → heisH ((S : E) • d) ((S : E) • b) ψ = ψ) :
    LevelL Λ ((NumberField.discr E).natAbs * S) ψ := by
  classical
  have h0 : ColsIn Λ (0 : Matrix (Fin n) (Fin N) E) := fun _ => Λ.zero_mem
  refine ⟨fun x hx a => (hΛ _).2 fun y hy => ?_, fun x y hy => ?_⟩
  · have key : ∀ γ : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E ((S * herm 1 y (xᵀ a)) * γ) = k := by
      intro γ
      set b : Matrix (Fin n) (Fin N) E := Matrix.of fun k a' => if a' = a then (γ : E) * y k else 0
        with hb
      have hbΛ : ColsIn Λ b := by
        intro a'
        by_cases ha : a' = a
        · have : bᵀ a' = γ • y := by ext k; simp [hb, ha]; rfl
          rw [this]; exact Λ.smul_mem _ hy
        · have : bᵀ a' = 0 := by ext k; simp [hb, ha]
          rw [this]; exact Λ.zero_mem
      have e := congrFun (h 0 b h0 hbΛ) x
      have e2 : ∑ k, ∑ a', ((S : E) • b) k a' *
          (2 * cc (x k a') - cc (((S : E) • (0 : Matrix (Fin n) (Fin N) E)) k a')) =
          (2 : ℚ) • ((S * herm 1 y (xᵀ a)) * γ) := by
        rw [Model.herm_one, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_eq_single a (fun a' _ ha => by simp [hb, ha]) (by simp)]
        simp only [hb, smul_zero, Matrix.zero_apply, cc_zero, Matrix.smul_apply, Matrix.of_apply,
          if_true, smul_eq_mul, Matrix.transpose_apply, Rat.smul_def, mul_zero]
        push_cast
        ring
      rw [heisH, e2, smul_zero, sub_zero, map_smul, mul_right_eq_self₀, or_iff_left hx,
        Complex.exp_eq_one_iff] at e
      obtain ⟨k, hk⟩ := e
      refine ⟨k, ?_⟩
      have hp : (2 * π * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
      have : ((Algebra.trace ℚ E ((S * herm 1 y (xᵀ a)) * γ) : ℚ) : ℂ) = k := by
        apply mul_right_cancel₀ hp
        rw [← hk, smul_eq_mul]; push_cast; ring
      exact_mod_cast this
    have h2 := Model.cc_integral (discr_mul_integral _ key)
    convert h2 using 1
    rw [Model.herm_one, Model.herm_one, cc_mul, cc_mul, cc_nat, cc_nat, cc_sum, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [cc_mul, Model.cc_cc, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  · have e := congrFun (h _ 0 (colsIn_smul (NumberField.discr E).natAbs hy) h0)
      (x + (((NumberField.discr E).natAbs * S : ℕ) : E) • y)
    rw [← e, heisH, smul_smul, Nat.cast_mul, mul_comm (S : E), add_sub_cancel_right]
    simp
end GlobalTheory.SW.WeilLevel
