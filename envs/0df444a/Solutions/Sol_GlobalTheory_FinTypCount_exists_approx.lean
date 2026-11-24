-- Prove2me | solution 1 for GlobalTheory.FinTypCount.exists_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:50:30.888486+00:00
-- url     : https://prove2.me/submissions/26bc7ceb-a3c0-40e2-ba53-30ca737d82e0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeAleph0SmoothIrreducibleUnitaryAdelic
import Theorems.Thm_GlobalTheory_FinTypCount_tmul_mem_ALint
import Theorems.Thm_GlobalTheory_FinTypCount_exists_nat_smul_int
import Theorems.Thm_GlobalTheory_AdLat_strong_approximation_mod_nat
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NG
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.FinTypCount
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
namespace GlobalTheory.FinTypCount
theorem _root_.solution (M : ℕ) (hM : 0 < M) (x : AL L) :
    ∃ c : L, ∃ y ∈ ALint L, x = c ⊗ₜ[L⁺] (1 : AFplus L) + M • y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x x' hx hx' =>
    obtain ⟨c, y, hy, rfl⟩ := hx
    obtain ⟨c', y', hy', rfl⟩ := hx'
    exact ⟨c + c', y + y', add_mem hy hy', by rw [TensorProduct.add_tmul, smul_add]; abel⟩
  | tmul e a =>
    obtain ⟨D, hD, o, ho⟩ := exists_nat_smul_int e
    obtain ⟨k, a', ha', rfl⟩ :=
      (GlobalTheory.AdLat.strong_approximation_mod_nat L⁺ (D * M) (Nat.mul_pos hD hM)).1 a
    refine ⟨algebraMap L⁺ L k * e, _, tmul_mem_ALint o ha', ?_⟩
    rw [TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one k, ← TensorProduct.smul_tmul,
      ← Algebra.smul_def, ho, TensorProduct.smul_tmul', TensorProduct.tmul_smul, mul_comm, mul_smul]
    simp only [TensorProduct.smul_tmul']
end GlobalTheory.FinTypCount
