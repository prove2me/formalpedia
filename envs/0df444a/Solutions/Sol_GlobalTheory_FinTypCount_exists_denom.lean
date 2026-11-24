-- Prove2me | solution 1 for GlobalTheory.FinTypCount.exists_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:06:04.075793+00:00
-- url     : https://prove2.me/submissions/4cfd3b76-2285-44b2-b605-89cc6688f6a6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeAleph0SmoothIrreducibleUnitaryAdelic
import Theorems.Thm_GlobalTheory_FinTypCount_tmul_mem_ALint
import Theorems.Thm_GlobalTheory_FinTypCount_exists_nat_smul_int
import Theorems.Thm_GlobalTheory_FinTypCount_exists_approx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NG
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.FinTypCount
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
namespace GlobalTheory.FinTypCount
theorem _root_.solution (x : AL L) : ∃ m : ℕ, 0 < m ∧ (m : AL L) * x ∈ ALint L := by
  obtain ⟨c, y, hy, rfl⟩ := exists_approx 1 one_pos x
  obtain ⟨D, hD, o, ho⟩ := exists_nat_smul_int c
  refine ⟨D, hD, ?_⟩
  have e1 : (D : AL L) * (c ⊗ₜ[L⁺] (1 : AFplus L)) = (o : L) ⊗ₜ[L⁺] (1 : AFplus L) := by
    rw [ho, ← nsmul_eq_mul, TensorProduct.smul_tmul']
  rw [mul_add, e1, one_smul]
  exact add_mem (tmul_mem_ALint o (fun v => one_mem _)) (Subring.mul_mem _ (natCast_mem _ _) hy)
end GlobalTheory.FinTypCount
