-- Prove2me | solution 1 for GlobalTheory.BrauerZero.mem_degreeOneDiff_of_forall_centralByPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:26:42.093348+00:00
-- url     : https://prove2.me/submissions/807c3d68-b1d0-49a6-bcdb-997c0307209d

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__BrauerDegreeZero_fefd58e19a2fa426
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInductionIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersIffSubCharacters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleCharacterLinearOrInducedAbelianByPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IndMulClassFunEqIndMulRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemClosureInducedCentralByPrimePower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndApplyOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionFromSubgroupTransStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionMemInducedDegreeOneCharDiffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedOneSubIndexMemDegreeOneCharacterDiffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLtCommutatorMemOfNeTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BrauerDegreeZero
import Theorems.Thm_GlobalTheory_BI_ind_mul_classFun_eq_ind_mul_restrict
import Theorems.Thm_GlobalTheory_BI_one_mem_closure_ind_centralByPrime


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BrauerZero
namespace GlobalTheory.BrauerZero
theorem _root_.solution (G : Type) [Group G] [Finite G] (f : G → ℂ)
    (hf : ∀ g x : G, f (x⁻¹ * g * x) = f g)
    (h : ∀ E : Subgroup G, (∃ l : ℕ, l.Prime ∧ ∀ y : E, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center E) →
      ∀ ψ ∈ Virt ℂ ℂ E, ind E (fun e => ψ e * f e) ∈ D0 G) : f ∈ D0 G := by
  have key : ∀ φ ∈ AddSubgroup.closure {φ : G → ℂ | ∃ (E : Subgroup G) (ψ : E → ℂ),
      (∃ l : ℕ, l.Prime ∧ ∀ y : E, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center E) ∧
        ψ ∈ Virt ℂ ℂ E ∧ φ = ind E ψ}, φ * f ∈ D0 G := by
    intro φ hφ
    induction hφ using AddSubgroup.closure_induction with
    | mem φ hφ =>
      obtain ⟨E, ψ, hl, hψ, rfl⟩ := hφ
      rw [ind_mul_classFun_eq_ind_mul_restrict G E ψ f hf]
      exact h E hl ψ hψ
    | zero => rw [zero_mul]; exact zero_mem _
    | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
    | neg a _ ha => rw [neg_mul]; exact neg_mem ha
  simpa using key 1 (one_mem_closure_ind_centralByPrime G)
end GlobalTheory.BrauerZero
