-- Prove2me | solution 1 for GlobalTheory.BrauerZero.ind_one_sub_index_mem_degreeOneDiff_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:27:49.698673+00:00
-- url     : https://prove2.me/submissions/e819f878-e823-4e9a-a6b1-e9da7270b93b

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
import Theorems.Thm_GlobalTheory_BrauerZero_step_ind_ind
import Theorems.Thm_GlobalTheory_BrauerZero_inducedClassFunction_mem_degreeOneCharacterDiff
import Theorems.Thm_GlobalTheory_BrauerZero_step_ind_one_sub_index_of_comm
import Theorems.Thm_GlobalTheory_BrauerZero_step_exists_gt_commutators_le
import Theorems.Thm_GlobalTheory_BrauerZero_ind_const
import Theorems.Thm_GlobalTheory_BrauerZero_ind_sub
import Theorems.Thm_GlobalTheory_BrauerZero_ind_top


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
theorem _root_.solution {G : Type} [Group G] [Finite G] [Group.IsNilpotent G] :
    ∀ (n : ℕ) (K : Subgroup G), K.index ≤ n →
      ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) ∈ D0 G := by
  intro n
  induction n with
  | zero => intro K hK; have := K.index_ne_zero_of_finite; omega
  | succ n ih =>
    intro K hK
    by_cases hKt : K = ⊤
    · subst hKt
      have e : ind (⊤ : Subgroup G) (fun _ => (1 : ℂ)) = fun _ => 1 :=
        ind_top (fun _ => (1 : ℂ)) (fun _ _ => rfl)
      rw [e, Subgroup.index_top]
      simp
    · obtain ⟨A, hKA, hc⟩ := step_exists_gt_commutators_le K hKt
      have h1 : ind (K.subgroupOf A) (fun _ => (1 : ℂ)) - (fun _ => ((K.subgroupOf A).index : ℂ)) ∈ D0 A :=
        step_ind_one_sub_index_of_comm (K.subgroupOf A) (fun a b => by
          rw [Subgroup.mem_subgroupOf]; simpa using hc a a.2 b b.2)
      have h2 := inducedClassFunction_mem_degreeOneCharacterDiff A _ h1
      have hrel := Subgroup.relIndex_mul_index hKA.le
      have hlt : 1 < K.relIndex A := by
        have h0 : (K.subgroupOf A).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        have h1' : (K.subgroupOf A).index ≠ 1 := fun h =>
          hKA.not_ge (Subgroup.subgroupOf_eq_top.1 (Subgroup.index_eq_one.1 h))
        unfold Subgroup.relIndex; omega
      have hA0 : A.index ≠ 0 := A.index_ne_zero_of_finite
      have h3 := ih A (by nlinarith)
      have t := step_ind_ind K A hKA.le (fun _ => (1 : ℂ))
      have key : ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) =
          ind A (ind (K.subgroupOf A) (fun _ => (1 : ℂ)) - (fun _ => ((K.subgroupOf A).index : ℂ))) +
            ((K.subgroupOf A).index : ℤ) • (ind A (fun _ => (1 : ℂ)) - (fun _ => (A.index : ℂ))) := by
        rw [ind_sub, ← t, ← hrel]
        funext g
        have hc1 := ind_const A (((K.subgroupOf A).index : ℕ) : ℂ) g
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, hc1, zsmul_eq_mul]
        simp only [Pi.mul_apply, Pi.sub_apply, Pi.intCast_apply, Pi.natCast_apply, Int.cast_natCast]
        simp only [Subgroup.relIndex]
        push_cast
        ring
      rw [key]
      exact add_mem h2 (zsmul_mem h3 _)
end GlobalTheory.BrauerZero
