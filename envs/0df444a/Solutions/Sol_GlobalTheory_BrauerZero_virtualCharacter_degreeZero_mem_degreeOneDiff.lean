-- Prove2me | solution 1 for GlobalTheory.BrauerZero.virtualCharacter_degreeZero_mem_degreeOneDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:35:00.270718+00:00
-- url     : https://prove2.me/submissions/e116a07a-38ba-4412-aec8-b36e4c1810ea

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
import Theorems.Thm_GlobalTheory_BrauerZero_inducedClassFunction_mem_degreeOneCharacterDiff
import Theorems.Thm_GlobalTheory_BrauerZero_mem_degreeOneDiff_of_forall_centralByPrime
import Theorems.Thm_GlobalTheory_BrauerZero_central_case
import Theorems.Thm_GlobalTheory_BI_virt_mul_comap_conj_ind_linear
import Theorems.Thm_GlobalTheory_BrauerZero_ind_apply_one


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
theorem _root_.solution : ∀ (n : ℕ) (G : Type) [Group G] [Finite G], Nat.card G ≤ n →
    ∀ f ∈ Virt ℂ ℂ G, f 1 = 0 → f ∈ D0 G := by
  intro n
  induction n with
  | zero => intro G _ _ hG; have := Nat.card_pos (α := G); omega
  | succ n ih =>
    intro G _ _ hG f hf hf1
    have hcl : ∀ g x : G, f (x⁻¹ * g * x) = f g := (virt_mul_comap_conj_ind_linear G).2.2.1 f hf
    refine mem_degreeOneDiff_of_forall_centralByPrime G f hcl ?_
    intro E hE ψ hψ
    have hV : (fun e : E => ψ e * f e) ∈ Virt ℂ ℂ E :=
      (virt_mul_comap_conj_ind_linear E).1 ψ hψ _
        ((virt_mul_comap_conj_ind_linear G).2.1 f hf E E.subtype)
    have h1 : (fun e : E => ψ e * f e) 1 = 0 := by simp [hf1]
    by_cases hlt : Nat.card E < Nat.card G
    · exact inducedClassFunction_mem_degreeOneCharacterDiff E _ (ih E (by omega) _ hV h1)
    · have htop : E = ⊤ := (Subgroup.card_eq_iff_eq_top E).1
        (le_antisymm (Subgroup.card_le_card_group E) (not_lt.1 hlt))
      have hVG : ind E (fun e => ψ e * f e) ∈ Virt ℂ ℂ G :=
        (virt_mul_comap_conj_ind_linear G).2.2.2.1 E _ hV
      have hG1 : ind E (fun e => ψ e * f e) 1 = 0 := by rw [ind_apply_one]; simp [hf1]
      subst htop
      obtain ⟨l, hl, hc⟩ := hE
      have hG' : ∃ l : ℕ, l.Prime ∧ ∀ y : G, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center G := by
        refine ⟨l, hl, fun y => ?_⟩
        obtain ⟨j, hj⟩ := hc ⟨y, Subgroup.mem_top y⟩
        refine ⟨j, Subgroup.mem_center_iff.2 fun z => ?_⟩
        have := Subgroup.mem_center_iff.1 hj ⟨z, Subgroup.mem_top z⟩
        simpa using congrArg Subtype.val this
      refine central_case G hG' (fun T hT g hg hg1 => ih T ?_ g hg hg1) _ hVG hG1
      have := Subgroup.card_le_card_group T
      have hne : Nat.card T ≠ Nat.card G := fun h => hT ((Subgroup.card_eq_iff_eq_top T).1 h)
      omega
end GlobalTheory.BrauerZero
