-- Prove2me | solution 1 for GlobalTheory.IrrPi.prod_mem_virt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:54:38.483444+00:00
-- url     : https://prove2.me/submissions/8d6d2163-0e06-44e2-bd11-9e031b9cd4f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingSelfIrreducibleAlgClos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_StarVirtualCharacterEqApplyInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingEqZeroOfDistinctIrredu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterIrreducibleExpansionNormSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleOfVirtualCharacterNormOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrrCharOneMulFinsumConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleCharacterOfProduct
import Theorems.Thm_GlobalTheory_BI_isChar_one
import Theorems.Thm_GlobalTheory_BI_virt_mul_comap_conj_ind_linear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.IrrPi
namespace GlobalTheory.IrrPi
theorem _root_.solution {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)]
    [∀ i, Finite (G i)] (ψ : ∀ i, G i → ℂ) (h : ∀ i, ψ i ∈ Virt ℂ ℂ (G i)) :
    (fun x : ∀ i, G i => ∏ i, ψ i (x i)) ∈ Virt ℂ ℂ (∀ i, G i) := by
  classical
  have key : ∀ s : Finset ι, (fun x : ∀ i, G i => ∏ i ∈ s, ψ i (x i)) ∈ Virt ℂ ℂ (∀ i, G i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact AddSubgroup.subset_closure (by simpa using isChar_one ℂ ℂ (∀ i, G i))
    | insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (virt_mul_comap_conj_ind_linear (∀ i, G i)).1 _
        ((virt_mul_comap_conj_ind_linear (G i)).2.1 _ (h i) _ (Pi.evalMonoidHom G i)) _ ih
  exact key _
end GlobalTheory.IrrPi
