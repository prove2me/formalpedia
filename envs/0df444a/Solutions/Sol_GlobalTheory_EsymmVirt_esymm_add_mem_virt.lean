-- Prove2me | solution 1 for GlobalTheory.EsymmVirt.esymm_add_mem_virt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:52:35.966501+00:00
-- url     : https://prove2.me/submissions/a8b6ba38-e28e-40fd-a60a-b2289adbfc9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MatrixTraceIffIsCharacterOverSubfieldComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterEsymmRootsCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MultisetPowerSumNewtonIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EsymmMemVirtualCharactersOfPowerSumEigenvalues
import Theorems.Thm_GlobalTheory_EsymmVirt_esymm_add
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
open GlobalTheory GlobalTheory.EsymmVirt
variable {G : Type} [Group G] [Finite G]
namespace GlobalTheory.EsymmVirt
theorem _root_.solution {A B : G → Multiset ℂ}
    (hA : ∀ s, (fun g => (A g).esymm s) ∈ Virt ℂ ℂ G)
    (hB : ∀ s, (fun g => (B g).esymm s) ∈ Virt ℂ ℂ G) (s : ℕ) :
    (fun g => (A g + B g).esymm s) ∈ Virt ℂ ℂ G := by
  have : (fun g => (A g + B g).esymm s) = ∑ i ∈ Finset.range (s + 1),
      (fun g => (A g).esymm i) * (fun g => (B g).esymm (s - i)) := by
    funext g
    simp [esymm_add, Finset.sum_apply]
  rw [this]
  exact sum_mem fun i _ => (virt_mul_comap_conj_ind_linear G).1 _ (hA _) _ (hB _)
end GlobalTheory.EsymmVirt
