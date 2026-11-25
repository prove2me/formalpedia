-- Prove2me | solution 1 for GlobalTheory.EsymmVirt.esymm_mem_virt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:06:18.141776+00:00
-- url     : https://prove2.me/submissions/395c20be-f028-4d8f-917e-e4471b17e8e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MatrixTraceIffIsCharacterOverSubfieldComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterEsymmRootsCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MultisetPowerSumNewtonIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EsymmMemVirtualCharactersOfPowerSumEigenvalues
import Theorems.Thm_P2M_GlobalTheory_EsymmVirt_esymm_zero__0112da44c67e
import Theorems.Thm_GlobalTheory_EsymmVirt_esymm_add
import Theorems.Thm_GlobalTheory_EsymmVirt_esymm_eq_of_psum_eq
import Theorems.Thm_GlobalTheory_EsymmVirt_exists_multisets
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
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ) (x : G → Multiset ℂ),
    φ ∈ Virt ℂ ℂ G → (∀ (g : G) (j : ℕ), 0 < j → φ (g ^ j) = ((x g).map (· ^ j)).sum) →
    ∀ s : ℕ, (fun g => (x g).esymm s) ∈ Virt ℂ ℂ G := by
  intro G _ _ φ x hφ hx s
  obtain ⟨A, B, hA, hB, h⟩ := exists_multisets hφ
  have he : ∀ g n, (x g + B g).esymm n = (A g).esymm n := fun g n =>
    esymm_eq_of_psum_eq _ _ (fun j hj => by
      rw [Multiset.map_add, Multiset.sum_add, ← hx g j hj, h g j hj]) n
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    have : (fun g => (x g).esymm s) = (fun g => (A g).esymm s) - ∑ i ∈ Finset.range s,
        (fun g => (x g).esymm i) * (fun g => (B g).esymm (s - i)) := by
      funext g
      have := he g s
      rw [esymm_add, Finset.sum_range_succ, Nat.sub_self, esymm_zero', mul_one] at this
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.mul_apply]
      linear_combination this
    rw [this]
    exact sub_mem (hA s) (sum_mem fun i hi =>
      (virt_mul_comap_conj_ind_linear G).1 _ (ih i (Finset.mem_range.1 hi)) _ (hB _))
end GlobalTheory.EsymmVirt
