-- Prove2me | solution 1 for GlobalTheory.EsymmVirt.exists_multisets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:04:53.636925+00:00
-- url     : https://prove2.me/submissions/478db54b-2043-4518-b40c-53b2d05b3b1f

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
import Theorems.Thm_GlobalTheory_EsymmVirt_one_mem_virt
import Theorems.Thm_GlobalTheory_EsymmVirt_esymm_add_mem_virt
import Theorems.Thm_GlobalTheory_BI_isChar_esymm_roots_charpoly
import Theorems.Thm_GlobalTheory_BI_isChar_mem_virt_complex
import Theorems.Thm_GlobalTheory_BI_matrixChar_iff_isChar
import Theorems.Thm_GlobalTheory_CharpolyPow_roots_charpoly_pow
import Theorems.Thm_GlobalTheory_HasLogGrowth_neg


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
theorem _root_.solution {φ : G → ℂ} (hφ : φ ∈ Virt ℂ ℂ G) :
    ∃ A B : G → Multiset ℂ, (∀ s, (fun g => (A g).esymm s) ∈ Virt ℂ ℂ G) ∧
      (∀ s, (fun g => (B g).esymm s) ∈ Virt ℂ ℂ G) ∧
      ∀ g j, 0 < j → φ (g ^ j) + ((B g).map (· ^ j)).sum = ((A g).map (· ^ j)).sum := by
  have h0 : ∀ s, (fun _ : G => (0 : Multiset ℂ).esymm s) ∈ Virt ℂ ℂ G := by
    intro s
    cases s with
    | zero => simpa only [esymm_zero'] using one_mem_virt
    | succ s =>
      have : (fun _ : G => (0 : Multiset ℂ).esymm (s + 1)) = 0 := by
        funext g
        simp [Multiset.esymm, Multiset.powersetCard_zero_right]
      rw [this]
      exact zero_mem _
  induction hφ using AddSubgroup.closure_induction with
  | mem a ha =>
    obtain ⟨n, ρ, hρ⟩ := (matrixChar_iff_isChar G a).2 ha
    refine ⟨fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots, fun _ => 0,
      fun s => isChar_mem_virt_complex (isChar_esymm_roots_charpoly G n s ρ), h0, fun g j _ => ?_⟩
    rw [hρ, map_pow, Units.val_pow_eq_pow_val, Matrix.trace_eq_sum_roots_charpoly,
      GlobalTheory.CharpolyPow.roots_charpoly_pow]
    simp
  | zero => exact ⟨fun _ => 0, fun _ => 0, h0, h0, fun g j _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, B, hA, hB, h⟩ := hx
    obtain ⟨A', B', hA', hB', h'⟩ := hy
    refine ⟨fun g => A g + A' g, fun g => B g + B' g, esymm_add_mem_virt hA hA',
      esymm_add_mem_virt hB hB', fun g j hj => ?_⟩
    simp only [Pi.add_apply, Multiset.map_add, Multiset.sum_add]
    linear_combination h g j hj + h' g j hj
  | neg x _ hx =>
    obtain ⟨A, B, hA, hB, h⟩ := hx
    refine ⟨B, A, hB, hA, fun g j hj => ?_⟩
    simp only [Pi.neg_apply]
    linear_combination - h g j hj
end GlobalTheory.EsymmVirt
