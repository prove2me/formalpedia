-- Prove2me | solution 1 for GlobalTheory.CuspGL.star_virt_eq_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:01.91904+00:00
-- url     : https://prove2.me/submissions/e4ccebf5-ca38-43fb-a7c8-e8cb4573c125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_StarVirtualCharacterEqApplyInv
import Theorems.Thm_GlobalTheory_BadShare_ZCalc_character_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
open Polynomial
namespace GlobalTheory.CuspGL
namespace _root_.GlobalTheory.CuspGL
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ),
    χ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G → ∀ g, star (χ g) = χ g⁻¹ := by
  intro G _ _ χ hχ
  have := Fintype.ofFinite G
  unfold _root_.GlobalTheory.BI.Virt at hχ
  induction hχ using AddSubgroup.closure_induction with
  | mem ψ hψ =>
    obtain ⟨n, ρ, h⟩ := hψ
    intro g
    have key := _root_.GlobalTheory.BadShare.ZCalc.character_inv (FDRep.of ρ) g
    simp only [h, Algebra.algebraMap_self, RingHom.id_apply]
    exact key.symm
  | zero => intro g; simp
  | add ψ φ _ _ h₁ h₂ => intro g; simp [h₁ g, h₂ g]
  | neg ψ _ h₁ => intro g; simp [h₁ g]
end _root_.GlobalTheory.CuspGL
end GlobalTheory.CuspGL
