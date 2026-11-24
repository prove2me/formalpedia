-- Prove2me | solution 1 for GlobalTheory.BI.isChar_zero_and_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:00:21.686197+00:00
-- url     : https://prove2.me/submissions/f628209d-76a8-4da1-9527-69ed64dcb353

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldZeroAndAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.BI
namespace GlobalTheory.BI
private theorem exists_representation_character_eq_add (K : Type) [Field K] (G : Type) [Group G]
    (n m : ℕ) (ρ : Representation K G (Fin n → K)) (σ : Representation K G (Fin m → K)) :
    ∃ τ : Representation K G (Fin (n + m) → K),
      ∀ g, τ.character g = ρ.character g + σ.character g := by
  let e : ((Fin n → K) × (Fin m → K)) ≃ₗ[K] (Fin (n + m) → K) :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) K K).symm ≪≫ₗ
      LinearEquiv.funCongrLeft K K finSumFinEquiv.symm
  refine ⟨{ toFun := fun g => e.conj ((ρ g).prodMap (σ g)), map_one' := ?_, map_mul' := ?_ },
    fun g => ?_⟩
  · simp only [map_one, LinearMap.prodMap_one]
    exact e.conj_id
  · intro g h
    simp only [map_mul]
    rw [← LinearMap.prodMap_mul]
    exact e.conj_comp _ _
  · simp only [Representation.character]
    show LinearMap.trace K _ (e.conj _) = _
    rw [LinearMap.trace_conj', LinearMap.trace_prodMap']
end GlobalTheory.BI
end

set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
namespace _root_.GlobalTheory.BI
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    (G : Type) [Group G], _root_.GlobalTheory.BI.IsChar K L (0 : G → L) ∧
      ∀ a b : G → L, _root_.GlobalTheory.BI.IsChar K L a → _root_.GlobalTheory.BI.IsChar K L b →
        _root_.GlobalTheory.BI.IsChar K L (a + b) := by
  intro K L _ _ _ G _
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.BI.IsChar
    refine ⟨0, 1, fun g => ?_⟩
    simp [Representation.character]
  · intro a b ha hb
    unfold _root_.GlobalTheory.BI.IsChar at ha hb ⊢
    obtain ⟨n, ρ, hρ⟩ := ha
    obtain ⟨m, σ, hσ⟩ := hb
    obtain ⟨τ, hτ⟩ := exists_representation_character_eq_add K G n m ρ σ
    refine ⟨n + m, τ, fun g => ?_⟩
    rw [Pi.add_apply, hρ g, hσ g, hτ g, map_add]
end _root_.GlobalTheory.BI
end GlobalTheory.BI
