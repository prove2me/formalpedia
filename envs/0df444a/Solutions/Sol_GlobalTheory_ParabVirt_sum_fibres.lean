-- Prove2me | solution 1 for GlobalTheory.ParabVirt.sum_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:19:54.822522+00:00
-- url     : https://prove2.me/submissions/d6a1abe9-4d8b-4301-9443-b20e9a45a8d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParabolicInductionTrivialPreservesVirtualCharact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.ParabVirt
open Polynomial
namespace GlobalTheory.ParabVirt
namespace _root_.GlobalTheory.ParabVirt
theorem _root_.solution {G X : Type} [Group G] [Fintype G] [Fintype X]
    (H : Subgroup G) (π : G → X)
    (hs : Function.Surjective π) (hπ : ∀ s t, π s = π t ↔ s⁻¹ * t ∈ H) (f : X → ℂ) :
    ∑ t, f (π t) = (Nat.card H : ℂ) * ∑ x, f x := by
  classical
  have hcard : ∀ s : G, (Finset.univ.filter (fun t => π t = π s)).card = Nat.card H := by
    intro s
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun t => ⟨s⁻¹ * t.1, (hπ s t.1).1 t.2.symm⟩
        invFun := fun h => ⟨s * h.1, ((hπ s (s * h.1)).2 (by simpa using h.2)).symm⟩
        left_inv := fun t => by ext; simp
        right_inv := fun h => by ext; simp }
  calc ∑ t, f (π t) = ∑ x, ∑ t ∈ Finset.univ.filter (fun t => π t = x), f (π t) :=
        (Finset.sum_fiberwise _ _ _).symm
    _ = ∑ x, (Nat.card H : ℂ) * f x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        obtain ⟨s, rfl⟩ := hs x
        rw [Finset.sum_congr rfl (g := fun _ => f (π s))
          (fun t ht => by rw [(Finset.mem_filter.1 ht).2]), Finset.sum_const, hcard, nsmul_eq_mul]
    _ = _ := (Finset.mul_sum _ _ _).symm
end _root_.GlobalTheory.ParabVirt
end GlobalTheory.ParabVirt
