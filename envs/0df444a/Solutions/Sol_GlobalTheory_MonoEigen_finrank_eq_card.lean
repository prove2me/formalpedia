-- Prove2me | solution 1 for GlobalTheory.MonoEigen.finrank_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:52:59.370802+00:00
-- url     : https://prove2.me/submissions/e3835fbf-3719-4429-8fa8-3a766c75d0b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinrankEigenspaceMonomialMatrixLift
import Theorems.Thm_GlobalTheory_MonoEigen_apply_pow
import Theorems.Thm_GlobalTheory_MonoEigen_exists_rep
import Theorems.Thm_GlobalTheory_MonoEigen_exists_vec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.MonoEigen
variable {K : Type} [Field K] {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → K)
namespace GlobalTheory.MonoEigen
theorem _root_.solution (E : Submodule K (Fin n → K))
    (hE : ∀ v, v ∈ E ↔ ∀ j, v (σ j) = a j * v j) :
    Module.finrank K E = Nat.card {j // GoodRep σ a j} := by
  classical
  let f : E →ₗ[K] ({j // GoodRep σ a j} → K) :=
    (LinearMap.funLeft K K Subtype.val).comp E.subtype
  have hf : ∀ (v : E) s, f v s = v.1 s.1 := fun _ _ => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro v h0
    have hv := (hE _).1 v.2
    ext i
    obtain ⟨j, hj, m, rfl⟩ := exists_rep σ i
    have : v.1 j = 0 := by
      by_cases hg : GoodRep σ a j
      · have := congrFun h0 ⟨j, hg⟩
        simpa [hf] using this
      · have : ¬ ∀ m : ℕ, (σ ^ m) j = j → orbProd σ a m j = 1 := fun h => hg ⟨hj, h⟩
        push_neg at this
        obtain ⟨r, hr, hne⟩ := this
        have h2 := apply_pow σ a hv r j
        rw [hr] at h2
        by_contra h3
        exact hne (mul_right_cancel₀ h3 (by rw [← h2, one_mul]))
    simp [apply_pow σ a hv, this]
  have hsurj : Function.Surjective f := by
    intro w
    choose u hu h1 h0 using fun s : {j // GoodRep σ a j} => exists_vec σ a s.2
    refine ⟨∑ s, w s • ⟨u s, (hE _).2 (hu s)⟩, ?_⟩
    ext t
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single t]
    · simp [hf, h1]
    · intro s _ hst
      simp [hf, h0 s t.1 t.2 (fun h => hst (Subtype.ext h).symm)]
    · simp
  rw [(LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]
end GlobalTheory.MonoEigen
