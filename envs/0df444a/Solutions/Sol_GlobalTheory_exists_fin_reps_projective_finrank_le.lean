-- Prove2me | solution 1 for GlobalTheory.exists_fin_reps_projective_finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:41:28.390902+00:00
-- url     : https://prove2.me/submissions/68c4cfde-603c-4b88-9c12-1fe36377409a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFinRepsProjectiveFinrankLeNumberField
import Theorems.Thm_GlobalTheory_ProjModClasses_exists_equiv_model

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
open ProjModClasses
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] (q : ℕ), ∃ (n : ℕ) (R : Fin n → ModuleCat.{0} (𝓞 E)),
    (∀ k, Module.Finite (𝓞 E) (R k) ∧ Module.Projective (𝓞 E) (R k) ∧ Module.finrank (𝓞 E) (R k) ≤ q) ∧
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∃ k, Nonempty (X ≃ₗ[𝓞 E] R k) := by
  intro E _ _ q
  let T := Σ r : Fin (q + 1), (Fin r → ClassGroup (𝓞 E))
  let g : T → ModuleCat.{0} (𝓞 E) := fun t => ModuleCat.of (𝓞 E) (Model t.2)
  let P : T → Prop := fun t => Module.Finite (𝓞 E) (g t) ∧ Module.Projective (𝓞 E) (g t) ∧
    Module.finrank (𝓞 E) (g t) ≤ q
  let S := {t : T // P t}
  haveI : Finite S := inferInstance
  let eS := Finite.equivFin S
  refine ⟨Nat.card S, fun k => g (eS.symm k).1, fun k => (eS.symm k).2, ?_⟩
  intro X _ _ _ _ hq
  obtain ⟨c, ⟨eX⟩⟩ := exists_equiv_model (R := 𝓞 E) (Module.finrank (𝓞 E) X) X rfl
  let t : T := ⟨⟨Module.finrank (𝓞 E) X, Nat.lt_succ_of_le hq⟩, c⟩
  have ht : P t := by
    refine ⟨Module.Finite.equiv eX, Module.Projective.of_equiv eX, ?_⟩
    change Module.finrank (𝓞 E) (Model c) ≤ q
    rw [← eX.finrank_eq]
    exact hq
  refine ⟨eS ⟨t, ht⟩, ?_⟩
  show Nonempty (X ≃ₗ[𝓞 E] (g (eS.symm (eS ⟨t, ht⟩)).1))
  rw [Equiv.symm_apply_apply]
  exact ⟨eX⟩
end GlobalTheory
