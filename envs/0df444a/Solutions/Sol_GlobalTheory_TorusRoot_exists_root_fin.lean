-- Prove2me | solution 1 for GlobalTheory.TorusRoot.exists_root_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:43.378965+00:00
-- url     : https://prove2.me/submissions/6a958424-be6e-4ed7-8025-5687902ace0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsPthRootTorusPointNilpotentAugmentedExt
import Theorems.Thm_GlobalTheory_TorusRoot_exists_root_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TorusRoot
namespace GlobalTheory.TorusRoot
theorem _root_.solution (Ω : Type) [Field Ω] (p : ℕ) [hp : Fact p.Prime] [CharP Ω p] (n : ℕ) :
    ∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω) (_ : IsNilpotent (RingHom.ker π))
    (a : Fin n → Aˣ) (_ : ∀ i, π (a i).val = 1),
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra Ω A') (f : A →ₐ[Ω] A') (π' : A' →ₐ[Ω] Ω)
      (s : Fin n → A'ˣ), Function.Injective f ∧ π'.comp f = π ∧ IsNilpotent (RingHom.ker π') ∧
      (∀ i, π' (s i).val = 1) ∧ ∀ i, s i ^ p = Units.map (f : A →* A') (a i) := by
  induction n with
  | zero =>
    intro A _ _ π hπ a _
    exact ⟨A, inferInstance, inferInstance, AlgHom.id Ω A, π, a, Function.injective_id, rfl, hπ,
      fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro A _ _ π hπ a ha
    obtain ⟨B, _, _, f, ρ, s, hf, hρ, hρn, hs1, hs⟩ :=
      ih A π hπ (fun i => a i.succ) (fun i => ha i.succ)
    have h0 : ρ (Units.map (f : A →* B) (a 0)).val = 1 := by
      have := congrArg (fun φ : A →ₐ[Ω] Ω => φ (a 0).val) hρ
      simpa [ha 0] using this
    obtain ⟨C, _, _, g, σ, t, hg, hσ, hσn, ht1, ht⟩ :=
      exists_root_one Ω p B ρ hρn _ h0
    refine ⟨C, inferInstance, inferInstance, g.comp f, σ,
      Fin.cons t (fun i => Units.map (g : B →* C) (s i)), hg.comp hf, ?_, hσn, ?_, ?_⟩
    · rw [← AlgHom.comp_assoc, hσ, hρ]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ht1
      · have := congrArg (fun φ : B →ₐ[Ω] Ω => φ (s j).val) hσ
        simpa [hs1 j] using this
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero, ht]; rfl
      · rw [Fin.cons_succ, ← map_pow, hs j]; rfl
end GlobalTheory.TorusRoot
