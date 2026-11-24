-- Prove2me | solution 1 for GlobalTheory.exists_prime_hom_zmod_of_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:53.419861+00:00
-- url     : https://prove2.me/submissions/145831d8-4484-4300-9f3a-ba2de61e524b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsPrimeHomZmodOfNeTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (X : Type) [AddCommGroup X] [Module.Finite ℤ X]
    (Λ : AddSubgroup X) (h : Λ ≠ ⊤) :
    ∃ l : ℕ, l.Prime ∧ ∃ f : X →+ ZMod l, f ≠ 0 ∧ ∀ x ∈ Λ, f x = 0 := by
  have h1 : (AddSubgroup.toIntSubmodule Λ) ≠ ⊤ := by
    intro h'
    apply h
    ext x
    have : x ∈ AddSubgroup.toIntSubmodule Λ := by rw [h']; trivial
    exact ⟨fun _ => trivial, fun _ => this⟩
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (AddSubgroup.toIntSubmodule Λ)).resolve_left h1
  have hs : IsSimpleModule ℤ (X ⧸ M) := isSimpleModule_iff_isCoatom.mpr hM
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
  obtain ⟨n, hn⟩ := (IsPrincipalIdealRing.principal I).principal
  have hn' : I = Ideal.span {((n.natAbs : ℕ) : ℤ)} := by
    rw [Int.span_natAbs]; exact hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hb : I = ⊥ := by simpa using hn
    exact Ring.ne_bot_of_isMaximal_of_not_isField hI Int.not_isField hb
  have hp : (n.natAbs).Prime := by
    have := hI.isPrime
    rw [hn'] at this
    have h2 := (Ideal.span_singleton_prime (by simpa using hn0)).mp this
    exact Nat.prime_iff_prime_int.mpr h2
  let g : (ℤ ⧸ I) ≃+* ZMod n.natAbs :=
    (Ideal.quotEquivOfEq hn').trans (Int.quotientSpanNatEquivZMod n.natAbs)
  refine ⟨n.natAbs, hp, g.toAddMonoidHom.comp (e.toLinearMap.toAddMonoidHom.comp M.mkQ.toAddMonoidHom), ?_, ?_⟩
  · intro h0
    apply hM.1
    rw [eq_top_iff]
    intro x _
    have hx : g (e (M.mkQ x)) = 0 := DFunLike.congr_fun h0 x
    rw [map_eq_zero_iff _ g.injective, map_eq_zero_iff _ e.injective] at hx
    exact (Submodule.Quotient.mk_eq_zero M).mp hx
  · intro x hx
    have : M.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero M).mpr (hle hx)
    change g (e (M.mkQ x)) = 0
    rw [this, map_zero, map_zero]
end GlobalTheory
