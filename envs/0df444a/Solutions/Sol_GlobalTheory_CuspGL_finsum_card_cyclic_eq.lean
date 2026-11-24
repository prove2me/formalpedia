-- Prove2me | solution 1 for GlobalTheory.CuspGL.finsum_card_cyclic_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:04:03.569118+00:00
-- url     : https://prove2.me/submissions/a1b946e5-12cb-4481-b313-1a877f9110cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumCardCyclicVectorsInvariantSubspaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (g : Module.End F V) :
    ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W},
      (Nat.card {v : W.1 // ∀ U : Submodule F (W.1),
        (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤} : ℂ)
      = (Nat.card F : ℂ) ^ Module.finrank F V := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Submodule F V) :=
    Finite.of_injective (fun W : Submodule F V => (W : Set V)) SetLike.coe_injective
  haveI : Fintype {W : Submodule F V // ∀ x ∈ W, g x ∈ W} := Fintype.ofFinite _
  have key : ∀ (W W' : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}) (v : W.1),
      (∀ U : Submodule F (W.1), (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤) →
      (v : V) ∈ W'.1 → W.1 ≤ W'.1 := by
    intro W W' v hv hv' x hx
    have h := hv (W'.1.comap W.1.subtype) (fun y hy => W'.2 _ hy) hv'
    have : (⟨x, hx⟩ : W.1) ∈ W'.1.comap W.1.subtype := h ▸ Submodule.mem_top
    exact this
  let f : (Σ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, {v : W.1 // ∀ U : Submodule F (W.1),
        (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤}) → V := fun p => (p.2.1 : V)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨W, v, hv⟩ ⟨W', v', hv'⟩ h
      have h' : (v : V) = v' := h
      have hW : W = W' := Subtype.ext (le_antisymm (key W W' v hv (h' ▸ v'.2))
        (key W' W v' hv' (h' ▸ v.2)))
      subst hW
      have : v = v' := Subtype.ext h'
      subst this
      rfl
    · intro v
      let S : Set (Submodule F V) := {U | (∀ x ∈ U, g x ∈ U) ∧ v ∈ U}
      have hinv : ∀ x ∈ sInf S, g x ∈ sInf S := by
        intro x hx
        rw [Submodule.mem_sInf] at hx ⊢
        exact fun p hp => hp.1 x (hx p hp)
      have hv : v ∈ sInf S := by
        rw [Submodule.mem_sInf]
        exact fun p hp => hp.2
      refine ⟨⟨⟨sInf S, hinv⟩, ⟨v, hv⟩, ?_⟩, rfl⟩
      intro U hU hvU
      have hle : sInf S ≤ U.map (sInf S).subtype := by
        refine sInf_le ⟨?_, ⟨_, hvU, rfl⟩⟩
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨_, hU y hy, rfl⟩
      rw [eq_top_iff]
      rintro ⟨x, hx⟩ -
      obtain ⟨y, hy, hyx⟩ := hle hx
      have : y = ⟨x, hx⟩ := Subtype.ext hyx
      exact this ▸ hy
  have hc := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_sigma, Module.natCard_eq_pow_finrank (K := F)] at hc
  rw [finsum_eq_sum_of_fintype]
  exact_mod_cast hc
end GlobalTheory.CuspGL
