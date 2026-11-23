-- Prove2me | solution 1 for GlobalTheory.UnimodularLatticeLemma.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:50.380155+00:00
-- url     : https://prove2.me/submissions/ff6c04d2-982c-4656-8297-9d49c55f51c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnimodularLatticeLemma
namespace GlobalTheory.UnimodularLatticeLemma
theorem _root_.solution {L : Type} [Field L] [IsAlgClosed L] {ι V : Type} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] [Nontrivial V] (f : ι → Module.End L V)
    (hc : ∀ (a b : ι), f a * f b = f b * f a) :
    ∃ (v : V), v ≠ (0 : V) ∧ ∀ (b : ι), ∃ (μ : L), (f b : V → V) v = μ • v := by
  classical
  let S : Set (Submodule L V) := {W | W ≠ ⊥ ∧ ∀ b, ∀ x ∈ W, f b x ∈ W}
  have hS : (⊤ : Submodule L V) ∈ S := ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top⟩
  obtain ⟨W, hW, hmin⟩ := (wellFounded_lt (α := Submodule L V)).has_min S ⟨⊤, hS⟩
  have key : ∀ b, ∃ μ : L, ∀ x ∈ W, f b x = μ • x := by
    intro b
    have hWb : ∀ x ∈ W, f b x ∈ W := hW.2 b
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW.1
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((f b).restrict hWb)
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hw1 : (f b).restrict hWb w = μ • w := hw.apply_eq_smul
    have hw0 : w ≠ 0 := hw.2
    let W' : Submodule L V := W ⊓ LinearMap.ker (f b - μ • 1)
    have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ f b x = μ • x := by
      intro x
      simp only [W', Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    have hW'S : W' ∈ S := by
      refine ⟨?_, ?_⟩
      · intro h
        apply hw0
        have : (w : V) ∈ W' := by
          rw [hmem]
          refine ⟨w.2, ?_⟩
          have := congrArg Subtype.val hw1
          simpa using this
        rw [h, Submodule.mem_bot] at this
        exact Subtype.ext this
      · intro c x hx
        rw [hmem] at hx ⊢
        refine ⟨hW.2 c x hx.1, ?_⟩
        have h1 : f b (f c x) = (f b * f c) x := rfl
        rw [h1, hc b c, Module.End.mul_apply, hx.2, map_smul]
    have hle : W' ≤ W := inf_le_left
    have heq : W' = W := by
      by_contra hne
      exact hmin W' hW'S (lt_of_le_of_ne hle hne)
    refine ⟨μ, fun x hx => ?_⟩
    have : x ∈ W' := heq ▸ hx
    exact ((hmem x).1 this).2
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW.1
  refine ⟨v, hv0, fun b => ?_⟩
  obtain ⟨μ, hμ⟩ := key b
  exact ⟨μ, hμ v hvW⟩
end GlobalTheory.UnimodularLatticeLemma
