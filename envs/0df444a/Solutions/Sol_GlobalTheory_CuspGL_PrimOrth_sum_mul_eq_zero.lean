-- Prove2me | solution 1 for GlobalTheory.CuspGL.PrimOrth.sum_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:06:30.364804+00:00
-- url     : https://prove2.me/submissions/feceb91f-13c6-4f56-9d98-db4f9849a872

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndomorphismInnerProductPrimitiveMobiu

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.PrimOrth
variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
namespace GlobalTheory.CuspGL.PrimOrth
theorem _root_.solution [Fintype (Module.End F V)] {φ : Module.End F V → ℂ} (hφ : IsPrimitive φ)
    {A : Submodule F V} (h0 : A ≠ ⊥) (h1 : A ≠ ⊤) (f : Module.End F V → ℂ)
    (hf : ∀ g, ∀ h ∈ nilRad A, f (g + h) = f g) (hf0 : ∀ g, ¬ (∀ x ∈ A, g x ∈ A) → f g = 0) :
    ∑ g, φ g * f g = 0 := by
  classical
  have hfin : (nilRad A).Finite := Set.toFinite _
  have hne : (hfin.toFinset.card : ℂ) ≠ 0 := by
    have : hfin.toFinset.Nonempty := ⟨0, by
      rw [Set.Finite.mem_toFinset]
      exact ⟨fun x => by simp, fun x _ => by simp⟩⟩
    exact_mod_cast this.card_pos.ne'
  have key : ∑ h ∈ hfin.toFinset, ∑ g, φ g * f g = 0 := by
    have : ∀ h ∈ hfin.toFinset, ∑ g, φ g * f g = ∑ g, φ (g + h) * f g := by
      intro h hh
      rw [Set.Finite.mem_toFinset] at hh
      rw [← Equiv.sum_comp (Equiv.addRight h)]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [Equiv.coe_addRight, hf g h hh]
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [← Finset.sum_mul]
    by_cases hg : ∀ x ∈ A, g x ∈ A
    · have := hφ A h0 h1 g hg
      rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at this
      rw [this, zero_mul]
    · rw [hf0 g hg, mul_zero]
  rw [Finset.sum_const, nsmul_eq_mul] at key
  exact (mul_eq_zero.mp key).resolve_left hne
end GlobalTheory.CuspGL.PrimOrth
