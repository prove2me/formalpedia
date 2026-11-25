-- Prove2me | solution 1 for GroundTheory.LocalField.apply_eq_smul_of_forall_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:41:36.241525+00:00
-- url     : https://prove2.me/submissions/0bf4396a-d477-47a7-bdf8-ecd10de0419a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionMonomial
import Theorems.Thm_GroundTheory_LocalField_charInner_character_character
import Theorems.Thm_GroundTheory_LocalField_character_linRep
import Theorems.Thm_GroundTheory_LocalField_linRep_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {G : Type*} [Group G] {A : Subgroup G} [A.Normal] [Fintype A]
namespace GroundTheory.LocalField
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [hρ : ρ.IsIrreducible] (l : A →* ℂˣ)
    (h : charInner A (ρ.character ∘ A.subtype) (fun a ↦ (l a : ℂ)) ≠ 0)
    (hl : ∀ (g : G) (a : A), l (conjNormal A g a) = l a) (a : A) (v : V) :
    ρ a v = (l a : ℂ) • v := by
  have hrank : finrank ℂ (IntertwiningMap (linRep l) (ρ.comp A.subtype)) ≠ 0 := by
    rw [← Nat.cast_ne_zero (R := ℂ), ← charInner_character_character, character_linRep]
    exact h
  have : Nontrivial (IntertwiningMap (linRep l) (ρ.comp A.subtype)) :=
    Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hrank)
  obtain ⟨F, hF⟩ := exists_ne (0 : IntertwiningMap (linRep l) (ρ.comp A.subtype))
  let W : Subrepresentation ρ :=
    { toSubmodule :=
        { carrier := {w | ∀ a : A, ρ a w = (l a : ℂ) • w}
          add_mem' := fun {w w'} hw hw' a ↦ by rw [map_add, hw a, hw' a, smul_add]
          zero_mem' := fun a ↦ by rw [map_zero, smul_zero]
          smul_mem' := fun c w hw a ↦ by rw [map_smul, hw a, smul_comm] }
      apply_mem_toSubmodule := fun g w hw a ↦ by
        have hag : (a : G) * g = g * (conjNormal A g a : G) := by simp [mul_assoc]
        change ρ a (ρ g w) = (l a : ℂ) • ρ g w
        rw [← Module.End.mul_apply, ← map_mul, hag, map_mul, Module.End.mul_apply]
        rw [show ρ (conjNormal A g a : G) w = (l (conjNormal A g a) : ℂ) • w from hw _, hl, map_smul] }
  have hF1 : F 1 ∈ W.toSubmodule := fun a ↦ by
    have := IntertwiningMap.isIntertwining _ _ F a 1
    rw [linRep_apply, mul_one,
      show ((l a : ℂˣ) : ℂ) = (l a : ℂ) • (1 : ℂ) by rw [smul_eq_mul, mul_one], map_smul] at this
    exact this.symm
  have hW : W = ⊤ := by
    refine (hρ.eq_bot_or_eq_top W).resolve_left fun hb ↦ hF ?_
    have h0 : F 1 = 0 := by
      have := hF1
      rw [hb] at this
      exact this
    apply IntertwiningMap.ext
    apply LinearMap.ext_ring
    rw [IntertwiningMap.toLinearMap_apply, h0]
    rfl
  have hv : v ∈ W.toSubmodule := by
    rw [hW]
    exact Submodule.mem_top
  exact hv a
end GroundTheory.LocalField
