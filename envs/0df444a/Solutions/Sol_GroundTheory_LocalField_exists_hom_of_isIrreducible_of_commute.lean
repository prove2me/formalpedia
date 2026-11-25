-- Prove2me | solution 1 for GroundTheory.LocalField.exists_hom_of_isIrreducible_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:04:31.294988+00:00
-- url     : https://prove2.me/submissions/4c35ef1f-97cf-4c98-84eb-4d6ecc6cb236

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford

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
variable {G : Type*} [Group G]
namespace GroundTheory.LocalField
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (σ : Representation ℂ G V) [hσ : σ.IsIrreducible]
    (hc : ∀ a b, σ a * σ b = σ b * σ a) :
    ∃ l : G →* ℂˣ, σ.character = fun g ↦ (l g : ℂ) := by
  have hs : ∀ a, ∃ c : ℂ, σ a = c • (1 : Module.End ℂ V) := by
    intro a
    obtain ⟨c, hc'⟩ := (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := σ)).2 ⟨σ a, fun b ↦ hc a b⟩
    refine ⟨c, ?_⟩
    have := congrArg IntertwiningMap.toLinearMap hc'
    rw [Algebra.algebraMap_eq_smul_one] at this
    exact this.symm
  choose c hc' using hs
  have hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    apply (bot_ne_top : (⊥ : Subrepresentation σ) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    exact Subsingleton.elim _ _
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let U : Subrepresentation σ := ⟨ℂ ∙ v, fun a w hw ↦ by
    rw [hc' a]
    exact Submodule.smul_mem _ _ hw⟩
  have hU : U = ⊤ := by
    refine (hσ.eq_bot_or_eq_top U).resolve_left fun h ↦ hv ?_
    have : v ∈ U.toSubmodule := Submodule.mem_span_singleton_self v
    rw [h] at this
    exact this
  have hrank : finrank ℂ V = 1 := by
    have h1 := finrank_span_singleton (K := ℂ) hv
    have h2 : (ℂ ∙ v) = ⊤ := congrArg Subrepresentation.toSubmodule hU
    rw [h2, finrank_top] at h1
    exact h1
  have hchar : ∀ a, σ.character a = c a := by
    intro a
    simp [Representation.character, hc' a, LinearMap.trace_one, hrank]
  have hmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    have h := map_mul σ a b
    rw [hc', hc', hc', smul_mul_smul, one_mul] at h
    have h' := congrArg (fun T : Module.End ℂ V ↦ T v) h
    simp only [LinearMap.smul_apply, Module.End.one_apply] at h'
    exact smul_left_injective ℂ hv h'
  have hone : c 1 = 1 := by
    rw [← hchar, char_one, hrank, Nat.cast_one]
  let f : G →* ℂ := { toFun := c, map_one' := hone, map_mul' := hmul }
  refine ⟨f.toHomUnits, ?_⟩
  funext g
  simp [f, hchar]
end GroundTheory.LocalField
