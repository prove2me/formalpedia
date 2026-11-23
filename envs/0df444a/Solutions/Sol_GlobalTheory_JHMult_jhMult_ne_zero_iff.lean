-- Prove2me | solution 1 for GlobalTheory.JHMult.jhMult_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:59.349704+00:00
-- url     : https://prove2.me/submissions/52e5928c-d061-40ed-a94e-d6397e83b7ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_JhMultSubAddQuot
import Theorems.Thm_GlobalTheory_JHMult_subMap_mono
import Theorems.Thm_GlobalTheory_JHMult_step_iff
import Theorems.Thm_GlobalTheory_JHMult_step_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.JHMult
variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
namespace GlobalTheory.JHMult
theorem _root_.solution {σ : Representation F G W} {ρ : Representation F G V} :
    jhMult σ ρ ≠ 0 ↔ IsSubquotient σ ρ := by
  constructor
  · intro h
    by_contra hn
    refine h (le_antisymm (iSup₂_le ?_) zero_le)
    rintro r ⟨S, T, -, -, h3⟩
    rcases r with _ | n
    · simp
    obtain ⟨f, h1, h2, -⟩ := step_iff.1 (h3 0)
    refine absurd ⟨S 0, ⟨f ∘ₗ (S 0).toSubmodule.subtype, fun g => ?_⟩, fun w => ?_⟩ hn
    · exact LinearMap.ext fun v => h2 g v.1 v.2
    · obtain ⟨v, hv, rfl⟩ := h1 w
      exact ⟨⟨v, hv⟩, rfl⟩
  · rintro ⟨S, f, hf⟩
    let ι : S.toRepresentation.IntertwiningMap ρ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
    have hs : Step σ (⊤ : Subrepresentation S.toRepresentation) f.ker :=
      ⟨f.toLinearMap, fun w => by
        obtain ⟨v, rfl⟩ := hf w
        exact ⟨v, trivial, rfl⟩, fun g v _ => f.isIntertwining _ _ g v, fun v _ => Iff.rfl⟩
    have h1 : OccursTimes σ ρ 1 := ⟨fun _ => subMap ι ⊤, fun _ => subMap ι f.ker,
      fun _ => subMap_mono ι le_top, fun i j h => absurd (Subsingleton.elim i j) h.ne,
      fun _ => step_iff.2 (step_map ι Subtype.val_injective hs)⟩
    have : ((1 : ℕ) : ℕ∞) ≤ jhMult σ ρ := le_iSup₂_of_le 1 h1 le_rfl
    intro h0
    rw [h0] at this
    simp at this
end GlobalTheory.JHMult
