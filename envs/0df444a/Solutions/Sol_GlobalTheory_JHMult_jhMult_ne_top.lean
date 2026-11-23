-- Prove2me | solution 1 for GlobalTheory.JHMult.jhMult_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:52.862267+00:00
-- url     : https://prove2.me/submissions/e7d71003-3689-4f2b-a156-07d561a2a1b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_JhMultSubAddQuot
import Theorems.Thm_GlobalTheory_JHMult_step_iff
import Theorems.Thm_GlobalTheory_JHMult_Step_not_le

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
theorem _root_.solution {σ : Representation F G W} {ρ : Representation F G V}
    (hσ : σ.IsIrreducible) (h : HasFiniteLength ρ) : jhMult σ ρ ≠ ⊤ := by
  have hl : Module.length (MonoidAlgebra F G) ρ.asModule ≠ ⊤ := Module.length_ne_top_iff.2 h
  refine ne_top_of_le_ne_top (b := Module.length (MonoidAlgebra F G) ρ.asModule + 1)
    (by simpa using hl) (iSup₂_le ?_)
  rintro r ⟨S, T, h1, h2, h3⟩
  rcases r with _ | n
  · simp
  have hm : StrictMono fun i => Subrepresentation.subrepresentationSubmoduleOrderIso (S i) := by
    intro i j hij
    refine Subrepresentation.subrepresentationSubmoduleOrderIso.strictMono
      ((h2 i j hij).trans_lt (lt_of_le_not_ge (h1 j) ((step_iff.1 (h3 j)).not_le hσ)))
  have := Order.LTSeries.length_le_krullDim (LTSeries.mk n _ hm)
  rw [← Module.coe_length] at this
  have h' : (n : ℕ∞) ≤ Module.length (MonoidAlgebra F G) ρ.asModule := by
    exact WithBot.coe_le_coe.1 this
  push_cast
  exact add_le_add h' le_rfl
end GlobalTheory.JHMult
