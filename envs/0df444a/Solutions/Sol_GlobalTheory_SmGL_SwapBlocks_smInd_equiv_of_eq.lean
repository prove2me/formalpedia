-- Prove2me | solution 1 for GlobalTheory.SmGL.SwapBlocks.smInd_equiv_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:10:30.151932+00:00
-- url     : https://prove2.me/submissions/75a9dc62-d828-4fdd-b4a3-bcf65e5e8ca7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl


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
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.SwapBlocks
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.SmGL.SwapBlocks
theorem _root_.solution [TopologicalSpace G] [IsTopologicalGroup G] {H H' : Subgroup G} (h : H = H')
    (σ : Representation ℂ H V) (σ' : Representation ℂ H' V)
    (hσ : ∀ g (hg : g ∈ H) (hg' : g ∈ H'), σ ⟨g, hg⟩ = σ' ⟨g, hg'⟩) :
    Nonempty ((smInd H σ).Equiv (smInd H' σ')) := by
  subst h
  obtain rfl : σ = σ' := MonoidHom.ext fun g => hσ g.1 g.2 g.2
  exact ⟨Representation.Equiv.refl _⟩
end GlobalTheory.SmGL.SwapBlocks
