-- Prove2me | solution 1 for GlobalTheory.BetaCounterexample.std_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:35:21.817417+00:00
-- url     : https://prove2.me/submissions/83b9fdaa-70d3-4754-ab19-25ff7b393540

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal
import Theorems.Thm_GlobalTheory_BetaCounterexample_ln_std

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BetaCounterexample
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l)
namespace GlobalTheory.BetaCounterexample
theorem _root_.solution (n : ℕ) (β : c.F) (hβ : β = 1 ∨ β = -1) :
    β ≠ 0 ∧ BetaIs (Dw := Dw) c (⟨stdLat E n⟩ : GenLat E n) β ∧ BetaAbs (Dw := Dw) c (⟨stdLat E n⟩ : GenLat E n) β := by
  have h1 : Submodule.span (𝓞 c.F) {β} = 1 := by
    rcases hβ with rfl | rfl
    · exact (Submodule.one_eq_span).symm
    · rw [Submodule.one_eq_span, ← Set.neg_singleton, Submodule.span_neg]
  refine ⟨by rcases hβ with rfl | rfl <;> simp, ?_, ?_⟩
  · unfold BetaIs
    rw [h1, one_mul, ln_std]
  · intro σ
    rw [ln_std]
    rcases hβ with rfl | rfl <;> simp
end GlobalTheory.BetaCounterexample
