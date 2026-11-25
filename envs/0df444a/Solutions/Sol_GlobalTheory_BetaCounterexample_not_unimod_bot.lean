-- Prove2me | solution 1 for GlobalTheory.BetaCounterexample.not_unimod_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:27:25.947006+00:00
-- url     : https://prove2.me/submissions/6e70329c-7ef6-4002-88bb-09bae2d963fc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal

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
theorem _root_.solution {n : ℕ} (hn : 0 < n) : ¬ (⟨⊥⟩ : GenLat E n).Unimod := by
  intro h
  have := (h (fun _ => 1)).2 (by
    intro w hw
    rw [(Submodule.mem_bot _).1 hw]
    simp)
  have h1 := congrFun ((Submodule.mem_bot _).1 this) ⟨0, hn⟩
  simp at h1
end GlobalTheory.BetaCounterexample
