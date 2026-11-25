-- Prove2me | solution 1 for GlobalTheory.BetaCounterexample.betaH_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:27:03.808771+00:00
-- url     : https://prove2.me/submissions/46639949-110c-4054-8795-d73ebeb842a9

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
theorem _root_.solution {n m : ℕ} (Λ : GenLat E n) (Λ' : GenLat E m)
    (h : ∀ β : c.F, (β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) ↔
      (β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ' β ∧ BetaAbs (Dw := Dw) c Λ' β)) :
    betaH (Dw := Dw) c Λ = betaH (Dw := Dw) c Λ' := by
  unfold betaH
  have e := funext fun β => propext (h β)
  generalize (fun β : c.F => β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) = p at e ⊢
  subst e
  rfl
end GlobalTheory.BetaCounterexample
