-- Prove2me | solution 1 for GlobalTheory.PushHarm.push_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:41:27.640088+00:00
-- url     : https://prove2.me/submissions/04036699-d84f-4bbc-bcf8-b294531cb965

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UnitaryDetClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PushMemHarmK

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
open GlobalTheory GlobalTheory.PushHarm
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l) {n : ℕ}
namespace GlobalTheory.PushHarm
theorem _root_.solution (γ : Matrix (Fin n) (Fin n) E) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (j : Fin n) :
    push c γ (X (⟨σ, i, j⟩ : LtN Dw n)) =
      ∑ k, C (embF c σ (γ k j)) * X (⟨σ, i, k⟩ : LtN Dw n) := by
  simp [push, letB]
end GlobalTheory.PushHarm
