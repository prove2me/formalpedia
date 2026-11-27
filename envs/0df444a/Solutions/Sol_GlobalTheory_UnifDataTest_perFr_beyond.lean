-- Prove2me | solution 1 for GlobalTheory.UnifDataTest.perFr_beyond
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:35:50.453311+00:00
-- url     : https://prove2.me/submissions/8a6a0431-f051-4542-bf83-330604da87bb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_RelabBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnifDataTest
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
namespace GlobalTheory.UnifDataTest
theorem _root_.solution (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) {τ : E →+* ℂ} (h : τ ∉ X.Ψ) (hr : 0 < r)
    {i : ℕ} (hi : X.p0 ≤ i + 1) :
    perFr X x v τ i =
      hermC (conjEmb τ) X.Gm (col (mat x ⟨conjEmb τ, conj_mem X h⟩) ⟨0, hr⟩) (Data.emb (conjEmb τ) v) := by
  have h0 : X.p0 - 1 - i = 0 := by omega
  unfold perFr
  rw [dif_neg h, dif_pos (conj_mem X h), dif_pos (h0 ▸ hr)]
  simp only [h0]
end GlobalTheory.UnifDataTest
