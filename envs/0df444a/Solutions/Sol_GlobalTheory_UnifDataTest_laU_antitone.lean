-- Prove2me | solution 1 for GlobalTheory.UnifDataTest.laU_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:35:32.962226+00:00
-- url     : https://prove2.me/submissions/562f2575-98a8-41d8-bdf0-b7040c8e3d04

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
theorem _root_.solution (U : Unf Xo c σ r) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n) (k : U.Comp)
    (τ : (U.X k).Ψ) (j j' : Fin r) (hj : j ≤ j') (hb : (U.X k).p0 ≤ (j : ℕ) ∨ (j' : ℕ) < (U.X k).p0) :
    laU U a n k τ j' ≤ laU U a n k τ j := by
  have hjj : (j : ℕ) ≤ j' := hj
  rcases hb with hb | hb
  · have hb' : (U.X k).p0 ≤ (j' : ℕ) := hb.trans hjj
    have := hd.1 (Function.invFun (relab c σ) τ.1) (show (j : ℕ) - (U.X k).p0 ≤ (j' : ℕ) - (U.X k).p0 by omega)
    simp only [laU, hb, hb', if_true]
    simp only at this
    omega
  · have h1 : ¬ (U.X k).p0 ≤ (j' : ℕ) := by omega
    have h2 : ¬ (U.X k).p0 ≤ (j : ℕ) := by omega
    have := hd.1 (Function.invFun (relab c σ) (conjEmb τ.1))
      (show (U.X k).p0 - 1 - (j' : ℕ) ≤ (U.X k).p0 - 1 - (j : ℕ) by omega)
    simp only [laU, h1, h2, if_false]
    simp only at this
    omega
end GlobalTheory.UnifDataTest
