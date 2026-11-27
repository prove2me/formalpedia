-- Prove2me | solution 1 for GlobalTheory.UnifDataTest.laU_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:35:35.875985+00:00
-- url     : https://prove2.me/submissions/9a9890ba-8759-450f-bb06-2f8327e22e10

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_RelabBijective
import Theorems.Thm_GlobalTheory_UnifDataTest_relab_bijective
import Theorems.Thm_GlobalTheory_UnifDataTest_relab_conj

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
theorem _root_.solution (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) (τ : E →+* ℂ)
    (hτ : relab c σ τ ∈ (U.X k).Ψ) (i : ℕ) (hi : i < (U.X k).p0) (hr : (U.X k).p0 - 1 - i < r) :
    laU U a n k ⟨_, hτ⟩ ⟨_, hr⟩ = -(a (conjEmb τ, i) : ℤ) - (n / 2 : ℕ) := by
  have h1 : ¬ (U.X k).p0 ≤ (U.X k).p0 - 1 - i := by omega
  have h2 : (U.X k).p0 - 1 - ((U.X k).p0 - 1 - i) = i := by omega
  simp only [laU, h1, if_false, h2, ← relab_conj, Function.leftInverse_invFun (relab_bijective c σ).1 (conjEmb τ)]
end GlobalTheory.UnifDataTest
