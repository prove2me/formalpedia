-- Prove2me | solution 1 for GlobalTheory.UnifDataTest.relab_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:25.497199+00:00
-- url     : https://prove2.me/submissions/4d580058-e7ec-4754-8957-1b41898b3cd6

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
theorem _root_.solution (c : Coeff l) (σ : c.F →+* ℂ) : Function.Bijective (relab (E := E) c σ) := by
  refine Finite.injective_iff_bijective.1 fun τ τ' h => ?_
  ext a
  have h1 : σ (embF c τ a) = σ (embF c τ' a) := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective h1)
end GlobalTheory.UnifDataTest
