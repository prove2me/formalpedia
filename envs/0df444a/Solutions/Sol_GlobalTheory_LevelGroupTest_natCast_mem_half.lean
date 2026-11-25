-- Prove2me | solution 1 for GlobalTheory.LevelGroupTest.natCast_mem_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:01:11.774081+00:00
-- url     : https://prove2.me/submissions/c3fc4052-3515-49a0-ab09-9333c9b4c5b2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LiftLaSpec
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_LevelGroupEqTopOfCoprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevelGroupTest
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
namespace GlobalTheory.LevelGroupTest
theorem _root_.solution (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := by
    rw [← l.prod]; exact Ideal.mul_le_left
  exact h (Ideal.subset_span rfl)
end GlobalTheory.LevelGroupTest
