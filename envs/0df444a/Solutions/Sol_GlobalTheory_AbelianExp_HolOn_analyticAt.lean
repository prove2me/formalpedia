-- Prove2me | solution 1 for GlobalTheory.AbelianExp.HolOn.analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:35:03.686532+00:00
-- url     : https://prove2.me/submissions/32de36f8-4fd1-496e-a08c-57bafd28cacf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ContinuousOnValue
import Theorems.Thm_GlobalTheory_SCV_analyticAt_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.AbelianExp
attribute [local instance] pointTopology
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E'] {W : Set E} {X Y : Over (Sp ℂ)} {a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)}
namespace GlobalTheory.AbelianExp
namespace HolOn
theorem _root_.solution [FiniteDimensional ℂ E] (h : HolOn W a) {g : ℕ} {U : X.left.Opens}
    (t : Fin g → Γ(X.left, U)) {w : E} (hw : w ∈ W) (hU : ⊤ ≤ (a w).left ⁻¹ᵁ U) :
    AnalyticAt ℂ (fun w i => valAt' (a w).left U (t i)) w := by
  rw [analyticAt_pi_iff]
  intro i
  exact GlobalTheory.SCV.analyticAt_of_differentiableOn (h U (t i)).2 ((h U (t i)).1.mem_nhds ⟨hw, hU⟩)
end HolOn
end GlobalTheory.AbelianExp
