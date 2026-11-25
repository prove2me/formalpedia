-- Prove2me | solution 1 for GlobalTheory.AbelianExp.HolOn.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:33:27.455989+00:00
-- url     : https://prove2.me/submissions/cefee10e-cd45-42f1-a646-ca1e2895d7f6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ContinuousOnValue

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
theorem _root_.solution (h : HolOn W a) {W' : Set E'} (hW' : IsOpen W') {φ : E' → E}
    (hφ : DifferentiableOn ℂ φ W') (hm : Set.MapsTo φ W' W) : HolOn W' fun w => a (φ w) := by
  intro U f
  have hset : {w | w ∈ W' ∧ ⊤ ≤ (a (φ w)).left ⁻¹ᵁ U} =
      W' ∩ φ ⁻¹' {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} := by
    ext w
    constructor
    · rintro ⟨hw, hU⟩
      exact ⟨hw, hm hw, hU⟩
    · rintro ⟨hw, -, hU⟩
      exact ⟨hw, hU⟩
  rw [hset]
  exact ⟨hφ.continuousOn.isOpen_inter_preimage hW' (h U f).1,
    (h U f).2.comp (hφ.mono Set.inter_subset_left) (fun w hw => hw.2)⟩
end HolOn
end GlobalTheory.AbelianExp
