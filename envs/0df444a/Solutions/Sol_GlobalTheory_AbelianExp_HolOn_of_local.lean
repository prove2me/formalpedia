-- Prove2me | solution 1 for GlobalTheory.AbelianExp.HolOn.of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:35:04.503516+00:00
-- url     : https://prove2.me/submissions/8a900972-2728-4a2d-b87e-afac5b44301a

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
theorem _root_.solution
    (h : ∀ z, ∃ (W : Set E) (b : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)), z ∈ W ∧ HolOn W b ∧ a =ᶠ[𝓝 z] b)
    (U : X.left.Opens) (f : Γ(X.left, U)) : IsOpen {z | ⊤ ≤ (a z).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (a z).left U f) {z | ⊤ ≤ (a z).left ⁻¹ᵁ U} := by
  have key : ∀ z, ⊤ ≤ (a z).left ⁻¹ᵁ U → {z | ⊤ ≤ (a z).left ⁻¹ᵁ U} ∈ 𝓝 z ∧
      DifferentiableAt ℂ (fun z => valAt' (a z).left U f) z := by
    intro z hzU
    obtain ⟨W', b, hzW, hb, hab⟩ := h z
    have hbz : b z = a z := hab.self_of_nhds.symm
    have hmem : z ∈ {w | w ∈ W' ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U} := ⟨hzW, by rw [hbz]; exact hzU⟩
    have hN := (hb U f).1.mem_nhds hmem
    constructor
    · filter_upwards [hN, hab] with y hy hy'
      show ⊤ ≤ (a y).left ⁻¹ᵁ U
      rw [hy']
      exact hy.2
    · refine ((hb U f).2.differentiableAt hN).congr_of_eventuallyEq ?_
      filter_upwards [hab] with y hy
      rw [hy]
  exact ⟨isOpen_iff_mem_nhds.2 fun z hz => (key z hz).1,
    fun z hz => (key z hz).2.differentiableWithinAt⟩
end HolOn
end GlobalTheory.AbelianExp
