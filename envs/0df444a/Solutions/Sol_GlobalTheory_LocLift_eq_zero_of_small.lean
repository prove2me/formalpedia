-- Prove2me | solution 1 for GlobalTheory.LocLift.eq_zero_of_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:46:55.791043+00:00
-- url     : https://prove2.me/submissions/b5b069f9-c4df-482d-9102-299c7d262ecb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Q : Type} [Group Q]
namespace GlobalTheory.LocLift
theorem _root_.solution {T : Type} [TopologicalSpace T] {B : Set T} (hB : IsPreconnected B) {d : T → W}
    (hd : ContinuousOn d B) {r : ℝ} (hr : 0 < r) (h : ∀ b ∈ B, ‖d b‖ < r → d b = 0) {b₀ : T} (hb₀ : b₀ ∈ B)
    (h0 : d b₀ = 0) : ∀ b ∈ B, d b = 0 := by
  intro b hb
  refine h b hb (not_le.1 fun hle => ?_)
  obtain ⟨c, hc, hc'⟩ := hB.intermediate_value hb₀ hb hd.norm
    (show r / 2 ∈ Set.Icc ‖d b₀‖ ‖d b‖ from ⟨by rw [h0, norm_zero]; positivity, by linarith⟩)
  have hc'' : ‖d c‖ = r / 2 := hc'
  have := h c hc (by linarith)
  rw [this, norm_zero] at hc''
  linarith
end GlobalTheory.LocLift
