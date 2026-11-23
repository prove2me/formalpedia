-- Prove2me | solution 1 for GlobalTheory.SelfCube.exists_glue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:43.437734+00:00
-- url     : https://prove2.me/submissions/67e598a7-ec84-4a94-b0cc-6eb672764de4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube

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
noncomputable section
open GlobalTheory GlobalTheory.SelfCube
namespace GlobalTheory.SelfCube
theorem _root_.solution {g : ℕ} {J : Type*} (D : J → Set (Fin g → ℂ))
    (G : J → (Fin g → ℂ) → ℂ) (hD : ∀ j, IsOpen (D j)) (hcov : ∀ z, ∃ j, z ∈ D j)
    (hG : ∀ j, DifferentiableOn ℂ (G j) (D j))
    (hc : ∀ j j' z, z ∈ D j → z ∈ D j' → G j z = G j' z) :
    ∃ F : (Fin g → ℂ) → ℂ, Differentiable ℂ F ∧ ∀ j z, z ∈ D j → F z = G j z := by
  choose c hc' using hcov
  refine ⟨fun z => G (c z) z, fun z => ?_, fun j z hz => hc _ _ _ (hc' z) hz⟩
  have hev : (fun w => G (c w) w) =ᶠ[𝓝 z] G (c z) := by
    filter_upwards [(hD (c z)).mem_nhds (hc' z)] with w hw using hc _ _ _ (hc' w) hw
  exact ((hG (c z)).differentiableAt ((hD (c z)).mem_nhds (hc' z))).congr_of_eventuallyEq hev
end GlobalTheory.SelfCube
