-- Prove2me | solution 1 for GlobalTheory.PullHermitian.exists_glue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:05.623896+00:00
-- url     : https://prove2.me/submissions/832e74f7-bbda-4f10-836d-c823316e203c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.PullHermitian
namespace GlobalTheory.PullHermitian
theorem _root_.solution {E κ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (V : κ → Set E)
    (hV : ∀ i, IsOpen (V i)) (hc : ∀ z, ∃ i, z ∈ V i) (φ : κ → E → ℂ)
    (hφ : ∀ i, DifferentiableOn ℂ (φ i) (V i))
    (ha : ∀ i j z, z ∈ V i → z ∈ V j → φ i z = φ j z) :
    ∃ r : E → ℂ, Differentiable ℂ r ∧ ∀ i z, z ∈ V i → r z = φ i z := by
  choose c hc using hc
  have hr : ∀ i z, z ∈ V i → φ (c z) z = φ i z := fun i z hz => ha _ _ z (hc z) hz
  refine ⟨fun z => φ (c z) z, fun z => ?_, hr⟩
  have hn := (hV (c z)).mem_nhds (hc z)
  exact ((hφ (c z)).differentiableAt hn).congr_of_eventuallyEq
    (Filter.mem_of_superset hn fun y hy => hr _ y hy)
end GlobalTheory.PullHermitian
