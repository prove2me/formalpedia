-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.mem_coeffKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:46:20.974699+00:00
-- url     : https://prove2.me/submissions/53c1639c-143a-4568-9aa8-b6336a8dc00a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Filter Topology MeasureTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (hρ : IsSmooth ρ) {ℓt : Module.Dual ℂ (smoothVectors (Representation.dual ρ))}
    {k : locallyConstantCompactSupport G ℂ ℂ} :
    k ∈ coeffKer μ hρ ℓt ↔ ∀ ξ : smoothVectors (Representation.dual ρ),
      ℓt (coeffL μ hρ (ξ : Module.Dual ℂ V) k) = 0 :=
  Iff.rfl
end GroundTheory.Automorphic.Whittaker
