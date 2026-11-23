-- Prove2me | solution 1 for GlobalTheory.HolHom.isHolTo_of_holAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:26.288954+00:00
-- url     : https://prove2.me/submissions/5bb7ece1-8f0f-4ea6-b495-9e5fc87d9e4a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolHom
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
namespace GlobalTheory.HolHom
theorem _root_.solution {B : Set V} {c : V → (Sp ℂ ⟶ X)} (hB : IsOpen B) (h : ∀ z ∈ B, HolAt c z) :
    IsHolTo B c := by
  intro U f
  refine ⟨isOpen_iff_mem_nhds.2 fun z hz => ?_, fun z hz => ((h z hz.1 U hz.2).2 f).differentiableWithinAt⟩
  filter_upwards [hB.mem_nhds hz.1, (h z hz.1 U hz.2).1] with t h1 h2 using ⟨h1, h2⟩
end GlobalTheory.HolHom
