-- Prove2me | solution 1 for GlobalTheory.HolHom.holAt_of_isHolTo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:25.678804+00:00
-- url     : https://prove2.me/submissions/9ff26d22-be0c-49ee-887a-9e00d9b77331

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
theorem _root_.solution {B : Set V} {c : V → (Sp ℂ ⟶ X)} (h : IsHolTo B c) {z : V} (hz : z ∈ B) : HolAt c z := by
  intro U hU
  have hn : {b ∈ B | ⊤ ≤ c b ⁻¹ᵁ U} ∈ 𝓝 z := (h U 0).1.mem_nhds ⟨hz, hU⟩
  exact ⟨mem_of_superset hn fun t ht => ht.2, fun f => (h U f).2.differentiableAt hn⟩
end GlobalTheory.HolHom
