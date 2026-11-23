-- Prove2me | solution 1 for GlobalTheory.HolHom.HolAt.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:32.205801+00:00
-- url     : https://prove2.me/submissions/875eb8a1-1531-4252-a3a5-6f2476570ae1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_valR_comp

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
namespace HolAt
theorem _root_.solution {Y : Scheme.{0}} {c : V → (Sp ℂ ⟶ X)} {z : V} (h : HolAt c z) (φ : X ⟶ Y) :
    HolAt (fun t => c t ≫ φ) z := by
  intro U hU
  refine ⟨(h (φ ⁻¹ᵁ U) hU).1, fun f => ?_⟩
  simp only [valAt'_eq_valR, valR_comp]
  exact (h (φ ⁻¹ᵁ U) hU).2 _
end HolAt
end GlobalTheory.HolHom
