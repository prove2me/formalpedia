-- Prove2me | solution 1 for GlobalTheory.HolHom.isDerivAt0_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:49:50.186253+00:00
-- url     : https://prove2.me/submissions/c820618b-fb95-43cd-bd12-1a36b9d92b72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_le_preimage_dual_iff

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
theorem _root_.solution {g : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 e w v ↔ IsDerivAt e 0 w v := by
  refine and_congr_right fun h => forall_congr' fun U => ?_
  constructor
  · intro H hU f
    have hv := (le_preimage_dual_iff h U).2 hU
    rw [valR_eq _ _ hv]
    exact H hv f
  · intro H hv f
    have := H ((le_preimage_dual_iff h U).1 hv) f
    rw [valR_eq _ _ hv] at this
    exact this
end GlobalTheory.HolHom
