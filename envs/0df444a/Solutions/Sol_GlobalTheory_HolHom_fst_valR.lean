-- Prove2me | solution 1 for GlobalTheory.HolHom.fst_valR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:22.708042+00:00
-- url     : https://prove2.me/submissions/92f62f99-a0ac-42c1-ab6b-5df441e5ee7b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_valR_spMap
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
theorem _root_.solution {v : Sp (DualNumber ℂ) ⟶ X} {x : Sp ℂ ⟶ X}
    (h : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = x) {U : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    TrivSqZeroExt.fst (valR v U f) = valAt' x U f := by
  have := valR_spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom v U ((le_preimage_dual_iff h U).2 hU) f
  rw [h] at this
  exact this.symm
end GlobalTheory.HolHom
