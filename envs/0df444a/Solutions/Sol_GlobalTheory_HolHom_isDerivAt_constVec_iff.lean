-- Prove2me | solution 1 for GlobalTheory.HolHom.isDerivAt_constVec_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:42.290247+00:00
-- url     : https://prove2.me/submissions/2a0db895-eb57-4345-83c0-d3cabc457259

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_valR_spMap
import Theorems.Thm_GlobalTheory_HolHom_fst_constVec

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
theorem _root_.solution {c : V → (Sp ℂ ⟶ X)} {z w : V} : IsDerivAt c z w (constVec (c z)) ↔
    ∀ U : X.Opens, ⊤ ≤ c z ⁻¹ᵁ U → ∀ f : Γ(X, U), fderiv ℂ (fun t => valAt' (c t) U f) z w = 0 := by
  refine (and_iff_right (fst_constVec _)).trans (forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => ?_)
  rw [valR_spMap _ _ _ hU, eq_comm, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]
end GlobalTheory.HolHom
