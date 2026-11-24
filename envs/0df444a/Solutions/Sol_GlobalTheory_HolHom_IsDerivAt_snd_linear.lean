-- Prove2me | solution 1 for GlobalTheory.HolHom.IsDerivAt.snd_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:36:09.020311+00:00
-- url     : https://prove2.me/submissions/d71ad81e-b375-4e23-9db2-44e73949dd6e

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory.HolHom
namespace IsDerivAt
theorem _root_.solution {X : Scheme.{0}} {c : V → (Sp ℂ ⟶ X)} {z w₁ w₂ : V} {a₁ a₂ : ℂ}
    {v₁ v₂ v : Sp (DualNumber ℂ) ⟶ X} (h₁ : IsDerivAt c z w₁ v₁) (h₂ : IsDerivAt c z w₂ v₂)
    (h : IsDerivAt c z (a₁ • w₁ + a₂ • w₂) v) (U : X.Opens) (hU : ⊤ ≤ c z ⁻¹ᵁ U) (f : Γ(X, U)) :
    TrivSqZeroExt.snd (valR v U f) = a₁ * TrivSqZeroExt.snd (valR v₁ U f) + a₂ * TrivSqZeroExt.snd (valR v₂ U f) := by
  rw [h.2 U hU, h₁.2 U hU, h₂.2 U hU, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
end IsDerivAt
end GlobalTheory.HolHom
