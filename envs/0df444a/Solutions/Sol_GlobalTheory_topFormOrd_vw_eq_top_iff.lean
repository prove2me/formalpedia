-- Prove2me | solution 1 for GlobalTheory.topFormOrd_vw_eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:35.953695+00:00
-- url     : https://prove2.me/submissions/8a15ee63-3ac7-49c8-85d6-75072dadd96b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_GlobalTheory_ordTop_vw_eq_top_iff
import Theorems.Thm_GlobalTheory_topFormCoeff_smul_topFormGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (V : Type*) {F : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
  [Algebra V F] [IsFractionRing V F]
variable {V}
variable (F) {K : Type*} [CommRing K] [Algebra K V] [Algebra K F] [IsScalarTower K V F] {n : ℕ}
variable {F} (b : Basis (Fin n) V Ω[V⁄K])
namespace GlobalTheory
theorem _root_.solution (ω : ⋀[F]^n Ω[F⁄K]) : topFormOrd_vw F b ω = ⊤ ↔ ω = 0 := by
  rw [topFormOrd_vw, ordTop_vw_eq_top_iff]
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  rw [← topFormCoeff_smul_topFormGen b ω, h, zero_smul]
end GlobalTheory
