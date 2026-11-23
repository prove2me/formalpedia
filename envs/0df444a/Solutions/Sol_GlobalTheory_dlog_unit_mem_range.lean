-- Prove2me | solution 1 for GlobalTheory.dlog_unit_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:00.854256+00:00
-- url     : https://prove2.me/submissions/212bc940-f3cb-4642-9abe-218b7711107a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent

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
variable (K : Type*) {F : Type*} [CommRing K] [Field F] [Algebra K F] {p : ℕ}
variable {V : Type*} [CommRing V] [Algebra K V] [Algebra V F] [IsScalarTower K V F]
namespace GlobalTheory
theorem _root_.solution (u : Vˣ) :
    (algebraMap V F u)⁻¹ • D K F (algebraMap V F u)
      ∈ LinearMap.range (KaehlerDifferential.map K K V F) := by
  refine ⟨((u⁻¹ : Vˣ) : V) • D K V u, ?_⟩
  rw [map_smul, map_D, ← map_units_inv, algebraMap_smul]
end GlobalTheory
