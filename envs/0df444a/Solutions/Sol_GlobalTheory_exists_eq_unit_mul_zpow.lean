-- Prove2me | solution 1 for GlobalTheory.exists_eq_unit_mul_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:02.479681+00:00
-- url     : https://prove2.me/submissions/bc60ce4c-5ad2-4e12-b59b-99b005422530

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
variable (V : Type*) {F : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
  [Algebra V F] [IsFractionRing V F]
variable {V}
namespace GlobalTheory
theorem _root_.solution {t : V} (ht : Irreducible t) {f : F} (hf : f ≠ 0) :
    ∃ (m : ℤ) (u : Vˣ), f = algebraMap V F u * algebraMap V F t ^ m := by
  obtain ⟨m, u, h⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible ht hf
  exact ⟨m, u, by rw [h, Units.smul_def, Algebra.smul_def]⟩
end GlobalTheory
