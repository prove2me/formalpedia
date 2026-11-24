-- Prove2me | solution 1 for GlobalTheory.mem_regForms_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:35:30.179832+00:00
-- url     : https://prove2.me/submissions/d5afb53c-d47a-4585-a74b-5289af738fbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_P2M_GlobalTheory_eq_lift_det_smul__Multi_7c34f112c031

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
omit [IsDomain V] [IsDiscreteValuationRing V]
namespace GlobalTheory
theorem _root_.solution (ω : ⋀[F]^n Ω[F⁄K]) :
    ω ∈ regForms K V F n ↔ ∃ a : V, ω = a • topFormGen F b := by
  constructor
  · rintro ⟨η, rfl⟩
    refine ⟨exteriorPower.alternatingMapLinearEquiv b.det η, ?_⟩
    rw [topFormGen, ← map_smul, ← eq_lift_det_smul_ιMulti]
  · rintro ⟨a, rfl⟩
    exact Submodule.smul_mem _ _ ⟨_, rfl⟩
end GlobalTheory
