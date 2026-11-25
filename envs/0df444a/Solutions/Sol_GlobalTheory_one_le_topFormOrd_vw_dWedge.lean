-- Prove2me | solution 1 for GlobalTheory.one_le_topFormOrd_vw_dWedge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:58:44.297236+00:00
-- url     : https://prove2.me/submissions/400b51ea-1325-4f26-99c0-28fa1632ec42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_GlobalTheory_exists_dWedge_eq_smul_regForms
import Theorems.Thm_GlobalTheory_le_topFormOrd_vw_iff

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
theorem _root_.solution (x : Fin n → V) {i j : Fin n} (hij : i ≠ j)
    (hi : x i ∈ maximalIdeal V) (hj : x j ∈ maximalIdeal V) :
    1 ≤ topFormOrd_vw F b (dWedge K fun k => algebraMap V F (x k)) := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  rw [ht.maximalIdeal_eq, Ideal.mem_span_singleton] at hi hj
  obtain ⟨η, hη, h⟩ := exists_dWedge_eq_smul_regForms K F t x hij hi hj
  exact (le_topFormOrd_vw_iff b ht 1 _).mpr ⟨η, hη, by rw [h, zpow_one, algebraMap_smul]⟩
end GlobalTheory
