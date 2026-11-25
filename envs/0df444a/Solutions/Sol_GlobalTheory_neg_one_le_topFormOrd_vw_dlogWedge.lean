-- Prove2me | solution 1 for GlobalTheory.neg_one_le_topFormOrd_vw_dlogWedge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:58:42.628675+00:00
-- url     : https://prove2.me/submissions/7e42e7a6-bdf1-4c29-9dde-1f48528bc5f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_GlobalTheory_smul_dlogWedge_mem_regForms
import Theorems.Thm_GlobalTheory_exists_eq_unit_mul_zpow
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
theorem _root_.solution (S : Finset (Fin n)) (x : Fin n → F)
    (hS : ∀ k ∈ S, x k ≠ 0) (hS' : ∀ k ∉ S, x k ∈ Set.range (algebraMap V F)) :
    ((-1 : ℤ) : WithTop ℤ) ≤ topFormOrd_vw F b (dlogWedge K S x) := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  have h₀ : algebraMap V F t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V F)).mpr ht.ne_zero
  refine (le_topFormOrd_vw_iff b ht (-1) _).mpr ⟨_, smul_dlogWedge_mem_regForms K t h₀ S x
    (fun k hk => exists_eq_unit_mul_zpow ht (hS k hk)) hS', ?_⟩
  rw [← algebraMap_smul F t, smul_smul, zpow_neg_one, inv_mul_cancel₀ h₀, one_smul]
end GlobalTheory
