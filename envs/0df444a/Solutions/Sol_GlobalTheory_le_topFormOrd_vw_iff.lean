-- Prove2me | solution 1 for GlobalTheory.le_topFormOrd_vw_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:53:05.187804+00:00
-- url     : https://prove2.me/submissions/a948f567-3a8d-4667-8337-d5b0150c096b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_GlobalTheory_le_ordTop_vw_iff
import Theorems.Thm_GlobalTheory_topFormCoeff_topFormGen
import Theorems.Thm_GlobalTheory_topFormCoeff_smul_topFormGen
import Theorems.Thm_GlobalTheory_mem_regForms_iff
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15


attribute [local simp] GlobalTheory.topFormCoeff_topFormGen

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
theorem _root_.solution {t : V} (ht : Irreducible t) (m : ℤ) (ω : ⋀[F]^n Ω[F⁄K]) :
    (m : WithTop ℤ) ≤ topFormOrd_vw F b ω ↔
      ∃ η ∈ regForms K V F n, ω = algebraMap V F t ^ m • η := by
  rw [topFormOrd_vw, le_ordTop_vw_iff ht]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨_, (mem_regForms_iff b _).mpr ⟨a, rfl⟩, ?_⟩
    rw [← algebraMap_smul F a, smul_smul, ← ha, topFormCoeff_smul_topFormGen]
  · rintro ⟨η, hη, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_regForms_iff b η).mp hη
    exact ⟨a, by rw [← algebraMap_smul F a, smul_smul, map_smul, topFormCoeff_topFormGen,
      smul_eq_mul, mul_one]⟩
end GlobalTheory
