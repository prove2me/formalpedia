-- Prove2me | solution 1 for GlobalTheory.TopForm.IsFreeGen.of_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:17.450976+00:00
-- url     : https://prove2.me/submissions/d44c001b-b09f-4e5f-94bb-5f82f604cafc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
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



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
namespace GlobalTheory.TopForm
namespace IsFreeGen
theorem _root_.solution {φ : M →ₗ[A] N} (hφ : IsBaseChange B φ) {ω : M}
    (h : IsFreeGen A ω) : IsFreeGen B (φ ω) := by
  let e : A ≃ₗ[A] M := LinearEquiv.ofBijective (LinearMap.toSpanSingleton A M ω) h
  let e' : B ≃ₗ[B] N := (Algebra.TensorProduct.rid A B B).symm.toLinearEquiv ≪≫ₗ
    (e.baseChange A B A M) ≪≫ₗ hφ.equiv
  have : (fun b : B => b • φ ω) = e' := by
    funext b
    have he : e 1 = ω := one_smul A ω
    simp [e', he]
  rw [IsFreeGen, this]
  exact e'.bijective
end IsFreeGen
end GlobalTheory.TopForm
