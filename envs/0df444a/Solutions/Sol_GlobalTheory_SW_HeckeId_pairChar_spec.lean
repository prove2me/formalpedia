-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.pairChar_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:58:40.767808+00:00
-- url     : https://prove2.me/submissions/b6c28123-5b11-4d1f-ba96-f345344f6753

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_HeckeId_int_of_eT
import Theorems.Thm_GlobalTheory_SW_Nbr_cc_cc
import Theorems.Thm_GlobalTheory_SW_Nbr_co_co
import Theorems.Thm_GlobalTheory_SW_Nbr_coe_co
import Theorems.Thm_GlobalTheory_SW_Nbr_good_conj
import Theorems.Thm_GlobalTheory_SW_Nbr_herm_sr
import Theorems.Thm_GlobalTheory_SW_Nbr_int_move
import Theorems.Thm_GlobalTheory_SW_Nbr_mem_conjI


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
open Nbr
variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ : Lt E n}
    (hS : SD Λ) {b : 𝓞 E} (hb : b ∈ conjI P) (u : X →ₗ[𝓞 E] (Fin n → E))
    (hQ : ∀ c ∈ conjI P, ∀ ξ, u (c • ξ) ∈ Λ) (η : X) :
    (∀ c ∈ P, ∀ ξ, pairChar u b η (c • ξ) = 1) ∧
      ((∀ ξ, pairChar u b η ξ = 1) ↔ ∀ ξ, Int' (u η) (u (b • ξ))) := by
  have k : ∀ c ∈ conjI P, ∀ ξ, Int' (c • u η) (u (b • ξ)) := fun c hc ξ => by
    rw [← map_smul]; exact (hS _).1 (hQ c hc η) _ (hQ b hb ξ)
  refine ⟨fun c hc ξ => eT_int ?_, fun H ξ => int_of_eT hP.1 hP.2.2.2.2 ?_ fun c => ?_,
    fun H ξ => eT_int (H ξ)⟩
  · have := (int_move _ _ _).1 (k (co c) (mem_conjI.2 (by rwa [co_co])) ξ)
    rwa [co_co, ← map_smul, smul_comm] at this
  · have := k (q : ℕ) ((good_conj hP).2.2.1 ▸ Ideal.absNorm_mem _) ξ
    unfold Int' at this
    rw [osmul, herm_sl] at this
    exact this
  · have : eT (herm 1 (u η) (u (b • co c • ξ))) = 1 := H (co c • ξ)
    rwa [smul_comm, map_smul, osmul, herm_sr, coe_co, cc_cc] at this
end GlobalTheory.SW.HeckeId
