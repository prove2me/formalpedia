-- Prove2me | solution 1 for GlobalTheory.LowerOps.ext_of_eigLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:52:04.711733+00:00
-- url     : https://prove2.me/submissions/0fb45d8e-2edc-4810-bb3b-5a23d5cbe5ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodConjugateIntegral
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.LowerOps
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}
namespace GlobalTheory.LowerOps
theorem _root_.solution [IsDomain O] [IsFractionRing O K] (ρ : orderC c →+* Module.End O H) (D : O) (hD : D ≠ 0)
    (hsum : ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat (K := K) ρ σ) (S T : Module.End K (K ⊗[O] H))
    (hST : ∀ σ : E →+* K, ∀ y ∈ eigLat (K := K) ρ σ, S (inK K H y) = T (inK K H y)) : S = T := by
  have hD' : algebraMap O K D ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hD
  have hsub : ∀ y ∈ ⨆ σ : E →+* K, eigLat (K := K) ρ σ, S (inK K H y) = T (inK K H y) := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem σ y hy => exact hST σ y hy
    | zero => simp
    | add y z _ _ hy hz => simp [map_add, hy, hz]
  have hH : ∀ h : H, S (inK K H h) = T (inK K H h) := by
    intro h
    have h1 : inK (O := O) K H (D • h) = algebraMap O K D • inK (O := O) K H h := by
      rw [map_smul, algebraMap_smul K D (inK K H h)]
    have h2 := hsub _ (hsum h)
    rw [h1, map_smul, map_smul] at h2
    exact smul_right_injective _ hD' h2
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul k h =>
    have : k ⊗ₜ[O] h = k • inK K H h := by simp [inK, TensorProduct.smul_tmul']
    rw [this, map_smul, map_smul, hH]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
end GlobalTheory.LowerOps
