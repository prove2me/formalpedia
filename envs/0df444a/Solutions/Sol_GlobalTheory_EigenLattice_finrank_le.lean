-- Prove2me | solution 1 for GlobalTheory.EigenLattice.finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:25:02.414853+00:00
-- url     : https://prove2.me/submissions/2533ad62-4d6d-45e6-bf73-58856d1e400e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralSecond
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
open GlobalTheory GlobalTheory.EigenLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}
namespace GlobalTheory.EigenLattice
theorem _root_.solution [Module.Free O H] [Module.Finite O H] (ρ : orderC c →+* Module.End O H) (σ : E →+* K)
    (h1 : Module.finrank K (eigK ρ σ) = 1) : Module.finrank O (eigLat ρ σ) ≤ 1 := by
  haveI : Module.Flat O K := IsLocalization.flat K (nonZeroDivisors O)
  haveI : Module.Finite K (eigK ρ σ) := Module.finite_of_finrank_eq_succ h1
  set N := eigLat ρ σ
  have hinj : Function.Injective (N.subtype.baseChange K) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ N.injective_subtype
  have hmem : ∀ z, N.subtype.baseChange K z ∈ eigK ρ σ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k n =>
      rw [LinearMap.baseChange_tmul]
      have hn : inK K H (n : H) ∈ eigK ρ σ := n.2
      have : k ⊗ₜ[O] (N.subtype n) = k • inK K H (n : H) := by
        simp [inK, TensorProduct.smul_tmul']
      rw [this]; exact (eigK ρ σ).smul_mem k hn
    | add x y hx hy => rw [map_add]; exact (eigK ρ σ).add_mem hx hy
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := (N.subtype.baseChange K).codRestrict (eigK ρ σ) hmem)
    (fun a b hab => hinj (by simpa using congrArg Subtype.val hab))
  rw [Module.finrank_baseChange, h1] at hle
  exact hle
end GlobalTheory.EigenLattice
