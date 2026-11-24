-- Prove2me | solution 1 for GlobalTheory.EigenLattice.exists_ne_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:25:01.30039+00:00
-- url     : https://prove2.me/submissions/aeecba8e-03fd-4940-a3e9-53330a1eb144

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
theorem _root_.solution (ρ : orderC c →+* Module.End O H) (σ : E →+* K) (h1 : Module.finrank K (eigK ρ σ) = 1) :
    ∃ g : H, g ≠ 0 ∧ g ∈ eigLat ρ σ := by
  have : Nontrivial (eigK ρ σ) := Module.nontrivial_of_finrank_eq_succ h1
  obtain ⟨⟨v, hv⟩, hv0⟩ := _root_.exists_ne (0 : eigK ρ σ)
  have hv0' : v ≠ 0 := fun h => hv0 (by ext; simp [h])
  haveI : IsLocalizedModule (nonZeroDivisors O) (inK K H) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K (inK K H)).2 (TensorProduct.isBaseChange O H K)
  obtain ⟨⟨h, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors O) (inK K H) v
  have hsK : algebraMap O K (s : O) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (nonZeroDivisors.ne_zero s.2)
  have hs' : inK K H h = algebraMap O K (s : O) • v := by
    simp only at hs; rw [← hs, Submonoid.smul_def, algebraMap_smul]
  refine ⟨h, ?_, ?_⟩
  · intro h0; rw [h0, map_zero] at hs'; exact (smul_ne_zero hsK hv0') hs'.symm
  · show inK K H h ∈ eigK ρ σ
    rw [hs']; exact (eigK ρ σ).smul_mem _ hv
end GlobalTheory.EigenLattice
