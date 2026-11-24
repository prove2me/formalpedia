-- Prove2me | solution 1 for GlobalTheory.EigenLattice.sat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:25:05.181161+00:00
-- url     : https://prove2.me/submissions/d11745e2-16b9-41ff-90ee-c0f3633b5f9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralSecond

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.EigenLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}
namespace GlobalTheory.EigenLattice
theorem _root_.solution (ρ : orderC c →+* Module.End O H) (σ : E →+* K) : IsSat (eigLat ρ σ) := by
  intro x h hx hxh
  have hK : (algebraMap O K x) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hx
  show inK K H h ∈ eigK ρ σ
  have h1 : inK K H (x • h) ∈ eigK ρ σ := hxh
  rw [map_smul, ← algebraMap_smul K] at h1
  have := (eigK ρ σ).smul_mem (algebraMap O K x)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hK, one_smul] at this
end GlobalTheory.EigenLattice
