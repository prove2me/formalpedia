-- Prove2me | solution 1 for GlobalTheory.CondAway.coordAt_rTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:56:07.731854+00:00
-- url     : https://prove2.me/submissions/c2a15e18-be13-45e8-a39a-57b67ebd5883

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentConductorIff
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
open GlobalTheory GlobalTheory.CondAway
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.CondAway
theorem _root_.solution (O : Type) [CommRing O] {K : Type} [Field K] [Algebra O K] {c c' : Ideal (OF E)} (s : E)
    (g : orderC c →ₗ[ℤ] orderC c') (hg : ∀ x, (g x : E) = s * x) (σ : E →+* K) (t : orderC c ⊗[ℤ] O) :
    coordAt O c' σ (g.rTensor O t) = σ s * coordAt O c σ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [LinearMap.rTensor_tmul]
    show σ (g a) * algebraMap O K x = σ s * (σ a * algebraMap O K x)
    rw [hg, map_mul, mul_assoc]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, mul_add]
end GlobalTheory.CondAway
