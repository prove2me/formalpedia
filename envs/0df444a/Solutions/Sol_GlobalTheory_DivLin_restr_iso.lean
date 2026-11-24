-- Prove2me | solution 1 for GlobalTheory.DivLin.restr_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:41:09.685685+00:00
-- url     : https://prove2.me/submissions/9a360d1b-b1a4-476c-8d51-db3706ffc2c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScaledRestrictionEndomorphisms
import Theorems.Thm_GlobalTheory_DivLin_algebraMap_bilin
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
open GlobalTheory GlobalTheory.DivLin
variable {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
  {H : Type} [AddCommGroup H] [Module O H]
variable [Module.Free O H]
namespace GlobalTheory.DivLin
theorem _root_.solution {D : O} {N N' : Module.End K (K ⊗[O] H)} {M M' : Module.End O H} (B : LinearMap.BilinForm O H)
    (hM : IsScaledRestr D N M) (hM' : IsScaledRestr D N' M') (h : ∀ x y, B.baseChange K (N x) (N' y) = 0) (x y : H) :
    B (M x) (M' y) = 0 := by
  apply IsFractionRing.injective O K
  rw [algebraMap_bilin, hM, hM', map_zero]
  simp only [map_smul, LinearMap.smul_apply, h, smul_zero]
end GlobalTheory.DivLin
