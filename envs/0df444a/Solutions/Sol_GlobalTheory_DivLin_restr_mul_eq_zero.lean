-- Prove2me | solution 1 for GlobalTheory.DivLin.restr_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:41:10.74592+00:00
-- url     : https://prove2.me/submissions/65b92da5-45b5-48bf-9e08-a14aaeee1e14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScaledRestrictionEndomorphisms
import Theorems.Thm_GlobalTheory_DivLin_inK_injective_of_free
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
theorem _root_.solution {D : O} {N N' : Module.End K (K ⊗[O] H)} {M M' : Module.End O H}
    (hM : IsScaledRestr D N M) (hM' : IsScaledRestr D N' M') (h : N * N' = 0) : M * M' = 0 := by
  ext x; apply inK_injective_of_free (O := O) K H
  simp only [Module.End.mul_apply, LinearMap.zero_apply, map_zero]
  rw [hM, hM', map_smul, ← Module.End.mul_apply N N', h]; simp
end GlobalTheory.DivLin
