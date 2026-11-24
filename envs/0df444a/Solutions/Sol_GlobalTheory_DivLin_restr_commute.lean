-- Prove2me | solution 1 for GlobalTheory.DivLin.restr_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:04:38.681898+00:00
-- url     : https://prove2.me/submissions/84470d92-13df-4577-952f-62df4badab15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScaledRestrictionEndomorphisms
import Theorems.Thm_GlobalTheory_DivLin_inK_injective_of_free
import Theorems.Thm_GlobalTheory_DivLin_inK_apply_end
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
theorem _root_.solution {D : O} {N : Module.End K (K ⊗[O] H)} {M : Module.End O H} (f : Module.End O H)
    (hM : IsScaledRestr D N M) (h : Commute N (f.baseChange K)) : Commute M f := by
  ext x; apply inK_injective_of_free (O := O) K H
  simp only [Module.End.mul_apply]
  rw [hM, inK_apply_end, inK_apply_end, hM, map_smul]
  congr 1
  exact LinearMap.congr_fun h.eq _
end GlobalTheory.DivLin
