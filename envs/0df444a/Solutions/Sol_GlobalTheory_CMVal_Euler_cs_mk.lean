-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.cs_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:22:37.136525+00:00
-- url     : https://prove2.me/submissions/71c30937-c56f-4876-91bc-db9e7bd8b645

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
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
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {G : Type} [CommGroup G] (U : Subgroup G) (ω : G →* ℂ)
variable {U ω}
namespace GlobalTheory.CMVal.Euler
theorem _root_.solution (hω : ∀ u ∈ U, ω u = 1) {M : Set G} (hM : Stable U M) (y : G) :
    cs U ω M (QuotientGroup.mk y) = M.indicator ω y := by
  classical
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U y
  unfold cs
  rw [hu, Set.indicator_apply, Set.indicator_apply, map_mul, hω u u.2, mul_one]
  simp only [hM u u.2 y]
end GlobalTheory.CMVal.Euler
