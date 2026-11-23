-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.exists_place
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:00:03.200719+00:00
-- url     : https://prove2.me/submissions/8b33e02f-2150-450d-955c-189388768725

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
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
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Model
namespace GlobalTheory.CMVal.Model
theorem _root_.solution : ∃ v : HeightOneSpectrum (OF K), ((43 : ℕ) : OF K) ∈ v.asIdeal := by
  haveI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  have hmax : (Ideal.span {((43 : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 43
  obtain ⟨⟨P, hP, hl⟩⟩ := (Ideal.span {((43 : ℕ) : ℤ)}).nonempty_primesOver (S := OF K)
  refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {((43 : ℕ) : ℤ)}) (by simp) P⟩, ?_⟩
  have : ((43 : ℕ) : ℤ) ∈ P.under ℤ := hl.over ▸ Ideal.mem_span_singleton_self _
  simpa [Ideal.mem_comap] using this
end GlobalTheory.CMVal.Model
