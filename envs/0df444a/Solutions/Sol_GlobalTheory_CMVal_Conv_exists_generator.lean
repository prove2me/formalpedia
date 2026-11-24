-- Prove2me | solution 1 for GlobalTheory.CMVal.Conv.exists_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:03:59.59947+00:00
-- url     : https://prove2.me/submissions/651e5eef-c675-4cc4-b928-562e81a3f2b4

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CountableIdealSummableAbsNormRpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIntegersOfMemHatO
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
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Conv
variable {E : Type} [Field E] [NumberField E]
omit [NumberField E]
namespace GlobalTheory.CMVal.Conv
theorem _root_.solution : ∃ g : Ideal (𝓞 E) → 𝓞 E, ∀ b : 𝓞 E, ∃ u : (𝓞 E)ˣ, g (Ideal.span {b}) * u = b := by
  classical
  refine ⟨fun I => if h : ∃ b, Ideal.span {b} = I then h.choose else 0, fun b => ?_⟩
  have h : ∃ b', Ideal.span {b'} = Ideal.span {b} := ⟨b, rfl⟩
  simp only [dif_pos h]
  exact Ideal.span_singleton_eq_span_singleton.1 h.choose_spec
end GlobalTheory.CMVal.Conv
