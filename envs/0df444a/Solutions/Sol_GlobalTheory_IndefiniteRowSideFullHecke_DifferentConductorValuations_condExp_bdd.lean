-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.condExp_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:55:07.881164+00:00
-- url     : https://prove2.me/submissions/5862b23b-488a-4931-bbec-28ccb1879ae9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
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
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
theorem _root_.solution (𝔣 : Ideal (OF E)) {l : ℕ} (hl : l ≠ 0) :
    BddAbove (expIn 𝔣 '' {v : HeightOneSpectrum (OF E) | (l : OF E) ∈ v.asIdeal}) := by
  refine (Set.Finite.image _ ?_).bddAbove
  have h : Ideal.span {(l : OF E)} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hl
  refine (Ideal.finite_factors h).subset fun v hv => ?_
  simpa [Ideal.dvd_span_singleton] using hv
end GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
