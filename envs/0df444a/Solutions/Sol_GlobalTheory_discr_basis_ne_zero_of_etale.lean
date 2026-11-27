-- Prove2me | solution 1 for GlobalTheory.discr_basis_ne_zero_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:41:04.019528+00:00
-- url     : https://prove2.me/submissions/f2554487-0100-4ff2-9c25-d638f22fff82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_algebraMap_discr_basis_ne_zero
import Theorems.Thm_GlobalTheory_nonempty_equiv_algHom_of_etale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct
open GlobalTheory
variable (K : Type*) {S : Type*} (L : Type*) [Field K] [CommRing S] [Algebra K S] [Field L]
  [Algebra K L] [IsSepClosed L] [Algebra.Etale K S]
variable {K L} {ι : Type*} [Fintype ι]
namespace GlobalTheory
theorem _root_.solution [DecidableEq ι] (e : Basis ι K S) :
    Algebra.discr K e ≠ 0 := by
  obtain ⟨P⟩ := nonempty_equiv_algHom_of_etale K S (AlgebraicClosure K)
    (Module.finrank_eq_card_basis e).symm
  intro h
  exact algebraMap_discr_basis_ne_zero e P.injective (by rw [h, map_zero])
end GlobalTheory
