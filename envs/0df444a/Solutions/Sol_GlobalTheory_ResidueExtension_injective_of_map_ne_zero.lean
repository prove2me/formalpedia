-- Prove2me | solution 1 for GlobalTheory.ResidueExtension.injective_of_map_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:56:39.786854+00:00
-- url     : https://prove2.me/submissions/18c35586-1095-4124-a2e1-a698acb64ee0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsCompleteDiscreteValuationRingWithResidues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory
open GlobalTheory.ResidueExtension
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]
namespace GlobalTheory.ResidueExtension
theorem _root_.solution {B : Type} [CommRing B] [IsDomain B] (j : O →+* B) {π : O}
    (hπ : Irreducible π) (h : j π ≠ 0) : Function.Injective j := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hπ
  rw [map_mul, map_pow] at hx
  exact mul_ne_zero (u.isUnit.map j).ne_zero (pow_ne_zero n h) hx
end GlobalTheory.ResidueExtension
