-- Prove2me | solution 1 for GlobalTheory.PDivGroup.pointsMap_mulP_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:02:08.628735+00:00
-- url     : https://prove2.me/submissions/5dba0052-0564-464a-8a7e-bbcd4be3f932

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
import Theorems.Thm_GlobalTheory_PDivGroup_natCard_ker_ptsMap_mulP
import Theorems.Thm_GlobalTheory_PDivGroup_natCard_pts_eq
import Theorems.Thm_GlobalTheory_PDivGroup_natCard_conv_pts_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv TateFree
variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)
variable (C : Type) [Field C] [Algebra O C] [IsIntegrallyClosedIn O C] [IsAlgClosed C]
  [CharZero C]
include C
variable [Fact p.Prime]
namespace GlobalTheory.PDivGroup
theorem _root_.solution (n : ℕ) : Function.Surjective (pointsMap O (G.mulP n)) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have : Finite (WithConv (G.A n →ₐ[O] O)) :=
    Nat.finite_of_card_ne_zero (by rw [G.natCard_conv_pts_eq C]; positivity)
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (pointsMap O (G.mulP n)).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, natCard_ker_ptsMap_mulP,
    G.natCard_pts_eq C, G.natCard_conv_pts_eq C, add_mul, pow_add] at h
  rw [← MonoidHom.range_eq_top]
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [G.natCard_conv_pts_eq C]
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos hp _) h).symm
end GlobalTheory.PDivGroup
