-- Prove2me | solution 1 for GlobalTheory.WeylRowAll.coeff_zero_toInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:34:52.518531+00:00
-- url     : https://prove2.me/submissions/2c7637ab-ba3f-446d-b032-4545247d5e9f

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeylRowActionMemWeylLatticeSquare
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.WeylRowAll
namespace GlobalTheory.WeylRowAll
theorem _root_.solution (R : Type) [CommRing R] (p : Polynomial R) :
    (toInv R p).coeff 0 = p.eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k a =>
    simp only [toInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
      Polynomial.eval_monomial, HahnSeries.single_pow, HahnSeries.C_apply,
      HahnSeries.single_mul_single]
    rcases k with _ | k
    · simp
    · rw [HahnSeries.coeff_single_of_ne]
      · simp
      · simp; omega
end GlobalTheory.WeylRowAll
