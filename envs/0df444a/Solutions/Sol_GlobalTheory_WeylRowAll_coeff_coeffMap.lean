-- Prove2me | solution 1 for GlobalTheory.WeylRowAll.coeff_coeffMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:34:05.224175+00:00
-- url     : https://prove2.me/submissions/e981d047-ecc9-4cbc-8539-fe99a18a6269

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
theorem _root_.solution {R S σ : Type} [CommRing R] [CommRing S] (c : S →+ R)
    (F : MvPolynomial σ S) (m : σ →₀ ℕ) : coeff m (coeffMap c F) = c (coeff m F) := by
  classical
  simp only [coeffMap, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero]
end GlobalTheory.WeylRowAll
