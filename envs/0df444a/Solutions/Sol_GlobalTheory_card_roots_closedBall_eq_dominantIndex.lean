-- Prove2me | solution 1 for GlobalTheory.card_roots_closedBall_eq_dominantIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:57:18.606772+00:00
-- url     : https://prove2.me/submissions/ccbba56d-d2e7-4d42-bd02-e8c673c940fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NewtonPolygonLastDominantIndexMulXSubCStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NewtonPolygonDominantIndexXSubCMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallEqDominantIndex
import Theorems.Thm_GlobalTheory_dominantIndex_prod_X_sub_C

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ), 0 < ρ → f ≠ 0 → (∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧ ∀ j, Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) := by
  intro K _ _ _ f ρ hρ hf
  have key := dominantIndex_prod_X_sub_C K ρ hρ f.roots f.leadingCoeff
    (leadingCoeff_ne_zero.mpr hf)
  rw [C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree] at key
  exact key
end GlobalTheory
