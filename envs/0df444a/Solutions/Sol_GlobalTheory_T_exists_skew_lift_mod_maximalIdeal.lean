-- Prove2me | solution 1 for GlobalTheory.T.exists_skew_lift_mod_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:23:55.36604+00:00
-- url     : https://prove2.me/submissions/20d95585-d007-410b-94cf-63fc417c8818

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftModMaximalSkew
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftModMaximalSkewStatement
import Theorems.Thm_GlobalTheory_lift_mod_maximal_skew


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ Z₀ : Matrix (Fin n) (Fin n) O, (∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O) →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ ∀ i j, Z i j - Z₀ i j ∈ IsLocalRing.maximalIdeal O := by
  first | exact @GlobalTheory.lift_mod_maximal_skew | exact GlobalTheory.lift_mod_maximal_skew | (intros; apply GlobalTheory.lift_mod_maximal_skew <;> assumption)
end _root_.GlobalTheory.T
