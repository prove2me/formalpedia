-- Prove2me | solution 1 for GlobalTheory.WeylRankEmbed.rename_lpMinor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:33:56.659419+00:00
-- url     : https://prove2.me/submissions/bda1a7a3-19d6-4dd2-ad07-8b41960895e9

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_RenameUpperLeftCornerMemWeylLattice
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
open MvPolynomial Formalism.GradedWeylDivisibility
open GlobalTheory
open GlobalTheory.WeylRankEmbed
variable (R : Type) [CommRing R] {a b : ℕ} (hab : a ≤ b)
namespace GlobalTheory.WeylRankEmbed
theorem _root_.solution (s : ℕ) (h1 : s ≤ a) (h2 : s ≤ b) :
    rename (corner hab) (lpMinor R s h1 h1) = lpMinor R s h2 h2 := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext p q : 2
  simp [corner]
end GlobalTheory.WeylRankEmbed
