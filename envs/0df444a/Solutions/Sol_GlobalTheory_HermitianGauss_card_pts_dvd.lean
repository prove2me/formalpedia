-- Prove2me | solution 1 for GlobalTheory.HermitianGauss.card_pts_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:49:42.140709+00:00
-- url     : https://prove2.me/submissions/bef08b3a-d6fd-46de-994e-62e80a95270f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModule
import Theorems.Thm_GlobalTheory_HermitianGauss_card_pts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.HermitianGauss
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]
namespace GlobalTheory.HermitianGauss
theorem _root_.solution {A B : Submodule R M} (h : A ≤ B) : (pts A).card ∣ (pts B).card := by
  rw [card_pts, card_pts]
  exact AddSubgroup.card_dvd_of_le (show A.toAddSubgroup ≤ B.toAddSubgroup from h)
end GlobalTheory.HermitianGauss
