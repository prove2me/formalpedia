-- Prove2me | solution 1 for GlobalTheory.CoeffWord.pairwise_positions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:40.665304+00:00
-- url     : https://prove2.me/submissions/e1b42843-8443-4cd9-a84d-eef92f0a5a63

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UnitriMonomialOfLowerTri
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
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
noncomputable section
open GlobalTheory GlobalTheory.CoeffWord
variable {R : Type} [CommRing R] {r n : ℕ}
namespace GlobalTheory.CoeffWord
theorem _root_.solution :
    (positions r n).Pairwise fun q p => q ≠ p ∧ p.2.val ≤ q.2.val := by
  rw [positions, List.pairwise_flatMap]
  constructor
  · intro s _
    rw [List.pairwise_map]
    refine List.Pairwise.imp ?_ ((List.nodup_finRange r).filter _)
    intro a b hab
    exact ⟨fun h => hab (congrArg Prod.fst h), le_rfl⟩
  · rw [List.pairwise_reverse]
    refine List.Pairwise.imp ?_ (List.pairwise_lt_finRange n)
    intro s t hst x hx y hy
    simp only [List.mem_map] at hx hy
    obtain ⟨a, -, rfl⟩ := hx
    obtain ⟨b, -, rfl⟩ := hy
    exact ⟨fun h => hst.ne' (congrArg Prod.snd h), hst.le⟩
end GlobalTheory.CoeffWord
