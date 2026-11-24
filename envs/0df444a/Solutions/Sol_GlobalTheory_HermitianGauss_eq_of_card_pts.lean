-- Prove2me | solution 1 for GlobalTheory.HermitianGauss.eq_of_card_pts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:35:07.811866+00:00
-- url     : https://prove2.me/submissions/c3d9af18-2773-4ef3-b9b2-befb7815392b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModule
import Theorems.Thm_GlobalTheory_HermitianGauss_mem_pts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermitianGauss.mem_pts

set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.HermitianGauss
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]
namespace GlobalTheory.HermitianGauss
theorem _root_.solution {A B : Submodule R M} (h : A ≤ B) (hc : (pts B).card ≤ (pts A).card) : A = B := by
  have hs : pts A ⊆ pts B := fun y hy => mem_pts.mpr (h (mem_pts.mp hy))
  have he := Finset.eq_of_subset_of_card_le hs hc
  refine le_antisymm h fun y hy => ?_
  have : y ∈ pts A := by rw [he]; exact mem_pts.mpr hy
  exact mem_pts.mp this
end GlobalTheory.HermitianGauss
