-- Prove2me | solution 1 for GlobalTheory.DegCnt.RatNormal.comb_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:18.95904+00:00
-- url     : https://prove2.me/submissions/082ae5ae-a9db-4f90-9fe8-b097ca3b50b5

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsInvLower
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_Xa


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.HermitianLatticeCounting.P
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.RatNormal
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.RatNormal
theorem _root_.solution (F : FlagD H r) {j : ℕ} (hj : j ≤ r) (M : Matrix (Fin j) (Fin j) K)
    (h0 : ∀ a b, a < b → M a b = 0) (h1 : ∀ a, M a a = 1) (a : Fin j) :
    ∑ b, M a b • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) b) - F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a) ∈
      F.Xa a.val := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), h1, one_smul, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun b hb => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hb) with hb | hb
  · exact Submodule.smul_mem _ _ (e_mem_Xa F (Fin.castLE hj b) hb)
  · rw [h0 a b hb, zero_smul]; exact Submodule.zero_mem _
end GlobalTheory.DegCnt.RatNormal
