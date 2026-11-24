-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s057_avoids_of_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:43:51.707848+00:00
-- url     : https://prove2.me/submissions/09711335-646e-4de9-ad9f-f9ae950a2656

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_shortZero_map_pullSeq
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution (S : PosSeq 24)
    (e : Fin 24 ≃ Fin 24)
    (hAvoid : AvoidsInnerJointPair (fun i => S (e i))) :
    AvoidsInnerJointPair S := by
  classical
  intro I J hI hJ
  let t : Fin 24 ↪ Fin 24 := e.symm.toEmbedding
  have hFun : pullSeq (fun i => S (e i)) t = S := by
    funext i
    simp [pullSeq, t]
  have hPullI : ShortZero (pullSeq (fun i => S (e i)) t) I := by
    rw [hFun]
    exact hI
  have hPullJ : ShortZero (pullSeq (fun i => S (e i)) t) J := by
    rw [hFun]
    exact hJ
  have hI' : ShortZero (fun i => S (e i)) (I.map t) :=
    shortZero_map_pullSeq (fun i => S (e i)) t hPullI
  have hJ' : ShortZero (fun i => S (e i)) (J.map t) :=
    shortZero_map_pullSeq (fun i => S (e i)) t hPullJ
  have hIntersection :=
    hAvoid (I.map t) (J.map t) hI' hJ'
  change posSum (fun i => S (e i)) (I.map t ∩ J.map t) = 0 at hIntersection
  rw [← Finset.map_inter (f := t) I J] at hIntersection
  change posSum (fun i => S (e i)) ((I ∩ J).map t) = 0 at hIntersection
  have hSumEq :
      posSum (fun i => S (e i)) ((I ∩ J).map t) = posSum S (I ∩ J) := by
    simp [posSum, t]
  rw [hSumEq] at hIntersection
  exact hIntersection
end InverseZeroSum.Candidate3
