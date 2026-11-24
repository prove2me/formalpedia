-- Prove2me | solution 1 for GlobalTheory.PMonE.prep_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:33:52.604792+00:00
-- url     : https://prove2.me/submissions/fcd69e40-e16f-4c1a-a130-0f9e67869c99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOne
import Theorems.Thm_GlobalTheory_PMonE_prep_pow_sub_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
variable {F : Type} [NormedField F] {m : Type} [Fintype m]
variable [IsUltrametricDist F]
omit [IsUltrametricDist F]
namespace GlobalTheory.PMonE
theorem _root_.solution (p : ℕ) [Fact p.Prime] [CharP F p] (e D : ℕ) (M U : ℕ → Matrix m m F) (A : Matrix m m F)
    (hD : U D = 0) (hU : ∀ n, n < D → U n = M (n + 1) + U (n + 1) * A.map (fun a => a ^ (p ^ e) ^ (n + 1)))
    (h0 : M 0 = -(U 0 * A)) (x : m → F) :
    gsum (p ^ e) D M x = gsum (p ^ e) D U (fun i => x i ^ p ^ e - A.mulVec x i) := by
  unfold gsum
  simp only [prep_pow_sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, sum_sub_distrib]
  rw [sum_range_succ', sum_range_succ, sum_range_succ', hD, h0]
  have : ∑ n ∈ range D, (U n).mulVec (fun i => x i ^ (p ^ e) ^ (n + 1)) =
      ∑ n ∈ range D, (M (n + 1)).mulVec (fun i => x i ^ (p ^ e) ^ (n + 1)) +
      ∑ n ∈ range D, (U (n + 1) * A.map (fun a => a ^ (p ^ e) ^ (n + 1))).mulVec
        (fun i => x i ^ (p ^ e) ^ (n + 1)) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [← Matrix.add_mulVec, ← hU n (mem_range.1 hn)]
  rw [this]
  have hA : A.map (fun a => a ^ (p ^ e) ^ 0) = A := by ext i j; simp
  rw [hA, Matrix.neg_mulVec, Matrix.zero_mulVec]
  abel
end GlobalTheory.PMonE
