-- Prove2me | solution 1 for GlobalTheory.exists_mul_mul_eq_one_of_le_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:44:44.381797+00:00
-- url     : https://prove2.me/submissions/4dd55629-2403-402a-bbd5-66c6dc6600ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenSetOfLeRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k : Type} [Field k] {m n : Type} [Fintype m] [Fintype n]
    {κ : ℕ} (x : Matrix m n k) (h : κ ≤ x.rank) :
    ∃ (A : Matrix (Fin κ) m k) (B : Matrix n (Fin κ) k), A * x * B = 1 := by
  classical
  obtain ⟨w, hw⟩ := exists_linearIndependent_of_le_finrank
    (R := k) (M := LinearMap.range x.mulVecLin) (n := κ) h
  choose v hv using fun i => (w i).2
  let B : Matrix n (Fin κ) k := Matrix.of fun j i => v i j
  have hw' : LinearIndependent k (fun i => (w i : m → k)) :=
    hw.map' (LinearMap.range x.mulVecLin).subtype (Submodule.ker_subtype _)
  have hcol : (x * B).col = fun i => (w i : m → k) := by
    funext i j
    rw [← hv i]
    simp [B, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col]
  have hinj : Function.Injective (x * B).mulVec := by
    rw [Matrix.mulVec_injective_iff, hcol]
    exact hw'
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' (x * B))
    (LinearMap.ker_eq_bot.2 (fun a b hab => hinj (by simpa only [Matrix.toLin'_apply] using hab)))
  refine ⟨LinearMap.toMatrix' g, B, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  rw [Matrix.mul_assoc, this]
end GlobalTheory
