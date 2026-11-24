-- Prove2me | solution 1 for GlobalTheory.Tw.CentralizerAdjoin.commute_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:39:11.829881+00:00
-- url     : https://prove2.me/submissions/d940cf79-8721-48dd-93ba-1c238c3694f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.CentralizerAdjoin
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
open GlobalTheory.Tw.Model
namespace GlobalTheory.Tw.CentralizerAdjoin
theorem _root_.solution (N g : Matrix (Fin n) (Fin n) R) (hg : g ∈ Algebra.adjoin R {N}) :
    g * N = N * g := by
  induction hg using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.mp hx]
  | algebraMap r => exact Algebra.commutes r N
  | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.mul_add, hx, hy]
  | mul x y _ _ hx hy => rw [Matrix.mul_assoc, hy, ← Matrix.mul_assoc, hx, Matrix.mul_assoc]
end GlobalTheory.Tw.CentralizerAdjoin
