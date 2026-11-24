-- Prove2me | solution 1 for GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:23:22.534598+00:00
-- url     : https://prove2.me/submissions/b70131b0-0ccb-438c-8e1f-3d63c15fbb30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_dm_fst
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_snd_aeval

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
variable {n : ℕ} {R : Type} [CommRing R]
namespace GlobalTheory.Tw.CentralizerAdjoin
theorem _root_.solution (N g : Matrix (Fin n) (Fin n) R) (hs : N.charpoly.Separable)
    (hc : g * N = N * g) : g ∈ Algebra.adjoin R {N} := by
  obtain ⟨Q, hQ⟩ := snd_aeval N g hc (dm N g).charpoly
  have hf : (dm N g).map (TrivSqZeroExt.fstHom R R R).toRingHom = N := dm_fst N g
  rw [← Matrix.charpoly_map, hf, Matrix.aeval_self_charpoly, Matrix.map_zero _ rfl] at hQ
  obtain ⟨a, b, hab⟩ := hs
  have h1 : aeval N b * aeval N (derivative N.charpoly) = 1 := by
    have := congrArg (aeval N) hab
    rwa [map_add, map_mul, map_mul, Matrix.aeval_self_charpoly, Matrix.mul_zero, zero_add, map_one] at this
  have h2 : g = - aeval N (b * Q) := by
    rw [map_mul, ← Matrix.mul_neg, ← eq_neg_iff_add_eq_zero.mpr hQ.symm, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [h2]
  exact neg_mem (aeval_mem_adjoin_singleton R N)
end GlobalTheory.Tw.CentralizerAdjoin
