-- Prove2me | solution 1 for GlobalTheory.JR.Step.MatchNotIm.embHom_last_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:09:43.511104+00:00
-- url     : https://prove2.me/submissions/07f36895-a34e-47a9-a913-d48051a306e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedInvariantsAndHankelDetMapRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftWithLastBasis
import Theorems.Thm_GlobalTheory_JR_Step_MatchNotIm_last_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.MatchNotIm
variable {r : ℕ} {k : Type} [CommRing k]
namespace GlobalTheory.JR.Step.MatchNotIm
theorem _root_.solution (g : Matrix (Fin r) (Fin r) k) (i : Fin (r + 1)) :
    embHom r k g i (Fin.last r) = if i = Fin.last r then 1 else 0 := by
  rw [last_eq]
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i
  · simp [embHom, Matrix.reindex_apply, Fin.ext_iff, (Fin.is_lt _).ne]
  · rw [Subsingleton.elim i 0]; simp [embHom, Matrix.reindex_apply]
end GlobalTheory.JR.Step.MatchNotIm
