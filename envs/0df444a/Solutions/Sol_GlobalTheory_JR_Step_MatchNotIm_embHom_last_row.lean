-- Prove2me | solution 1 for GlobalTheory.JR.Step.MatchNotIm.embHom_last_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:09:44.347833+00:00
-- url     : https://prove2.me/submissions/3b31aedf-627f-4302-b00d-cc8028490436

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
theorem _root_.solution (g : Matrix (Fin r) (Fin r) k) (j : Fin (r + 1)) :
    embHom r k g (Fin.last r) j = if j = Fin.last r then 1 else 0 := by
  rw [last_eq]
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases j with j | j
  · simp [embHom, Matrix.reindex_apply, Fin.ext_iff, (Fin.is_lt _).ne]
  · rw [Subsingleton.elim j 0]; simp [embHom, Matrix.reindex_apply]
end GlobalTheory.JR.Step.MatchNotIm
