-- Prove2me | solution 1 for GlobalTheory.BCT.SuppFin.isOpen_vle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:59:05.396094+00:00
-- url     : https://prove2.me/submissions/ad59b458-79c5-48c8-b314-a5ec6baa57de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlAdicCompletionEntriesBoundedOfIsCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter
noncomputable section
open GlobalTheory GlobalTheory.BCT GlobalTheory.BCT.SuppFin
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.BCT.SuppFin
theorem _root_.solution (w : HeightOneSpectrum (𝓞 E)) (m : ℤ) :
    IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} =
      {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])
end GlobalTheory.BCT.SuppFin
