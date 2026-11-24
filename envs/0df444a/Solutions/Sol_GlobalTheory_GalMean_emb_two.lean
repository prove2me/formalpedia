-- Prove2me | solution 1 for GlobalTheory.GalMean.emb_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:15:42.304673+00:00
-- url     : https://prove2.me/submissions/406315c5-5c07-4fcd-bde4-c8f2677a35d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeanLogNormConjugatesOverIdealClasses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.GalMean
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
namespace GlobalTheory.GalMean
theorem _root_.solution {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (hK2 : Module.finrank ℚ K = 2)
    (hc : (starRingEnd ℂ).comp φK ≠ φK) (g : K →+* ℂ) : g = φK ∨ g = (starRingEnd ℂ).comp φK := by
  classical
  by_contra h
  push_neg at h
  have h3 : ({g, φK, (starRingEnd ℂ).comp φK} : Finset (K →+* ℂ)).card = 3 :=
    Finset.card_eq_three.2 ⟨g, φK, _, h.1, h.2, hc.symm, rfl⟩
  have := Finset.card_le_univ ({g, φK, (starRingEnd ℂ).comp φK} : Finset (K →+* ℂ))
  rw [h3, NumberField.Embeddings.card, hK2] at this
  omega
end GlobalTheory.GalMean
