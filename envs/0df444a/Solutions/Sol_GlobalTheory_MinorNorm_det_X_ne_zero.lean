-- Prove2me | solution 1 for GlobalTheory.MinorNorm.det_X_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:30:28.83185+00:00
-- url     : https://prove2.me/submissions/5656542f-5156-4485-b8f5-85ff897b140c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
variable {σ : Type}
namespace GlobalTheory.MinorNorm
theorem _root_.solution {k : ℕ} (v : Fin k → Fin k → σ)
    (hv : ∀ r c s e, v r c = v s e → r = s ∧ c = e) :
    (Matrix.of fun r c => (X (v r c) : MvPolynomial σ ℂ)).det ≠ 0 := by
  classical
  intro h
  have := congrArg (eval fun w => if ∃ r, w = v r r then (1 : ℂ) else 0) h
  rw [RingHom.map_det, map_zero] at this
  have e : (eval fun w => if ∃ r, w = v r r then (1 : ℂ) else 0).mapMatrix
      (Matrix.of fun r c => (X (v r c) : MvPolynomial σ ℂ)) = 1 := by
    ext r c
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, of_apply, eval_X, Matrix.one_apply]
    congr 1
    apply propext
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨h1, h2⟩ := hv _ _ _ _ hs
      rw [h1, h2]
    · rintro rfl; exact ⟨r, rfl⟩
  rw [e, det_one] at this
  exact one_ne_zero this
end GlobalTheory.MinorNorm
