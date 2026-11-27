-- Prove2me | solution 1 for GlobalTheory.UTrans.Model.nontrivial_transvection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:28.073701+00:00
-- url     : https://prove2.me/submissions/9838769d-c295-4e89-b95b-2f317cf7f603

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_NontrivialTransvection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.Model
open GlobalTheory.UTrans
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory.UTrans.Model
theorem _root_.solution :
    !![1, Complex.I; 0, 1] ∈ TvGen (starRingEnd ℂ) !![0, 1; 1, 0] := by
  apply Submonoid.subset_closure
  refine ⟨![1, 0], Complex.I, ?_, ?_, ?_⟩
  · simp [hf, Fin.sum_univ_two]
  · simp [Complex.conj_I]
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [tv, Fin.sum_univ_two]
end GlobalTheory.UTrans.Model
