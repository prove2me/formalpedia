-- Prove2me | solution 1 for GroundTheory.Global.Complex.exists_ringEquiv_extend_of_trdeg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:46:08.887982+00:00
-- url     : https://prove2.me/submissions/f9400207-c2e6-4d7c-b006-d23f133ab33d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ExistsRingEquivExtendOfIsTranscendenceBasis
import Theorems.Thm_GroundTheory_Global_exists_ringEquiv_extend_of_trdeg_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Cardinal Polynomial IntermediateField
namespace GroundTheory.Global
namespace Complex
theorem _root_.solution (F₁ F₂ : Subfield ℂ) (e : F₁ ≃+* F₂)
    (h : Algebra.trdeg F₁ ℂ = Algebra.trdeg F₂ ℂ) :
    ∃ σ : ℂ ≃+* ℂ, ∀ a : F₁, σ a = e a :=
  GroundTheory.Global.exists_ringEquiv_extend_of_trdeg_eq e h
end Complex
end GroundTheory.Global
