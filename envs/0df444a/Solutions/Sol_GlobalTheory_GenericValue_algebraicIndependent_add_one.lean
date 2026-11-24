-- Prove2me | solution 1 for GlobalTheory.GenericValue.algebraicIndependent_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:18:26.744326+00:00
-- url     : https://prove2.me/submissions/934c94ab-c608-4566-aeec-e28d23ae3192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsAlgHomOfIsTranscendenceBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GenericValue
open MvPolynomial
variable {K : Type} [Field K]
namespace GlobalTheory.GenericValue
theorem _root_.solution {E ι : Type} [CommRing E] [Algebra K E] {v : ι → E}
    (hv : AlgebraicIndependent K v) : AlgebraicIndependent K fun i => v i + 1 := by
  have h₁ : AlgebraicIndependent K fun i : ι => (X i + 1 : MvPolynomial ι K) := by
    refine AlgebraicIndependent.of_comp (aeval fun i : ι => (X i - 1 : MvPolynomial ι K)) ?_
    convert algebraicIndependent_X ι K using 1
    funext i
    simp
  convert h₁.map' (algebraicIndependent_iff_injective_aeval.1 hv) using 1
  funext i
  simp
end GlobalTheory.GenericValue
