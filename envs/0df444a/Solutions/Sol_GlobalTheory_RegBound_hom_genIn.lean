-- Prove2me | solution 1 for GlobalTheory.RegBound.hom_genIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:55:18.54998+00:00
-- url     : https://prove2.me/submissions/3488b10f-1321-4387-b09d-c1fee3a4bc77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
namespace GlobalTheory.RegBound
theorem _root_.solution (I : Ideal (MvPolynomial σ K)) (d : ℕ) :
    ∀ F ∈ genIn I d, ∀ e, homogeneousComponent e F ∈ genIn I d := by
  intro F hF e
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
  exact homogeneousComponent_mem_of_mem
    (Ideal.homogeneous_span (homogeneousSubmodule σ K) _ fun G hG => ⟨d, hG.2⟩) hF e
end GlobalTheory.RegBound
