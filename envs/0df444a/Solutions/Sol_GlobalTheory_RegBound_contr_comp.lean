-- Prove2me | solution 1 for GlobalTheory.RegBound.contr_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:54.332806+00:00
-- url     : https://prove2.me/submissions/1bb1808a-de6c-434e-8fd5-1d919d0f4b93

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
variable {L : Type} [Field L] [Algebra K L]
namespace GlobalTheory.RegBound
theorem _root_.solution (φ : L →ₗ[K] K) (e : ℕ) (F : MvPolynomial σ L) :
    contr φ (homogeneousComponent e F) = homogeneousComponent e (contr φ F) := by
  classical
  ext m
  simp only [coeff_contr, coeff_homogeneousComponent]
  split_ifs <;> simp
end GlobalTheory.RegBound
