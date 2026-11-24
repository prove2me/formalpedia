-- Prove2me | solution 1 for GlobalTheory.AugCot.finrank_kaehler_of_isStandardSmoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:14:31.635898+00:00
-- url     : https://prove2.me/submissions/3a956bf6-64c7-4250-a94b-64d211d0c629

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d

set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.AugCot
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R)
namespace GlobalTheory.AugCot
theorem _root_.solution [Nontrivial A] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] : Module.finrank A Ω[A⁄R] = n := by
  rw [Module.finrank, Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n]
  simp
end GlobalTheory.AugCot
