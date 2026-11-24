-- Prove2me | solution 1 for GlobalTheory.AugCot.baseChangeEquiv_tmul_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:01:23.377085+00:00
-- url     : https://prove2.me/submissions/85774543-532c-476d-813a-ea3e286c5025

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul

set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.AugCot
variable {R R' A A' : Type*} [CommRing R] [CommRing R'] [CommRing A] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra R A'] [IsScalarTower R R' A']
  {ε : A →ₐ[R] R} {ε' : A' →ₐ[R'] R'}
namespace GlobalTheory.AugCot
theorem _root_.solution (r : R') (a : A) :
    baseChangeEquiv R' ε (r ⊗ₜ d ε a) = r • d _ (1 ⊗ₜ a) := by
  simp [baseChangeEquiv, IsBaseChange.equiv_tmul]
end GlobalTheory.AugCot
