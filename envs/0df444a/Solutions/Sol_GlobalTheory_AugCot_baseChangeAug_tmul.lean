-- Prove2me | solution 1 for GlobalTheory.AugCot.baseChangeAug_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:48:46.65674+00:00
-- url     : https://prove2.me/submissions/d0220983-ec41-4cb8-bd51-3ee9eceb11e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    baseChangeAug R' ε (r ⊗ₜ a) = r * algebraMap R R' (ε a) := by
  simp [baseChangeAug]
end GlobalTheory.AugCot
