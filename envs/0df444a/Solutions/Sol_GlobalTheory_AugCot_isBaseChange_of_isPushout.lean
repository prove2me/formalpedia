-- Prove2me | solution 1 for GlobalTheory.AugCot.isBaseChange_of_isPushout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:25:38.45064+00:00
-- url     : https://prove2.me/submissions/0c18fa9a-98a4-44ec-a612-1f8930c1fbe8

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
theorem _root_.solution [Algebra A A'] [IsScalarTower R A A']
    [hP : Algebra.IsPushout R R' A A']
    (h : ∀ a, ε' (IsScalarTower.toAlgHom R A A' a) = algebraMap R R' (ε a)) :
    IsBaseChange R' (mapBase (IsScalarTower.toAlgHom R A A') h) :=
  isBaseChange_mapBase _ h hP.out
end GlobalTheory.AugCot
