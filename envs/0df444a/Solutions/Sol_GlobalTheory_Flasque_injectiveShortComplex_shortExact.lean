-- Prove2me | solution 1 for GlobalTheory.Flasque.injectiveShortComplex_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:18.724248+00:00
-- url     : https://prove2.me/submissions/41c3ec84-2aa3-467b-a11c-64403f14f04c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w v u
open GlobalTheory
open GlobalTheory.Flasque
variable {A : Type u} [Category.{v} A] [Abelian A]
open CategoryTheory Abelian Opposite Limits TopologicalSpace
variable {A : Type u} [Category.{v} A] [Abelian A]
namespace GlobalTheory.Flasque
namespace _root_.GlobalTheory.Flasque
theorem _root_.solution [EnoughInjectives A] (F : A) :
    (_root_.GlobalTheory.Flasque.injectiveShortComplex F).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
end _root_.GlobalTheory.Flasque
end GlobalTheory.Flasque
