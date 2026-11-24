-- Prove2me | solution 1 for GlobalTheory.ProjModClasses.nonempty_equiv_of_mk0_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:38:48.169496+00:00
-- url     : https://prove2.me/submissions/e8c34dbc-f82a-4307-8d41-a68be6d8080f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFinRepsProjectiveFinrankLeNumberField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
open GlobalTheory.ProjModClasses
variable {R : Type} [CommRing R] [IsDomain R] [IsDedekindDomain R]
namespace GlobalTheory.ProjModClasses
theorem _root_.solution {I J : nonZeroDivisors (Ideal R)}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) : Nonempty ((I : Ideal R) ≃ₗ[R] (J : Ideal R)) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 h
  exact ⟨(mulEquiv hx I).trans ((LinearEquiv.ofEq _ _ hxy).trans (mulEquiv hy J).symm)⟩
end GlobalTheory.ProjModClasses
