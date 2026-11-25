-- Prove2me | solution 1 for GlobalTheory.T.exists_unramified_odd_degree_quadratic_local_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:08:23.079748+00:00
-- url     : https://prove2.me/submissions/a9446a94-c488-48e8-b8f3-7201d381a8cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExtStatement
import Theorems.Thm_GlobalTheory_UnitLemma_UnrExt_exists_unramified_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (d : ℕ), Odd d → ∃ (K' : UQ) (φ : K.E →+* K'.E), K'.q = K.q ^ d ∧ (∀ x, φ (K.c x) = K'.c (φ x)) ∧ (∀ x, val K'.O (φ x) = val K.O x) ∧ (K.Odd → K'.Odd) ∧ @Module.finrank K.E K'.E _ _ (φ.toAlgebra).toModule = d ∧ ∃ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) ∧ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤ := by
  first | exact @GlobalTheory.UnitLemma.UnrExt.exists_unramified_ext | exact GlobalTheory.UnitLemma.UnrExt.exists_unramified_ext | (intros; apply GlobalTheory.UnitLemma.UnrExt.exists_unramified_ext <;> assumption)
end _root_.GlobalTheory.T
