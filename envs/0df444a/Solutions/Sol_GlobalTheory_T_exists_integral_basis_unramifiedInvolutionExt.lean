-- Prove2me | solution 1 for GlobalTheory.T.exists_integral_basis_unramifiedInvolutionExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:32:50.449669+00:00
-- url     : https://prove2.me/submissions/e23c75b5-c2aa-4415-99d3-3d04c697a3d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExtStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_IntBasis_intBasis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d → letI : Algebra K.E K'.E := φ.toAlgebra; ∃ w : Module.Basis (Fin d) K.E K'.E, ∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k := by
  first | exact @GlobalTheory.UnitLemma.Unr.IntBasis.intBasis | exact GlobalTheory.UnitLemma.Unr.IntBasis.intBasis | (intros; apply GlobalTheory.UnitLemma.Unr.IntBasis.intBasis <;> assumption)
end _root_.GlobalTheory.T
