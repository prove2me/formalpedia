-- Prove2me | solution 1 for GlobalTheory.T.isUnit_det_conjugationMatrix_integralBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:13:22.173801+00:00
-- url     : https://prove2.me/submissions/b20b11bf-5bed-480e-b14c-bd5efee95278

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitDetConjugationMatrixIntegralBasis
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitDetConjugationMatrixIntegralBasisStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_conj_matrix_det_isUnit


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
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), (∀ x, φ (K.c x) = K'.c (φ x)) → letI : Algebra K.E K'.E := φ.toAlgebra; ∀ w : Module.Basis (Fin d) K.E K'.E, (∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k) → ∃ u : K.O, IsUnit u ∧ algebraMap K.O K.E u = (Matrix.of fun m l => w.repr (K'.c (w l)) m).det := by
  first | exact @GlobalTheory.UnitLemma.Unr.conj_matrix_det_isUnit | exact GlobalTheory.UnitLemma.Unr.conj_matrix_det_isUnit | (intros; apply GlobalTheory.UnitLemma.Unr.conj_matrix_det_isUnit <;> assumption)
end _root_.GlobalTheory.T
