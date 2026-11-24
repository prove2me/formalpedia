-- Prove2me | solution 1 for GlobalTheory.T.unit_prescribed_residue_reduced_finite_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:21:11.566992+00:00
-- url     : https://prove2.me/submissions/123f97db-a6b2-478d-8812-4d1df0ee0f1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitPrescribedResidueReducedFiniteAlgebra
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitPrescribedResidueReducedFiniteAlgebraStatement
import Theorems.Thm_GlobalTheory_UnitLemma_unit_prescribed_residue


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
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), IsReduced B.A → ∀ (m : MaximalSpectrum B.A) (z : B.A ⧸ m.asIdeal), z ≠ 0 → ∃ y : B.Aˣ, Ideal.Quotient.mk m.asIdeal (y : B.A) = z ∧ ∀ m' : MaximalSpectrum B.A, m' ≠ m → Ideal.Quotient.mk m'.asIdeal (y : B.A) = 1 := by
  first | exact @GlobalTheory.UnitLemma.unit_prescribed_residue | exact GlobalTheory.UnitLemma.unit_prescribed_residue | (intros; apply GlobalTheory.UnitLemma.unit_prescribed_residue <;> assumption)
end _root_.GlobalTheory.T
