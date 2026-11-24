-- Prove2me | solution 1 for GlobalTheory.T.matrix_additive_haar_normalized
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:12:30.798411+00:00
-- url     : https://prove2.me/submissions/62d46e30-0cd6-44ac-a719-e55da0f38b3d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalized
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_QLHaarAdd_haarAdd_intMat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n m : ℕ, BorelSpace (Matrix (Fin n) (Fin m) F) ∧ IsOpen (intMat O n m) ∧ IsCompact (intMat O n m) ∧ (∃ dx : Measure (Matrix (Fin n) (Fin m) F), dx.IsAddLeftInvariant ∧ dx (intMat O n m) = 1) ∧ (∀ (dx : Measure (Matrix (Fin n) (Fin m) F)), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → dx.IsAddHaarMeasure) ∧ (∀ (dx : Measure (Matrix (Fin n) (Fin m) F)), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → ∀ (dy : Measure (Matrix (Fin n) (Fin m) F)), dy.IsAddLeftInvariant → dy (intMat O n m) = 1 → dx = dy) := by
  first | exact @GlobalTheory.CompanionTheory.QLHaarAdd.haarAdd_intMat | exact GlobalTheory.CompanionTheory.QLHaarAdd.haarAdd_intMat | (intros; apply GlobalTheory.CompanionTheory.QLHaarAdd.haarAdd_intMat <;> assumption)
end _root_.GlobalTheory.T
