-- Prove2me | solution 1 for GlobalTheory.T.unimodular_hermitian_matrix_congruent_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:59:52.31312+00:00
-- url     : https://prove2.me/submissions/08a1e7b8-ef42-4616-b982-aa36c91d1db2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOneStatement
import Theorems.Thm_GlobalTheory_HermUnimod_unimodular_hermitian_eq_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (s : ℕ) (G : Matrix (Fin s) (Fin s) E), G.IsHermitian → (∀ i j, ‖G i j‖ ≤ 1) → ‖G.det‖ = 1 → ∃ h : Matrix (Fin s) (Fin s) E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1 := by
  first | exact @GlobalTheory.HermUnimod.unimodular_hermitian_eq_conj | exact GlobalTheory.HermUnimod.unimodular_hermitian_eq_conj | (intros; apply GlobalTheory.HermUnimod.unimodular_hermitian_eq_conj <;> assumption)
end _root_.GlobalTheory.T
