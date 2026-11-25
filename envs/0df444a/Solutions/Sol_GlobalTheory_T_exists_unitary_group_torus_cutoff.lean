-- Prove2me | solution 1 for GlobalTheory.T.exists_unitary_group_torus_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:24:09.590812+00:00
-- url     : https://prove2.me/submissions/4143fc72-5216-4e2e-866a-cfa9ff3f4b43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitaryGroupTorusCutoff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitaryGroupTorusCutoffStatement
import Theorems.Thm_GlobalTheory_JR_TorusCutOff_exists_unitary_cutoff


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F), A.IsGen τ p → ∀ (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (hx : A.IsIsom x j) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) → ∀ (ν : Measure (unitary A.L)), ν.IsHaarMeasure → ∀ Z : Set (Matrix (Fin r) (Fin r) E), IsCompact Z → ∃ α : Matrix.unitaryGroup (Fin r) E → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ g : Matrix.unitaryGroup (Fin r) E, g.1 * Ax.1 * star g.1 ∈ Z → ∫ t, α (g * (A.uHom hx t)⁻¹) ∂ν = 1 := by
  first | exact @GlobalTheory.JR.TorusCutOff.exists_unitary_cutoff | exact GlobalTheory.JR.TorusCutOff.exists_unitary_cutoff | (intros; apply GlobalTheory.JR.TorusCutOff.exists_unitary_cutoff <;> assumption)
end _root_.GlobalTheory.T
