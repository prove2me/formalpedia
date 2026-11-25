-- Prove2me | solution 1 for GlobalTheory.T.hermitianBlock_invariants_iff_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:18:37.237032+00:00
-- url     : https://prove2.me/submissions/be172894-c369-4985-8a3d-af41e7fc103e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometryStatement
import Theorems.Thm_GlobalTheory_EtIsom_herm_iff_isom


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → (∀ (a : A.K) (X : Hn r F E), IsUnit a → HasInv X (A.invK τ p lam a) → ∀ (x : A.K) (y : A.L), IsUnit y → a = x * A.NL y → ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom x j ∧ (∀ z, j (algebraMap A.K A.L τ * z) = X.1.1 *ᵥ j z) ∧ j y = X.2.1) ∧ ∀ (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∃ Ax : selfAdjoint (Matrix (Fin r) (Fin r) E), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) ∧ ∀ y, HasInv ((Ax, j y, lam) : Hn r F E) (A.invK τ p lam (x * A.NL y)) := by
  first | exact @GlobalTheory.EtIsom.herm_iff_isom | exact GlobalTheory.EtIsom.herm_iff_isom | (intros; apply GlobalTheory.EtIsom.herm_iff_isom <;> assumption)
end _root_.GlobalTheory.T
