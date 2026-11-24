-- Prove2me | solution 1 for GlobalTheory.T.unitary_admissible_matrix_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:59:05.538531+00:00
-- url     : https://prove2.me/submissions/a2490951-5f43-4d48-9a69-fbf27f5be7e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficientStatement
import Theorems.Thm_GlobalTheory_exists_vector_of_smooth_antilinear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V)
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), IsAdmissible σ → (∀ v w, Bf w v = starRingEnd ℂ (Bf v w)) →
    (∀ v, v ≠ 0 → 0 < (Bf v v).re) → (∀ g v w, Bf (σ g v) (σ g w) = Bf v w) →
    ∀ (L : V →ₗ⋆[ℂ] ℂ) (S : Subgroup (GL (Fin r) k)), IsOpen (S : Set (GL (Fin r) k)) →
      (∀ s ∈ S, ∀ w, L (σ s w) = L w) → ∃ u : V, ∀ w, L w = Bf u w := by
  first | exact @GlobalTheory.exists_vector_of_smooth_antilinear | exact GlobalTheory.exists_vector_of_smooth_antilinear | (intros; apply GlobalTheory.exists_vector_of_smooth_antilinear <;> assumption)
end _root_.GlobalTheory.T
