-- Prove2me | solution 1 for GlobalTheory.LemmaTwoFortyThirteen.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:20.094875+00:00
-- url     : https://prove2.me/submissions/cf4f457c-d5e2-4e9d-94df-7d487bcbf455

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ImportsAlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LemmaTwoFortyThirteen
namespace GlobalTheory.LemmaTwoFortyThirteen
theorem _root_.solution {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) (h : ∀ v : V, ∃ a : R, a ≠ (0 : R) ∧ a • v ∈ M) :
    Submodule.span K (↑M : Set V) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨a, ha, hav⟩ := h v
  have hK : algebraMap R K a ≠ 0 := by
    simpa using (IsFractionRing.injective R K).ne ha
  have hv : v = (algebraMap R K a)⁻¹ • (a • v) := by
    rw [← algebraMap_smul K a v, smul_smul, inv_mul_cancel₀ hK, one_smul]
  rw [hv]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hav)
end GlobalTheory.LemmaTwoFortyThirteen
