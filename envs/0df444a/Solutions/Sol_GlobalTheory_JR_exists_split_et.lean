-- Prove2me | solution 1 for GlobalTheory.JR.exists_split_et
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:31:16.2838+00:00
-- url     : https://prove2.me/submissions/b2e6b4b7-7380-4f06-a7a4-1af2c6618c6b

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSplitEtaleHermitianPairIsometry
import Theorems.Thm_GlobalTheory_JR_SplitEt_algebraMap_norm_eq_mul_star
import Theorems.Thm_GlobalTheory_JR_SplitEt_norm_pi_apply
import Theorems.Thm_GlobalTheory_JR_SplitEt_trace_pi_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), ∃ (A : Et F E) (e : A.K ≃ₐ[F] (Fin r → F)) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom 1 j ∧ ∀ y i, algebraMap F E (e (A.NL y) i) = j y i * star (j y i) := by
  intro F E _ _ _ _ _ r
  refine ⟨SplitEt.splitEt F E r, AlgEquiv.refl, LinearEquiv.refl E _, ?_, ?_⟩
  · intro y y'
    show star y ⬝ᵥ y' = Algebra.trace E (Fin r → E) (algebraMap (Fin r → F) (Fin r → E) 1 * star y * y')
    rw [map_one, one_mul, SplitEt.trace_pi_apply]
    simp [dotProduct]
  · intro y i
    show algebraMap F E (Algebra.norm (Fin r → F) y i) = y i * star (y i)
    rw [SplitEt.norm_pi_apply, SplitEt.algebraMap_norm_eq_mul_star]
end GlobalTheory.JR
