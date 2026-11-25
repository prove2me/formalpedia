-- Prove2me | solution 1 for GlobalTheory.HaarScaleMatrix.integral_comp_addEquiv_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:49:54.262297+00:00
-- url     : https://prove2.me/submissions/c471263d-0b0b-4098-b10d-e3311aed398d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRk
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarMeasureAdditiveAutomorphismScale
import Theorems.Thm_GlobalTheory_HaarScaleMatrix_secondCountable_of_localField
import Theorems.Thm_GlobalTheory_HaarScaleMatrix_integral_comp_addEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv MeasureTheory
open GlobalTheory GlobalTheory.HaarScaleMatrix
namespace GlobalTheory.HaarScaleMatrix
theorem _root_.solution :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (e d : ℕ)
    [MeasurableSpace (Matrix (Fin e) (Fin d) k)] [BorelSpace (Matrix (Fin e) (Fin d) k)]
    (μ : Measure (Matrix (Fin e) (Fin d) k)) [μ.IsAddHaarMeasure]
    (L : Matrix (Fin e) (Fin d) k ≃+ Matrix (Fin e) (Fin d) k), Continuous L → Continuous L.symm →
    ∃ c : ℝ, 0 < c ∧ ∀ f : Matrix (Fin e) (Fin d) k → ℂ, ∫ x, f (L x) ∂μ = (c : ℂ) * ∫ x, f x ∂μ := by
  intro k _ _ _ _ e d _ _ μ _ L hL hL'
  haveI := secondCountable_of_localField k
  haveI : LocallyCompactSpace (Matrix (Fin e) (Fin d) k) :=
    inferInstanceAs (LocallyCompactSpace (Fin e → Fin d → k))
  haveI : SecondCountableTopology (Matrix (Fin e) (Fin d) k) :=
    inferInstanceAs (SecondCountableTopology (Fin e → Fin d → k))
  exact integral_comp_addEquiv μ L hL hL'
end GlobalTheory.HaarScaleMatrix
