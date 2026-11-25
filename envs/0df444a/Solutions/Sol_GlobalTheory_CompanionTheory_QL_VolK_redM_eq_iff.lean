-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.VolK.redM_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:44:13.105143+00:00
-- url     : https://prove2.me/submissions/5060d586-ccc1-446f-ab70-e33d2342a279

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureUniformizerMultipleMatricesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatrices
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_VolK_red_eq_iff

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.VolK
variable {F : Type} [Field F] [ValuativeRel F]
namespace GlobalTheory.CompanionTheory.QL.VolK
theorem _root_.solution {r : ℕ} {ϖ : F}
    (hlt : ∀ x : F, ValuativeRel.valuation F x < 1 ↔ ∃ o ∈ 𝒪[F], x = ϖ * o)
    {x y : Matrix (Fin r) (Fin r) F} (hx : x ∈ intMat 𝒪[F] r r) (hy : y ∈ intMat 𝒪[F] r r) :
    redM x = redM y ↔ x - y ∈ (IIset 𝒪[F] ϖ : Set (Matrix (Fin r) (Fin r) F)) := by
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    exact (red_eq_iff hlt (hx i j) (hy i j)).1 this
  · intro h
    ext i j
    exact (red_eq_iff hlt (hx i j) (hy i j)).2 (h i j)
end GlobalTheory.CompanionTheory.QL.VolK
