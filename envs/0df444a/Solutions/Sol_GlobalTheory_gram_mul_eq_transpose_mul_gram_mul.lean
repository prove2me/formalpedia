-- Prove2me | solution 1 for GlobalTheory.gram_mul_eq_transpose_mul_gram_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:59:12.243338+00:00
-- url     : https://prove2.me/submissions/acc6a872-6ec0-4799-82b1-ebba1c989bdf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_ScaledBoundInequality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormProdSignMulDetSubmatrixSubOneLe
import Theorems.Thm_GlobalTheory_gram_eq_transpose_mul_mul_map_star

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Matrix hiding gram
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]
namespace GlobalTheory
theorem _root_.solution {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x A : Matrix (Fin r) (Fin r) ℂ) : gram τ G (x * A) = Aᵀ * gram τ G x * A.map star := by
  have h : (x * A).map star = x.map star * A.map star :=
    Matrix.map_mul (f := starRingEnd ℂ)
  rw [gram_eq_transpose_mul_mul_map_star, gram_eq_transpose_mul_mul_map_star, h, transpose_mul]
  simp only [Matrix.mul_assoc]
end GlobalTheory
