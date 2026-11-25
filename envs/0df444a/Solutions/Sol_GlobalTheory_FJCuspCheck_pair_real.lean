-- Prove2me | solution 1 for GlobalTheory.FJCuspCheck.pair_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:42:31.300803+00:00
-- url     : https://prove2.me/submissions/b89d378e-68a4-4629-90e6-8afcdc480890

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_TransvMemZGam
import Theorems.Thm_GlobalTheory_FJCuspCheck_cc_kappa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj.FJ
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.FJCuspCheck
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace GlobalTheory.FJCuspCheck
theorem _root_.solution (X : Data E r) (χ β : Matrix (Fin ρ) (Fin ρ) E) (hχ : IsHermE χ) (hβ : IsSkew β) :
    cc (Matrix.trace (χ.transpose * β) / (X.κ0 / 2)) = Matrix.trace (χ.transpose * β) / (X.κ0 / 2) := by
  have hk := cc_kappa X
  have ht : cc (Matrix.trace (χ.transpose * β)) = -Matrix.trace (χ.transpose * β) := by
    have h1 : ∀ a b, IsCMField.complexConj E (χ a b) = χ b a := hχ
    have h2 : ∀ a b, IsCMField.complexConj E (β a b) = -β b a := hβ
    simp only [cc, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, map_sum,
      map_mul, h1, h2, mul_neg, Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
  unfold cc at hk ht ⊢
  rw [map_div₀, map_div₀, hk, ht, map_ofNat, neg_div 2 X.κ0, neg_div_neg_eq]
end GlobalTheory.FJCuspCheck
