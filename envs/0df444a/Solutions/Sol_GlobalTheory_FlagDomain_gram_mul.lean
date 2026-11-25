-- Prove2me | solution 1 for GlobalTheory.FlagDomain.gram_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:10.121938+00:00
-- url     : https://prove2.me/submissions/ed5fc1d9-8422-446f-99df-8461fb9b5396

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DefiniteFrameLeadingMinorsSign
import Theorems.Thm_GlobalTheory_FlagDomain_gram_eq_transpose_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexOrder ComplexConjugate Matrix
open GlobalTheory GlobalTheory.FlagDomain
namespace GlobalTheory.FlagDomain
theorem _root_.solution {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (P * Q) = Qᵀ * gram τ G P * Q.map (starRingEnd ℂ) := by
  rw [gram_eq_transpose_mul, gram_eq_transpose_mul, Matrix.transpose_mul,
    Matrix.map_mul]
  simp only [Matrix.mul_assoc]
end GlobalTheory.FlagDomain
