-- Prove2me | solution 1 for GlobalTheory.FlagDomain.gram_eq_transpose_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:46:19.14667+00:00
-- url     : https://prove2.me/submissions/f706e838-9270-480e-9113-958fe0c924d1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DefiniteFrameLeadingMinorsSign

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
    (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
end GlobalTheory.FlagDomain
