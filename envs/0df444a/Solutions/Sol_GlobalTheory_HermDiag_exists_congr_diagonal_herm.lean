-- Prove2me | solution 1 for GlobalTheory.HermDiag.exists_congr_diagonal_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:15:40.53086+00:00
-- url     : https://prove2.me/submissions/fd6294b1-8809-4d9a-a834-7654c77d9a0f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Theorems.Thm_GlobalTheory_HermDiag_exists_congr_diagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermDiag
open Module Matrix
open NumberField ReciprocityTheory.ChartRestriction.G
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.HermDiag
theorem _root_.solution {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, FD.cc (G a b) = G b a) :
    ∃ (P : Matrix (Fin r) (Fin r) E) (d : Fin r → E), P.det ≠ 0 ∧
      Pᵀ * G * P.map FD.cc = Matrix.diagonal d ∧
      (∀ i, FD.cc (d i) = d i) ∧ (G.det ≠ 0 → ∀ i, d i ≠ 0) :=
  exists_congr_diagonal (c := (IsCMField.complexConj E : E →+* E))
    two_ne_zero (IsCMField.complexConj_apply_apply E) hG
end GlobalTheory.HermDiag
