-- Prove2me | solution 1 for GlobalTheory.HermDiag.exists_congr_diagonal_herm_col_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:19:50.859359+00:00
-- url     : https://prove2.me/submissions/6402f1e9-6931-420e-b00f-dca7a8d4a1a4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Theorems.Thm_GlobalTheory_HermDiag_exists_congr_diagonal_col_eq
import Theorems.Thm_GlobalTheory_HermDiag_herm_eq_dotProduct

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
    (hG : ∀ a b, FD.cc (G a b) = G b a) {x : Fin r → E} (hx : FD.herm G x x ≠ 0) (i₀ : Fin r) :
    ∃ (P : Matrix (Fin r) (Fin r) E) (d : Fin r → E), P.det ≠ 0 ∧
      Pᵀ * G * P.map FD.cc = Matrix.diagonal d ∧
      (∀ i, FD.cc (d i) = d i) ∧ (G.det ≠ 0 → ∀ i, d i ≠ 0) ∧
      (∀ k, P k i₀ = x k) ∧ d i₀ = FD.herm G x x := by
  simp only [herm_eq_dotProduct] at hx ⊢
  exact exists_congr_diagonal_col_eq (c := (IsCMField.complexConj E : E →+* E))
    two_ne_zero (IsCMField.complexConj_apply_apply E) hG hx i₀
end GlobalTheory.HermDiag
