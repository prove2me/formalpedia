-- Prove2me | solution 1 for GlobalTheory.Inertia.congr_sgn_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:29:14.882123+00:00
-- url     : https://prove2.me/submissions/e5992ed6-7663-4024-b5f7-c8d37f082c25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_le
import Theorems.Thm_GlobalTheory_Inertia_posIndex_eq_of_congr_sgn
import Theorems.Thm_GlobalTheory_Inertia_exists_congr_sgn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
variable {r s : ℕ}
namespace GlobalTheory.Inertia
theorem _root_.solution {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.IsHermitian) (hG0 : G.det ≠ 0)
    (p : ℕ) :
    (p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      Pᵀ * G * P.map conj = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) ↔
      p = posIndex G := by
  constructor
  · rintro ⟨hp, P, hP, h⟩
    exact (posIndex_eq_of_congr_sgn hp hP h).symm
  · rintro rfl
    exact ⟨posIndex_le G, exists_congr_sgn hG hG0⟩
end GlobalTheory.Inertia
