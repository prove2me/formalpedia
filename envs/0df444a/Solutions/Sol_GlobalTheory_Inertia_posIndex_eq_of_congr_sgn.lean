-- Prove2me | solution 1 for GlobalTheory.Inertia.posIndex_eq_of_congr_sgn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:03:38.415087+00:00
-- url     : https://prove2.me/submissions/67c21980-2ca0-4db3-aaf1-5d1a28bc1598

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_congr
import Theorems.Thm_GlobalTheory_Inertia_posIndex_diagonal_sgn

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
theorem _root_.solution {G P : Matrix (Fin r) (Fin r) ℂ} {p : ℕ} (hp : p ≤ r)
    (hP : P.det ≠ 0)
    (h : Pᵀ * G * P.map conj = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) :
    posIndex G = p := by
  rw [← posIndex_congr G hP, h, posIndex_diagonal_sgn hp]
end GlobalTheory.Inertia
