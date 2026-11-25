-- Prove2me | solution 1 for GlobalTheory.Inertia.existsUnique_congr_sgn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:02:20.92072+00:00
-- url     : https://prove2.me/submissions/b4b7ff8f-454d-4beb-b8ad-4195425ec6b1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_congr_sgn_iff

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
theorem _root_.solution {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.IsHermitian)
    (hG0 : G.det ≠ 0) :
    ∃! p : ℕ, p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      Pᵀ * G * P.map conj = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ) :=
  ⟨posIndex G, (congr_sgn_iff hG hG0 _).2 rfl, fun p hp => (congr_sgn_iff hG hG0 p).1 hp⟩
end GlobalTheory.Inertia
