-- Prove2me | solution 1 for GlobalTheory.HermWitt.eq_zero_of_forall_dotProduct_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:43.678553+00:00
-- url     : https://prove2.me/submissions/cc2018db-3287-42a0-b138-1f5343e250fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag
variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.HermWitt
theorem _root_.solution {G : Matrix n n E} (hG : G.det ≠ 0) {x : n → E}
    (hx : ∀ y, y ⬝ᵥ G *ᵥ (c ∘ x) = 0) : x = 0 := by
  have h1 : G *ᵥ (c ∘ x) = 0 := by
    funext i
    simpa using hx (Pi.single i 1)
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hG h1
  funext i
  exact (map_eq_zero c).1 (congrFun h3 i)
end GlobalTheory.HermWitt
