-- Prove2me | solution 1 for GlobalTheory.TorsionMatrix.det_eq_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:34:56.57993+00:00
-- url     : https://prove2.me/submissions/6e98e4a9-c917-461a-8eb7-51e684b48cf6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NormCardQuotientSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MatrixPolynomialDetNormFixedPoints
import Theorems.Thm_GlobalTheory_TorsionMatrix_map_ev
import Theorems.Thm_GlobalTheory_TorsionMatrix_ev_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.TorsionMatrix
open Matrix
variable {Q κ : Type} [AddCommGroup Q] [Fintype κ] {N : ℕ} [NeZero N]
namespace GlobalTheory.TorsionMatrix
theorem _root_.solution [DecidableEq κ] (g : Q →+ Q) {pt pt' : κ → Q} (h : ∀ i, N • pt i = 0)
    (h' : ∀ i, N • pt' i = 0)
    (hb : ∀ y : Q, N • y = 0 → ∃! c : κ → ZMod N, ∑ i, (c i).val • pt i = y)
    (hb' : ∀ y : Q, N • y = 0 → ∃! c : κ → ZMod N, ∑ i, (c i).val • pt' i = y)
    (M M' : Matrix κ κ (ZMod N)) (hM : ∀ j, g (pt j) = ∑ i, (M i j).val • pt i)
    (hM' : ∀ j, g (pt' j) = ∑ i, (M' i j).val • pt' i) : M.det = M'.det := by
  choose P hP using fun j => (hb' _ (h j)).exists
  choose P' hP' using fun j => (hb _ (h' j)).exists
  have e1 := map_ev (AddMonoidHom.id Q) h h' (Matrix.of P)ᵀ fun j => (hP j).symm
  have e2 := map_ev (AddMonoidHom.id Q) h' h (Matrix.of P')ᵀ fun j => (hP' j).symm
  simp only [AddMonoidHom.id_apply] at e1 e2
  have f1 : (Matrix.of P)ᵀ * (Matrix.of P')ᵀ = 1 := by
    refine Matrix.mulVec_injective (funext fun t => ev_injective h' hb' ?_)
    rw [← mulVec_mulVec, ← e1, ← e2, one_mulVec]
  have f2 : (Matrix.of P)ᵀ * M = M' * (Matrix.of P)ᵀ := by
    refine Matrix.mulVec_injective (funext fun t => ev_injective h' hb' ?_)
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← e1, ← map_ev g h' h' M' hM', ← e1,
      ← map_ev g h h M hM]
  have hu := Matrix.isUnit_det_of_right_inverse f1
  have := congrArg Matrix.det f2
  rw [det_mul, det_mul, mul_comm] at this
  exact hu.mul_right_cancel this
end GlobalTheory.TorsionMatrix
