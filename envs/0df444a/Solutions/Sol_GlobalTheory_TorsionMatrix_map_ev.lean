-- Prove2me | solution 1 for GlobalTheory.TorsionMatrix.map_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:07:14.230501+00:00
-- url     : https://prove2.me/submissions/1720f2fa-c815-4f24-ba8f-8f8347371592

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NormCardQuotientSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MatrixPolynomialDetNormFixedPoints
import Theorems.Thm_GlobalTheory_TorsionMatrix_val_mul_smul
import Theorems.Thm_GlobalTheory_TorsionMatrix_ev_apply

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
theorem _root_.solution (g : Q →+ Q) {pt pt' : κ → Q} (h : ∀ i, N • pt i = 0) (h' : ∀ i, N • pt' i = 0)
    (M : Matrix κ κ (ZMod N)) (hM : ∀ j, g (pt j) = ∑ i, (M i j).val • pt' i) (t : κ → ZMod N) :
    g (ev pt h t) = ev pt' h' (M *ᵥ t) := by
  have : M *ᵥ t = ∑ j, fun i => M i j * t j := by
    funext i
    simp [mulVec, dotProduct, Finset.sum_apply]
  rw [this, map_sum, ev_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_nsmul, hM, ev_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => (val_mul_smul (h' i) _ _).symm
end GlobalTheory.TorsionMatrix
