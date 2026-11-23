-- Prove2me | solution 1 for GlobalTheory.UnipotentInvariant.leadMinor_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:49.695666+00:00
-- url     : https://prove2.me/submissions/a52cc08d-9078-43c1-af68-d18993447bf8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory
open GlobalTheory.UnipotentInvariant
variable {K : Type*} [Field K] {p : ℕ}
namespace GlobalTheory.UnipotentInvariant
theorem _root_.solution (i : Fin p) (d : Fin p → K) :
    leadMinor i (diagonal d) = ∏ a ∈ Finset.Iic i, d a := by
  unfold leadMinor
  have : (Matrix.of fun a b : Fin (i.val + 1) =>
      diagonal d (Fin.castLE i.isLt a) (Fin.castLE i.isLt b)) =
      diagonal fun a => d (Fin.castLE i.isLt a) := by
    ext a b
    simp [diagonal_apply]
  rw [this, det_diagonal]
  refine Finset.prod_bij (fun a _ => Fin.castLE i.isLt a) ?_ ?_ ?_ ?_
  · intro a _
    simp only [Finset.mem_Iic, Fin.le_def, Fin.val_castLE]
    omega
  · intro a _ b _ h
    exact Fin.castLE_injective _ h
  · intro b hb
    simp only [Finset.mem_Iic, Fin.le_def] at hb
    exact ⟨⟨b.val, by omega⟩, Finset.mem_univ _, rfl⟩
  · intro a _
    rfl
end GlobalTheory.UnipotentInvariant
