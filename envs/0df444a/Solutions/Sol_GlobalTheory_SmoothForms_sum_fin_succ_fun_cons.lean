-- Prove2me | solution 1 for GlobalTheory.SmoothForms.sum_fin_succ_fun_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:17.617812+00:00
-- url     : https://prove2.me/submissions/d4a01ec2-ea3d-4b94-83ee-a4e0b345a92b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PowEntryCommutator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms
variable {A : Type} [Ring A] {n : ℕ}
namespace GlobalTheory.SmoothForms
theorem _root_.solution {M : Type} [AddCommMonoid M] (k : ℕ) (f : (Fin (k + 1) → Fin n) → M) :
    ∑ idx, f idx = ∑ c : Fin n, ∑ idx : Fin k → Fin n, f (Fin.cons c idx) := by
  rw [← Fintype.sum_prod_type']
  exact ((Fin.consEquiv fun _ : Fin (k + 1) => Fin n).sum_comp f).symm
end GlobalTheory.SmoothForms
