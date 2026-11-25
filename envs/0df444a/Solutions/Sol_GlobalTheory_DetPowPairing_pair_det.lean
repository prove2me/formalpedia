-- Prove2me | solution 1 for GlobalTheory.DetPowPairing.pair_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:14:24.449192+00:00
-- url     : https://prove2.me/submissions/e936d6b3-543d-4090-8b8c-eaa60ceff055

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Theorems.Thm_GlobalTheory_DetPowPairing_pair_list

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
noncomputable section
open GlobalTheory GlobalTheory.DetPowPairing
open MvPolynomial
variable {σ : Type} {C : Type} [CommRing C]
namespace GlobalTheory.DetPowPairing
theorem _root_.solution (n : ℕ) (P Q : MvPolynomial (Fin n × Fin n) C) :
    pair (P * cayDet n C) Q = pair P (cayOp n C Q) := by
  have hdet : cayDet n C = ∑ s : Equiv.Perm (Fin n),
      (Equiv.Perm.sign s : ℤ) • ((List.finRange n).map fun i => (X (s i, i) : MvPolynomial _ C)).prod := by
    rw [cayDet, Matrix.det_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Units.smul_def, Fin.prod_univ_def]
    rfl
  rw [hdet, cayOp, Finset.mul_sum, map_sum, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_smul_comm, map_zsmul, LinearMap.smul_apply, LinearMap.smul_apply, map_zsmul]
  exact congrArg (fun t => (Equiv.Perm.sign s : ℤ) • t) (pair_list (fun i => (s i, i)) (List.finRange n) P Q)
end GlobalTheory.DetPowPairing
