-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.Normal.sum_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:32:55.97881+00:00
-- url     : https://prove2.me/submissions/8c3a1eff-2ecb-48f6-9b65-41bcf2f2baa8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfNormal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.Normal
variable {ι : Type}
variable [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.Mem.Lift.Normal
theorem _root_.solution (X : Matrix ι ι ℂ) (A : (ι → ℂ) →ₗ[ℂ] ℂ) (v : ι → ℂ) :
    ∑ k, ∑ j, X k j * (v j * A (Pi.single k 1)) = A (X *ᵥ v) := by
  have hx : X *ᵥ v = ∑ k, (∑ j, X k j * v j) • (Pi.single k (1 : ℂ) : ι → ℂ) := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply]
  rw [hx, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end GlobalTheory.Mem.Lift.Normal
