-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.Ccr.comm_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:34:50.871192+00:00
-- url     : https://prove2.me/submissions/22994880-6faa-4091-82f4-98c975ca5101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsIsCCRXOpDOp

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
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.Ccr
namespace GlobalTheory.Mem.Lift.Ccr
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] (p p' q q' : A) (s t c₁ c₂ c₃ c₄ : ℂ)
    (h₁ : p * q = q * p + c₁ • (1 : A)) (h₂ : p * q' = q' * p + c₂ • (1 : A))
    (h₃ : p' * q = q * p' + c₃ • (1 : A)) (h₄ : p' * q' = q' * p' + c₄ • (1 : A)) :
    (p + s • p') * (q + t • q') = (q + t • q') * (p + s • p') + (c₁ + t * c₂ + s * c₃ + s * t * c₄) • (1 : A) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h₁, h₂, h₃, h₄]
  module
end GlobalTheory.Mem.Lift.Ccr
