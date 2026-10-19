-- Prove2me | solution 1 for OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_channel_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:47:42.691471+00:00
-- url     : https://prove2.me/submissions/49454a35-6a49-4489-ba08-fdecf3bbb2ab

import Mathlib
import Definitions.Def_CrouzeixHilbert
import Definitions.Def_OAIQWCH000
import Theorems.Thm_OAI_CrouzeixHilbert_Conformal_ExteriorCollar_physical_intertwines

section
-- module Solutions.OAIQW_CrouzeixHilbert.PhysicalModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Module. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixHilbert

namespace Conformal.ExteriorCollar

open Boundary

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma physicalRepresentative_trace {k : ℕ} (a : ℤ × (Fin k × Fin k)) (c : ℂ) :
    C.matrixAnalyticTrace C.closure_subset_outerDomain (C.physicalRepresentative a c)
      (C.physicalRepresentative_holomorphic a c).continuousOn = c • C.physicalChannel a := by
  ext t i j
  simp only [matrixAnalyticTrace, physicalRepresentative, physicalChannel, scalarChannel,
    ContinuousMap.coe_mk, ContinuousMap.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Moments. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

variable {n : ℕ} (A : Operator (EuclideanSpace ℂ (Fin n)))
    (hKU : numericalClosure A ⊆ U) (hU : IsOpen U)

variable [Nonempty (Fin n)]

variable (R : InteriorCollar U)

omit [Nonempty (Fin n)] in
lemma tensorIntegral_matrixDensity_trace (D : Operator (EuclideanSpace ℂ (Fin n)))
    (hD : spectralRadius ℂ D < 1) {V : Set ℂ} (hUV : closure U ⊆ V)
    (F : ℂ → Coeff n) (hF : ContinuousOn F V) :
    tensorIntegral (C.matrixDensity R D hD) (C.matrixAnalyticTrace hUV F hF) =
      ∫ t, tensorOperator (C.operatorDensity R D hD t) (F (C.boundaryMap t)) ∂circleMeasure := by
  simp only [tensorIntegral, matrixDensity, matrixAnalyticTrace, ContinuousMap.coe_mk,
    matrixOperatorMap_apply, operatorToMatrix_apply, StarAlgEquiv.apply_symm_apply]

include hKU hU in
lemma physical_channel_intertwines_oai (hc : Convex ℝ U)
    (D S : Operator (EuclideanSpace ℂ (Fin n)))
    (hN : ‖D‖ ≤ 1) (hD : spectralRadius ℂ D < 1)
    (hI : S * holomorphicEval A R.domain R.f = D * S)
    (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    tensorOperator S (1 : Coeff n) *
        matrixHolomorphicEval A C.outerDomain (C.physicalRepresentative a c) =
      tensorIntegral (C.matrixDensity R D hD) (c • C.physicalChannel a) *
        tensorOperator S (1 : Coeff n) := by
  rw [← C.physicalRepresentative_trace a c,
    C.tensorIntegral_matrixDensity_trace R D hD]
  exact C.physical_intertwines R hU hc A D S hKU hN hD hI
    C.isOpen_outerDomain C.closure_subset_outerDomain (C.physicalRepresentative_holomorphic a c)

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

theorem solution : type_of% @OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_channel_intertwines_oai := @OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_channel_intertwines_oai
