-- Prove2me | solution 1 for GlobalTheory.SW.Emb.det_cor_den
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:15.900487+00:00
-- url     : https://prove2.me/submissions/fc4dcd61-0ccc-4bb3-bf49-8319eb694131

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Emb
noncomputable section
variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ}
namespace GlobalTheory.SW.Emb
theorem _root_.solution (C D : Matrix (Fin N) (Fin N) R) (Z : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    (cor 0 C * Z + cor 1 D).det = (C * Z.submatrix Fin.succ Fin.succ + D).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have e : (cor 0 C * Z + cor 1 D).submatrix Fin.succ (Fin.succAbove 0) = C * Z.submatrix Fin.succ Fin.succ + D := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_succ]
  rw [e]
  simp [Matrix.mul_apply, Fin.sum_univ_succ]
end GlobalTheory.SW.Emb
