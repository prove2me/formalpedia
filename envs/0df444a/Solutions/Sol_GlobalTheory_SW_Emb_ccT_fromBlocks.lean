-- Prove2me | solution 1 for GlobalTheory.SW.Emb.ccT_fromBlocks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:08.660272+00:00
-- url     : https://prove2.me/submissions/cef46837-f369-4d0f-8d29-c171922a54ac

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.Emb
theorem _root_.solution {m : ℕ} (A B C D : Matrix (Fin m) (Fin m) E) :
    ccT (Matrix.fromBlocks A B C D) = Matrix.fromBlocks (ccT A) (ccT C) (ccT B) (ccT D) := by
  simp [ccT, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]
end GlobalTheory.SW.Emb
