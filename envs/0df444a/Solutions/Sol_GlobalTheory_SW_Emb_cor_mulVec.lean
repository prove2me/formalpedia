-- Prove2me | solution 1 for GlobalTheory.SW.Emb.cor_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:09.190599+00:00
-- url     : https://prove2.me/submissions/453c2694-d41b-4dd0-9dbb-4e409b32b7a0

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
theorem _root_.solution (a : R) (A : Matrix (Fin N) (Fin N) R) (x : R) (v : Fin N → R) :
    cor a A *ᵥ (Fin.cons x v : Fin (N + 1) → R) = (Fin.cons (a * x) (A *ᵥ v) : Fin (N + 1) → R) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
end GlobalTheory.SW.Emb
