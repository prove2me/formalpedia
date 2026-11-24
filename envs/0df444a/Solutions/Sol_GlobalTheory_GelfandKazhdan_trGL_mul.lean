-- Prove2me | solution 1 for GlobalTheory.GelfandKazhdan.trGL_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:10.847901+00:00
-- url     : https://prove2.me/submissions/2bd6da82-55cb-41ff-bf46-09a7ea7df7a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaireStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixConjTransposeBySymmetricTausskyZassenhausStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TransposeInvariantOfConjInvariantDistributionGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
noncomputable section
open GlobalTheory GlobalTheory.GelfandKazhdan
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.GelfandKazhdan
theorem _root_.solution (g h : GL n R) : trGL (g * h) = trGL h * trGL g :=
  Units.ext (Matrix.transpose_mul _ _)
end GlobalTheory.GelfandKazhdan
