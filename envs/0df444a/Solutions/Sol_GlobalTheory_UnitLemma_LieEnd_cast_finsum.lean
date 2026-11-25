-- Prove2me | solution 1 for GlobalTheory.UnitLemma.LieEnd.cast_finsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:03:41.858142+00:00
-- url     : https://prove2.me/submissions/bba6bc01-8453-4517-8c52-3345ddf33d53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetEqOneOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GramDetEqNormMulGramDetOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaSelfAdjointLieOfCountLimitDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.LieEnd
open GlobalTheory.UnitLemma Polynomial Filter Topology
variable {K : UQ}
namespace GlobalTheory.UnitLemma.LieEnd
theorem _root_.solution {ι : Type} (f : ι → ℚ) : ((∑ᶠ i, f i : ℚ) : ℝ) = ∑ᶠ i, (f i : ℝ) := (Rat.castHom ℝ).toAddMonoidHom.map_finsum_of_injective Rat.cast_injective f
end GlobalTheory.UnitLemma.LieEnd
