-- Prove2me | solution 1 for GlobalTheory.Mass.StabSplit.res_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:34:41.671538+00:00
-- url     : https://prove2.me/submissions/07e773f8-2e09-4c29-95ac-91908b5ca4ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteUnitaryStabilizerSubspaceProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.StabSplit
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.Mass.StabSplit
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (g : isom h)
    (hg : g • U = U) (x : U) : (((res h U g hg).1 x : U) : V) = g.1 x := rfl
end GlobalTheory.Mass.StabSplit
