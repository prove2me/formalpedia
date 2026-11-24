-- Prove2me | solution 1 for GlobalTheory.BoxCosetSum.mem_boxSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:51.806839+00:00
-- url     : https://prove2.me/submissions/84790029-9a40-4f95-9041-df4c445d16c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScalingOpenSubgroupsFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.BoxCosetSum
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.BoxCosetSum
theorem _root_.solution {κ : Type} {B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)}
    {u : κ → FiniteAdeleRing (𝓞 F) F} :
    u ∈ boxSub κ B ↔ ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v := Iff.rfl
end GlobalTheory.BoxCosetSum
