-- Prove2me | solution 1 for GlobalTheory.Ex.QStr.chr_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:55:58.361794+00:00
-- url     : https://prove2.me/submissions/81ba9694-cd33-4aef-a6b7-cafd54bc7747

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.QStr
variable {X U ι : Type} [AddCommGroup X] [CommGroup U] [Fintype ι] (v : Module.Basis ι ℤ X)
namespace GlobalTheory.Ex.QStr
theorem _root_.solution (u : ι → U) (χ : Multiplicative X) : chr v u χ = ∏ i, u i ^ v.repr χ.toAdd i := rfl
end GlobalTheory.Ex.QStr
