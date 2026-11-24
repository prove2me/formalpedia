-- Prove2me | solution 1 for GlobalTheory.Ex.QStr.chr_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:06:04.005885+00:00
-- url     : https://prove2.me/submissions/af9d20ab-2737-4bc0-af97-8b889b52a139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Theorems.Thm_GlobalTheory_Ex_QStr_chr_basis

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
theorem _root_.solution : Function.Injective (chr (U := U) v) := fun u u' h =>
  funext fun i => by rw [← chr_basis v u, h, chr_basis]
end GlobalTheory.Ex.QStr
