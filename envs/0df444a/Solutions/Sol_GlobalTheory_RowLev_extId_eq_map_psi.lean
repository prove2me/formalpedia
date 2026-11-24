-- Prove2me | solution 1 for GlobalTheory.RowLev.extId_eq_map_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:15:34.196848+00:00
-- url     : https://prove2.me/submissions/e85e33e1-bbe7-4eff-9bf9-1d3b5fee2942

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntAfApproxInterUnitConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExtIdMulSupNatCastConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev
namespace GlobalTheory.RowLev
theorem _root_.solution (I : AutInst) (𝔞 : Ideal (𝓞 I.E)) : extId I 𝔞 = 𝔞.map (Inhab.psi I.F I.E) := by
  unfold extId Ideal.map
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, e⟩
    exact ⟨a, ha, Subtype.ext e.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
end GlobalTheory.RowLev
