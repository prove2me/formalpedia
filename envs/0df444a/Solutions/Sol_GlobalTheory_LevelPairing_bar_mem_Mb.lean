-- Prove2me | solution 1 for GlobalTheory.LevelPairing.bar_mem_Mb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:35.310906+00:00
-- url     : https://prove2.me/submissions/98e48478-c554-4097-ae0e-e161a58a4e3f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Theorems.Thm_GlobalTheory_LevelPairing_bar_bar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevelPairing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace GlobalTheory.LevelPairing
theorem _root_.solution {a : 𝓞 E} (ha : a ∈ Mfr l) : H.bar a ∈ l.Mb := by
  obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 ha
  have : H.bar ((H.bar : 𝓞 E →+* 𝓞 E) b) = b := bar_bar H b
  rwa [this]
end GlobalTheory.LevelPairing
