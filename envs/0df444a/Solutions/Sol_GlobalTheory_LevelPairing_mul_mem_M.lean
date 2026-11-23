-- Prove2me | solution 1 for GlobalTheory.LevelPairing.mul_mem_M
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:34.553977+00:00
-- url     : https://prove2.me/submissions/11294df5-7fea-44e9-b5cb-e7b0cff776d4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos

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
theorem _root_.solution {a b : 𝓞 E} (ha : a ∈ l.Mb) (hb : b ∈ Mfr l) : a * b ∈ Ideal.span {(l.M : 𝓞 E)} :=
  l.prod ▸ Ideal.mul_mem_mul ha hb
end GlobalTheory.LevelPairing
