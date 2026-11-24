-- Prove2me | solution 1 for GlobalTheory.BetaEx.map_smul_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:01:26.122855+00:00
-- url     : https://prove2.me/submissions/a4041124-fefc-40d7-8aa4-983eb29f79b1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal

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
open GlobalTheory GlobalTheory.BetaEx
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E F : Type} [Field E] [Field F] (φ : E →+* F)
namespace GlobalTheory.BetaEx
theorem _root_.solution (b : 𝓞 E) (x : E) : φ (b • x) = RingOfIntegers.mapRingHom φ b • φ x := by
  change φ ((b : E) * x) = _
  rw [map_mul]; rfl
end GlobalTheory.BetaEx
