-- Prove2me | solution 1 for GlobalTheory.CoeffRingTest.zeta_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:31:31.208308+00:00
-- url     : https://prove2.me/submissions/777d14b2-55c7-4cd1-849c-e85435eb1e59

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_FullIffBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffRingTest
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {O L : Type} [CommRing O] [Field L] (ι : O →+* L) (σ : L →+* ℂ)
namespace GlobalTheory.CoeffRingTest
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zeta n) n := Complex.isPrimitiveRoot_exp n hn
end GlobalTheory.CoeffRingTest
