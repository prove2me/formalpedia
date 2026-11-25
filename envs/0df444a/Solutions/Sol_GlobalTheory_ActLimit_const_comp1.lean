-- Prove2me | solution 1 for GlobalTheory.ActLimit.const_comp1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:35:05.499026+00:00
-- url     : https://prove2.me/submissions/0a072bcd-cedd-4af1-9383-3f1e38263c5e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupActionLimitsIntegralEndomorphisms
import Theorems.Thm_GlobalTheory_ActLimit_const_ev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.ActLimit
variable {C : Type} [Field C] {V : VF C}
variable {dd : ℕ}
namespace GlobalTheory.ActLimit
theorem _root_.solution {n : ℕ} {φ : Pt C 1 dd} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {a : Pt C n dd}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.constantCoeff (comp1 φ a i) = 0 :=
  const_ev (fun j i => by fin_cases j; exact ha i) (hφ i)
end GlobalTheory.ActLimit
