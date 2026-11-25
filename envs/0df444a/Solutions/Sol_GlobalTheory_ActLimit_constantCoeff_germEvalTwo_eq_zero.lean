-- Prove2me | solution 1 for GlobalTheory.ActLimit.constantCoeff_germEvalTwo_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:35:07.1398+00:00
-- url     : https://prove2.me/submissions/9b3e2572-697e-4854-b52b-96e97dca661c

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
theorem _root_.solution {n : ℕ} {a b : Pt C n dd} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) {f : PS C 2 dd} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (ev ![a, b] f) = 0 :=
  const_ev (fun j i => by fin_cases j; exacts [ha i, hb i]) hf
end GlobalTheory.ActLimit
