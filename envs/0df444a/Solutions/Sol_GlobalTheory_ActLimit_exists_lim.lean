-- Prove2me | solution 1 for GlobalTheory.ActLimit.exists_lim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:38:13.902639+00:00
-- url     : https://prove2.me/submissions/a7d95350-90e2-4ac7-ac5c-9a5c6b6e74cd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupActionLimitsIntegralEndomorphisms
import Theorems.Thm_GlobalTheory_ActLimit_exists_tends

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
theorem _root_.solution [CharZero C] {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) {a : ℕ → O}
    (ha : ActCv Y a) : ∃ e : Pt C 1 dd, ∀ i, TendsS V (fun n => Y.B.A.act (a n) i) (e i) := by
  choose e he using fun i μ => exists_tends Y.cpl (s := fun n => MvPowerSeries.coeff μ (Y.B.A.act (a n) i))
    fun N => ha N i μ
  exact ⟨fun i μ => e i μ, he⟩
end GlobalTheory.ActLimit
