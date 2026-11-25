-- Prove2me | solution 1 for GlobalTheory.DerivEndo.ev_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:19:50.83796+00:00
-- url     : https://prove2.me/submissions/69b37cfc-36b9-45c6-a2cb-909277aa8a6e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_GermPointsNoConstantTermFirstZero
import Theorems.Thm_GlobalTheory_DerivEndo_NoConst_hasSubst

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.DerivEndo
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.DerivEndo
theorem _root_.solution {m n : ℕ} {a : Fin m → Pt R n d} (ha : NoConst a) {κ : Type} (s : Finset κ)
    (f : κ → PS R m d) : ev a (∑ k ∈ s, f k) = ∑ k ∈ s, ev a (f k) := by
  unfold ev
  rw [← coe_substAlgHom ha.hasSubst]
  exact map_sum _ f s
end GlobalTheory.DerivEndo
