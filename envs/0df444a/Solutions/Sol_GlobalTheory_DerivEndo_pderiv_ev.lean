-- Prove2me | solution 1 for GlobalTheory.DerivEndo.pderiv_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:19:44.046287+00:00
-- url     : https://prove2.me/submissions/5f974055-9fe1-4e93-90a7-be1b7a5fb8ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_GermPointsNoConstantTermFirstZero
import Theorems.Thm_GlobalTheory_DerivEndo_NoConst_hasSubst
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_subst


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
theorem _root_.solution {m n : ℕ} {a : Fin m → Pt R n d} (ha : NoConst a) (f : PS R m d)
    (v : Fin n × Fin d) :
    pderiv R v (ev a f) = ∑ j, ∑ i, ev a (pderiv R (j, i) f) * pderiv R v (a j i) := by
  unfold ev
  rw [GlobalTheory.FormalCalc.pderiv_subst ha.hasSubst, Fintype.sum_prod_type]
end GlobalTheory.DerivEndo
