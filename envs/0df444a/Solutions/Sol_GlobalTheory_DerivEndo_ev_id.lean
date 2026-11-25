-- Prove2me | solution 1 for GlobalTheory.DerivEndo.ev_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:14:03.727589+00:00
-- url     : https://prove2.me/submissions/799c4990-5dae-42d9-ae00-5d4ff12a092e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_GermPointsNoConstantTermFirstZero

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
theorem _root_.solution (f : PS R 1 d) : ev (n := 1) ![pt R d 0] f = f := by
  have hX : (fun p : Fin 1 × Fin d => (![pt R d 0] : Fin 1 → Pt R 1 d) p.1 p.2) = X := by
    funext p
    rcases p with ⟨j, i⟩
    rw [Fin.fin_one_eq_zero j]
    rfl
  unfold ev
  rw [hX, subst_self]
  rfl
end GlobalTheory.DerivEndo
