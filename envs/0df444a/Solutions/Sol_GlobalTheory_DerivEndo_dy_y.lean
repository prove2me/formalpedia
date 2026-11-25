-- Prove2me | solution 1 for GlobalTheory.DerivEndo.dy_y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:34:37.619617+00:00
-- url     : https://prove2.me/submissions/9619ba7e-3f51-4c4c-88b1-8b9ff58f1668

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_GermPointsNoConstantTermFirstZero
import Theorems.Thm_GlobalTheory_DerivEndo_noConst_one
import Theorems.Thm_GlobalTheory_DerivEndo_cc_pt
import Theorems.Thm_GlobalTheory_DerivEndo_pderiv_ev

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
theorem _root_.solution (h : PS R 1 d) (i : Fin d) :
    pderiv R ((1 : Fin 2), i) (ev (n := 2) ![pt R d 1] h) =
      ev (n := 2) ![pt R d 1] (pderiv R ((0 : Fin 1), i) h) := by
  have hy : NoConst (![pt R (n := 2) d 1] : Fin 1 → Pt R 2 d) := noConst_one (cc_pt 1)
  rw [pderiv_ev hy, Fin.sum_univ_one, Finset.sum_eq_single i]
  · show _ * pderiv R ((1 : Fin 2), i) (X ((1 : Fin 2), i)) = _
    rw [pderiv_X_self, mul_one]
  · intro k _ hk
    show _ * pderiv R ((1 : Fin 2), i) (X ((1 : Fin 2), k)) = 0
    rw [pderiv_X_of_ne (by simp [hk]), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h
end GlobalTheory.DerivEndo
