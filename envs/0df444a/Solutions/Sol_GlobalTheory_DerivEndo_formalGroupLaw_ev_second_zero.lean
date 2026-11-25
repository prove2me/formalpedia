-- Prove2me | solution 1 for GlobalTheory.DerivEndo.formalGroupLaw_ev_second_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:27:08.049935+00:00
-- url     : https://prove2.me/submissions/eb3e0899-5ca9-46c3-8824-a5d2d146a4ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_GermPointsNoConstantTermFirstZero
import Theorems.Thm_GlobalTheory_DerivEndo_noConst_two
import Theorems.Thm_GlobalTheory_DerivEndo_cc_pt
import Theorems.Thm_GlobalTheory_DerivEndo_ev_pt
import Theorems.Thm_GlobalTheory_DerivEndo_ev_ev
import Theorems.Thm_GlobalTheory_DerivEndo_germPointsNoConstantTerm_first_zero

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
theorem _root_.solution (G : FGLaw R d) (c : Fin d) :
    ev (n := 1) ![pt R d 0, 0] (G.F c) = pt R (n := 1) d 0 c := by
  have hs : NoConst (![pt R (n := 2) d 1, pt R (n := 2) d 0] : Fin 2 → Pt R 2 d) :=
    noConst_two (cc_pt 1) (cc_pt 0)
  have hfam : (fun j i => ev (n := 1) ![pt R d 0, 0]
      ((![pt R (n := 2) d 1, pt R (n := 2) d 0] : Fin 2 → Pt R 2 d) j i)) =
        (![0, pt R d 0] : Fin 2 → Pt R 1 d) := by
    funext j i
    fin_cases j
    · show ev (n := 1) ![pt R d 0, 0] (pt R d 1 i) = 0
      rw [ev_pt germPointsNoConstantTerm_first_zero]
      rfl
    · show ev (n := 1) ![pt R d 0, 0] (pt R d 0 i) = pt R d 0 i
      rw [ev_pt germPointsNoConstantTerm_first_zero]
      rfl
  rw [← G.comm c, ev_ev germPointsNoConstantTerm_first_zero hs, hfam]
  exact G.unit c
end GlobalTheory.DerivEndo
