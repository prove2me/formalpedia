-- Prove2me | solution 1 for GlobalTheory.DerivEndo.add_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:13:59.325026+00:00
-- url     : https://prove2.me/submissions/63a64c14-6918-466a-91eb-14146cbdf644

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
section
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.DerivEndo
variable {R : Type} [CommRing R] {d : ℕ}
private theorem ev_xy_eq (f : PS R 2 d) :
    ev (n := 2) (![pt R (n := 2) d 0, pt R (n := 2) d 1] : Fin 2 → Pt R 2 d) f = f := by
  have hX : (fun p : Fin 2 × Fin d =>
      (![pt R (n := 2) d 0, pt R (n := 2) d 1] : Fin 2 → Pt R 2 d) p.1 p.2) = X := by
    funext p
    rcases p with ⟨j, i⟩
    fin_cases j <;> rfl
  unfold ev
  rw [hX, subst_self]
  rfl
end GlobalTheory.DerivEndo
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.DerivEndo
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.DerivEndo
theorem _root_.solution (G : FGLaw R d) : G.add (pt R (n := 2) d 0) (pt R (n := 2) d 1) = G.F := by
  funext c
  exact ev_xy_eq (G.F c)
end GlobalTheory.DerivEndo
