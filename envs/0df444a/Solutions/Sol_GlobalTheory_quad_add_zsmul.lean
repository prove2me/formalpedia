-- Prove2me | solution 1 for GlobalTheory.quad_add_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:52:50.697994+00:00
-- url     : https://prove2.me/submissions/779f62fd-f3a0-4661-883e-48dbcbc782f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPosZsmulMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ}
namespace GlobalTheory
theorem _root_.solution (hs : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (y w : X) (t : ℤ) : Q (y + t • w) = Q y + t * Bf y w + t ^ 2 * Q w := by
  have h1 := hQ (y + t • w)
  have h2 := hQ y
  have h3 := hQ w
  have h4 := hs w y
  simp only [map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul] at h1
  have h5 : 2 * Q (y + t • w) = 2 * (Q y + t * Bf y w + t ^ 2 * Q w) := by
    linear_combination h1 - h2 + t * h4 - t ^ 2 * h3
  exact mul_left_cancel₀ two_ne_zero h5
end GlobalTheory
