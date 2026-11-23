-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.tor_mul_s_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:25.197932+00:00
-- url     : https://prove2.me/submissions/13c3789f-7f1c-4595-b0cc-06b1c9c52028

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
attribute [instance] NumB.grp
attribute [instance] NumD.add NumD.free NumD.fin
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.NumD
variable (N : NumD O)
namespace GlobalTheory.Ex.NumD
theorem _root_.solution (t : Multiplicative N.X →* Oˣ) (g : N.Gt) (χ : N.X) :
    (N.tor t * g).s χ = t (Multiplicative.ofAdd χ) * g.s χ := by
  rw [Gt.mul_s, tor_b, N.cub.face₂, div_one, torus_generator_apply]
end GlobalTheory.Ex.NumD
