-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.exists_tor_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:42.776247+00:00
-- url     : https://prove2.me/submissions/fbb9f1a1-f8a0-4c64-9c90-874587098364

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__944b82dcaa95


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
theorem _root_.solution (g : N.Gt) : (∃ t, N.tor t = g) ↔ g.b = 1 := by
  constructor
  · rintro ⟨t, rfl⟩; rfl
  · intro h
    refine ⟨MonoidHom.mk' (fun χ => g.s χ.toAdd) fun a b => ?_, Gt.ext h.symm rfl⟩
    have := g.mult a.toAdd b.toAdd
    rwa [h, N.cub.face₃, mul_one] at this
end GlobalTheory.Ex.NumD
