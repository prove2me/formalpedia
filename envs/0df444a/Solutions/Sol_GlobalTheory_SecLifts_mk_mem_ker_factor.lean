-- Prove2me | solution 1 for GlobalTheory.SecLifts.mk_mem_ker_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:55:31.465834+00:00
-- url     : https://prove2.me/submissions/c3524ac1-3f87-4d62-bd0e-65f92cb0ebb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompatibleSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SecLifts
namespace GlobalTheory.SecLifts
theorem _root_.solution {R : Type} [CommRing R] {I J : Ideal R} (h : I ≤ J) (x : R) :
    Ideal.Quotient.mk I x ∈ RingHom.ker (Ideal.Quotient.factor h) ↔ x ∈ J := by
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
end GlobalTheory.SecLifts
