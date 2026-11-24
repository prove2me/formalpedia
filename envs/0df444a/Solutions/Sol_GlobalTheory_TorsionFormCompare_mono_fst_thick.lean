-- Prove2me | solution 1 for GlobalTheory.TorsionFormCompare.mono_fst_thick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:32:59.034297+00:00
-- url     : https://prove2.me/submissions/eb4682b5-57b4-4e20-b67a-3081f1556e25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GmMulEqOfResMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUniformizationIdentityPullback

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
open GlobalTheory GlobalTheory.TorsionFormCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace GlobalTheory.TorsionFormCompare
theorem _root_.solution {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Sp R)) :
    Mono (pullback.fst G.hom (thick R I e)) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance
end GlobalTheory.TorsionFormCompare
