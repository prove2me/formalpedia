-- Prove2me | solution 1 for GlobalTheory.TorusConst.comp_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:34:05.141405+00:00
-- url     : https://prove2.me/submissions/291425ca-8b83-425b-87b4-f5aa825eef52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
import Theorems.Thm_GlobalTheory_TorusConst_comp_aevalTower
import Theorems.Thm_GlobalTheory_TorusConst_ev_comp_inc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusConst
open Polynomial TorusToProper
variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))}
open LaurentPolynomial
variable {L : Type} [Field L] [Algebra K L]
namespace GlobalTheory.TorusConst
theorem _root_.solution {A A' : Type} [CommRing A] [Algebra K A] [CommRing A'] [Algebra K A']
    (g : A →ₐ[K] A') (c : L →ₐ[K] A) (x : Aˣ) :
    g.comp (ev c x) = ev (g.comp c) (Units.map (g : A →* A') x) := by
  have h : (g.comp (ev c x)).comp (inc K L) =
      (ev (g.comp c) (Units.map (g : A →* A') x)).comp (inc K L) := by
    rw [AlgHom.comp_assoc, ev_comp_inc, ev_comp_inc, comp_aevalTower]
    rfl
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (X : L[X]))
  exact RingHom.ext fun p => AlgHom.congr_fun h p
end GlobalTheory.TorusConst
