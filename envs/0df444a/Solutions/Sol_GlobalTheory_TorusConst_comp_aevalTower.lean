-- Prove2me | solution 1 for GlobalTheory.TorusConst.comp_aevalTower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:45.503749+00:00
-- url     : https://prove2.me/submissions/d2c40770-c957-4040-a19c-3e691906d0bd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst

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
namespace GlobalTheory.TorusConst
theorem _root_.solution {R A A' : Type} [CommRing R] [Algebra K R] [CommRing A] [Algebra K A]
    [CommRing A'] [Algebra K A'] (g : A →ₐ[K] A') (c : R →ₐ[K] A) (x : A) :
    g.comp (aevalTower c x) = aevalTower (g.comp c) (g x) := by
  apply Polynomial.algHom_ext'
  · ext r
    simp
  · simp
end GlobalTheory.TorusConst
