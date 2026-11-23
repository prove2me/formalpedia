-- Prove2me | solution 1 for GlobalTheory.TorusConst.spm_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:15:33.482804+00:00
-- url     : https://prove2.me/submissions/ce443013-f57a-4c4f-b70d-0e60e1f5ced1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
import Theorems.Thm_GlobalTheory_TorusConst_comp_aevalTower
import Theorems.Thm_GlobalTheory_TorusToProper_spm_comp


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
    [CommRing A'] [Algebra K A'] (F : sp K R[X] ⟶ B) (g : A →ₐ[K] A') (c : R →ₐ[K] A) (x : A) :
    spm g ≫ val F c x = val F (g.comp c) (g x) := by
  rw [val, ← Category.assoc, spm_comp, comp_aevalTower, val]
end GlobalTheory.TorusConst
