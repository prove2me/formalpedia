-- Prove2me | solution 1 for GlobalTheory.TorusConst.val_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:33:56.372799+00:00
-- url     : https://prove2.me/submissions/dafb512e-feeb-460f-b165-7a17f30fd777

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
import Theorems.Thm_GlobalTheory_TorusConst_spm_val

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
variable [GrpObj B] {L R : Type} [Field L] [Algebra K L] [CommRing R] [Algebra K R]
namespace GlobalTheory.TorusConst
theorem _root_.solution (b : sp K L[X] ⟶ B) (i : L →ₐ[K] R) (s : R) {A : Type} [CommRing A] [Algebra K A]
    (c : R →ₐ[K] A) (x : A) :
    val (twist b i s) c x = val b (c.comp i) (c s * x) * (val b (c.comp i) x)⁻¹ := by
  have h : (aevalTower c x).comp (CAlgHom.comp i) = c.comp i := by
    ext a
    simp
  rw [val, twist, MonObj.comp_mul, GrpObj.comp_inv, spm_val, spm_val, h, map_mul, aevalTower_C,
    aevalTower_X]
end GlobalTheory.TorusConst
