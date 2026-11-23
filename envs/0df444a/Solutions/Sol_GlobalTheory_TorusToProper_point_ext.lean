-- Prove2me | solution 1 for GlobalTheory.TorusToProper.point_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:20.97139+00:00
-- url     : https://prove2.me/submissions/e7d6ca4e-9174-45f5-a2aa-7eb691146f5e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusToProper
variable {K : Type} [Field K]
namespace GlobalTheory.TorusToProper
theorem _root_.solution {V F : Type} [CommRing V] [IsDomain V] [Algebra K V] [CommRing F] [Algebra K F]
    (j : V →ₐ[K] F) (hj : Function.Injective j)
    {B : Over (Spec (CommRingCat.of K))} [IsSeparated B.hom] {b b' : sp K V ⟶ B}
    (h : spm j ≫ b = spm j ≫ b') : b = b' := by
  ext1
  have hd : IsDominant (Spec.map (CommRingCat.ofHom j.toRingHom)) := by
    constructor
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j.toRingHom).2
      (by rw [(RingHom.injective_iff_ker_eq_bot j.toRingHom).1 hj]; exact bot_le)
  have : IsReduced (sp K V).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of V)))
  exact ext_of_isDominant_of_isSeparated B.hom ((Over.w b).trans (Over.w b').symm)
    (Spec.map (CommRingCat.ofHom j.toRingHom)) (congrArg CommaMorphism.left h)
end GlobalTheory.TorusToProper
