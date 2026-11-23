-- Prove2me | solution 1 for GlobalTheory.TorusToProper.pt_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:56.493119+00:00
-- url     : https://prove2.me/submissions/4a38d2d4-b655-4dff-ad9a-8fce5543d0a8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Theorems.Thm_GlobalTheory_TorusToProper_charRing_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_ext_ZU


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
variable (K) (X : Type) [AddCommGroup X]
namespace GlobalTheory.TorusToProper
theorem _root_.solution {R R' : Type} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R'] (g : R →ₐ[K] R')
    (φ : Multiplicative X →* Rˣ) :
    pt K X R' ((Units.map (g : R →* R')).comp φ) = spm g ≫ pt K X R φ := by
  apply torus_ext
  change (ptFun K X R' _).left ≫ _ = (Spec.map _ ≫ (ptFun K X R φ).left) ≫ _
  rw [Category.assoc, ptFun_fst, ptFun_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply Rosenlicht.ringHom_ext_ZU
  intro y
  simp [charRing_single]
end GlobalTheory.TorusToProper
