-- Prove2me | solution 1 for GlobalTheory.LogKS.existsUnique_isTranslate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:05:26.954795+00:00
-- url     : https://prove2.me/submissions/d3fc14f1-c824-414e-aa09-7a7c6ef0403a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped Matrix
open GlobalTheory GlobalTheory.LogKS
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
namespace GlobalTheory.LogKS
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {x : Sp R ⟶ X}
    {g : Sp S ⟶ t.G.left} (hg : g ≫ t.G.hom = spMap φ ≫ x) {v : Sp (DualNumber R) ⟶ t.G.left}
    (hv : IsTanAtG t x v) : ∃! w, IsTranslate t φ g v w := by
  have e : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp φ := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have h2 : (spMap (dualMap φ) ≫ v) ≫ t.G.hom = (tEpsG (g ≫ t.G.hom)).hom := by
    show _ = spMap (algebraMap S (DualNumber S)) ≫ g ≫ t.G.hom
    rw [Category.assoc, hv.1, hg, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
  refine ⟨_, ⟨Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ g) (Category.assoc _ _ _),
    Over.homMk (spMap (dualMap φ) ≫ v) h2, rfl, rfl, rfl⟩, ?_⟩
  rintro w ⟨g', v', h₁, h₂, rfl⟩
  congr 2
  · exact Over.OverMorphism.ext h₁
  · exact Over.OverMorphism.ext h₂
end GlobalTheory.LogKS
