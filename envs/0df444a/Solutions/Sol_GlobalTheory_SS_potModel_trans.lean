-- Prove2me | solution 1 for GlobalTheory.SS.potModel_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:24:41.691091+00:00
-- url     : https://prove2.me/submissions/e4a5bebf-4c8e-4235-a10e-06af0ed53e32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PotModelTrans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


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
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace GlobalTheory.SS
namespace _root_.GlobalTheory.SS
theorem _root_.solution : ∀ (V K V₁ K₁ : Type) [CommRing V] [Field K] [Algebra V K] [CommRing V₁] [Field K₁] [Algebra V₁ K₁] [Algebra V V₁] [Algebra K K₁], (algebraMap V₁ K₁).comp (algebraMap V V₁) = (algebraMap K K₁).comp (algebraMap V K) → Module.Finite V V₁ → IsLocalHom (algebraMap V V₁) → ∀ (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (A₁ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K₁)) [GrpObj A₁] (φ : A₁.left ⟶ A.left), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A₁ A (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K₁)) φ → ∀ Q, _root_.GlobalTheory.SS.PotModel V₁ K₁ A₁ Q → _root_.GlobalTheory.SS.PotModel V K A Q := by
  intro V K V₁ K₁ _ _ _ _ _ _ _ _ hcomm hfin hloc A _ A₁ _ φ hφ Q hP
  obtain ⟨W, L, _, _, _, _, _, _, _, _, h1, h2, h3, h4, G, _, ⟨e, he⟩, hQ⟩ := hP
  letI : Algebra V W := ((algebraMap V₁ W).comp (algebraMap V V₁)).toAlgebra
  letI : Algebra K L := ((algebraMap K₁ L).comp (algebraMap K K₁)).toAlgebra
  have hA : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K₁ L))).obj A₁) A (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L)) (pullback.fst A₁.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K₁ L)) ≫ φ) := by
    refine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback.comp (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A₁ _) hφ).congr ?_ rfl
    rw [← _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
  obtain ⟨e', he', -⟩ := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.grpPullback_iso hA (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A _)
  refine ⟨W, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, h4, G, inferInstance, ⟨e ≪≫ e', ?_⟩, hQ⟩
  · show (algebraMap W L).comp ((algebraMap V₁ W).comp (algebraMap V V₁)) = ((algebraMap K₁ L).comp (algebraMap K K₁)).comp (algebraMap V K)
    rw [← RingHom.comp_assoc, h1, RingHom.comp_assoc, hcomm, RingHom.comp_assoc]
  · exact (RingHom.finite_algebraMap.mpr h2).comp (RingHom.finite_algebraMap.mpr hfin)
  · show IsLocalHom ((algebraMap V₁ W).comp (algebraMap V V₁))
    infer_instance
  · rw [Iso.trans_hom]
    infer_instance
end _root_.GlobalTheory.SS
end GlobalTheory.SS
