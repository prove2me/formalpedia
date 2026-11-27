-- Prove2me | solution 1 for GlobalTheory.ZJ.isSemiAbelian_of_splitAll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:36:42.254465+00:00
-- url     : https://prove2.me/submissions/5403069a-b5a2-4404-9d2d-dc57563f6915

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyTorusExtensionOfIsGt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsSemiAbelianOfSplitAll
import Theorems.Thm_GlobalTheory_ZJ_SplitAll_fieldPoint
import Theorems.Thm_GlobalTheory_UnitRigidity_smooth_geometricallyConnected_of_isGt
import Theorems.Thm_GlobalTheory_nonempty_torusExtension_of_isGt


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
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ
namespace GlobalTheory.ZJ
theorem _root_.solution : ∀ (Z : Scheme.{0}) (G : Over Z) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom], SplitAll G → IsSemiAbelian G ∧ (∀ (K : Type) [Field K] (t : Sp K ⟶ Z), ∃ E : SplitExt (Sp K), E.IsGt ((Over.pullback t).obj G)) ∧ ∀ x : Z, ∃ (k : Type) (_ : Field k) (_ : Algebra (Z.residueField x) k), FiniteDimensional (Z.residueField x) k ∧ Algebra.IsSeparable (Z.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField x) k)) ≫ Z.fromSpecResidueField x)).obj G) := by
  intro Z G _ hc hs hsep hq h
  refine ⟨⟨hc, hs, hsep, hq, ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ q => ?_⟩,
    fun Ω _ _ q => ?_⟩, h.fieldPoint, fun x => ⟨Z.residueField x, inferInstance, inferInstance, inferInstance,
      inferInstance, h.fieldPoint _ _⟩⟩
  · obtain ⟨E, hE⟩ := h.fieldPoint K q
    have hg : GeometricallyConnected (pullback.snd G.hom q) :=
      (UnitRigidity.smooth_geometricallyConnected_of_isGt E _ hE).2
    rw [← (pullbackLeftPullbackSndIso G.hom q (𝟙 _) ≪≫ pullback.congrHom rfl (Category.id_comp q)).hom.homeomorph.connectedSpace_iff]
    exact pullback_of_geometrically hg.1 K (𝟙 _)
  · obtain ⟨E, hE⟩ := h.fieldPoint Ω q
    exact nonempty_torusExtension_of_isGt E _ hE
end GlobalTheory.ZJ
