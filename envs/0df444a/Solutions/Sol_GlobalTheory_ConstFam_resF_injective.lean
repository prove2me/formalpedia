-- Prove2me | solution 1 for GlobalTheory.ConstFam.resF_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:24:00.901728+00:00
-- url     : https://prove2.me/submissions/d0b255e4-2454-470b-bfeb-9d21a3f56139

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_GC_fam__eq_3a137bedd551
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.ConstFam
theorem _root_.solution (j : ℕ) (α : D.X) : Function.Injective (resF D F j α) := by
  have := D.P.isAb.smooth
  have hinj : Function.Injective (toF (R := R) F) :=
    (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R _)
  have : IsDominant (Spec.map (CommRingCat.ofHom (toF (R := R) F))) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [CommRingCat.hom_ofHom, (RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (Spec.map (CommRingCat.ofHom (toF (R := R) F)))
  have : IsSchemeTheoreticallyDominant (DegPre.prB D F).left := .of_isPullback (isPullback_prB D F).flip
  have : QuasiCompact (DegPre.prB D F).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_prB D F).flip inferInstance
  intro s t h
  refine SecOver.ext _ _ fun i => (DegPre.prB D F).left.app_injective _ (fn_ext fun y hy => ?_)
  have e := congrArg (fun q : SecFMod D F j α => gs (𝟙 _) y _ (LB.Sec.f q i)) h
  have hy' : (𝟙 (DegPre.BF D F).left : _ ⟶ _) y ∈ LB.wchart D.P.L (DegPre.famφ D F α) i :=
    (wchart_eq (GC.famφ_eq D F α) i).ge hy
  exact (gs_pull _ _ y _ hy _).trans ((gs_pullFn _ _ _ _ y hy').symm.trans (e.trans
    ((gs_pullFn _ _ _ _ y hy').trans (gs_pull _ _ y _ hy _).symm)))
end GlobalTheory.ConstFam
