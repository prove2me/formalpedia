-- Prove2me | solution 1 for GlobalTheory.UU.exists_tq_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:33:19.058026+00:00
-- url     : https://prove2.me/submissions/8a3e83df-c43e-4003-a21c-fb3e246e9f03

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ESecCompOfIsGrpPullback
import Theorems.Thm_GlobalTheory_UU_isMonHom_of_over_isMonHom
import Theorems.Thm_GlobalTheory_UU_eSec_comp_of_isGrpPullback
import Theorems.Thm_GlobalTheory_UU_IsWt_pull
import Theorems.Thm_GlobalTheory_SplitTorus_isGrpPullback_bcMap
import Theorems.Thm_GlobalTheory_UU_TorusCompat_isMonHom
import Theorems.Thm_GlobalTheory_UU_existsUnique_torusCompat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S S' : Scheme.{0}} {f : S' ⟶ S}
namespace GlobalTheory.UU
theorem _root_.solution : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G]
    (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F →
    ∀ Q : TQ G X, ∃ Q' : TQ G' X, TorusCompat f F Q'.i Q.i := by
  intro S S' f X _ G _ G' _ F hF Q
  letI := Q.grp
  letI := Q.comm
  haveI := Q.q_hom
  haveI := Q.i_hom
  obtain ⟨i', hi', -⟩ := existsUnique_torusCompat hF.1 Q.i
  haveI : IsMonHom i' := TorusCompat.isMonHom hF hi'
  have hB := isGrpPullback_pullback Q.B f
  let q' : G' ⟶ (Over.pullback f).obj Q.B :=
    Over.homMk (pullback.lift (F ≫ Q.q.left) G'.hom (by rw [Category.assoc, Over.w Q.q, hF.1.w]))
      (by exact pullback.lift_snd _ _ _)
  have hq'fst : q'.left ≫ pullback.fst Q.B.hom f = F ≫ Q.q.left := pullback.lift_fst _ _ _
  haveI : IsMonHom q' := isMonHom_of_over_isMonHom hF hB Q.q q' hq'fst
  have hBsq : IsPullback F q'.left Q.q.left (pullback.fst Q.B.hom f) := by
    refine IsPullback.of_bot ?_ hq'fst.symm (IsPullback.of_hasPullback Q.B.hom f)
    have e1 : q'.left ≫ pullback.snd Q.B.hom f = G'.hom := pullback.lift_snd _ _ _
    rw [e1, Over.w Q.q]
    exact hF.1
  have hAb : IsAbelianScheme ((Over.pullback f).obj Q.B) := by
    haveI := Q.isAb.smooth
    haveI := Q.isAb.proper
    haveI := Q.isAb.geomConnected
    exact ⟨inferInstance, by simp only [Over.pullback_obj_hom]; infer_instance,
      by simp only [Over.pullback_obj_hom]; infer_instance, by simp only [Over.pullback_obj_hom]; infer_instance⟩
  have hη : (η[(Over.pullback f).obj Q.B]).left ≫ pullback.fst Q.B.hom f = f ≫ (η[Q.B]).left :=
    eSec_comp_of_isGrpPullback hB
  have hT' : (toUnit (splitTorus S' X)).left = (splitTorus S' X).hom := by
    have := Over.w (toUnit (splitTorus S' X))
    simpa using this
  have hT : (toUnit (splitTorus S X)).left = (splitTorus S X).hom := by
    have := Over.w (toUnit (splitTorus S X))
    simpa using this
  have hker0 : IsPullback Q.i.left (splitTorus S X).hom Q.q.left (η[Q.B]).left := by
    have h0 : IsPullback Q.i.left (toUnit (splitTorus S X)).left Q.q.left (η[Q.B]).left :=
      Q.isKernel.map (Over.forget S)
    rw [hT] at h0
    exact h0
  have hcomp : IsPullback (i'.left ≫ F) (splitTorus S' X).hom Q.q.left
      ((η[(Over.pullback f).obj Q.B]).left ≫ pullback.fst Q.B.hom f) := by
    rw [← torusCompat_iff.mp hi', hη]
    exact (SplitTorus.isGrpPullback_bcMap f X).1.paste_horiz hker0
  have hcommA : i'.left ≫ q'.left = (splitTorus S' X).hom ≫ (η[(Over.pullback f).obj Q.B]).left := by
    apply hB.1.hom_ext
    · simpa only [Category.assoc, hq'fst] using hcomp.w
    · rw [Category.assoc, Over.w q', Over.w i', Category.assoc, Over.w η[(Over.pullback f).obj Q.B]]
      simp
  have hA : IsPullback i'.left (splitTorus S' X).hom q'.left (η[(Over.pullback f).obj Q.B]).left :=
    IsPullback.of_right hcomp hcommA hBsq
  have hker : IsPullback i' (toUnit (splitTorus S' X)) q' η := by
    apply IsPullback.of_map (Over.forget S')
    · apply Over.OverMorphism.ext
      show i'.left ≫ q'.left = (toUnit (splitTorus S' X)).left ≫ (η[(Over.pullback f).obj Q.B]).left
      rw [hT']
      exact hcommA
    · show IsPullback i'.left (toUnit (splitTorus S' X)).left q'.left (η[(Over.pullback f).obj Q.B]).left
      rw [hT']
      exact hA
  have hloc : ∀ (b : ((Over.pullback f).obj Q.B).left) (χ : X),
      ∃ V, b ∈ V ∧ ∃ u : (Γ(G'.left, q'.left ⁻¹ᵁ V))ˣ, IsWt i' (q'.left ⁻¹ᵁ V) (↑u) χ := by
    intro b χ
    obtain ⟨V, hbV, u, hu⟩ := Q.loc ((pullback.fst Q.B.hom f).base b) χ
    have hle : q'.left ⁻¹ᵁ (pullback.fst Q.B.hom f ⁻¹ᵁ V) ≤ F ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hq'fst]
    refine ⟨pullback.fst Q.B.hom f ⁻¹ᵁ V, hbV, Units.map (F.appLE _ _ hle).hom.toMonoidHom u, ?_⟩
    exact IsWt.pull hF hi' hle hu
  exact ⟨TQ.mk _ hAb q' i' inferInstance inferInstance
    (MorphismProperty.of_isPullback (P := @Flat) hBsq Q.q_flat)
    (MorphismProperty.of_isPullback (P := @Surjective) hBsq Q.q_surj)
    (MorphismProperty.of_isPullback (P := @IsAffineHom) hBsq Q.q_affine) hker hloc, hi'⟩
end GlobalTheory.UU
