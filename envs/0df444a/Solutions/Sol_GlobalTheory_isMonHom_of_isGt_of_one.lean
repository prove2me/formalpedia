-- Prove2me | solution 1 for GlobalTheory.isMonHom_of_isGt_of_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:16:12.340499+00:00
-- url     : https://prove2.me/submissions/10502541-655e-4310-a2e1-c31feb25072e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsMonHomPointedSplitExtToAbelianVarietyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusPointEqOneOfAxes
import Theorems.Thm_GlobalTheory_splitTorus_point_eq_one_of_axes
import Theorems.Thm_GlobalTheory_T_isMonHom_pointed_splitExt_to_abelianVariety
import Theorems.Thm_GlobalTheory_TorusConst_Glue_symm
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (E E' : SplitExt (Sp K)) (G G' : Over (Sp K)) [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G'], E.IsGt G → E'.IsGt G' → ∀ f : G ⟶ G', η[G] ≫ f = η[G'] → IsMonHom f := by
  intro K _ _ E E' G G' _ _ _ _ h ⟨D⟩ f hf
  have := D.q_hom
  have := D.i_hom
  have hk := D.isKernel
  have hq : IsMonHom (f ≫ D.q) := GlobalTheory.T.isMonHom_pointed_splitExt_to_abelianVariety K E G h E'.B E'.isAbelian (f ≫ D.q) (by
    rw [reassoc_of% hf]; exact IsMonHom.one_hom D.q)
  have hf1 : ∀ {W : Over (Sp K)}, (1 : W ⟶ G) ≫ f = 1 := by
    intro W
    rw [Hom.one_def, Hom.one_def, Category.assoc, hf]
  let d : G ⊗ G ⟶ G' := ((fst G G * snd G G) ≫ f) / ((fst G G ≫ f) * (snd G G ≫ f))
  have hd : d ≫ D.q = 1 := by
    simp only [d]
    rw [GrpObj.div_comp, Category.assoc, MonObj.mul_comp, MonObj.mul_comp, Category.assoc,
      Category.assoc, div_self']
  let t : G ⊗ G ⟶ splitTorus (Sp K) E'.X := hk.lift d (toUnit _) (by rw [hd, Hom.one_def])
  have ht : t ≫ D.i = d := hk.lift_fst _ _ _
  have inj : ∀ a : G ⟶ G ⊗ G, a ≫ d = 1 → a ≫ t = 1 := fun a ha =>
    hk.hom_ext (by rw [Category.assoc, ht, ha, MonObj.one_comp]) (toUnit_unique _ _)
  have t1 : t = 1 := by
    refine splitTorus_point_eq_one_of_axes K E G h E'.X t (inj _ ?_) (inj _ ?_)
    · simp only [d]
      rw [GrpObj.comp_div, MonObj.comp_mul, ← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd,
        lift_fst_assoc, lift_snd_assoc, hf1, _root_.mul_one, _root_.mul_one, div_self']
    · simp only [d]
      rw [GrpObj.comp_div, MonObj.comp_mul, ← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd,
        lift_fst_assoc, lift_snd_assoc, hf1, _root_.one_mul, _root_.one_mul, div_self']
  rw [t1, MonObj.one_comp] at ht
  have hm : (fst G G * snd G G) ≫ f = (fst G G ≫ f) * (snd G G ≫ f) := div_eq_one.mp ht.symm
  refine ⟨hf, ?_⟩
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at hm
  rw [hm]
  congr 1
end GlobalTheory
