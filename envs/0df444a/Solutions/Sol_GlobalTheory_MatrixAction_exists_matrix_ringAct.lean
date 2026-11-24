-- Prove2me | solution 1 for GlobalTheory.MatrixAction.exists_matrix_ringAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:28:19.580042+00:00
-- url     : https://prove2.me/submissions/5879ac65-4c6e-493b-98cd-20131f7df8b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMatrixRingAct
import Theorems.Thm_GlobalTheory_MatrixAction_comp_finsetProd
import Theorems.Thm_GlobalTheory_MatrixAction_finsetProd_comp
import Theorems.Thm_GlobalTheory_MatrixAction_isMonHom_of_points
import Theorems.Thm_GlobalTheory_MatrixAction_act_add
import Theorems.Thm_GlobalTheory_MatrixAction_act_zero
import Theorems.Thm_GlobalTheory_MatrixAction_act_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open GlobalTheory GlobalTheory.MatrixAction
variable {S : Scheme.{0}}
namespace GlobalTheory.MatrixAction
theorem _root_.solution : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (j : ℕ) (p : IsPowGrp G' G j) (O : Type) [Ring O] (ιG : RingAct G O), ∃ ι' : RingAct G' (Matrix (Fin j) (Fin j) O), (∀ (m : (Matrix (Fin j) (Fin j) O)) (i : Fin j), ι'.act m ≫ p.pr i = ∏ l, p.pr l ≫ ιG.act (m i l)) := by
  intro S G G' _ _ _ _ j p O _ ιG
  have hext : ∀ {T : Over S} {a b : T ⟶ G'}, (∀ i, a ≫ p.pr i = b ≫ p.pr i) → a = b :=
    fun h => p.lim.hom_ext fun i => h i.as
  have hp := p.hom
  have hι := ιG.hom
  let A : Matrix (Fin j) (Fin j) O → (G' ⟶ G') := fun m =>
    p.lim.lift (Fan.mk G' fun i => ∏ l, p.pr l ≫ ιG.act (m i l))
  have hA : ∀ m i, A m ≫ p.pr i = ∏ l, p.pr l ≫ ιG.act (m i l) := fun m i =>
    p.lim.fac (Fan.mk G' fun i => ∏ l, p.pr l ≫ ιG.act (m i l)) ⟨i⟩
  refine ⟨⟨A, fun m => ?_, ?_, fun a b => ?_, fun a b => ?_⟩, hA⟩
  · refine isMonHom_of_points _ (fun T => hext fun i => ?_) (fun T x y => hext fun i => ?_)
    · rw [Category.assoc, hA, comp_finsetProd, MonObj.one_comp (p.pr i)]
      refine Finset.prod_eq_one fun l _ => ?_
      rw [← Category.assoc, MonObj.one_comp, MonObj.one_comp]
    · rw [MonObj.mul_comp _ _ (p.pr i), Category.assoc, Category.assoc, Category.assoc, hA, comp_finsetProd,
        comp_finsetProd, comp_finsetProd, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [← Category.assoc, MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc]
  · refine hext fun i => ?_
    rw [hA, Category.id_comp, Finset.prod_eq_single i]
    · rw [Matrix.one_apply_eq, ιG.map_one, Category.comp_id]
    · intro l _ hl
      rw [Matrix.one_apply_ne hl.symm, act_zero, MonObj.comp_one]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · refine hext fun i => ?_
    rw [Category.assoc, hA, hA, comp_finsetProd]
    have e1 : ∀ k, A b ≫ p.pr k ≫ ιG.act (a i k)
        = ∏ l, p.pr l ≫ ιG.act (a i k * b k l) := fun k => by
      rw [← Category.assoc, hA, finsetProd_comp]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [ιG.map_mul, Category.assoc]
    rw [Finset.prod_congr rfl fun k _ => e1 k, Finset.prod_comm]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, act_sum, comp_finsetProd]
  · refine hext fun i => ?_
    change _ = (A a * A b) ≫ p.pr i
    rw [MonObj.mul_comp, hA, hA, hA, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [Matrix.add_apply, act_add, MonObj.comp_mul]
end GlobalTheory.MatrixAction
