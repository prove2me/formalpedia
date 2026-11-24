-- Prove2me | solution 1 for GlobalTheory.ThetaBaseChange.exists_moved
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:08:30.916837+00:00
-- url     : https://prove2.me/submissions/a34af388-a05b-4de0-b15f-acb240d0ea9d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Theorems.Thm_GlobalTheory_FieldBaseChange_exists_move


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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
variable {S S' W : Scheme.{0}} {t : W ⟶ S} {t' : W ⟶ S'}
  {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {Φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
  {ω : (Over.mk t ⊗ A).left ⟶ (Over.mk t' ⊗ A').left} {Y Y' N N' V V' : Scheme.{0}} {M : LB N} {M' : LB N'}
namespace GlobalTheory.ThetaBaseChange
theorem _root_.solution (hL : L.IsLB) (hL' : L'.IsLB) (h₂ : ω ≫ (snd (Over.mk t') A').left ≫ Φ = (snd (Over.mk t) A).left)
    {c₁ : Y' ⟶ A'.left} {n₁ : A'.left ⟶ Y'} (hn : n₁ ≫ c₁ = 𝟙 _) {v₂ : LB.Iso (L'.pull c₁) (L.pull (c₁ ≫ Φ))}
    (hv₂ : v₂.IsGen) {v : LB.Iso L' (L.pull Φ)}
    (hv : ∀ (Z : Scheme.{0}) (f : Z ⟶ A'.left) (z : Z) (j : L.ι) (i : L'.ι),
      Φ (f z) ∈ L.U j → f z ∈ L'.U i → gw v f z j i = isoVal v₂ (f ≫ n₁) z j i) {k : ℤ}
    (s' : LB.Sec (LPow A' L' k (Over.mk t'))) : ∃ s : LB.Sec (LPow A L k (Over.mk t)), Moved v ω s' s := by
  have hn' : ∀ {V : Scheme.{0}} (h : A'.left ⟶ V), n₁ ≫ c₁ ≫ h = h := fun h => by
    rw [← Category.assoc, hn, Category.id_comp]
  have e₁ : ω ≫ (snd (Over.mk t') A').left = (ω ≫ (snd (Over.mk t') A').left ≫ n₁) ≫ c₁ := by
    rw [Category.assoc, Category.assoc, hn, Category.comp_id]
  have e₂ : (snd (Over.mk t) A).left = (ω ≫ (snd (Over.mk t') A').left ≫ n₁) ≫ c₁ ≫ Φ := by
    rw [← h₂, Category.assoc, Category.assoc, hn']
  obtain ⟨b, hb⟩ := exists_move hL' hL hv₂ (ω ≫ (snd (Over.mk t') A').left ≫ n₁) k ω e₁ e₂ s'
  refine ⟨b, fun Z r z i i' hi hi' => ?_⟩
  have hΦ : Φ (((r ≫ ω) ≫ (snd (Over.mk t') A').left) z) ∈ L.U i := by
    rw [← h₂] at hi
    exact hi
  have m₂ : (c₁ ≫ Φ) ((ω ≫ (snd (Over.mk t') A').left ≫ n₁) (r z)) ∈ L.U i := by
    rw [e₂] at hi
    exact hi
  have m₁ : (ω ≫ (snd (Over.mk t') A').left) (r z) ∈ L'.U i' := hi'
  rw [e₁] at m₁
  rw [hv _ _ _ _ _ hΦ hi', hb Z r z i i' m₂ m₁]
  simp only [Category.assoc]
end GlobalTheory.ThetaBaseChange
