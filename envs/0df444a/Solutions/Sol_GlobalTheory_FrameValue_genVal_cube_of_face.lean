-- Prove2me | solution 1 for GlobalTheory.FrameValue.genVal_cube_of_face
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:40:58.393311+00:00
-- url     : https://prove2.me/submissions/c56ec13e-30ad-4d4e-9f5f-0b05fe537c7f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
import Theorems.Thm_GlobalTheory_FrameValue_genVal_pull
import Theorems.Thm_GlobalTheory_FrameValue_genVal_one
import Theorems.Thm_GlobalTheory_FrameValue_genVal_corr
import Theorems.Thm_GlobalTheory_FrameValue_differentiable_genVal
import Theorems.Thm_GlobalTheory_FrameValue_chi_ne_zero
import Theorems.Thm_GlobalTheory_FrameValue_genVal_add_period
import Theorems.Thm_GlobalTheory_FrameValue_ahFactor_zero
import Theorems.Thm_GlobalTheory_FrameValue_prod_thK
import Theorems.Thm_GlobalTheory_FrameValue_sum_three
import Theorems.Thm_GlobalTheory_FrameValue_isLift_cube
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_add_left
import Theorems.Thm_GlobalTheory_CubeValues_ex_add_period
import Theorems.Thm_GlobalTheory_CubeValues_ex_zero
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_add_left
import Theorems.Thm_GlobalTheory_entire_apply_eq_of_periodic_of_span_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FrameValue
open CubeValues SymmetricSemicharacter EigenNorm
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
namespace GlobalTheory.FrameValue
theorem _root_.solution (hL : L.IsLB) (h : u.IsAH Hm χ) (t : LB.Gen (LB.LinComb L (thφ A (x3 A)) thε)) (ht : t.IsGen)
    (hf : LB.Gen.Corr L _ _ (Y := (G2 A).left) _ _ (LB.pullGen L (thφ A (x3 A)) thε t (faceMap A 0).left) (LB.oneGen L))
    (x : Fin 3 → Fin g → ℂ) : genVal u hL t (pt3 u x).left (cubeLift x) = 1 := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, x = ![a, b, c] := ⟨x 0, x 1, x 2, by ext i : 1; fin_cases i <;> rfl⟩
  let p : A ⟶ G3 A := lift (𝟙 A) (lift (toUnit A ≫ u.ex b) (toUnit A ≫ u.ex c))
  have hp : ∀ w, (u.ex w).left ≫ p.left = (pt3 u ![w, b, c]).left := fun w => by
    rw [← Over.comp_left]
    congr 1
    simp [p, pt3, comp_lift, Subsingleton.elim (toUnit (𝟙_ (Over (Sp ℂ)))) (𝟙 _)]
  have hd : Differentiable ℂ fun w => genVal u hL t (pt3 u ![w, b, c]).left (cubeLift ![w, b, c]) := by
    have := differentiable_genVal hL ht p.left (q := id) differentiable_id (z := fun w => cubeLift ![w, b, c])
      (fun I => Differentiable.fun_sum fun k _ => by fin_cases k <;> simp <;> fun_prop)
      (fun w => by rw [id, hp]; exact isLift_cube u _)
    simpa only [id, hp] using this
  have hper : ∀ w, ∀ l ∈ (u.Λ : Set (Fin g → ℂ)), genVal u hL t (pt3 u ![w + l, b, c]).left (cubeLift ![w + l, b, c]) =
      genVal u hL t (pt3 u ![w, b, c]).left (cubeLift ![w, b, c]) := fun w l hl => by
    have e₁ : pt3 u ![w + l, b, c] = pt3 u ![w, b, c] := by simp [pt3, ex_add_period u w l hl]
    have e₂ : cubeLift ![w + l, b, c] = fun I => cubeLift ![w, b, c] I +
        ((∑ a ∈ I.down, (![⟨l, hl⟩, 0, 0] : Fin 3 → u.Λ) a : u.Λ) : Fin g → ℂ) := by
      funext I
      rw [cubeLift, cubeLift, Submodule.coe_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by fin_cases k <;> simp
    rw [e₁, e₂, genVal_add_period hL h t (isLift_cube u _)]
    refine (congrArg (· * _) ?_).trans (_root_.one_mul _)
    refine (prod_thK fun I => ahFactor Hm χ (∑ a ∈ I, (![⟨l, hl⟩, 0, 0] : Fin 3 → u.Λ) a) (∑ a ∈ I, ![w, b, c] a)).trans ?_
    have n := chi_ne_zero h ⟨l, hl⟩
    simp only [sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val, add_zero, ahFactor_zero hL h]
    simp only [ahFactor, hermForm_add_left, mul_add, Complex.exp_add]
    field_simp
  rw [entire_apply_eq_of_periodic_of_span_real hd u.full hper a 0]
  have e : (pt3 u ![0, b, c]).left = (lift (u.ex b) (u.ex c)).left ≫ (faceMap A 0).left := by
    rw [← Over.comp_left]
    congr 1
    simp [faceMap, pt3, comp_lift, x2, pzero, ex_zero, Hom.one_def]
  have hz := isLift_cube u ![0, b, c]
  rw [e] at hz ⊢
  rw [← genVal_pull, ← genVal_one (u := u) hL (lift (u.ex b) (u.ex c)).left PEmpty.elim]
  refine genVal_corr hL hf (fun k => (Category.assoc _ _ _).symm.trans (hz k)) (fun k => k.elim) fun f => ?_
  refine (prod_thK fun I => f (∑ a ∈ I, ![0, b, c] a)).trans ?_
  simp only [sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val, zero_add, Fintype.prod_empty]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel
end GlobalTheory.FrameValue
