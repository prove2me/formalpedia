-- Prove2me | solution 1 for GlobalTheory.FrameValue.genVal_sym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:08:40.861547+00:00
-- url     : https://prove2.me/submissions/76caea3f-756a-45b1-bc1a-ec4ac7c389e5

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
import Theorems.Thm_GlobalTheory_FrameValue_const_of_norm_periodic
import Theorems.Thm_GlobalTheory_FrameValue_hermForm_neg_left
import Theorems.Thm_GlobalTheory_FrameValue_hermForm_neg_right
import Theorems.Thm_GlobalTheory_FrameValue_isLift_sym
import Theorems.Thm_GlobalTheory_CubeValues_ex_add_period
import Theorems.Thm_GlobalTheory_CubeValues_ex_zero


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
theorem _root_.solution (hL : L.IsLB) (h : u.IsAH Hm χ)
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1])) (hs : s.IsGen)
    (h₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ s (eSec A)) (LB.oneGen L)) :
    (∀ z, genVal u hL s (u.ex z).left ![-z, z] = 1) ∧ ∀ l, χ (-l) = χ l := by
  have hd : Differentiable ℂ fun w => genVal u hL s (u.ex w).left ![-w, w] := by
    have := differentiable_genVal hL hs (𝟙 _) (q := id) differentiable_id (z := fun w => ![-w, w])
      (fun k => by fin_cases k <;> simp <;> fun_prop) (fun w => by rw [id, Category.comp_id]; exact isLift_sym u w)
    simpa only [id, Category.comp_id] using this
  have hper : ∀ (l : u.Λ) w, genVal u hL s (u.ex (w + l)).left ![-(w + l), w + l] =
      χ (-l) / χ l * genVal u hL s (u.ex w).left ![-w, w] := fun l w => by
    have e₂ : ![-(w + l), w + l] = fun k => ![-w, w] k + ((![-l, l] : Fin 2 → u.Λ) k : Fin g → ℂ) := by
      funext k
      fin_cases k <;> simp [add_comm]
    rw [ex_add_period u w l l.2, e₂, genVal_add_period hL h s (isLift_sym u w)]
    congr 1
    have n := chi_ne_zero h l
    simp [ahFactor, hermForm_neg_left, hermForm_neg_right]
    field_simp
  have hc := const_of_norm_periodic u hd (fun l w => by
    rw [hper, norm_mul, norm_div, h.2.2.1, h.2.2.1, div_one, _root_.one_mul])
  have e : (u.ex 0).left = 𝟙 (Sp ℂ) ≫ eSec A := by rw [ex_zero, Hom.one_def]; simp [eSec]
  have h1 : genVal u hL s (u.ex 0).left ![-0, 0] = 1 := by
    have hz := isLift_sym u 0
    rw [e] at hz ⊢
    rw [← genVal_pull, ← genVal_one (u := u) hL (𝟙 (Sp ℂ)) PEmpty.elim]
    refine genVal_corr hL h₀ (fun k => (Category.assoc _ _ _).symm.trans (hz k)) (fun k => k.elim) fun f => ?_
    simp
  refine ⟨fun z => (hc z 0).trans h1, fun l => ?_⟩
  have := hper l 0
  rw [hc _ 0, h1, _root_.mul_one] at this
  exact (div_eq_one_iff_eq (chi_ne_zero h l)).1 this.symm
end GlobalTheory.FrameValue
