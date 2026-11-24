-- Prove2me | solution 1 for GlobalTheory.GrpLoc.isGrpPullback_id_of_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:12:52.271276+00:00
-- url     : https://prove2.me/submissions/d52a77fd-1f97-4799-af24-99e2ef6087e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsGrpPullbackLocalOnBase
import Theorems.Thm_GlobalTheory_GrpLoc_hom_ext_loc
import Theorems.Thm_GlobalTheory_GrpLoc_range_of_isPullback
import Theorems.Thm_GlobalTheory_GrpLoc_mul_left_pre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.GrpLoc
namespace GlobalTheory.GrpLoc
theorem _root_.solution {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (φ : A.left ⟶ A'.left) [IsIso φ]
    (w : φ ≫ A'.hom = A.hom)
    (h : ∀ p : S, ∃ (W : Scheme.{0}) (x : W ⟶ S) (B : Over W) (_ : GrpObj B) (a : B.left ⟶ A.left),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsGrpPullback B A x a ∧ IsGrpPullback B A' x (a ≫ φ)) :
    IsGrpPullback A A' (𝟙 S) φ := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simpa using w⟩, ?_⟩
  intro T x y x₀ y₀ hx hy
  apply hom_ext_loc
  intro t
  obtain ⟨W, xS, B, _, a, hxo, ⟨w0, hw0⟩, hB, hB'⟩ := h (T.hom t)
  refine ⟨pullback T.hom xS, pullback.fst T.hom xS, inferInstance,
    (range_of_isPullback (IsPullback.of_hasPullback T.hom xS) t).2 ⟨w0, hw0⟩, ?_⟩
  let TW : Over W := Over.mk (pullback.snd T.hom xS)
  have cx : (pullback.fst T.hom xS ≫ x.left) ≫ A.hom = pullback.snd T.hom xS ≫ xS := by
    rw [Category.assoc, Over.w x, pullback.condition]
  have cy : (pullback.fst T.hom xS ≫ y.left) ≫ A.hom = pullback.snd T.hom xS ≫ xS := by
    rw [Category.assoc, Over.w y, pullback.condition]
  have cx' : (pullback.fst T.hom xS ≫ x.left ≫ φ) ≫ A'.hom = pullback.snd T.hom xS ≫ xS := by
    simpa [w] using cx
  have cy' : (pullback.fst T.hom xS ≫ y.left ≫ φ) ≫ A'.hom = pullback.snd T.hom xS ≫ xS := by
    simpa [w] using cy
  let XB : TW ⟶ B := Over.homMk (hB.1.lift _ _ cx) (hB.1.lift_snd _ _ cx)
  let YB : TW ⟶ B := Over.homMk (hB.1.lift _ _ cy) (hB.1.lift_snd _ _ cy)
  let x' : Over.mk (TW.hom ≫ xS) ⟶ A := Over.homMk (pullback.fst T.hom xS ≫ x.left) cx
  let y' : Over.mk (TW.hom ≫ xS) ⟶ A := Over.homMk (pullback.fst T.hom xS ≫ y.left) cy
  let x₁ : Over.mk (TW.hom ≫ xS) ⟶ A' := Over.homMk (pullback.fst T.hom xS ≫ x.left ≫ φ) cx'
  let y₁ : Over.mk (TW.hom ≫ xS) ⟶ A' := Over.homMk (pullback.fst T.hom xS ≫ y.left ≫ φ) cy'
  have e1 : (x' * y').left = (XB * YB).left ≫ a :=
    hB.2 TW XB YB x' y' (hB.1.lift_fst _ _ cx).symm (hB.1.lift_fst _ _ cy).symm
  have e2 : (x₁ * y₁).left = (XB * YB).left ≫ a ≫ φ := by
    refine hB'.2 TW XB YB x₁ y₁ ?_ ?_
    · simp only [x₁, XB, Over.homMk_left]
      rw [← Category.assoc (hB.1.lift _ _ cx), hB.1.lift_fst, Category.assoc]
    · simp only [y₁, YB, Over.homMk_left]
      rw [← Category.assoc (hB.1.lift _ _ cy), hB.1.lift_fst, Category.assoc]
  have hk : pullback.fst T.hom xS ≫ T.hom = (Over.mk (TW.hom ≫ xS)).hom := by
    simp [TW, pullback.condition]
  have hk' : pullback.fst T.hom xS ≫ (Over.mk (T.hom ≫ 𝟙 S)).hom = (Over.mk (TW.hom ≫ xS)).hom := by
    simp [TW, pullback.condition]
  have m1 := mul_left_pre (pullback.fst T.hom xS) hk x y x' y' rfl rfl
  have m2 := mul_left_pre (pullback.fst T.hom xS) hk' x₀ y₀ x₁ y₁
    (by simp only [x₁, Over.homMk_left, hx]) (by simp only [y₁, Over.homMk_left, hy])
  rw [← m2, e2, ← Category.assoc, ← e1, m1, Category.assoc]
end GlobalTheory.GrpLoc
