-- Prove2me | solution 1 for GlobalTheory.HomExt.comp_pow_eq_one_of_pullback_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:49:50.050106+00:00
-- url     : https://prove2.me/submissions/305689da-c378-4aaa-8da2-426c082c705c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CompPowEqOneOfPullbackHom
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_TorsionLift_ptsEquiv_left
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_torusCoord_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply
attribute [local simp] GlobalTheory.laurentEval_single
attribute [local simp] GlobalTheory.torusCoord_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.HomExt
namespace GlobalTheory.HomExt
theorem _root_.solution {X T Z : Scheme.{0}} (g : T ⟶ X) {G G' Γ : Over X}
    [GrpObj G] [GrpObj G'] (F : (Over.pullback g).obj G ⟶ (Over.pullback g).obj G') [IsMonHom F]
    (p : Γ ⟶ G) (q : Γ ⟶ G') (c : Z ⟶ Γ.left) (s : Z ⟶ pullback G.hom g)
    (h₁ : s ≫ pullback.fst G.hom g = c ≫ p.left)
    (h₂ : s ≫ F.left ≫ pullback.fst G'.hom g = c ≫ q.left) (n : ℕ)
    (h : c ≫ (p ^ n).left = c ≫ (1 : Γ ⟶ G).left) :
    c ≫ (q ^ n).left = c ≫ (1 : Γ ⟶ G').left := by

  let pc : Over.mk (c ≫ Γ.hom) ⟶ Γ := Over.homMk c
  let ps : Over.mk (s ≫ pullback.snd G.hom g) ⟶ (Over.pullback g).obj G := Over.homMk s
  have ht : (Over.mk (s ≫ pullback.snd G.hom g)).hom ≫ g = c ≫ Γ.hom := by
    simp only [Over.mk_hom, Category.assoc, ← pullback.condition, reassoc_of% h₁, Over.w]
  have hp : GlobalTheory.TorsionLift.ptsEquiv g G _ _ ht ps = pc ≫ p := by
    apply Over.OverMorphism.ext
    rw [GlobalTheory.TorsionLift.ptsEquiv_left]
    simpa [ps, pc] using h₁
  have hq : GlobalTheory.TorsionLift.ptsEquiv g G' _ _ ht (ps ≫ F) = pc ≫ q := by
    apply Over.OverMorphism.ext
    rw [GlobalTheory.TorsionLift.ptsEquiv_left]
    simpa [ps, pc] using h₂
  have h1 : (1 : Over.mk (c ≫ Γ.hom) ⟶ G) = pc ≫ 1 := (MonObj.comp_one pc).symm
  have hpn : (pc ≫ p) ^ n = 1 := by
    rw [← MonObj.comp_pow, h1]
    apply Over.OverMorphism.ext
    exact h
  have hps : ps ^ n = 1 := by
    apply (GlobalTheory.TorsionLift.ptsEquiv g G _ _ ht).injective
    rw [map_pow, hp, hpn, map_one]
  have hqn : (pc ≫ q) ^ n = 1 := by
    rw [← hq, ← map_pow, ← MonObj.pow_comp, hps, MonObj.one_comp, map_one]
  have key : pc ≫ q ^ n = pc ≫ 1 := by
    rw [MonObj.comp_pow, hqn, MonObj.comp_one]
  exact congrArg (fun x => Over.Hom.left x) key
end GlobalTheory.HomExt
