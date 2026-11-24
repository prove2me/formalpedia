-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.orbit_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:10.357934+00:00
-- url     : https://prove2.me/submissions/801d4f2f-e765-4320-903e-bbbe15586317

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_OrbitTrans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
private theorem exists_hom_of_comp_snd_eq_comp_smul {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {M X Y : C} [MonObj M] [ModObj M X] (a b : Y ⟶ M ⊗ X)
    (h : b ≫ SemiCartesianMonoidalCategory.snd M X = a ≫ ModObj.smul (M := M) (X := X)) :
    ∃ r : Y ⟶ M ⊗ X, r ≫ SemiCartesianMonoidalCategory.snd M X = a ≫ SemiCartesianMonoidalCategory.snd M X ∧
      r ≫ ModObj.smul (M := M) (X := X) = b ≫ ModObj.smul (M := M) (X := X) := by
  have key : ∀ c : Y ⟶ M ⊗ X, c ≫ ModObj.smul (M := M) (X := X) =
      (c ≫ SemiCartesianMonoidalCategory.fst M X) • (c ≫ SemiCartesianMonoidalCategory.snd M X) := by
    intro c
    rw [CategoryTheory.Hom.smul_def, CartesianMonoidalCategory.lift_comp_fst_snd]
  refine ⟨CartesianMonoidalCategory.lift
    ((b ≫ SemiCartesianMonoidalCategory.fst M X) * (a ≫ SemiCartesianMonoidalCategory.fst M X))
    (a ≫ SemiCartesianMonoidalCategory.snd M X), CartesianMonoidalCategory.lift_snd _ _, ?_⟩
  rw [← CategoryTheory.Hom.smul_def, mul_smul, ← key a, ← h, ← key b]
end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
theorem _root_.solution {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] (x y w : X.left) :
    y ∈ orbit G X x → w ∈ orbit G X y → w ∈ orbit G X x := by
  simp only [GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.orbit, Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff]
  rintro ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := (ModObj.smul (M := G) (X := X)).left) (g := (SemiCartesianMonoidalCategory.snd G X).left)
    p q hq.symm
  have e₁ : (SemiCartesianMonoidalCategory.snd G X).left ≫ X.hom = (G ⊗ X).hom := Over.w _
  have e₂ : (ModObj.smul (M := G) (X := X)).left ≫ X.hom = (G ⊗ X).hom := Over.w _
  have hw : pullback.snd (ModObj.smul (M := G) (X := X)).left (SemiCartesianMonoidalCategory.snd G X).left ≫
      (G ⊗ X).hom =
      pullback.fst (ModObj.smul (M := G) (X := X)).left (SemiCartesianMonoidalCategory.snd G X).left ≫
      (G ⊗ X).hom := by
    rw [← e₂, pullback.condition_assoc, e₁, e₂]
  obtain ⟨r, hr₁, hr₂⟩ := exists_hom_of_comp_snd_eq_comp_smul
    (Y := Over.mk (pullback.fst (ModObj.smul (M := G) (X := X)).left
      (SemiCartesianMonoidalCategory.snd G X).left ≫ (G ⊗ X).hom))
    (Over.homMk (pullback.fst (ModObj.smul (M := G) (X := X)).left
      (SemiCartesianMonoidalCategory.snd G X).left) rfl)
    (Over.homMk (pullback.snd (ModObj.smul (M := G) (X := X)).left
      (SemiCartesianMonoidalCategory.snd G X).left) hw)
    (Over.OverMorphism.ext (by
      simp only [Over.comp_left, Over.homMk_left]
      exact pullback.condition.symm))
  refine ⟨r.left z, ?_, ?_⟩
  · have h₁ := congrArg Over.Hom.left hr₁
    simp only [Over.comp_left, Over.homMk_left] at h₁
    rw [← Scheme.Hom.comp_apply, h₁, Scheme.Hom.comp_apply, hz₁, hp]
  · have h₂ := congrArg Over.Hom.left hr₂
    simp only [Over.comp_left, Over.homMk_left] at h₂
    rw [← Scheme.Hom.comp_apply, h₂, Scheme.Hom.comp_apply, hz₂]
end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
