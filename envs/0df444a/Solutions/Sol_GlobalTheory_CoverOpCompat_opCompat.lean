-- Prove2me | solution 1 for GlobalTheory.CoverOpCompat.opCompat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:50:45.681241+00:00
-- url     : https://prove2.me/submissions/89252436-393e-4698-b148-3291653b0567

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GroupLawsOnCoverAgreeOnCommonPoints
import Theorems.Thm_GlobalTheory_CoverOpCompat_push_mul
import Theorems.Thm_GlobalTheory_CoverOpCompat_push_inv
import Theorems.Thm_GlobalTheory_CoverOpCompat_push_one
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CoverOpCompat
namespace GlobalTheory.CoverOpCompat
theorem _root_.solution : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left) (B : ∀ i j, Over (U i ⊓ U j).toScheme) [∀ i j, GrpObj (B i j)] (a : ∀ i j, (B i j).left ⟶ (G i).left) (b : ∀ i j, (B i j).left ⟶ (G j).left), (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i j, IsGrpPullback (B i j) (G i) (S.homOfLE inf_le_left) (a i j)) → (∀ i j, IsGrpPullback (B i j) (G j) (S.homOfLE inf_le_right) (b i j)) → (∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) → (∀ i j (T : Scheme.{0}) (r : T ⟶ (U i).toScheme) (r' : T ⟶ (U j).toScheme) (x y : Over.mk r ⟶ G i) (x' y' : Over.mk r' ⟶ G j), x.left ≫ ψ i = x'.left ≫ ψ j → y.left ≫ ψ i = y'.left ≫ ψ j → (x * y).left ≫ ψ i = (x' * y').left ≫ ψ j ∧ (x⁻¹).left ≫ ψ i = (x'⁻¹).left ≫ ψ j) ∧ ∀ i j, S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ (1 : Out.baseOver (U i).toScheme ⟶ G i).left ≫ ψ i = S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ (1 : Out.baseOver (U j).toScheme ⟶ G j).left ≫ ψ j := by
  intro S I U A G _ ψ B _ a b _ ha hb hsq
  refine ⟨fun i j T r r' x y x' y' hx hy => ?_, fun i j => ?_⟩
  ·
    let p : T ⟶ (B i j).left := (hsq i j).lift x.left x'.left hx
    let q : T ⟶ (B i j).left := (hsq i j).lift y.left y'.left hy
    have hpa : p ≫ a i j = x.left := (hsq i j).lift_fst _ _ _
    have hpb : p ≫ b i j = x'.left := (hsq i j).lift_snd _ _ _
    have hqa : q ≫ a i j = y.left := (hsq i j).lift_fst _ _ _
    have hqb : q ≫ b i j = y'.left := (hsq i j).lift_snd _ _ _
    let ρ : T ⟶ (U i ⊓ U j).toScheme := p ≫ (B i j).hom
    have er : r = ρ ≫ S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) := by
      show r = (p ≫ (B i j).hom) ≫ _
      rw [Category.assoc, ← (ha i j).1.w, ← Category.assoc, hpa]
      exact (Over.w x).symm
    have er' : r' = ρ ≫ S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) := by
      show r' = (p ≫ (B i j).hom) ≫ _
      rw [Category.assoc, ← (hb i j).1.w, ← Category.assoc, hpb]
      exact (Over.w x').symm
    have eq : q ≫ (B i j).hom = ρ := by
      apply (cancel_mono (S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).1
      rw [Category.assoc, ← (ha i j).1.w, ← Category.assoc, hqa]
      exact (Over.w y).trans er
    let P : Over.mk ρ ⟶ B i j := Over.homMk p rfl
    let Q : Over.mk ρ ⟶ B i j := Over.homMk q eq
    have m1 := push_mul (ha i j) er P Q x y hpa.symm hqa.symm
    have m2 := push_mul (hb i j) er' P Q x' y' hpb.symm hqb.symm
    have i1 := push_inv (ha i j) er P x hpa.symm
    have i2 := push_inv (hb i j) er' P x' hpb.symm
    refine ⟨?_, ?_⟩
    · rw [m1, m2]
      simp only [Category.assoc]
      rw [(hsq i j).w]
    · rw [i1, i2]
      simp only [Category.assoc]
      rw [(hsq i j).w]
  ·
    have e1 := congrArg (· ≫ ψ i) (push_one (ha i j))
    have e2 := congrArg (· ≫ ψ j) (push_one (hb i j))
    simp only [Category.assoc] at e1 e2
    rw [e1, e2, (hsq i j).w]
end GlobalTheory.CoverOpCompat
