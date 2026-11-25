-- Prove2me | solution 1 for GlobalTheory.QcSub.PowerMultiple.res_pow_mul_mem_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:12:40.647787+00:00
-- url     : https://prove2.me/submissions/a16c1575-94e7-4a31-8451-4439aeca9915

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowMulMemAdjoinOfLocalizationAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineInterFiniteBasicOpenCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemAdjoinRestrictedSectionsOfLocalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulMemSubalgebraOfResBasicOpen
import Theorems.Thm_GlobalTheory_QcSub_gen_eq_adjoin
import Theorems.Thm_GlobalTheory_QcSub_isLocalizationAway
import Theorems.Thm_GlobalTheory_T_exists_pow_mul_mem_adjoin_of_localizationAway


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
open GlobalTheory GlobalTheory.QcSub GlobalTheory.QcSub.PowerMultiple
variable {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
namespace GlobalTheory.QcSub.PowerMultiple
theorem _root_.solution
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {D W V : X.Opens} (hD : IsAffineOpen D) (hDW : D ≤ W) (hDV : D ≤ V)
    (T : Set (F.obj (op V))) (f : Γ(X, W)) (a : F.obj (op W))
    (ha : ∀ (W' : X.Opens), IsAffineOpen W' → ∀ (h1 : W' ≤ X.basicOpen f) (h2 : W' ≤ V),
      (F.map (homOfLE h1).op).hom ((F.map (homOfLE (X.basicOpen_le f)).op).hom a) ∈
        gen F α h2 T) :
    ∃ m : ℕ, (F.map (homOfLE hDW).op).hom ((α.app (op W)).hom f ^ m * a) ∈ gen F α hDV T := by
  set fD : Γ(X, D) := (X.presheaf.map (homOfLE hDW).op).hom f with hfD
  have hbo : X.basicOpen fD = D ⊓ X.basicOpen f := Scheme.basicOpen_res X f (homOfLE hDW).op
  have hD'D : X.basicOpen fD ≤ D := X.basicOpen_le fD
  have hD'f : X.basicOpen fD ≤ X.basicOpen f := hbo.le.trans inf_le_right
  have hD'V : X.basicOpen fD ≤ V := hD'D.trans hDV
  have hD' : IsAffineOpen (X.basicOpen fD) := hD.basicOpen fD
  letI iRA : Algebra Γ(X, D) (F.obj (op D)) := (α.app (op D)).hom.toAlgebra
  letI iRR' : Algebra Γ(X, D) Γ(X, X.basicOpen fD) :=
    (X.presheaf.map (homOfLE hD'D).op).hom.toAlgebra
  letI iR'A' : Algebra Γ(X, X.basicOpen fD) (F.obj (op (X.basicOpen fD))) :=
    (α.app (op (X.basicOpen fD))).hom.toAlgebra
  letI iAA' : Algebra (F.obj (op D)) (F.obj (op (X.basicOpen fD))) :=
    (F.map (homOfLE hD'D).op).hom.toAlgebra
  letI iRA' : Algebra Γ(X, D) (F.obj (op (X.basicOpen fD))) :=
    ((F.map (homOfLE hD'D).op).hom.comp (α.app (op D)).hom).toAlgebra
  haveI : IsScalarTower Γ(X, D) (F.obj (op D)) (F.obj (op (X.basicOpen fD))) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Γ(X, D) Γ(X, X.basicOpen fD) (F.obj (op (X.basicOpen fD))) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    have := congr($(α.naturality (homOfLE hD'D).op).hom r)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  haveI : IsLocalization.Away fD Γ(X, X.basicOpen fD) := hD.isLocalization_basicOpen fD
  haveI : IsLocalization.Away (algebraMap Γ(X, D) (F.obj (op D)) fD)
      (F.obj (op (X.basicOpen fD))) := isLocalizationAway F α hα hD fD
  have hres : ∀ {U₁ U₂ U₃ : X.Opens} (h₁ : U₂ ≤ U₁) (h₂ : U₃ ≤ U₂) (y : F.obj (op U₁)),
      (F.map (homOfLE h₂).op).hom ((F.map (homOfLE h₁).op).hom y) =
        (F.map (homOfLE (h₂.trans h₁)).op).hom y := by
    intro U₁ U₂ U₃ h₁ h₂ y
    rw [← CommRingCat.comp_apply, ← F.map_comp]
    rfl
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_pow_mul_mem_adjoin_of_localizationAway (R := Γ(X, D)) (A := F.obj (op D))
    (R' := Γ(X, X.basicOpen fD)) (A' := F.obj (op (X.basicOpen fD))) fD
    ((F.map (homOfLE hDV).op).hom '' T) ((F.map (homOfLE hDW).op).hom a) (by
      have h0 := ha _ hD' hD'f hD'V
      rw [hres, gen_eq_adjoin] at h0
      change (F.map (homOfLE hD'D).op).hom ((F.map (homOfLE hDW).op).hom a) ∈ _
      rw [hres, Set.image_image]
      have hfun : (fun x => (algebraMap (F.obj (op D)) (F.obj (op (X.basicOpen fD))))
          ((F.map (homOfLE hDV).op).hom x)) = ⇑(F.map (homOfLE hD'V).op).hom :=
        funext fun x => hres _ _ x
      rw [hfun]
      exact h0)
  refine ⟨m, ?_⟩
  have hnat : (F.map (homOfLE hDW).op).hom ((α.app (op W)).hom f) = (α.app (op D)).hom fD := by
    have := congr($(α.naturality (homOfLE hDW).op).hom f)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  rw [map_mul, map_pow, hnat, gen_eq_adjoin]
  exact hm
end GlobalTheory.QcSub.PowerMultiple
