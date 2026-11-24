-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AbForms.exists_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:01:21.922837+00:00
-- url     : https://prove2.me/submissions/c0d9aa7a-46bd-4168-9345-1cb42ebb4426

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UOfIsBaseChange
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_exists_lift
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_tzo_fst
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_Zp_sg
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_spMap_inj
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_sg_fst
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_sg_snd
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_Zp_congr
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AbForms
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R : Type} [CommRing R]
variable {A : Over (Sp R)} [GrpObj A] {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W]
  [IsCentralScalar R W] {y₀ : Sp (TrivSqZeroExt R W) ⟶ A.left} (hy : IsCot A.hom η[A].left W y₀)
variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M] [Module R M] [IsScalarTower R B M]
variable {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M']
  [IsCentralScalar B' M'] [Module R M'] [IsScalarTower R B' M']
variable (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap (algebraMap R B))
variable [IsOpenImmersion x]
namespace GlobalTheory.CompanionTheory.AbForms
theorem _root_.solution (g : W →ₗ[R] M) :
    ∃ f : Ω[B⁄R] →ₗ[B] M, (f.restrictScalars R) ∘ₗ uOf hy x hx = g := by
  let c : Spo (sz (R := R) B M) ⟶ A := spo (TrivSqZeroExt.inlHom B M) rfl ≫ xo x hx
  have hz := tzo_fst (B := B) (M := M) hy g
  let y : Spo (sz (R := R) B M) ⟶ A := tzo hy g * c
  have hy1 : spo (fs B M) (fs_sz B M) ≫ y = xo x hx := by
    have h3 : spo (fs B M) (fs_sz B M) ≫ c = xo x hx := by
      change _ ≫ spo (TrivSqZeroExt.inlHom B M) rfl ≫ xo x hx = _
      rw [← Category.assoc, spo_comp _ _ _ _ (by rw [RingHom.comp_assoc]; exact fs_sz B M),
        spo_xo x hx _ (fs_inl B M)]
    change _ ≫ (tzo hy g * c) = _
    rw [MonObj.comp_mul, hz, _root_.one_mul, h3]
  have hy2 : spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ y.left = x := congrArg (fun t ↦ t.left) hy1
  obtain ⟨σ, hσ⟩ := exists_lift x y.left hy2
  have hw : σ.comp (algebraMap R B) = sz B M := spMap_inj (by
    rw [spMap_comp, ← hx, ← Category.assoc, ← hσ]
    exact Over.w y)
  have h1 : (fs B M).comp σ = RingHom.id B := spMap_inj (by
    refine (cancel_mono x).1 ?_
    rw [spMap_comp, Category.assoc, ← hσ, hy2, spMap_id, Category.id_comp])
  let δ : Derivation R B M := derOf σ (fun b ↦ congrArg (fun t ↦ t b) h1)
    (fun r ↦ congrArg (fun t ↦ t r) hw)
  let f : Ω[B⁄R] →ₗ[B] M := δ.liftKaehlerDifferential
  have e : sg f = σ := RingHom.ext fun b ↦ by
    ext
    · exact (sg_fst f b).trans (congrArg (fun t ↦ t b) h1).symm
    · exact (sg_snd f b).trans (Derivation.liftKaehlerDifferential_comp_D δ b)
  have hZ : Zp x hx σ hw = tzo hy g := by
    have h4 : spo σ hw ≫ xo x hx = y := Over.OverMorphism.ext hσ.symm
    change spo σ hw ≫ xo x hx * c⁻¹ = _
    rw [h4]
    exact mul_inv_cancel_right _ _
  have h5 : tzo (B := B) hy g = tzo hy ((f.restrictScalars R) ∘ₗ uOf hy x hx) := by
    rw [← hZ, ← Zp_sg hy x hx f]
    exact Zp_congr x hx e.symm _ _
  exact ⟨f, ((cot_unique hy (tzo hy g) (tzo_fst hy g)).unique rfl h5).symm⟩
end GlobalTheory.CompanionTheory.AbForms
