-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotLoc.equiv_of_universal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:00:59.679997+00:00
-- url     : https://prove2.me/submissions/1e8708f4-7223-4465-aa8c-84ba26773084

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_spMap_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_exists_unique_of_good
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_exists_good
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_tsz_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_rel_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_tsz_id_comp
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLoc
variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {e : Sp R ⟶ X}
  {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W] [IsCentralScalar R W]
  {y₀ : Sp (TrivSqZeroExt R W) ⟶ X}
  {R' : Type} [CommRing R'] [Algebra R R'] {A C : Type} [CommRing A] [CommRing C] [Algebra C A]
  [Algebra A R'] {j : Sp A ⟶ X} {k : Sp C ⟶ Sp R}
variable {M : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
  [Module R M] [IsScalarTower R R' M]
variable {N : Type} [AddCommGroup N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N]
  [Module R N] [IsScalarTower R R' N]
namespace GlobalTheory.CompanionTheory.CotLoc
theorem _root_.solution (hcot : IsCot s e W y₀) (hes : e ≫ s = 𝟙 _)
    [IsOpenImmersion j] [Mono k]
    (hjs : j ≫ s = spMap (algebraMap C A) ≫ k)
    (hje : spMap (algebraMap A R') ≫ j = spMap (algebraMap R R') ≫ e)
    (iW : W →ₗ[R] N) (ψ₁ : A →+* TrivSqZeroExt R' M) (h₁ : Good (C := C) ψ₁)
    (extW : ∀ u : W →ₗ[R] M, ∃ u' : N →ₗ[R'] M, (u'.restrictScalars R).comp iW = u)
    (extM : ∀ ψ : A →+* TrivSqZeroExt R' N, Good (C := C) ψ →
      ∃ v : M →ₗ[R'] N, (tsz (R := R') (B := R') v).comp ψ₁ = ψ)
    (uniqW : ∀ f g : N →ₗ[R'] N, (f.restrictScalars R).comp iW = (g.restrictScalars R).comp iW → f = g)
    (uniqM : ∀ f g : M →ₗ[R'] M, (tsz (R := R') (B := R') f).comp ψ₁ =
      (tsz (R := R') (B := R') g).comp ψ₁ → f = g) :
    Nonempty (N ≃ₗ[R'] M) := by
  obtain ⟨ψ₀, g₀, r₀⟩ := exists_good (M := N) hcot hes hjs hje iW
  obtain ⟨u₁, r₁, -⟩ := exists_unique_of_good (M := M) hcot hes hjs hje ψ₁ h₁
  obtain ⟨u', hu'⟩ := extW u₁
  obtain ⟨v, hv⟩ := extM ψ₀ g₀
  have ha : (v.restrictScalars R).comp u₁ = iW :=
    (exists_unique_of_good (M := N) hcot hes hjs hje ψ₀ g₀).unique
      (by rw [← hv]; exact rel_comp v r₁) r₀
  have hb : (tsz (R := R') (B := R') u').comp ψ₀ = ψ₁ := by
    apply spMap_injective
    rw [← cancel_mono j, rel_comp u' r₀, hu', r₁]
  have h1 : v.comp u' = LinearMap.id := by
    apply uniqW
    ext w
    have := congrArg (fun f => f w) ha
    have h2 := congrArg (fun f => f w) hu'
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at this h2 ⊢
    rw [h2, this]
    rfl
  have h2 : u'.comp v = LinearMap.id := by
    apply uniqM
    rw [tsz_id_comp]
    have := tsz_comp (R := R') (R' := R') v u'
    rw [LinearMap.restrictScalars_self] at this
    rw [← this, RingHom.comp_assoc, hv, hb]
  exact ⟨LinearEquiv.ofLinear u' v h2 h1⟩
end GlobalTheory.CompanionTheory.CotLoc
