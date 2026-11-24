-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AbForms.par_of_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:28:06.426968+00:00
-- url     : https://prove2.me/submissions/c618978f-9813-4e85-8832-cfa132fa863f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UOfIsBaseChange
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
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
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AbForms
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R : Type} [CommRing R]
variable {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CompanionTheory.AbForms
theorem _root_.solution (hS : Stein F) {W : Type} [AddCommGroup W] [Module R W] (g : ℕ) (hW : VB R W g)
    (u : ∀ T, W →ₗ[R] Ω[F.obj T⁄R]) (hu : ∀ T, IsBaseChange (F.obj T) (u T))
    (hc : ∀ ⦃T T' : C⦄ (φ : T ⟶ T') (w : W), u T' w = p1 F φ (u T w)) :
    Par F ∧ VB R (Glob1 F) g := by
  obtain ⟨hfin, hproj, hrank⟩ := hW
  obtain ⟨n, a, b, -, -, hab⟩ := Module.Finite.exists_comp_eq_id_of_projective R W
  let lam : Fin n → W →ₗ[R] R := fun k ↦ LinearMap.proj k ∘ₗ b
  let v : Fin n → W := fun k ↦ a (Pi.single k 1)
  have hdec : ∀ w, ∑ k, lam k w • v k = w := fun w ↦ by
    have e1 : a (b w) = w := LinearMap.congr_fun hab w
    conv_rhs => rw [← e1, pi_eq_sum_univ' (b w)]
    simp [lam, v, map_sum]
  let abelian₂ : ∀ k T, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T := fun k T ↦
    (hu T).lift (Algebra.linearMap R (F.obj T) ∘ₗ lam k)
  have hLam : ∀ k T w, abelian₂ k T (u T w) = algebraMap R (F.obj T) (lam k w) := fun k T w ↦
    (hu T).lift_eq _ w
  have hexp : ∀ T (ξ : Ω[F.obj T⁄R]), ∑ k, abelian₂ k T ξ • u T (v k) = ξ := fun T ξ ↦ by
    have e : (∑ k, (LinearMap.toSpanSingleton (F.obj T) _ (u T (v k))) ∘ₗ abelian₂ k T) = LinearMap.id :=
      (hu T).algHom_ext _ _ fun w ↦ by
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, hLam,
          LinearMap.id_apply, algebraMap_smul]
        have := congrArg (u T) (hdec w)
        rw [map_sum] at this
        simpa using this
    simpa using LinearMap.congr_fun e ξ
  have hcomp : ∀ k ⦃T T' : C⦄ (φ : T ⟶ T') (ξ : Ω[F.obj T⁄R]),
      mp F φ (abelian₂ k T ξ) = abelian₂ k T' (p1 F φ ξ) := fun k T T' φ ξ ↦ by
    refine (hu T).inductionOn ξ _ (by simp) (fun w ↦ ?_) (fun s n hn ↦ ?_) (fun a b ha hb ↦ ?_)
    · rw [← hc φ w, hLam, hLam]
      exact (mp F φ).commutes _
    · rw [(abelian₂ k T).map_smul, oneFormsMapOfFunctorMorphism_smul, (abelian₂ k T').map_smul, smul_eq_mul, smul_eq_mul, map_mul, hn]
    · simp only [map_add, ha, hb]
  let jm : W →ₗ[R] Glob1 F := LinearMap.codRestrict (Glob1 F) (LinearMap.pi u) fun w T T' φ ↦ hc φ w
  have hj : ∀ w T, (jm w).1 T = u T w := fun _ _ ↦ rfl
  have hinj : Function.Injective jm := (injective_iff_map_eq_zero jm).2 fun w h ↦ by
    have h0 : ∀ k, lam k w = 0 := fun k ↦ hS.2 (by
      rw [map_zero]
      funext T
      refine ((hLam k T w).symm.trans ?_)
      rw [← hj, h]
      exact map_zero _)
    rw [← hdec w]
    simp [h0]
  have hsurj : Function.Surjective jm := fun ω ↦ by
    have hd : ∀ k, ∃ r : R, Algebra.linearMap R (C0 F) r = fun T ↦ abelian₂ k T (ω.1 T) := fun k ↦
      (hS.1 _).1 (by
        funext T T' φ
        rw [amitsur_d0_apply, hcomp, ← ω.2 φ, sub_self]
        rfl)
    choose r hr using hd
    refine ⟨∑ k, r k • v k, Subtype.ext (funext fun T ↦ ?_)⟩
    rw [hj, map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun k _ ↦ ?_) (hexp T (ω.1 T))
    rw [map_smul, ← congrFun (hr k) T, ← algebraMap_smul (F.obj T) (r k) (u T (v k))]
    rfl
  let e : W ≃ₗ[R] Glob1 F := LinearEquiv.ofBijective jm ⟨hinj, hsurj⟩
  have he : ∀ T w, evForm F T (e w) = u T w := fun _ _ ↦ rfl
  refine ⟨fun T ↦ IsBaseChange.of_lift_unique _ fun Q _ _ _ _ q ↦ ?_,
    Module.Finite.equiv e, Module.Projective.of_equiv e, fun p ↦ ?_⟩
  · refine ⟨(hu T).lift (q ∘ₗ e.toLinearMap), ?_, fun q' hq' ↦ ?_⟩
    · refine LinearMap.ext fun ω ↦ ?_
      obtain ⟨w, rfl⟩ := e.surjective ω
      change (hu T).lift (q ∘ₗ e.toLinearMap) (evForm F T (e w)) = q (e w)
      rw [he]
      exact (hu T).lift_eq _ w
    · refine (hu T).algHom_ext _ _ fun w ↦ ?_
      rw [(hu T).lift_eq, ← he]
      exact LinearMap.congr_fun hq' (e w)
  · rw [← Module.rankAtStalk_eq_of_equiv e]
    exact hrank p
end GlobalTheory.CompanionTheory.AbForms
