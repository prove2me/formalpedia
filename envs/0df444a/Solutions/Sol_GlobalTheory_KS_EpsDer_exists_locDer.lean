-- Prove2me | solution 1 for GlobalTheory.KS.EpsDer.exists_locDer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:00:39.671897+00:00
-- url     : https://prove2.me/submissions/063c6b8c-287a-496b-bf2e-f0d2b83adbc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationOfDualNumberThickening
import Theorems.Thm_GlobalTheory_KS_EpsDer_pull_pull
import Theorems.Thm_GlobalTheory_KS_EpsDer_res_pull
import Theorems.Thm_GlobalTheory_KS_EpsDer_pull_res
import Theorems.Thm_GlobalTheory_KS_EpsDer_app_res
import Theorems.Thm_GlobalTheory_KS_EpsDer_id_pull
import Theorems.Thm_GlobalTheory_KS_EpsDer_spec_pull
import Theorems.Thm_GlobalTheory_KS_EpsDer_pull_const
import Theorems.Thm_GlobalTheory_KS_EpsDer_res_const
import Theorems.Thm_GlobalTheory_KS_EpsDer_const_eq
import Theorems.Thm_GlobalTheory_KS_EpsDer_dual_decomp
import Theorems.Thm_GlobalTheory_T_const_thickening_complex_functions_structure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.EpsDer
variable {X Y Z : Scheme.{0}}
private theorem appLE_app_of_comp_eq {A B C : Scheme.{0}} (f : C ⟶ B) (g : B ⟶ A) (k : C ⟶ A) (e : f ≫ g = k)
    {O : A.Opens} {V : C.Opens} (e₁ : V ≤ f ⁻¹ᵁ (g ⁻¹ᵁ O)) (e₂ : V ≤ k ⁻¹ᵁ O) (a : Γ(A, O)) :
    (f.appLE (g ⁻¹ᵁ O) V e₁).hom ((g.app O).hom a) = (k.appLE O V e₂).hom a := by
  rw [Scheme.Hom.app_eq_appLE]
  exact pull_pull f g k e le_rfl e₁ e₂ a
private theorem constFn_eps_mul_self {A : Scheme.{0}} (π : A ⟶ Sp (DualNumber ℂ)) (V : A.Opens) :
    constFn π V DualNumber.eps * constFn π V DualNumber.eps = 0 := by
  rw [const_eq, ← map_mul, DualNumber.eps_mul_eps, map_zero]
private theorem appLE_app_of_section' {A B : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ A) (e : f ≫ g = 𝟙 A) {O : A.Opens}
    (e₁ : O ≤ f ⁻¹ᵁ (g ⁻¹ᵁ O)) (a : Γ(A, O)) : (f.appLE (g ⁻¹ᵁ O) O e₁).hom ((g.app O).hom a) = a := by
  rw [appLE_app_of_comp_eq f g (𝟙 A) e e₁ le_rfl]
  exact id_pull _ a
end GlobalTheory.KS.EpsDer
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.EpsDer
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.KS.EpsDer
theorem _root_.solution : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y ⟶ X) (Φ : Y' ⟶ X), j ≫ Φ = m → Φ ≫ p = π ≫ spMap xD → ∃ d, LocDer q p m (fun r => (xD r).snd) ⊤ d ∧ ∀ (y : Sp ℂ ⟶ Y) (yt : Sp (DualNumber ℂ) ⟶ Y'), yt ≫ ρ = (spMap (algebraMap ℂ (DualNumber ℂ))) ≫ y → yt ≫ π = 𝟙 _ → ∀ (W : X.Opens) (h : ⊤ ≤ (yt ≫ Φ) ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom (((yt ≫ Φ).appLE W ⊤ h).hom f)) = valAt' y (m ⁻¹ᵁ W) (d W f) := by
  intro Y Y' q π ρ j hpb hjρ hjπ R _ xD X p m Φ hm hΦ
  obtain ⟨hO, -, hdec⟩ := GlobalTheory.T.const_thickening_complex_functions_structure Y Y' q π ρ j hpb hjρ hjπ

  have hW : ∀ W : X.Opens, ρ ⁻¹ᵁ (m ⁻¹ᵁ W) = Φ ⁻¹ᵁ W := fun W => by
    subst hm
    exact hO (Φ ⁻¹ᵁ W)
  have hjO : ∀ O : Y.Opens, j ⁻¹ᵁ (ρ ⁻¹ᵁ O) = O := fun O => by
    show (j ≫ ρ) ⁻¹ᵁ O = O
    rw [hjρ]
    rfl

  have uniq : ∀ (O : Y.Opens) (a b a' b' : Γ(Y, O)),
      (ρ.app O).hom a + constFn π _ DualNumber.eps * (ρ.app O).hom b =
        (ρ.app O).hom a' + constFn π _ DualNumber.eps * (ρ.app O).hom b' → a = a' ∧ b = b' := by
    intro O a b a' b' e
    have := (hdec O ((ρ.app O).hom a + constFn π _ DualNumber.eps * (ρ.app O).hom b)).unique
      (y₁ := (a, b)) (y₂ := (a', b')) rfl e
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hex : ∀ (W : X.Opens) (f : Γ(X, W)), ∃ ab : Γ(Y, m ⁻¹ᵁ W) × Γ(Y, m ⁻¹ᵁ W),
      (Φ.appLE W (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (hW W).le).hom f =
        (ρ.app _).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app _).hom ab.2 :=
    fun W f => (hdec (m ⁻¹ᵁ W) _).exists
  choose AB hAB using hex

  have Aeq : ∀ (W : X.Opens) (f : Γ(X, W)), (AB W f).1 = (m.app W).hom f := by
    intro W f
    have e := congrArg (j.appLE (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (m ⁻¹ᵁ W) (hjO _).ge).hom (hAB W f)
    rw [map_add, map_mul, pull_pull j Φ m hm (hW W).le (hjO _).ge le_rfl f,
      appLE_app_of_section' j ρ hjρ (hjO _).ge, appLE_app_of_section' j ρ hjρ (hjO _).ge, pull_const (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom j π q hjπ] at e
    have h0 : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom DualNumber.eps = 0 := by simp
    rw [h0, const_eq, map_zero, zero_mul, add_zero] at e
    rw [← e, Scheme.Hom.app_eq_appLE]
  refine ⟨fun W f => (AB W f).2, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro W _ f f'
    refine (uniq _ (AB W (f + f')).1 _ ((AB W f).1 + (AB W f').1) ((AB W f).2 + (AB W f').2) ?_).2
    rw [← hAB W (f + f')]
    simp only [map_add]
    rw [hAB W f, hAB W f']
    ring
  · intro W _ f f'
    rw [← Aeq W f, ← Aeq W f']
    refine (uniq _ (AB W (f * f')).1 _ ((AB W f).1 * (AB W f').1) ((AB W f).1 * (AB W f').2 + (AB W f').1 * (AB W f).2) ?_).2
    rw [← hAB W (f * f')]
    simp only [map_mul, map_add]
    rw [hAB W f, hAB W f']
    linear_combination ((ρ.app _).hom (AB W f).2 * (ρ.app _).hom (AB W f').2) * constFn_eps_mul_self π (ρ ⁻¹ᵁ (m ⁻¹ᵁ W))
  · intro W W' h _ f
    have hOO : m ⁻¹ᵁ W' ≤ m ⁻¹ᵁ W := fun _ hy => h hy
    have hV : ρ ⁻¹ᵁ (m ⁻¹ᵁ W') ≤ ρ ⁻¹ᵁ (m ⁻¹ᵁ W) := fun _ hy => hOO hy
    refine (uniq _ (AB W' (resG X h f)).1 _ (resG Y hOO (AB W f).1) (resG Y hOO (AB W f).2) ?_).2
    rw [← hAB W' (resG X h f), pull_res Φ (hW W').le h f, ← res_pull Φ (hW W).le hV f, hAB W f,
      map_add, map_mul, res_const, ← app_res ρ hOO (AB W f).1, ← app_res ρ hOO (AB W f).2]
  · intro W _ r
    have hc : ∀ c : ℂ, (ρ.app (m ⁻¹ᵁ W)).hom (constFn q (m ⁻¹ᵁ W) c) =
        constFn π (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (algebraMap ℂ (DualNumber ℂ) c) := fun c => by
      rw [Scheme.Hom.app_eq_appLE]
      exact pull_const (algebraMap ℂ (DualNumber ℂ)) ρ q π hpb.w le_rfl c
    have e1 : constFn π (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (xD r) =
        constFn π _ (algebraMap ℂ (DualNumber ℂ) (xD r).fst) +
          constFn π _ DualNumber.eps * constFn π _ (algebraMap ℂ (DualNumber ℂ) (xD r).snd) := by
      simp only [const_eq]
      rw [← map_mul, ← map_add, ← dual_decomp]
    refine (uniq _ (AB W (constFn p W r)).1 _ (constFn q _ (xD r).fst) (constFn q _ (xD r).snd) ?_).2
    rw [← hAB W (constFn p W r), pull_const xD Φ p π hΦ, e1, hc, hc]
  · intro y yt hy1 hy2 W h f
    have h2 : ⊤ ≤ y ⁻¹ᵁ (m ⁻¹ᵁ W) := by
      intro s _
      have ht : yt ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) s) ∈ ρ ⁻¹ᵁ (m ⁻¹ᵁ W) := by
        rw [hW W]
        exact h trivial
      have e : ρ (yt ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) s)) =
          y ((spMap (algebraMap ℂ (DualNumber ℂ))) ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) s)) :=
        congrArg (fun g : Sp (DualNumber ℂ) ⟶ Y => g ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) s)) hy1
      have hs : (spMap (algebraMap ℂ (DualNumber ℂ))) ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) s) = s :=
        Subsingleton.elim _ _
      show y s ∈ m ⁻¹ᵁ W
      rw [← hs, ← e]
      exact ht
    have h' : ⊤ ≤ yt ⁻¹ᵁ (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) := by
      rw [hW W]
      exact h
    have e1 : ((yt ≫ Φ).appLE W ⊤ h).hom f = (yt.appLE _ ⊤ h').hom ((Φ.appLE W _ (hW W).le).hom f) :=
      (pull_pull yt Φ (yt ≫ Φ) rfl (hW W).le h' h f).symm
    have e2 : ∀ a : Γ(Y, m ⁻¹ᵁ W), (yt.appLE _ ⊤ h').hom ((ρ.app (m ⁻¹ᵁ W)).hom a) =
        ((spMap (algebraMap ℂ (DualNumber ℂ))).appLE ⊤ ⊤ (fun _ _ => trivial)).hom ((y.appLE _ ⊤ h2).hom a) := by
      intro a
      rw [appLE_app_of_comp_eq yt ρ _ hy1 h' (fun x _ => h2 trivial),
        pull_pull (spMap (algebraMap ℂ (DualNumber ℂ))) y _ rfl h2 (fun _ _ => trivial) (fun x _ => h2 trivial)]
    have e3 : (yt.appLE _ ⊤ h').hom (constFn π (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) DualNumber.eps) =
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps := by
      unfold constFn
      rw [pull_pull yt π (𝟙 _) hy2 (U := ⊤) (V := ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (W := ⊤) (fun _ _ => trivial) h'
        (fun _ _ => trivial)]
      exact id_pull _ _
    have e4 : (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps) = DualNumber.eps :=
      congrArg (fun g => CommRingCat.Hom.hom g DualNumber.eps)
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv_hom_id
    show TrivSqZeroExt.snd ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom
      (((yt ≫ Φ).appLE W ⊤ h).hom f)) = valAt' y (m ⁻¹ᵁ W) (AB W f).2
    unfold valAt' valAt
    rw [dif_pos h2, e1, hAB W f, map_add, map_mul, e2, e2, e3, map_add, map_mul, e4]
    clear e1 e2 e3 e4 uniq hdec Aeq hAB hO hjO hpb hjρ hjπ hΦ hm
    have s1 := spec_pull (algebraMap ℂ (DualNumber ℂ)) (fun _ _ => trivial) ((y.appLE _ ⊤ h2).hom (AB W f).1)
    have s2 := spec_pull (algebraMap ℂ (DualNumber ℂ)) (fun _ _ => trivial) ((y.appLE _ ⊤ h2).hom (AB W f).2)
    rw [s1, s2]
    simp [TrivSqZeroExt.algebraMap_eq_inl]
end GlobalTheory.KS.EpsDer
