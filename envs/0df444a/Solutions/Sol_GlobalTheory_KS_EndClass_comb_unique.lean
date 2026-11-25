-- Prove2me | solution 1 for GlobalTheory.KS.EndClass.comb_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:14:47.184678+00:00
-- url     : https://prove2.me/submissions/7b7e656f-a15a-4fb7-bc20-adb9b2201712

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsAlongGroupHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsBasisVerticalDerivationsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerClassCohomologousAlongEndomorphism
import Theorems.Thm_P2M_GlobalTheory_KS_EndClass_pbT___bijective_504caa37308d
import Theorems.Thm_P2M_GlobalTheory_KS_EndClass_constFn_zero__8bf9ed36dcbe
import Theorems.Thm_P2M_GlobalTheory_KS_EndClass_pre___eq_20bc979cb662
import Theorems.Thm_P2M_GlobalTheory_KS_EndClass_pbT___comb_5bc8e4e36b6a
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply


section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
namespace GlobalTheory.KS.EndClass
variable {X Y Z T : Scheme.{0}}
private lemma rsT_sub_moduli' {Y : Scheme.{0}} {O₀ : Y.Opens} (a b : Γ(Y, O₀)) (O : Y.Opens) :
    rsT (a - b) O = rsT a O - rsT b O := by
  by_cases h : O ≤ O₀
  · simp only [rsT, dif_pos h, map_sub]
  · simp only [rsT, dif_neg h, sub_zero]
private lemma pbT_zero_eq_zero {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (V : Z.Opens) :
    pbT f (0 : Γ(Y, O₀)) V = 0 := by
  by_cases h : V ≤ f ⁻¹ᵁ O₀
  · simp only [pbT, dif_pos h, map_zero]
  · simp only [pbT, dif_neg h]
private lemma rsT_zero_eq_zero {Y : Scheme.{0}} {O₀ : Y.Opens} (O : Y.Opens) :
    rsT (0 : Γ(Y, O₀)) O = 0 := by
  by_cases h : O ≤ O₀
  · simp only [rsT, dif_pos h, map_zero]
  · simp only [rsT, dif_neg h]
private lemma locDerK_zero' {Y X : Scheme.{0}} {K R : Type} [Field K] [CommRing R] (q : Y ⟶ Sp K)
    (p : X ⟶ Sp R) (m : Y ⟶ X) (W₀ : X.Opens) :
    LocDerK q p m (fun _ => 0) W₀ (fun _ _ => 0) :=
  ⟨fun _ _ _ _ => (add_zero 0).symm, fun _ _ _ _ => by simp, fun _ _ _ _ _ => (rsT_zero_eq_zero _).symm,
    fun _ _ _ => (constFn_zero' q _).symm⟩
variable {K : Type} [Field K] {R : Type} [CommRing R] {g : ℕ}
end GlobalTheory.KS.EndClass
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.EndClass
variable {X Y Z T : Scheme.{0}}
variable {K : Type} [Field K] {R : Type} [CommRing R] {g : ℕ}
namespace GlobalTheory.KS.EndClass
theorem _root_.solution {q : Y ⟶ Sp K} {p : X ⟶ Sp R} {m : Y ⟶ X} {dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)}
    (hb : IsBasis q p m dd) (y : Z ⟶ Y) (O : Z.Opens) (W₀ : X.Opens) (hO : O ≤ y ⁻¹ᵁ m ⁻¹ᵁ W₀)
    (c c' : Fin g → Γ(Z, O))
    (h : ∀ W, W ≤ W₀ → ∀ f : Γ(X, W),
      ∑ a, rsT (c a) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) =
      ∑ a, rsT (c' a) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W)) :
    c = c' := by
  have hV₀ : ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀ = O.ι ⁻¹ᵁ O := by rw [pre_ι_eq, inf_eq_left.mpr hO]
  have hz : ∀ W, W ≤ W₀ → ∀ f : Γ(X, W), (fun _ _ => 0 : ∀ W : X.Opens, Γ(X, W) → Γ(O.toScheme, ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W)) W f =
      ∑ a, rsT ((fun a => pbT O.ι (c a - c' a) (((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀)) a) _ *
        pbT (O.ι ≫ y) (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
    intro W hW f
    have e := pbT_ι_comb dd y O hO hW (fun a => c a - c' a) f
    beta_reduce at e ⊢
    rw [← e]
    simp only [rsT_sub_moduli', sub_mul, Finset.sum_sub_distrib, h W hW f, sub_self, pbT_zero_eq_zero]
  have hz' : ∀ W, W ≤ W₀ → ∀ f : Γ(X, W), (fun _ _ => 0 : ∀ W : X.Opens, Γ(X, W) → Γ(O.toScheme, ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W)) W f =
      ∑ a, rsT ((0 : Fin g → Γ(O.toScheme, ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀)) a) _ *
        pbT (O.ι ≫ y) (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
    intro W hW f
    simp only [Pi.zero_apply, rsT_zero_eq_zero, zero_mul, Finset.sum_const_zero]
  obtain ⟨c₀, -, hu⟩ := hb O.toScheme (O.ι ≫ y) W₀ _ (locDerK_zero' _ p _ W₀)
  have e₁ := hu _ hz
  have e₂ := hu _ hz'
  funext a
  have ha : pbT O.ι (c a - c' a) (((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀) = pbT O.ι (0 : Γ(Z, O)) (((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀) := by
    rw [pbT_zero_eq_zero]
    exact congrFun (e₁.trans e₂.symm) a
  exact sub_eq_zero.mp ((pbT_ι_bijective O (le_refl O) hV₀).1 ha)
end GlobalTheory.KS.EndClass
