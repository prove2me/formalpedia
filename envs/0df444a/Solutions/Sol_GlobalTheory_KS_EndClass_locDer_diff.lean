-- Prove2me | solution 1 for GlobalTheory.KS.EndClass.locDer_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:56:11.654799+00:00
-- url     : https://prove2.me/submissions/2d53328e-5380-48b6-bafc-ed1fb1476dea

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
import Theorems.Thm_GlobalTheory_KS_EndClass_pbT_pbT
import Theorems.Thm_GlobalTheory_KS_EndClass_app_eq
import Theorems.Thm_GlobalTheory_KS_EndClass_resG_eq
import Theorems.Thm_P2M_GlobalTheory_KS_EndClass_constFn_zero__8bf9ed36dcbe
import Theorems.Thm_GlobalTheory_KS_InvField_pbT_pbT
import Theorems.Thm_GlobalTheory_KS_InvHom_pbT_pbT
import Theorems.Thm_GlobalTheory_KS_IsCob_add
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
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
private lemma rsT_eq_pbT_id {Y : Scheme.{0}} {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Y.Opens) :
    rsT s O = pbT (𝟙 Y) s O := by
  by_cases h : O ≤ O₀
  · have h' : O ≤ (𝟙 Y) ⁻¹ᵁ O₀ := h
    simp only [rsT, pbT, dif_pos h, dif_pos h', Scheme.Hom.appLE, resG]
    rfl
  · have h' : ¬ O ≤ (𝟙 Y) ⁻¹ᵁ O₀ := h
    simp only [rsT, pbT, dif_neg h, dif_neg h']
private lemma pbT_eq_appLE_hom {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} {V : Z.Opens} (h : V ≤ f ⁻¹ᵁ O₀)
    (s : Γ(Y, O₀)) : pbT f s V = (f.appLE O₀ V h).hom s := by
  simp only [pbT, dif_pos h]
private lemma rsT_sub_moduli' {Y : Scheme.{0}} {O₀ : Y.Opens} (a b : Γ(Y, O₀)) (O : Y.Opens) :
    rsT (a - b) O = rsT a O - rsT b O := by
  by_cases h : O ≤ O₀
  · simp only [rsT, dif_pos h, map_sub]
  · simp only [rsT, dif_neg h, sub_zero]
variable {K : Type} [Field K] {R : Type} [CommRing R] {g : ℕ}
private lemma pbT_add_of_open {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (a b : Γ(Y, O₀)) (V : Z.Opens) :
    pbT f (a + b) V = pbT f a V + pbT f b V := by
  by_cases h : V ≤ f ⁻¹ᵁ O₀
  · simp only [pbT, dif_pos h, map_add]
  · simp only [pbT, dif_neg h, add_zero]
private lemma pbT_mul_of_le_preimage {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (a b : Γ(Y, O₀)) {V : Z.Opens}
    (h : V ≤ f ⁻¹ᵁ O₀) : pbT f (a * b) V = pbT f a V * pbT f b V := by
  simp only [pbT, dif_pos h, map_mul]
private lemma pbT_congr {Y Z : Scheme.{0}} {f f' : Z ⟶ Y} (e : f = f') {O₀ : Y.Opens} (s : Γ(Y, O₀))
    (V : Z.Opens) : pbT f s V = pbT f' s V := by
  subst e
  rfl
private lemma pbT_rsT_eq_rsT_pbT {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ O : Y.Opens} {V₀ V : Z.Opens} (s : Γ(Y, O₀))
    (hO : O ≤ O₀) (hV : V ≤ f ⁻¹ᵁ O) (hV₀ : V₀ ≤ f ⁻¹ᵁ O₀) (hVV : V ≤ V₀) :
    pbT f (rsT s O) V = rsT (pbT f s V₀) V := by
  have hO' : O ≤ (𝟙 Y) ⁻¹ᵁ O₀ := hO
  have hVV' : V ≤ (𝟙 Z) ⁻¹ᵁ V₀ := hVV
  rw [rsT_eq_pbT_id, rsT_eq_pbT_id, pbT_pbT f (𝟙 Y) hO' hV, pbT_pbT (𝟙 Z) f hV₀ hVV']
  simp only [Category.comp_id, Category.id_comp]
private lemma pbT_constFn_of_le_preimage {Y Z : Scheme.{0}} {R : Type} [CommRing R] (f : Z ⟶ Y) (q : Y ⟶ Sp R)
    {O : Y.Opens} {V : Z.Opens} (h : V ≤ f ⁻¹ᵁ O) (r : R) : pbT f (constFn q O r) V = constFn (f ≫ q) V r := by
  rw [pbT_eq_appLE_hom f h]
  exact congrArg (fun φ : Γ(Sp R, ⊤) ⟶ Γ(Z, V) => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.Hom.appLE_comp_appLE f q ⊤ O V (by exact le_top) h)
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
theorem _root_.solution {q : Y ⟶ Sp K} {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {W₁ W₂ : X.Opens}
    {d₁ d₂ : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h₁ : LocDerK q p m D W₁ d₁) (h₂ : LocDerK q p m D W₂ d₂)
    (f : X ⟶ X) (f₀ : Y ⟶ Y) (hp : f ≫ p = p) (hq : f₀ ≫ q = q) (hm : f₀ ≫ m = m ≫ f)
    (t : T ⟶ Y) (ht : ⊤ ≤ t ⁻¹ᵁ m ⁻¹ᵁ W₁) :
    LocDerK ((t ≫ f₀) ≫ q) p ((t ≫ f₀) ≫ m) (fun _ => 0) W₂ (fun W h =>
      pbT t (d₁ (W₁ ⊓ f ⁻¹ᵁ W) (pbT f h _)) _ - pbT (t ≫ f₀) (d₂ W h) _) := by
  have ht' : t ⁻¹ᵁ m ⁻¹ᵁ W₁ = ⊤ := top_le_iff.mp ht
  have hM : ∀ W, ((t ≫ f₀) ≫ m) ⁻¹ᵁ W = t ⁻¹ᵁ m ⁻¹ᵁ (W₁ ⊓ f ⁻¹ᵁ W) := by
    intro W
    rw [Category.assoc, hm, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, ht', top_inf_eq]
    rfl
  have hL : ∀ W, ((t ≫ f₀) ≫ m) ⁻¹ᵁ W ≤ t ⁻¹ᵁ m ⁻¹ᵁ (W₁ ⊓ f ⁻¹ᵁ W) := fun W => le_of_eq (hM W)
  have hL' : ∀ W, ((t ≫ f₀) ≫ m) ⁻¹ᵁ W ≤ (t ≫ f₀) ⁻¹ᵁ m ⁻¹ᵁ W := fun W => le_rfl
  have hA : ∀ W (h : Γ(X, W)), pbT t ((m.app (W₁ ⊓ f ⁻¹ᵁ W)).hom (pbT f h (W₁ ⊓ f ⁻¹ᵁ W))) (((t ≫ f₀) ≫ m) ⁻¹ᵁ W) =
      (((t ≫ f₀) ≫ m).app W).hom h := by
    intro W h
    have e₁ : W₁ ⊓ f ⁻¹ᵁ W ≤ f ⁻¹ᵁ W := inf_le_right
    have e₂ : m ⁻¹ᵁ (W₁ ⊓ f ⁻¹ᵁ W) ≤ (m ≫ f) ⁻¹ᵁ W := m.preimage_mono inf_le_right
    rw [app_eq, app_eq, pbT_pbT m f e₁ le_rfl, pbT_pbT t (m ≫ f) e₂ (hL W)]
    exact pbT_congr (by rw [Category.assoc, hm]) _ _
  have hB : ∀ W (h : Γ(X, W)), pbT (t ≫ f₀) ((m.app W).hom h) (((t ≫ f₀) ≫ m) ⁻¹ᵁ W) =
      (((t ≫ f₀) ≫ m).app W).hom h := by
    intro W h
    rw [app_eq, app_eq, pbT_pbT (t ≫ f₀) m le_rfl (hL' W)]
  refine ⟨fun W hW h h' => ?_, fun W hW h h' => ?_, fun W W' hh hW h => ?_, fun W hW r => ?_⟩
  · rw [pbT_add_of_open, h₁.add (W₁ ⊓ f ⁻¹ᵁ W) inf_le_left, pbT_add_of_open, h₂.add W hW, pbT_add_of_open]
    abel
  · rw [pbT_mul_of_le_preimage f h h' (inf_le_right : W₁ ⊓ f ⁻¹ᵁ W ≤ f ⁻¹ᵁ W), h₁.mul (W₁ ⊓ f ⁻¹ᵁ W) inf_le_left,
      h₂.mul W hW, pbT_add_of_open, pbT_add_of_open, pbT_mul_of_le_preimage _ _ _ (hL W), pbT_mul_of_le_preimage _ _ _ (hL W),
      pbT_mul_of_le_preimage _ _ _ (hL' W), pbT_mul_of_le_preimage _ _ _ (hL' W), hA, hA, hB, hB]
    ring
  · have hV : W₁ ⊓ f ⁻¹ᵁ W' ≤ W₁ ⊓ f ⁻¹ᵁ W := inf_le_inf_left _ (f.preimage_mono hh)
    rw [h₂.res W W' hh hW, resG_eq, pbT_rsT_eq_rsT_pbT f h hh inf_le_right inf_le_right hV, ← resG_eq hV,
      h₁.res _ _ hV inf_le_left,
      pbT_rsT_eq_rsT_pbT t _ (m.preimage_mono hV) (hL W') (hL W) ((t ≫ f₀ ≫ m).preimage_mono hh),
      pbT_rsT_eq_rsT_pbT (t ≫ f₀) _ (m.preimage_mono hh) (hL' W') (hL' W) (((t ≫ f₀) ≫ m).preimage_mono hh),
      rsT_sub_moduli']
  · rw [pbT_constFn_of_le_preimage f p (inf_le_right : W₁ ⊓ f ⁻¹ᵁ W ≤ f ⁻¹ᵁ W), hp, h₁.base _ inf_le_left,
      h₂.base W hW, pbT_constFn_of_le_preimage t q (hL W), pbT_constFn_of_le_preimage (t ≫ f₀) q (hL' W), Category.assoc t f₀ q, hq,
      sub_self, constFn_zero']
end GlobalTheory.KS.EndClass
