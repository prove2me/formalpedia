-- Prove2me | solution 1 for GlobalTheory.KS.EndClass.cohom_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:48:16.498801+00:00
-- url     : https://prove2.me/submissions/7cf2c10a-6aeb-427d-80f9-df08eb0e5dff

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
import Theorems.Thm_P2M_GlobalTheory_KS_EndClass_pre___eq_20bc979cb662
import Theorems.Thm_GlobalTheory_KS_EndClass_comb_unique
import Theorems.Thm_GlobalTheory_KS_EndClass_comb_exists
import Theorems.Thm_GlobalTheory_KS_EndClass_locDer_diff
import Theorems.Thm_GlobalTheory_KS_InvField_pbT_pbT
import Theorems.Thm_GlobalTheory_KS_InvHom_pbT_pbT
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
private lemma pbT_congr {Y Z : Scheme.{0}} {f f' : Z ⟶ Y} (e : f = f') {O₀ : Y.Opens} (s : Γ(Y, O₀))
    (V : Z.Opens) : pbT f s V = pbT f' s V := by
  subst e
  rfl
private lemma pbT_constFn_of_le_preimage {Y Z : Scheme.{0}} {R : Type} [CommRing R] (f : Z ⟶ Y) (q : Y ⟶ Sp R)
    {O : Y.Opens} {V : Z.Opens} (h : V ≤ f ⁻¹ᵁ O) (r : R) : pbT f (constFn q O r) V = constFn (f ≫ q) V r := by
  rw [pbT_eq_appLE_hom f h]
  exact congrArg (fun φ : Γ(Sp R, ⊤) ⟶ Γ(Z, V) => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.Hom.appLE_comp_appLE f q ⊤ O V (by exact le_top) h)
private lemma pbT_sub' {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (a b : Γ(Y, O₀)) (V : Z.Opens) :
    pbT f (a - b) V = pbT f a V - pbT f b V := by
  by_cases h : V ≤ f ⁻¹ᵁ O₀
  · simp only [pbT, dif_pos h, map_sub]
  · simp only [pbT, dif_neg h, sub_zero]
private lemma pbT_rsT_of_le_of_le_preimage {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ O : Y.Opens} {L : Z.Opens} (s : Γ(Y, O₀))
    (hV : L ≤ f ⁻¹ᵁ O) (hO : O ≤ O₀) : pbT f (rsT s O) L = pbT f s L := by
  have hO' : O ≤ (𝟙 Y) ⁻¹ᵁ O₀ := hO
  rw [rsT_eq_pbT_id, pbT_pbT f (𝟙 Y) hO' hV, Category.comp_id]
private lemma rsT_rsT_of_le {Y : Scheme.{0}} {O₀ O O' : Y.Opens} (s : Γ(Y, O₀)) (h₁ : O ≤ O₀) (h₂ : O' ≤ O) :
    rsT (rsT s O) O' = rsT s O' := by
  have h₁' : O ≤ (𝟙 Y) ⁻¹ᵁ O₀ := h₁
  have h₂' : O' ≤ (𝟙 Y) ⁻¹ᵁ O := h₂
  rw [rsT_eq_pbT_id, rsT_eq_pbT_id, rsT_eq_pbT_id, pbT_pbT (𝟙 Y) (𝟙 Y) h₁' h₂', Category.comp_id]
private lemma rsT_pbT_of_le_preimage {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} {V₀ V : Z.Opens} (s : Γ(Y, O₀))
    (hV₀ : V₀ ≤ f ⁻¹ᵁ O₀) (hV : V ≤ V₀) : rsT (pbT f s V₀) V = pbT f s V := by
  have hV' : V ≤ (𝟙 Z) ⁻¹ᵁ V₀ := hV
  rw [rsT_eq_pbT_id, pbT_pbT (𝟙 Z) f hV₀ hV', Category.id_comp]
private lemma rsT_constFn_of_le {Y : Scheme.{0}} {R : Type} [CommRing R] (q : Y ⟶ Sp R) {O O' : Y.Opens}
    (h : O' ≤ O) (r : R) : rsT (constFn q O r) O' = constFn q O' r := by
  have h' : O' ≤ (𝟙 Y) ⁻¹ᵁ O := h
  rw [rsT_eq_pbT_id, pbT_constFn_of_le_preimage (𝟙 Y) q h', Category.id_comp]
private lemma rsT_sum_mul {Y : Scheme.{0}} {n : ℕ} {O O' : Y.Opens} (h : O' ≤ O) (u v : Fin n → Γ(Y, O)) :
    rsT (∑ a, u a * v a) O' = ∑ a, rsT (u a) O' * rsT (v a) O' := by
  rw [← resG_eq h, map_sum]
  simp only [map_mul]
  simp only [resG_eq h]
private lemma pbT_sum_mul {Y Z : Scheme.{0}} {n : ℕ} (f : Z ⟶ Y) {O : Y.Opens} {V : Z.Opens}
    (h : V ≤ f ⁻¹ᵁ O) (u v : Fin n → Γ(Y, O)) :
    pbT f (∑ a, u a * v a) V = ∑ a, pbT f (u a) V * pbT f (v a) V := by
  rw [pbT_eq_appLE_hom f h, map_sum]
  simp only [map_mul]
  simp only [← pbT_eq_appLE_hom f h]
private lemma rsT_sum_rsT_mul_pbT_inf {Y₁ Y₂ : Scheme.{0}} {n : ℕ} (y : Y₁ ⟶ Y₂) {O Q V : Y₁.Opens} {A : Y₂.Opens}
    (hQ : Q ≤ O) (hV : V ≤ y ⁻¹ᵁ A) (c : Fin n → Γ(Y₁, O)) (e : Fin n → Γ(Y₂, A)) :
    rsT (∑ a, rsT (c a) (O ⊓ V) * pbT y (e a) (O ⊓ V)) (Q ⊓ V) = ∑ a, rsT (c a) (Q ⊓ V) * pbT y (e a) (Q ⊓ V) := by
  rw [rsT_sum_mul (inf_le_inf_right V hQ)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [rsT_rsT_of_le _ inf_le_left (inf_le_inf_right V hQ), rsT_pbT_of_le_preimage y _ (inf_le_right.trans hV) (inf_le_inf_right V hQ)]
private lemma sum_mul_sum_eq_sum_sum_mul_mul {A : Type} [CommRing A] {n : ℕ} (t : Fin n → A) (C : Fin n → Fin n → A) (P : Fin n → A) :
    ∑ a, t a * ∑ b, C b a * P b = ∑ b, (∑ a, C b a * t a) * P b := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
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
    (hb : IsBasis q p m dd) {I : Type} {W : I → X.Opens} {D : R → K}
    {d : I → ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O)} {θ : Fin g → C1 (fun i => m ⁻¹ᵁ W i)}
    (hc : KSCoc q p m D W dd d θ)
    (f : X ⟶ X) (f₀ : Y ⟶ Y) (hp : f ≫ p = p) (hq : f₀ ≫ q = q) (hm : f₀ ≫ m = m ≫ f) (F : Matrix (Fin g) (Fin g) K)
    (hres : ∀ a O O' (s : Γ(Y, O)), O' ≤ O → dd a O' (rsT s O') = rsT (dd a O s) O')
    (hend : ∀ j (O : Y.Opens) (s : Γ(Y, O)), dd j (f₀ ⁻¹ᵁ O) ((f₀.app O).hom s) =
      ∑ a, constFn q _ (F a j) * (f₀.app O).hom (dd a O s)) (x : Fin g) :
    Cohom f₀ _ (lc q (F x) θ) (θ x) := by
  have hmW : ∀ W' : X.Opens, f₀ ⁻¹ᵁ m ⁻¹ᵁ W' = m ⁻¹ᵁ f ⁻¹ᵁ W' := fun W' => by
    rw [← Scheme.Hom.comp_preimage, hm]
    rfl
  have hVi : ∀ i k W', m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W' ≤ m ⁻¹ᵁ (W i ⊓ f ⁻¹ᵁ W') := by
    intro i k W'
    rw [Scheme.Hom.preimage_inf, ← hmW]
    exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hex : ∀ i k, ∃ c : Fin g → Γ(Y, m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k), ∀ W', W' ≤ W k → ∀ h : Γ(X, W'),
      rsT (d i (W i ⊓ f ⁻¹ᵁ W') (pbT f h (W i ⊓ f ⁻¹ᵁ W'))) (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') -
        pbT f₀ (d k W' h) (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') =
      ∑ a, rsT (c a) (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') *
        pbT f₀ (dd a (m ⁻¹ᵁ W') ((m.app W').hom h)) (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') := by
    intro i k
    have ht : ⊤ ≤ (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k).ι ⁻¹ᵁ m ⁻¹ᵁ W i := by
      rw [← Scheme.Opens.ι_preimage_self (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k)]
      exact Scheme.Hom.preimage_mono _ inf_le_left
    have hD := locDer_diff (hc.der i) (hc.der k) f f₀ hp hq hm _ ht
    refine comb_exists hb f₀ _ (W k) inf_le_right
      (fun W' h => rsT (d i (W i ⊓ f ⁻¹ᵁ W') (pbT f h (W i ⊓ f ⁻¹ᵁ W'))) _ - pbT f₀ (d k W' h) _) ?_
    convert hD using 1
    funext W' h
    have hL := le_of_eq (pre_ι_eq (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k) f₀ m W')
    rw [pbT_sub', pbT_rsT_of_le_of_le_preimage _ _ hL (hVi i k W'), pbT_pbT _ f₀ inf_le_right hL]
  choose c hc' using hex
  have hE : ∀ i k (Q : Y.Opens), Q ≤ m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k → ∀ W', W' ≤ W k → ∀ h : Γ(X, W'),
      ∑ a, rsT (c i k a) (Q ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') * pbT f₀ (dd a (m ⁻¹ᵁ W') ((m.app W').hom h)) (Q ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') =
      rsT (d i (W i ⊓ f ⁻¹ᵁ W') (pbT f h (W i ⊓ f ⁻¹ᵁ W'))) (Q ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') -
        pbT f₀ (d k W' h) (Q ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') := by
    intro i k Q hQ W' hW' h
    have e := rsT_sum_rsT_mul_pbT_inf f₀ hQ (le_refl (f₀ ⁻¹ᵁ m ⁻¹ᵁ W')) (c i k) (fun a => dd a (m ⁻¹ᵁ W') ((m.app W').hom h))
    rw [← hc' i k W' hW' h] at e
    rw [← e, rsT_sub_moduli', rsT_rsT_of_le _ (hVi i k W') (inf_le_inf_right _ hQ),
      rsT_pbT_of_le_preimage f₀ _ inf_le_right (inf_le_inf_right _ hQ)]
  refine ⟨fun i k => c i k x, fun i i' k => ?_, fun i k k' => ?_⟩
  · have hQ : m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ≤ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k := inf_le_right
    have hQi : m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ≤ m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hQi' : m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ≤ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k :=
      le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have key := comb_unique hb f₀ _ (W k) hQ
      (fun a => rsT (c i' k a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k) -
        rsT (c i k a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k))
      (fun a => rsT (lc q (F a) θ i i') (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k)) ?_
    · exact congrFun key x
    intro W' hW' h
    have hQ' : m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W' ≤ m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k :=
      inf_le_left
    have hQc : m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W' ≤ m ⁻¹ᵁ (W i ⊓ W i' ⊓ f ⁻¹ᵁ W') := by
      rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, ← hmW]
      exact le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
        (inf_le_left.trans (inf_le_left.trans inf_le_right))) inf_le_right
    have hQf : m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W' ≤ f₀ ⁻¹ᵁ m ⁻¹ᵁ W' := inf_le_right
    have hOcf : m ⁻¹ᵁ (W i ⊓ W i' ⊓ f ⁻¹ᵁ W') ≤ f₀ ⁻¹ᵁ m ⁻¹ᵁ W' := by
      rw [hmW]
      exact Scheme.Hom.preimage_mono _ inf_le_right
    have hOθ : m ⁻¹ᵁ (W i ⊓ W i' ⊓ f ⁻¹ᵁ W') ≤ m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' := Scheme.Hom.preimage_mono _ inf_le_left
    have EA : ∀ j, W i ⊓ W i' ⊓ f ⁻¹ᵁ W' ≤ W j ⊓ f ⁻¹ᵁ W' →
        rsT (d j (W j ⊓ f ⁻¹ᵁ W') (pbT f h (W j ⊓ f ⁻¹ᵁ W'))) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') =
        rsT (d j (W i ⊓ W i' ⊓ f ⁻¹ᵁ W') (pbT f h (W i ⊓ W i' ⊓ f ⁻¹ᵁ W'))) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') := by
      intro j hj
      rw [← rsT_rsT_of_le _ (Scheme.Hom.preimage_mono _ hj) hQc, ← (hc.der j).res _ _ hj inf_le_left, resG_eq,
        rsT_pbT_of_le_preimage f h inf_le_right hj]
    have Eu : (m.app (W i ⊓ W i' ⊓ f ⁻¹ᵁ W')).hom (pbT f h (W i ⊓ W i' ⊓ f ⁻¹ᵁ W')) =
        rsT ((f₀.app (m ⁻¹ᵁ W')).hom ((m.app W').hom h)) (m ⁻¹ᵁ (W i ⊓ W i' ⊓ f ⁻¹ᵁ W')) := by
      rw [app_eq m (pbT f h _), app_eq m h, app_eq f₀, pbT_pbT f₀ m le_rfl le_rfl,
        rsT_pbT_of_le_preimage (f₀ ≫ m) h (le_rfl : f₀ ⁻¹ᵁ m ⁻¹ᵁ W' ≤ (f₀ ≫ m) ⁻¹ᵁ W') hOcf,
        pbT_pbT m f inf_le_right le_rfl]
      exact pbT_congr hm.symm _ _
    have Edd : ∀ a, rsT (dd a (m ⁻¹ᵁ (W i ⊓ W i' ⊓ f ⁻¹ᵁ W')) ((m.app (W i ⊓ W i' ⊓ f ⁻¹ᵁ W')).hom
        (pbT f h (W i ⊓ W i' ⊓ f ⁻¹ᵁ W')))) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') =
        ∑ b, constFn q (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') (F b a) *
          pbT f₀ (dd b (m ⁻¹ᵁ W') ((m.app W').hom h)) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') := by
      intro a
      rw [Eu, hres a _ _ _ hOcf, rsT_rsT_of_le _ hOcf hQc, hend a (m ⁻¹ᵁ W') ((m.app W').hom h), rsT_sum_mul hQf]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [rsT_constFn_of_le _ hQf, app_eq f₀, rsT_pbT_of_le_preimage f₀ _ le_rfl hQf]
    simp only [rsT_sub_moduli', rsT_rsT_of_le _ hQi hQ', rsT_rsT_of_le _ hQi' hQ', sub_mul, Finset.sum_sub_distrib]
    rw [hE i' k _ hQi' W' hW' h, hE i k _ hQi W' hW' h, sub_sub_sub_cancel_right,
      EA i (le_inf (inf_le_left.trans inf_le_left) inf_le_right), EA i' (le_inf (inf_le_left.trans inf_le_right) inf_le_right),
      ← rsT_sub_moduli', hc.diff i i' _ inf_le_left, rsT_sum_mul hQc]
    have Elc : ∀ b, rsT (rsT (lc q (F b) θ i i') (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k)) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') =
        ∑ a, constFn q (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') (F b a) * rsT (θ a i i') (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') := by
      intro b
      rw [rsT_rsT_of_le _ inf_le_left hQ']
      exact (rsT_sum_mul (hQ'.trans inf_le_left) (fun a => constFn q _ (F b a)) (fun a => θ a i i')).trans
        (Finset.sum_congr rfl (fun a _ => by rw [rsT_constFn_of_le _ (hQ'.trans inf_le_left)]))
    refine (Finset.sum_congr rfl (fun a _ => ?_)).trans ((sum_mul_sum_eq_sum_sum_mul_mul (fun a => rsT (θ a i i') (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W'))
      (fun b a => constFn q (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') (F b a))
      (fun b => pbT f₀ (dd b (m ⁻¹ᵁ W') ((m.app W').hom h)) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W'))).trans
      (Finset.sum_congr rfl (fun b _ => ?_)))
    · rw [rsT_rsT_of_le _ hOθ hQc, Edd a]
    · rw [Elc b]
  · have hR : m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k' ≤ f₀ ⁻¹ᵁ m ⁻¹ᵁ (W k ⊓ W k') := by
      rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf]
      exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hRk : m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k' ≤ m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k := inf_le_left
    have hRk' : m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k' ≤ m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k' :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hRθ : m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k' ≤ f₀ ⁻¹ᵁ (m ⁻¹ᵁ W k ⊓ m ⁻¹ᵁ W k') := by
      rw [Scheme.Hom.preimage_inf]
      exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have key := comb_unique hb f₀ _ (W k ⊓ W k') hR
      (fun a => rsT (c i k a) (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k') -
        rsT (c i k' a) (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k'))
      (fun a => pbT f₀ (θ a k k') (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k')) ?_
    · exact congrFun key x
    intro W' hW' h
    have hR' : m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W' ≤
        m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k' := inf_le_left
    have hRf : m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W' ≤ f₀ ⁻¹ᵁ m ⁻¹ᵁ W' := inf_le_right
    have hWθ : m ⁻¹ᵁ W' ≤ m ⁻¹ᵁ W k ⊓ m ⁻¹ᵁ W k' := Scheme.Hom.preimage_mono _ hW'
    simp only [rsT_sub_moduli', rsT_rsT_of_le _ hRk hR', rsT_rsT_of_le _ hRk' hR', sub_mul, Finset.sum_sub_distrib]
    rw [hE i k _ hRk W' (hW'.trans inf_le_left) h, hE i k' _ hRk' W' (hW'.trans inf_le_right) h,
      sub_sub_sub_cancel_left, ← pbT_sub', hc.diff k k' W' hW', pbT_sum_mul f₀ hRf]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [pbT_rsT_of_le_of_le_preimage _ _ hRf hWθ, rsT_pbT_of_le_preimage f₀ _ hRθ hR']
end GlobalTheory.KS.EndClass
