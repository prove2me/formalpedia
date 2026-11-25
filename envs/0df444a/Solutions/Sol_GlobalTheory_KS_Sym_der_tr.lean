-- Prove2me | solution 1 for GlobalTheory.KS.Sym.der_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:16:56.104799+00:00
-- url     : https://prove2.me/submissions/0fa6c978-863f-4cfb-8cb1-cd609bf0b32e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstFnCompSpMap
import Theorems.Thm_GlobalTheory_KS_Sym_app_eq_pbT
import Theorems.Thm_GlobalTheory_KS_Sym_pbT_pbT
import Theorems.Thm_GlobalTheory_KS_Sym_tr_eq
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
namespace GlobalTheory.KS.Sym
variable {X X₂ Y Z : Scheme.{0}}
private lemma rsT_pbT_of_le_of_le_preimage (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) {O O' : Z.Opens} (h : O' ≤ O)
    (e : O ≤ f ⁻¹ᵁ O₀) : rsT (pbT f s O) O' = pbT f s O' := by
  unfold rsT pbT
  rw [dif_pos h, dif_pos e, dif_pos (h.trans e)]
  dsimp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
private lemma pbT_rsT_of_le_of_le_preimage' (f : Z ⟶ Y) {O₀ O₁ : Y.Opens} (s : Γ(Y, O₀)) (h : O₁ ≤ O₀) {O : Z.Opens}
    (e : O ≤ f ⁻¹ᵁ O₁) : pbT f (rsT s O₁) O = pbT f s O := by
  unfold rsT pbT
  rw [dif_pos h, dif_pos e, dif_pos (e.trans (fun x hx => h hx))]
  dsimp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
private lemma pbT_mul_moduli (f : Z ⟶ Y) {O₀ : Y.Opens} (a b : Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (a * b) O = pbT f a O * pbT f b O := by
  unfold pbT
  split_ifs <;> simp
private lemma pbT_app_pbT_eq_pbT_comp (p : Z ⟶ Y) (m : Y ⟶ X₂) (π : X₂ ⟶ X) {O : X.Opens} {V : X₂.Opens}
    (hV : V ≤ π ⁻¹ᵁ O) (f : Γ(X, O)) {O' : Z.Opens} (hO' : O' ≤ p ⁻¹ᵁ m ⁻¹ᵁ V) :
    pbT p ((m.app V).hom (pbT π f V)) O' = pbT (p ≫ m ≫ π) f O' := by
  rw [app_eq_pbT, pbT_pbT m π hV le_rfl f, pbT_pbT p (m ≫ π) (fun x hx => hV hx) hO' f]
private lemma pbT_add_moduli (f : Z ⟶ Y) {O₀ : Y.Opens} (a b : Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (a + b) O = pbT f a O + pbT f b O := by
  unfold pbT
  split_ifs <;> simp
variable {K R : Type} [Field K] [CommRing R]
end GlobalTheory.KS.Sym
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Sym
variable {X X₂ Y Z : Scheme.{0}}
variable {K R : Type} [Field K] [CommRing R]
namespace GlobalTheory.KS.Sym
theorem _root_.solution {q : Y ⟶ Sp K} {s : X₂ ⟶ Sp R} {m : Y ⟶ X₂} {D : R → K} {W : X₂.Opens}
    {d : ∀ O : X₂.Opens, Γ(X₂, O) → Γ(Y, m ⁻¹ᵁ O)} (hd : LocDerK q s m D W d) (p : Z ⟶ Y) (π : X₂ ⟶ X)
    {h : Z ⟶ X} (hh : h = p ≫ m ≫ π) {T : Z.Opens} (hT : T ≤ p ⁻¹ᵁ m ⁻¹ᵁ W) : Der h T (tr p m π W d) := by
  subst hh
  unfold Der
  refine ⟨fun O f f' O' h₁ h₂ => ?_, fun O O₁ f O' h₀ h₁ h₂ => ?_, fun O f O' O'' h₀ h₁ h₂ => ?_⟩
  · have hb : O' ≤ p ⁻¹ᵁ m ⁻¹ᵁ (π ⁻¹ᵁ O ⊓ W) := fun x hx => ⟨h₂ hx, hT (h₁ hx)⟩
    unfold tr
    rw [pbT_mul_moduli π, hd.mul _ inf_le_right, pbT_add_moduli, pbT_mul_moduli p, pbT_mul_moduli p,
      pbT_app_pbT_eq_pbT_comp p m π inf_le_left f hb, pbT_app_pbT_eq_pbT_comp p m π inf_le_left f' hb]
  · have hb : O' ≤ p ⁻¹ᵁ m ⁻¹ᵁ (π ⁻¹ᵁ O₁ ⊓ W) := fun x hx => ⟨h₂ hx, hT (h₁ hx)⟩
    rw [tr_eq hd p π f (O₃ := π ⁻¹ᵁ O₁ ⊓ W) (fun x hx => h₀ hx.1) inf_le_right hb]
    unfold tr
    rw [pbT_rsT_of_le_of_le_preimage' π f h₀ inf_le_left]
  · have hb : O' ≤ p ⁻¹ᵁ m ⁻¹ᵁ (π ⁻¹ᵁ O ⊓ W) := fun x hx => ⟨h₂ hx, hT (h₁ hx)⟩
    unfold tr
    rw [rsT_pbT_of_le_of_le_preimage p _ h₀ hb]
end GlobalTheory.KS.Sym
