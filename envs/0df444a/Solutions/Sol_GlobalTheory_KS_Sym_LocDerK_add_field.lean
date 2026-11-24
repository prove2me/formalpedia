-- Prove2me | solution 1 for GlobalTheory.KS.Sym.LocDerK_add_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:49:00.650247+00:00
-- url     : https://prove2.me/submissions/93cbdaaf-7ddf-4764-85c7-9201f005e76e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstFnCompSpMap
import Theorems.Thm_GlobalTheory_KS_Sym_app_eq_pbT
import Theorems.Thm_GlobalTheory_KS_Sym_constFn_comp_spMap
import Theorems.Thm_GlobalTheory_KS_IsCob_add

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
private lemma rsT_mul_moduli {O₀ : Z.Opens} (a b : Γ(Z, O₀)) (O : Z.Opens) :
    rsT (a * b) O = rsT a O * rsT b O := by
  unfold rsT
  split_ifs <;> simp
private lemma rsT_eq_resG_of_le_moduli {O₀ O : Z.Opens} (s : Γ(Z, O₀)) (h : O ≤ O₀) : rsT s O = resG Z h s := by
  unfold rsT
  rw [dif_pos h]
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
private lemma pbT_add_moduli (f : Z ⟶ Y) {O₀ : Y.Opens} (a b : Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (a + b) O = pbT f a O + pbT f b O := by
  unfold pbT
  split_ifs <;> simp
private lemma rsT_rsT_of_le_of_le {O₀ A B : Z.Opens} (s : Γ(Z, O₀)) (hB : B ≤ A) (hA : A ≤ O₀) :
    rsT (rsT s A) B = rsT s B := by
  unfold rsT
  rw [dif_pos hB, dif_pos hA, dif_pos (hB.trans hA)]
  dsimp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
private lemma rsT_add_moduli {O₀ : Z.Opens} (a b : Γ(Z, O₀)) (O : Z.Opens) :
    rsT (a + b) O = rsT a O + rsT b O := by
  unfold rsT
  split_ifs <;> simp
private lemma rsT_sum_moduli {κ : Type} {O₀ : Z.Opens} (s : Finset κ) (F : κ → Γ(Z, O₀)) (O : Z.Opens) :
    rsT (∑ i ∈ s, F i) O = ∑ i ∈ s, rsT (F i) O := by
  unfold rsT
  split_ifs <;> simp
private lemma pbT_constFn_preimage {R : Type} [CommRing R] (m : Z ⟶ Y) (s : Y ⟶ Sp R) (V : Y.Opens) (r : R) :
    pbT m (constFn s V r) (m ⁻¹ᵁ V) = constFn (m ≫ s) (m ⁻¹ᵁ V) r := by
  unfold pbT constFn
  rw [dif_pos le_rfl, ← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_comp_appLE]
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
theorem _root_.solution {g : ℕ} (x₀ : R →+* K) {q : Y ⟶ Sp K} {s : X ⟶ Sp R} {m : Y ⟶ X}
    (sq : m ≫ s = q ≫ spMap x₀) {D : R → K} {W : X.Opens}
    {d : ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O)} (hd : LocDerK q s m D W d) (t : Fin g → Γ(Y, m ⁻¹ᵁ W))
    {w : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)} (hw : ∀ a, IsVF q (w a)) :
    LocDerK q s m D W (fun O f => d O f + ∑ a, rsT (t a) _ * w a _ (pbT m f _)) := by
  have hv1 : ∀ a V (f f' : Γ(Y, V)), w a V (f + f') = w a V f + w a V f' := fun a => (hw a).1
  have hv2 : ∀ a V (f f' : Γ(Y, V)), w a V (f * f') = f * w a V f' + f' * w a V f := fun a => (hw a).2.1
  have hv3 : ∀ a V V' (f : Γ(Y, V)), V' ≤ V → w a V' (rsT f V') = rsT (w a V f) V' := fun a => (hw a).2.2.1
  have hv4 : ∀ a V c, w a V (constFn q V c) = 0 := fun a => (hw a).2.2.2
  refine ⟨fun V hV f f' => ?_, fun V hV f f' => ?_, fun V V' e hV f => ?_, fun V hV r => ?_⟩
  · rw [hd.add V hV, pbT_add_moduli]
    simp only [hv1, mul_add, Finset.sum_add_distrib]
    ring
  · rw [hd.mul V hV, pbT_mul_moduli, app_eq_pbT, app_eq_pbT]
    simp only [hv2, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    ring_nf
  · have e' : m ⁻¹ᵁ V' ≤ m ⁻¹ᵁ V := fun x hx => e hx
    have hVW : m ⁻¹ᵁ V ≤ m ⁻¹ᵁ W := fun x hx => hV hx
    rw [hd.res V V' e hV f, ← rsT_eq_resG_of_le_moduli f e, pbT_rsT_of_le_of_le_preimage' m f e le_rfl, ← rsT_pbT_of_le_of_le_preimage m f e' le_rfl,
      rsT_add_moduli, rsT_sum_moduli]
    simp only [hv3 _ _ _ _ e', rsT_mul_moduli, rsT_rsT_of_le_of_le _ e' hVW]
  · rw [hd.base V hV, pbT_constFn_preimage, sq, constFn_comp_spMap]
    simp only [hv4, mul_zero, Finset.sum_const_zero, add_zero]
end GlobalTheory.KS.Sym
