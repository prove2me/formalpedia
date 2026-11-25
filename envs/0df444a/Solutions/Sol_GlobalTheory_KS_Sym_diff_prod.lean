-- Prove2me | solution 1 for GlobalTheory.KS.Sym.diff_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:49.909359+00:00
-- url     : https://prove2.me/submissions/56f2baed-1066-4fa8-8523-b6eb859c25f1

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
import Theorems.Thm_GlobalTheory_KS_Sym_compat_of_affine
import Theorems.Thm_GlobalTheory_KS_Sym_LocDerK_mono
import Theorems.Thm_GlobalTheory_KS_Sym_LocDerK_add_field
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
private lemma pbT_add_moduli (f : Z ⟶ Y) {O₀ : Y.Opens} (a b : Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (a + b) O = pbT f a O + pbT f b O := by
  unfold pbT
  split_ifs <;> simp
private lemma rsT_self' {O₀ : Z.Opens} (s : Γ(Z, O₀)) : rsT s O₀ = s := by
  unfold rsT
  rw [dif_pos le_rfl]
  show (Z.presheaf.map (𝟙 (Opposite.op O₀))).hom s = s
  rw [CategoryTheory.Functor.map_id]
  rfl
private lemma pbT_sum' {κ : Type} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Finset κ) (F : κ → Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (∑ i ∈ s, F i) O = ∑ i ∈ s, pbT f (F i) O := by
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
theorem _root_.solution {g : ℕ} (x₀ : R →+* K) {q : Y ⟶ Sp K} {s : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K}
    {W W' W'' : X.Opens} {d d' e : ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O)} (hd : LocDerK q s m D W d)
    (hd' : LocDerK q s m D W' d') (he : LocDerK q s m D W'' e) (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
    (hW'' : IsAffineOpen W'')
    {q₂ : Z ⟶ Sp K} {s₂ : X₂ ⟶ Sp R} {m₂ : Z ⟶ X₂} (sq₂ : m₂ ≫ s₂ = q₂ ≫ spMap x₀) {Q Q' Q₀ : X₂.Opens}
    {d₂ d₂' : ∀ O : X₂.Opens, Γ(X₂, O) → Γ(Z, m₂ ⁻¹ᵁ O)} (hd₂ : LocDerK q₂ s₂ m₂ D Q d₂)
    (hd₂' : LocDerK q₂ s₂ m₂ D Q' d₂') {π π' : X₂ ⟶ X} {p p' : Z ⟶ Y}
    (sq : m₂ ≫ π = p ≫ m) (sq' : m₂ ≫ π' = p' ≫ m) (hQ : Q ≤ π ⁻¹ᵁ W) (hQ' : Q' ≤ π ⁻¹ᵁ W')
    (kQ : Q ≤ π' ⁻¹ᵁ W'') (kQ' : Q' ≤ π' ⁻¹ᵁ W'') (l : Q₀ ≤ Q) (l' : Q₀ ≤ Q')
    (c₁ : ∀ f : Γ(X, W), d₂ Q (pbT π f Q) = pbT p (d W f) _)
    (c₂ : ∀ f : Γ(X, W''), d₂ Q (pbT π' f Q) = pbT p' (e W'' f) _)
    (c₁' : ∀ f : Γ(X, W'), d₂' Q' (pbT π f Q') = pbT p (d' W' f) _)
    (c₂' : ∀ f : Γ(X, W''), d₂' Q' (pbT π' f Q') = pbT p' (e W'' f) _)
    (uniq : ∀ a b, LocDerK q₂ s₂ m₂ D Q₀ a → LocDerK q₂ s₂ m₂ D Q₀ b →
      (∀ f : Γ(X, W ⊓ W'), a Q₀ (pbT π f Q₀) = b Q₀ (pbT π f Q₀)) →
      (∀ f : Γ(X, W''), a Q₀ (pbT π' f Q₀) = b Q₀ (pbT π' f Q₀)) → ∀ O, O ≤ Q₀ → a O = b O)
    (θ : Fin g → Γ(Y, m ⁻¹ᵁ W ⊓ m ⁻¹ᵁ W')) {dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)}
    (hθ : ∀ f : Γ(X, W ⊓ W'), d' _ f - d _ f = ∑ a, rsT (θ a) _ * dd a _ ((m.app _).hom f))
    {w : Fin g → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (hw : ∀ a, IsVF q₂ (w a))
    (w₁ : ∀ a (V : Y.Opens) (h : Γ(Y, V)) O, O ≤ p ⁻¹ᵁ V → w a O (pbT p h O) = pbT p (dd a V h) O)
    (w₂ : ∀ a (V : Y.Opens) (h : Γ(Y, V)) O, O ≤ p' ⁻¹ᵁ V → w a O (pbT p' h O) = 0)
    (O : X₂.Opens) (hO : O ≤ Q₀) (f : Γ(X₂, O)) :
    d₂' O f - d₂ O f = ∑ a, pbT p (θ a) _ * w a _ (pbT m₂ f _) := by
  have key : ∀ x, π.base (m₂.base x) = m.base (p.base x) := fun x => by
    simpa using congrArg (fun φ : Z ⟶ X => φ.base x) sq
  have key' : ∀ x, π'.base (m₂.base x) = m.base (p'.base x) := fun x => by
    simpa using congrArg (fun φ : Z ⟶ X => φ.base x) sq'
  have hpe : m₂ ⁻¹ᵁ Q₀ ≤ p ⁻¹ᵁ m ⁻¹ᵁ (W ⊓ W') := fun x hx => by
    have b1 : π.base (m₂.base x) ∈ W := hQ (l hx)
    have b2 : π.base (m₂.base x) ∈ W' := hQ' (l' hx)
    rw [key] at b1 b2
    exact ⟨b1, b2⟩
  have hpe' : m₂ ⁻¹ᵁ Q₀ ≤ p' ⁻¹ᵁ m ⁻¹ᵁ W'' := fun x hx => by
    have b1 : π'.base (m₂.base x) ∈ W'' := kQ (l hx)
    rw [key'] at b1
    exact b1
  have hQ₀ : Q₀ ≤ π ⁻¹ᵁ (W ⊓ W') := fun x hx => ⟨hQ (l hx), hQ' (l' hx)⟩
  have hb := LocDerK_add_field x₀ sq₂ (LocDerK_mono hd₂ l) (fun a => pbT p (θ a) (m₂ ⁻¹ᵁ Q₀)) hw
  have agree1 : ∀ f : Γ(X, W ⊓ W'), d₂' Q₀ (pbT π f Q₀) = d₂ Q₀ (pbT π f Q₀) +
      ∑ a, rsT (pbT p (θ a) (m₂ ⁻¹ᵁ Q₀)) (m₂ ⁻¹ᵁ Q₀) * w a (m₂ ⁻¹ᵁ Q₀) (pbT m₂ (pbT π f Q₀) (m₂ ⁻¹ᵁ Q₀)) := by
    intro f
    rw [compat_of_affine hd' hW' hd₂' sq hQ' c₁' inf_le_right f l' hQ₀,
      compat_of_affine hd hW hd₂ sq hQ c₁ inf_le_left f l hQ₀,
      pbT_pbT m₂ π hQ₀ le_rfl, sq, ← pbT_pbT p m (O₁ := m ⁻¹ᵁ (W ⊓ W')) (fun x hx => hx) hpe]
    simp only [w₁ _ _ _ _ hpe, rsT_self']
    have hθf := hθ f
    rw [sub_eq_iff_eq_add'] at hθf
    rw [hθf, pbT_add_moduli, pbT_sum']
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [pbT_mul_moduli, app_eq_pbT, pbT_rsT_of_le_of_le_preimage' p (θ a) (O₁ := m ⁻¹ᵁ (W ⊓ W')) (fun x hx => hx) hpe]
  have agree2 : ∀ f : Γ(X, W''), d₂' Q₀ (pbT π' f Q₀) = d₂ Q₀ (pbT π' f Q₀) +
      ∑ a, rsT (pbT p (θ a) (m₂ ⁻¹ᵁ Q₀)) (m₂ ⁻¹ᵁ Q₀) * w a (m₂ ⁻¹ᵁ Q₀) (pbT m₂ (pbT π' f Q₀) (m₂ ⁻¹ᵁ Q₀)) := by
    intro f
    rw [compat_of_affine he hW'' hd₂' sq' kQ' c₂' le_rfl f l' (l'.trans kQ'),
      compat_of_affine he hW'' hd₂ sq' kQ c₂ le_rfl f l (l.trans kQ),
      pbT_pbT m₂ π' (l.trans kQ) le_rfl, sq', ← pbT_pbT p' m (O₁ := m ⁻¹ᵁ W'') (fun x hx => hx) hpe']
    simp only [w₂ _ _ _ _ hpe', mul_zero, Finset.sum_const_zero, add_zero]
  have hU := uniq d₂' (fun O f => d₂ O f + ∑ a, rsT (pbT p (θ a) (m₂ ⁻¹ᵁ Q₀)) (m₂ ⁻¹ᵁ O) *
      w a (m₂ ⁻¹ᵁ O) (pbT m₂ f (m₂ ⁻¹ᵁ O))) (LocDerK_mono hd₂' l') hb agree1 agree2 O hO
  have := congrFun hU f
  rw [this]
  beta_reduce
  rw [add_sub_cancel_left]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [rsT_pbT_of_le_of_le_preimage p (θ a) (fun x hx => hO hx) hpe]
end GlobalTheory.KS.Sym
