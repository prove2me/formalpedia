-- Prove2me | solution 1 for GlobalTheory.exists_BX_of_factorSystems
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:41:11.784849+00:00
-- url     : https://prove2.me/submissions/49918af1-a229-4a51-a914-b557fdaa2f2c

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsBXOfFactorSystems
import Theorems.Thm_ReciprocityTheory_PGsh_a1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
section GroupIdentities
variable {M : Type} [CommGroup M]
private lemma mul_rearrange_five {u u' u'' a b c d : M} (h : b * a = d * c) :
    u * u' * a * u'' * b = u * (u' * u'' * c) * d := by
  calc _ = u * u' * u'' * (b * a) := by ac_rfl
    _ = u * u' * u'' * (d * c) := by rw [h]
    _ = _ := by ac_rfl
private lemma fs_zero {u a b : M} (h : b * a = b * b) : a⁻¹ * u * b = u := by
  rw [← mul_left_cancel h, mul_right_comm, inv_mul_cancel, _root_.one_mul]
private lemma fs_inter {u u' w w' a b c d e f : M} (h : a * b * c = d * e * f) :
    u * u' * e * (w * w' * f) * d = u * w * b * (u' * w' * c) * a := by
  calc _ = u * u' * w * w' * (d * e * f) := by ac_rfl
    _ = u * u' * w * w' * (a * b * c) := by rw [h]
    _ = _ := by ac_rfl
private lemma fs_nat {u u' a b c d e : M} (h : a * b = c * d * e) :
    u * u' * a * b = u * c * (u' * d) * e := by
  calc _ = u * u' * (a * b) := by ac_rfl
    _ = u * u' * (c * d * e) := by rw [h]
    _ = _ := by ac_rfl
private lemma fs_zero_nat {a b c : M} (h : a * b = b * b * c) : a⁻¹ * b = c⁻¹ := by
  have h' : a = b * c := by
    apply mul_right_cancel (b := b)
    rw [h]; ac_rfl
  rw [h', mul_inv, mul_right_comm, inv_mul_cancel, _root_.one_mul]
end GroupIdentities
private lemma fs_sigma_eq {A U : Type} {x x' y y' : A} {u u' : U} :
    (⟨x, y, u⟩ : Σ _ : A, Σ _ : A, U) = ⟨x', y', u'⟩ ↔ x = x' ∧ y = y' ∧ u = u' := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl
private lemma fs_units_fibre {R₀ : Type} [CommRing R₀] {F R₁ R₂ R : LAlg R₀} {p₁ : LHom F R₁}
    {p₂ : LHom F R₂} {f₁ : LHom R₁ R} {f₂ : LHom R₂ R} (h : IsFibreSq p₁ p₂ f₁ f₂)
    (a : (R₁ : Type)ˣ) (b : (R₂ : Type)ˣ)
    (hab : Units.map (f₁.1 : (R₁ : Type) →* (R : Type)) a =
      Units.map (f₂.1 : (R₂ : Type) →* (R : Type)) b) :
    ∃! c : (F : Type)ˣ, Units.map (p₁.1 : (F : Type) →* (R₁ : Type)) c = a ∧
      Units.map (p₂.1 : (F : Type) →* (R₂ : Type)) c = b := by
  obtain ⟨c, ⟨h1, h2⟩, hu⟩ := h.2.2.2 (a : R₁.carrier) (b : R₂.carrier) (congrArg Units.val hab)
  have hc : IsUnit c := p₁.2.map_nonunit c (by
    have : (p₁.1 : F.carrier →+* R₁.carrier) c = a := h1
    rw [this]; exact a.isUnit)
  refine ⟨hc.unit, ⟨Units.ext h1, Units.ext h2⟩, ?_⟩
  rintro c' ⟨e1, e2⟩
  exact Units.ext (hu c' ⟨congrArg Units.val e1, congrArg Units.val e2⟩)
end GlobalTheory
end

set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] (B₀ : BX R₀) (δ : ∀ {R S : LAlg R₀}, LHom R S → B₀.G R → B₀.G R → (S : Type)ˣ)
    (t₁ t₂ : ∀ R : LAlg R₀, B₀.G R → B₀.G R → B₀.G R → (R : Type)ˣ) (w : ∀ R : LAlg R₀, B₀.G R → B₀.G R → (R : Type)ˣ),
    (∀ R x y, δ (LHom.id R) x y = 1) →
    (∀ {Q R S : LAlg R₀} (f : LHom Q R) (h : LHom R S) x y, δ (h.comp f) x y = Units.map (h.1 : (R : Type) →* (S : Type)) (δ f x y) * δ h (B₀.map f x) (B₀.map f y)) →
    (∀ R x x' x'' y, t₁ R (x + x') x'' y * t₁ R x x' y = t₁ R x (x' + x'') y * t₁ R x' x'' y) → (∀ R x x' y, t₁ R x x' y = t₁ R x' x y) →
    (∀ R x y y' y'', t₂ R x (y + y') y'' * t₂ R x y y' = t₂ R x y (y' + y'') * t₂ R x y' y'') → (∀ R x y y', t₂ R x y y' = t₂ R x y' y) →
    (∀ R x x' y y', t₁ R x x' (y + y') * t₂ R x y y' * t₂ R x' y y' = t₂ R (x + x') y y' * t₁ R x x' y * t₁ R x x' y') →
    (∀ {R S : LAlg R₀} (f : LHom R S) x x' y, Units.map (f.1 : (R : Type) →* (S : Type)) (t₁ R x x' y) * δ f (x + x') y =
      δ f x y * δ f x' y * t₁ S (B₀.map f x) (B₀.map f x') (B₀.map f y)) →
    (∀ {R S : LAlg R₀} (f : LHom R S) x y y', Units.map (f.1 : (R : Type) →* (S : Type)) (t₂ R x y y') * δ f x (y + y') =
      δ f x y * δ f x y' * t₂ S (B₀.map f x) (B₀.map f y) (B₀.map f y')) →
    (∀ R x y, w R x y * w R y x = 1) → (∀ R x x' y, t₁ R x x' y * w R (x + x') y = w R x y * w R x' y * t₂ R y x x') →
    (∀ {R S : LAlg R₀} (f : LHom R S) x y, Units.map (f.1 : (R : Type) →* (S : Type)) (w R x y) * δ f y x = δ f x y * w S (B₀.map f x) (B₀.map f y)) →
    ∃ (B : BX R₀) (κ : ∀ R, B.G R ≃+ B₀.G R) (b : ∀ R x y, B.P R x y),
      (∀ {R S : LAlg R₀} (f : LHom R S) x, κ S (B.map f x) = B₀.map f (κ R x)) ∧
      (∀ R x x' y, B.add1 (b R x y) (b R x' y) = B.smul (t₁ R (κ R x) (κ R x') (κ R y)) (b R (x + x') y)) ∧
      (∀ R x y y', B.add2 (b R x y) (b R x y') = B.smul (t₂ R (κ R x) (κ R y) (κ R y')) (b R x (y + y'))) ∧
      (∀ {R S : LAlg R₀} (f : LHom R S) x y, B.pmap f (b R x y) = B.smul (δ f (κ R x) (κ R y)) (b S (B.map f x) (B.map f y)))) := by
  intro R₀ _ B₀ δ t₁ t₂ w hid hcomp h1a h1c h2a h2c hint h1n h2n hww hw1 hwn
  let B : BX R₀ :=
    { B₀ with
      P := fun R _ _ => (R : Type)ˣ
      smul := fun l u => l * u
      one_smul := fun u => _root_.one_mul u
      mul_smul := fun l l' u => _root_.mul_assoc l l' u
      nonempty := fun _ _ _ => ⟨1⟩
      trans := fun u v => ⟨v * u⁻¹, by simp, fun l hl => by rw [← hl]; simp⟩
      pmap := fun {R S} f {x y} u => Units.map (f.1 : (R : Type) →* (S : Type)) u * δ f x y
      pmap_smul := fun f _ _ l u => by rw [map_mul, _root_.mul_assoc]
      pmap_id := fun {R x y} u => heq_of_eq (by rw [hid, _root_.mul_one]; rfl)
      pmap_comp := fun f g _ _ u => heq_of_eq (by rw [hcomp, map_mul, ← _root_.mul_assoc]; rfl)
      add1 := fun {R x x' y} u u' => u * u' * t₁ R x x' y
      add2 := fun {R x y y'} u u' => u * u' * t₂ R x y y'
      zero1 := fun {R} y => (t₁ R 0 0 y)⁻¹
      zero2 := fun {R} x => (t₂ R x 0 0)⁻¹
      addFst_assoc := fun u u' u'' => heq_of_eq (mul_rearrange_five (h1a _ _ _ _ _))
      addSnd_assoc := fun u u' u'' => heq_of_eq (mul_rearrange_five (h2a _ _ _ _ _))
      addFst_comm := fun u u' => heq_of_eq (by rw [h1c, _root_.mul_comm u])
      addSnd_comm := fun u u' => heq_of_eq (by rw [h2c, _root_.mul_comm u])
      zeroFst_add := fun {R x y} u => heq_of_eq (fs_zero (by
        simpa only [add_zero, zero_add] using h1a R 0 0 x y))
      zeroSnd_add := fun {R x y} u => heq_of_eq (fs_zero (by
        simpa only [add_zero, zero_add] using h2a R x 0 0 y))
      addFst_smul := fun l l' u u' => by ac_rfl
      addSnd_smul := fun l l' u u' => by ac_rfl
      interchange := fun u u' v v' => fs_inter (hint _ _ _ _ _)
      addFst_nat := fun f _ _ _ u u' => heq_of_eq (by
        rw [map_mul, map_mul]; exact fs_nat (h1n _ _ _ _))
      addSnd_nat := fun f _ _ _ u u' => heq_of_eq (by
        rw [map_mul, map_mul]; exact fs_nat (h2n _ _ _ _))
      zeroFst_nat := fun f y => heq_of_eq (by
        rw [map_inv]
        exact fs_zero_nat (by simpa only [add_zero, map_zero] using h1n f 0 0 y))
      zeroSnd_nat := fun f x => heq_of_eq (by
        rw [map_inv]
        exact fs_zero_nat (by simpa only [add_zero, map_zero] using h2n f x 0 0))
      sw := fun {R x y} u => u * w R x y
      sw_smul := fun l u => _root_.mul_assoc _ _ _
      sw_nat := fun f _ _ u => by rw [map_mul, _root_.mul_assoc, _root_.mul_assoc, hwn]
      swap_addFst := fun u u' => fs_nat (hw1 _ _ _ _)
      sw_sw := fun u => by rw [_root_.mul_assoc, hww, _root_.mul_one]
      fibre_P := by
        intro F R₁ R₂ R p₁ p₂ f₁ f₂ h
        rintro ⟨x₁, y₁, u₁⟩ ⟨x₂, y₂, u₂⟩ e
        obtain ⟨ex, ey, eu⟩ := fs_sigma_eq.1 e
        obtain ⟨x, ⟨rfl, rfl⟩, hx⟩ := B₀.fibre_G p₁ p₂ f₁ f₂ h x₁ x₂ ex
        obtain ⟨y, ⟨rfl, rfl⟩, hy⟩ := B₀.fibre_G p₁ p₂ f₁ f₂ h y₁ y₂ ey
        have hsq : f₁.comp p₁ = f₂.comp p₂ := Subtype.ext h.1
        have hδ := (hcomp p₁ f₁ x y).symm.trans (hsq ▸ hcomp p₂ f₂ x y)
        obtain ⟨u, ⟨hu1, hu2⟩, hu⟩ := fs_units_fibre h (u₁ / δ p₁ x y) (u₂ / δ p₂ x y) (by
          rw [map_div, map_div, div_eq_div_iff_mul_eq_mul]
          apply mul_right_cancel (b := δ f₁ (B₀.map p₁ x) (B₀.map p₁ y) *
            δ f₂ (B₀.map p₂ x) (B₀.map p₂ y))
          dsimp only at eu
          calc _ = (Units.map (f₁.1 : (R₁ : Type) →* (R : Type)) u₁ *
                δ f₁ (B₀.map p₁ x) (B₀.map p₁ y)) *
                (Units.map (f₂.1 : (R₂ : Type) →* (R : Type)) (δ p₂ x y) *
                δ f₂ (B₀.map p₂ x) (B₀.map p₂ y)) := by ac_rfl
            _ = _ := by rw [eu, ← hδ]; ac_rfl)
        refine ⟨⟨x, y, u⟩, ⟨fs_sigma_eq.2 ⟨rfl, rfl, ?_⟩, fs_sigma_eq.2 ⟨rfl, rfl, ?_⟩⟩, ?_⟩
        · dsimp only
          rw [hu1, div_mul_cancel]
        · dsimp only
          rw [hu2, div_mul_cancel]
        · rintro ⟨x', y', u'⟩ ⟨e1, e2⟩
          obtain ⟨a1, b1, c1⟩ := fs_sigma_eq.1 e1
          obtain ⟨a2, b2, c2⟩ := fs_sigma_eq.1 e2
          obtain rfl := hx x' ⟨a1, a2⟩
          obtain rfl := hy y' ⟨b1, b2⟩
          exact fs_sigma_eq.2 ⟨rfl, rfl, hu u' ⟨eq_div_iff_mul_eq'.2 c1, eq_div_iff_mul_eq'.2 c2⟩⟩ }
  refine ⟨B, fun R => AddEquiv.refl _, fun R _ _ => (1 : (R : Type)ˣ), fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro R x x' y
    exact show (1 : (R : Type)ˣ) * 1 * t₁ R x x' y = t₁ R x x' y * 1 by simp
  · intro R x y y'
    exact show (1 : (R : Type)ˣ) * 1 * t₂ R x y y' = t₂ R x y y' * 1 by simp
  · intro R S f x y
    exact show Units.map (f.1 : (R : Type) →* (S : Type)) 1 * δ f x y = δ f x y * 1 by simp
end GlobalTheory
