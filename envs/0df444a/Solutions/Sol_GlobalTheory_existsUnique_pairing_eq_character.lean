-- Prove2me | solution 1 for GlobalTheory.existsUnique_pairing_eq_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:37:48.664696+00:00
-- url     : https://prove2.me/submissions/bd41181d-05c7-4889-8131-e5868ab02f85

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {H M : Type} [CommGroup H] [CommMonoid M] (N : ℕ)
    [NeZero N] [HasEnoughRootsOfUnity M N] [hfin : Finite {x : H // x ^ N = 1}]
    (W : H → H → Mˣ → Prop)
    (hex : ∀ x y : H, x ^ N = 1 → y ^ N = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (hskew : ∀ x y c, W x y c → W y x c⁻¹)
    (hnd : ∀ x : H, x ^ N = 1 → (∀ y : H, y ^ N = 1 → W x y 1) → x = 1)
    (χ : {x : H // x ^ N = 1} → Mˣ)
    (hχ : ∀ x y, χ ⟨x.1 * y.1, by rw [mul_pow, x.2, y.2, _root_.one_mul]⟩ = χ x * χ y) :
    ∃! b : H, b ^ N = 1 ∧ ∀ x : {x : H // x ^ N = 1}, W x.1 b (χ x) := by
  classical
  let G : Subgroup H := (powMonoidHom N : H →* H).ker
  have hG : ∀ x : G, (x : H) ^ N = 1 := fun x => x.2
  haveI : Finite G := hfin
  choose e he huniq using fun x y : G => hex x y (hG x) (hG y)
  have hel : ∀ x x' y : G, e (x * x') y = e x y * e x' y := fun x x' y =>
    (huniq _ _ _ (hmul _ _ _ _ _ (he x y) (he x' y))).symm
  have hes : ∀ x y : G, e y x = (e x y)⁻¹ := fun x y =>
    (huniq _ _ _ (hskew _ _ _ (he x y))).symm
  have her : ∀ x y y' : G, e x (y * y') = e x y * e x y' := fun x y y' => by
    rw [hes (y * y') x, hel, hes y x, hes y' x, mul_inv]
  let Φ : G →* (G →* Mˣ) := MonoidHom.mk' (fun b => MonoidHom.mk' (fun x => e x b)
    (fun x x' => hel x x' b)) (fun b b' => MonoidHom.ext fun x => her x b b')
  have hΦ : ∀ b x, Φ b x = e x b := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    refine Subtype.ext (hnd b (hG b) fun y hy => ?_)
    have h1 : e ⟨y, hy⟩ b = 1 := by rw [← hΦ, hb]; rfl
    have h2 := he b ⟨y, hy⟩
    rwa [hes, h1, inv_one] at h2
  haveI : HasEnoughRootsOfUnity M (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd M (n := N)
      (Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (hG g))
  have hcard := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G M
  haveI : Finite (G →* Mˣ) := Nat.finite_of_card_ne_zero (hcard ▸ Nat.card_pos.ne')
  have hbij : Function.Bijective Φ := hinj.bijective_of_nat_card_le hcard.le
  let χ' : G →* Mˣ := MonoidHom.mk' (fun x => χ ⟨x.1, hG x⟩)
    (fun x y => hχ ⟨x.1, hG x⟩ ⟨y.1, hG y⟩)
  obtain ⟨b, hb⟩ := hbij.2 χ'
  refine ⟨b, ⟨hG b, fun x => ?_⟩, ?_⟩
  · have h1 : e ⟨x.1, x.2⟩ b = χ x := by rw [← hΦ, hb]; rfl
    rw [← h1]
    exact he ⟨x.1, x.2⟩ b
  · rintro b' ⟨hb', h⟩
    have : (⟨b', hb'⟩ : G) = b := by
      apply hinj
      rw [hb]
      ext1 x
      rw [hΦ]
      exact (huniq x ⟨b', hb'⟩ _ (h ⟨x.1, hG x⟩)).symm
    exact congrArg Subtype.val this
end GlobalTheory
