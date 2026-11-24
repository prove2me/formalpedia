-- Prove2me | solution 1 for GlobalTheory.SympTower.exists_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:30:01.591607+00:00
-- url     : https://prove2.me/submissions/a4c7fafe-733e-422a-bc9a-76a1a1b88a59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompatibleSymplectic
import Theorems.Thm_GlobalTheory_SympTower_exists_pairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.SympTower
namespace GlobalTheory.SympTower
theorem _root_.solution {F : Type} [Field F] {ζ : Fˣ} {n : ℕ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) {g : ℕ} {G : Type} [AddCommGroup G] (e : G → G → Fˣ)
    (Φ : G ≃+ (Fin (2 * g) → ZMod n)) (h1 : ∀ x y z, e (x + y) z = e x z * e y z)
    (h2 : ∀ x y z, e x (y + z) = e x y * e x z) (h3 : ∀ x, e x x = 1)
    (h4 : ∀ x, (∀ y, e x y = 1) → x = 0) :
    ∃ ev : ((Fin g → ℤ) × (Fin g → ℤ)) →+ G,
      ∀ a b, e (ev a) (ev b) = ζ ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  let χ : ZMod n → Fˣ := fun a => ((Additive.toMul (hζ.zmodEquivZPowers a) : Subgroup.zpowers ζ) : Fˣ)
  have χadd : ∀ a b, χ (a + b) = χ a * χ b := by intro a b; simp [χ]
  have χinj : Function.Injective χ := by
    intro a b h
    exact hζ.zmodEquivZPowers.injective (Additive.toMul.injective (Subtype.ext h))
  have χint : ∀ i : ℤ, χ i = ζ ^ i := by
    intro i; simp only [χ, hζ.zmodEquivZPowers_apply_coe_int]; rfl
  have χ0 : χ 0 = 1 := by simpa using χint 0
  have hpow : ∀ x y, e x y ^ n = 1 := by
    intro x y
    let f : G →+ Additive Fˣ := AddMonoidHom.mk' (fun x => Additive.ofMul (e x y))
      (fun a b => by rw [h1]; rfl)
    have hx : n • x = 0 := Φ.injective (by
      rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul])
    have := map_nsmul f n x
    rw [hx, map_zero] at this
    exact (congrArg Additive.toMul this).symm
  have hex : ∀ x y, ∃ a, χ a = e (Φ.symm x) (Φ.symm y) := by
    intro x y
    have hm : e (Φ.symm x) (Φ.symm y) ∈ Subgroup.zpowers ζ := by
      rw [hζ.zpowers_eq, mem_rootsOfUnity]; exact hpow _ _
    obtain ⟨i, hi⟩ := hm
    exact ⟨i, by rw [χint]; exact hi⟩
  choose b hb using hex
  have b1 : ∀ x y z, b (x + y) z = b x z + b y z := fun x y z =>
    χinj (by rw [χadd, hb, hb, hb, map_add, h1])
  have b2 : ∀ x y z, b x (y + z) = b x y + b x z := fun x y z =>
    χinj (by rw [χadd, hb, hb, hb, map_add, h2])
  let ω : (Fin (2 * g) → ZMod n) →ₗ[ZMod n] (Fin (2 * g) → ZMod n) →ₗ[ZMod n] ZMod n :=
    LinearMap.mk₂ (ZMod n) b b1
      (fun c x y => ZMod.map_smul (AddMonoidHom.mk' (fun x => b x y) (fun x z => b1 x z y)) c x)
      b2
      (fun c x y => ZMod.map_smul (AddMonoidHom.mk' (fun y => b x y) (fun y z => b2 x y z)) c y)
  have hω : ∀ x y, χ (ω x y) = e (Φ.symm x) (Φ.symm y) := hb
  have halt : ∀ x, ω x x = 0 := fun x => χinj (by rw [hω, h3, χ0])
  have hsk : ∀ x y, ω x y = - ω y x := by
    intro x y
    have := halt (x + y)
    simp only [map_add, LinearMap.add_apply, halt] at this
    linear_combination this
  obtain ⟨v, w, hv, hw, hvw⟩ := exists_pairs ω halt (by
    intro x hx
    have := h4 (Φ.symm x) (fun y => by
      have := hω x (Φ y)
      rw [hx, χ0, Φ.symm_apply_apply] at this
      exact this.symm)
    exact Φ.symm.injective (by rw [this, map_zero])) g le_rfl
  have hwv : ∀ i j, ω (w i) (v j) = if j = i then -1 else 0 := by
    intro i j; rw [hsk, hvw]; split_ifs <;> simp
  let E : ((Fin g → ℤ) × (Fin g → ℤ)) →+ (Fin (2 * g) → ZMod n) :=
    AddMonoidHom.mk' (fun a => ∑ i, (a.1 i : ZMod n) • v i + ∑ i, (a.2 i : ZMod n) • w i)
      (fun a b => by
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Int.cast_add, add_smul,
          Finset.sum_add_distrib]
        abel)
  refine ⟨Φ.symm.toAddMonoidHom.comp E, fun a c => ?_⟩
  change e (Φ.symm (E a)) (Φ.symm (E c)) = _
  rw [← hω, ← χint]
  congr 1
  simp [E, map_sum, LinearMap.sum_apply, hv, hw, hvw, hwv, dotProduct, mul_comm]
  ring
end GlobalTheory.SympTower
