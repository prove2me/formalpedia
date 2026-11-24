-- Prove2me | solution 1 for GlobalTheory.SympTower.ker_and_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:02:39.076252+00:00
-- url     : https://prove2.me/submissions/b2065f91-9166-4340-a0d1-d33fdfc6ff03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompatibleSymplectic

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
    (ev : ((Fin g → ℤ) × (Fin g → ℤ)) →+ G)
    (hev : ∀ a b, e (ev a) (ev b) = ζ ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1)) :
    (∀ a b, ev a = ev b ↔ ∃ e', a = b + n • e') ∧ Function.Surjective ev := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  have hnx : ∀ x : G, n • x = 0 := fun x => Φ.injective (by
      rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul])
  have h0 : ∀ y, e 0 y = 1 := by
    intro y
    have := h1 0 0 y
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hker : ∀ a, ev a = 0 → (∀ i, (n : ℤ) ∣ a.1 i) ∧ ∀ i, (n : ℤ) ∣ a.2 i := by
    intro a ha
    constructor
    · intro i
      have := hev a (0, Pi.single i 1)
      rw [ha, h0, eq_comm, hζ.zpow_eq_one_iff_dvd] at this
      simpa using this
    · intro i
      have := hev a (Pi.single i 1, 0)
      rw [ha, h0, eq_comm, hζ.zpow_eq_one_iff_dvd] at this
      simpa using this
  refine ⟨fun a b => ⟨fun h => ?_, ?_⟩, ?_⟩
  · obtain ⟨ha, hb⟩ := hker (a - b) (by rw [map_sub, h, sub_self])
    choose c hc using ha
    choose d hd using hb
    refine ⟨(c, d), ?_⟩
    ext i
    · have := hc i
      simp at this ⊢
      linarith
    · have := hd i
      simp at this ⊢
      linarith
  · rintro ⟨c, rfl⟩
    rw [map_add, map_nsmul, hnx, add_zero]
  · let f : (Fin g → ZMod n) × (Fin g → ZMod n) → G :=
      fun a => ev (fun i => ((a.1 i).val : ℤ), fun i => ((a.2 i).val : ℤ))
    have hf : Function.Injective f := by
      intro a b h
      obtain ⟨ha, hb⟩ := hker (_ - _) (by rw [map_sub]; exact sub_eq_zero.2 h)
      ext i
      · have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).2 (ha i)
        simpa [sub_eq_zero] using this
      · have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).2 (hb i)
        simpa [sub_eq_zero] using this
    haveI : Fintype G := Fintype.ofEquiv _ Φ.symm.toEquiv
    have hb : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by
      rw [Fintype.card_congr Φ.toEquiv]
      simp [two_mul, pow_add]⟩
    intro x
    obtain ⟨a, ha⟩ := hb.2 x
    exact ⟨_, ha⟩
end GlobalTheory.SympTower
