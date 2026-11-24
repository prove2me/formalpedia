-- Prove2me | solution 1 for GlobalTheory.IwaFlag.exists_triangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:57:32.096743+00:00
-- url     : https://prove2.me/submissions/4a0f2e5a-b32d-4741-8080-aa861c9ffbae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFlagDualMatrix
import Theorems.Thm_GlobalTheory_IwaFlag_smul_mem_of_sd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IwaFlag
variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {ρ : ℕ} {c : R →+* R} {ε : R} {O : AddSubgroup R}
  {h : V →ₗ[R] V →ₛₗ[c] R} {M : AddSubgroup V}
namespace GlobalTheory.IwaFlag
theorem _root_.solution (hεc : c ε = ε) (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hP : Princ ε O)
    (hM₁ : ∀ y ∈ M, ε • y = y) (hM₂ : ∀ y, ε • y = y → (y ∈ M ↔ ∀ x ∈ M, h y x ∈ O))
    (X : (Fin ρ → R) →ₗ[R] V) (f : Fin ρ → V) (hXf : ∀ t k, h (X t) (f k) = t k) (N : ℕ) (hN : 0 < N)
    (he : ∀ k, X (Pi.single k ((N : R) * ε)) ∈ M) (hf : ∀ k, ((N : R) * ε) • f k ∈ M) (i : Fin ρ) :
    ∃ (b : Fin ρ → R) (α' : R), (∀ l, i < l → b l = 0) ∧ X b ∈ M ∧ ε * α' = α' ∧ b i * α' = ε ∧
      ∀ t : Fin ρ → R, (∀ l, i < l → t l = 0) → X t ∈ M → α' * t i ∈ O := by
  have hfix : ∀ t, X t ∈ M → ∀ k, ε * t k = t k := fun t ht k => by
    have := congrArg (fun z => h z (f k)) (hM₁ _ ht)
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, hXf] using this
  let J : AddSubgroup R :=
    { carrier := {a | ∃ t : Fin ρ → R, (∀ l, i < l → t l = 0) ∧ X t ∈ M ∧ t i = a}
      zero_mem' := ⟨0, fun _ _ => rfl, by rw [map_zero]; exact M.zero_mem, rfl⟩
      add_mem' := by
        rintro _ _ ⟨t, h1, h2, rfl⟩ ⟨s, g1, g2, rfl⟩
        exact ⟨t + s, fun l hl => by simp [h1 l hl, g1 l hl], by rw [map_add]; exact M.add_mem h2 g2, rfl⟩
      neg_mem' := by
        rintro _ ⟨t, h1, h2, rfl⟩
        exact ⟨-t, fun l hl => by simp [h1 l hl], by rw [map_neg]; exact M.neg_mem h2, rfl⟩ }
  obtain ⟨α, ⟨b, hb1, hb2, rfl⟩, α', h1, h2, h3⟩ := hP J
    (by rintro _ ⟨t, -, h2, rfl⟩; exact hfix t h2 i)
    (by
      rintro o ho _ ⟨t, h1, h2, rfl⟩
      exact ⟨o • t, fun l hl => by simp [h1 l hl], by rw [map_smul]; exact smul_mem_of_sd hmul hM₁ hM₂ ho h2, rfl⟩)
    ⟨N, hN, Pi.single i ((N : R) * ε), fun l hl => Pi.single_eq_of_ne hl.ne' _, he i, Pi.single_eq_same _ _⟩
    ⟨N, hN, by
      rintro _ ⟨t, -, h2, rfl⟩
      have := (hM₂ _ (hM₁ _ h2)).1 h2 _ (hf i)
      rwa [map_smulₛₗ, hXf, map_mul, map_natCast, hεc, smul_eq_mul, mul_assoc, hfix t h2 i] at this⟩
  exact ⟨b, α', hb1, hb2, h1, h2, fun t ht1 ht2 => h3 _ ⟨t, ht1, ht2, rfl⟩⟩
end GlobalTheory.IwaFlag
