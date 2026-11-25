-- Prove2me | solution 1 for GlobalTheory.QuotientMapComposition.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:39:35.6867+00:00
-- url     : https://prove2.me/submissions/27bab5df-1147-4d68-b0fd-7df959983ab7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapMkOfComp
import Theorems.Thm_P2M_GlobalTheory_QuotientMapComposition_map_mk__of_comp_160cf9274fad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.QuotientMapComposition
namespace GlobalTheory.QuotientMapComposition
theorem _root_.solution : ∀ {A R₀ A' B₀ : Type} [inst : CommRing A] [inst_1 : CommRing R₀] [inst_2 : CommRing A'] [inst_3 : CommRing B₀] (φ : A →+* R₀) (ψ : A →+* A') (α : R₀ →+* B₀) (κ : A' →+* B₀), RingHom.comp α φ = RingHom.comp κ ψ → (∀ (a : A), (φ : A → R₀) a = (0 : R₀) → (ψ : A → A') a = (0 : A') → a = (0 : A)) → (∀ (r : R₀) (c : A'), (α : R₀ → B₀) r = (κ : A' → B₀) c → ∃ (a : A), (φ : A → R₀) a = r ∧ (ψ : A → A') a = c) → ∀ (s : A) (LA LR LA' LB : Type) [inst_4 : CommRing LA] [inst_5 : CommRing LR] [inst_6 : CommRing LA'] [inst_7 : CommRing LB] [inst_8 : Algebra A LA] [inst_9 : Algebra R₀ LR] [inst_10 : Algebra A' LA'] [inst_11 : Algebra B₀ LB] [IsLocalization.Away s LA] [IsLocalization.Away ((φ : A → R₀) s) LR] [IsLocalization.Away ((ψ : A → A') s) LA'] [IsLocalization.Away ((α : R₀ → B₀) ((φ : A → R₀) s)) LB] (Φ : LA →+* LR) (Ψ : LA →+* LA') (Aα : LR →+* LB) (Kκ : LA' →+* LB), RingHom.comp Φ (Algebra.algebraMap A LA) = RingHom.comp (Algebra.algebraMap R₀ LR) φ → RingHom.comp Ψ (Algebra.algebraMap A LA) = RingHom.comp (Algebra.algebraMap A' LA') ψ → RingHom.comp Aα (Algebra.algebraMap R₀ LR) = RingHom.comp (Algebra.algebraMap B₀ LB) α → RingHom.comp Kκ (Algebra.algebraMap A' LA') = RingHom.comp (Algebra.algebraMap B₀ LB) κ → (∀ (t : LA), (Φ : LA → LR) t = (0 : LR) → (Ψ : LA → LA') t = (0 : LA') → t = (0 : LA)) ∧ ∀ (a : LR) (b : LA'), (Aα : LR → LB) a = (Kκ : LA' → LB) b → ∃ (t : LA), (Φ : LA → LR) t = a ∧ (Ψ : LA → LA') t = b := by
  intro A R₀ A' B₀ _ _ _ _ φ ψ α κ h0 hinj hsurj s LA LR LA' LB _ _ _ _ _ _ _ _ _ _ _ _ Φ Ψ Aα Kκ hΦ hΨ hA hK
  have hu : κ (ψ s) = α (φ s) := (RingHom.congr_fun h0 s).symm
  constructor
  · intro t ht1 ht2
    obtain ⟨⟨a, _, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) t
    rw [map_mk'_of_comp φ Φ hΦ (Submonoid.powers s) (Submonoid.powers (φ s)) a _ ⟨φ s ^ n, n, rfl⟩ (by simp),
      IsLocalization.mk'_eq_zero_iff] at ht1
    rw [map_mk'_of_comp ψ Ψ hΨ (Submonoid.powers s) (Submonoid.powers (ψ s)) a _ ⟨ψ s ^ n, n, rfl⟩ (by simp),
      IsLocalization.mk'_eq_zero_iff] at ht2
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := ht1
    obtain ⟨⟨_, l, rfl⟩, hl⟩ := ht2
    change φ s ^ k * φ a = 0 at hk
    change ψ s ^ l * ψ a = 0 at hl
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨s ^ (k + l), k + l, rfl⟩, hinj _ ?_ ?_⟩
    · change φ (s ^ (k + l) * a) = 0
      rw [map_mul, map_pow, pow_add, mul_right_comm, hk, zero_mul]
    · change ψ (s ^ (k + l) * a) = 0
      rw [map_mul, map_pow, pow_add, mul_assoc, hl, mul_zero]
  · intro a b hab
    obtain ⟨⟨r, _, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (φ s)) a
    obtain ⟨⟨c, _, m, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (ψ s)) b
    rw [map_mk'_of_comp α Aα hA (Submonoid.powers (φ s)) (Submonoid.powers (α (φ s))) r _
        ⟨α (φ s) ^ n, n, rfl⟩ (by simp),
      map_mk'_of_comp κ Kκ hK (Submonoid.powers (ψ s)) (Submonoid.powers (α (φ s))) c _
        ⟨α (φ s) ^ m, m, rfl⟩ (by simp [hu]),
      IsLocalization.mk'_eq_iff_eq, IsLocalization.eq_iff_exists (Submonoid.powers (α (φ s)))] at hab
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := hab
    change α (φ s) ^ k * (α (φ s) ^ m * α r) = α (φ s) ^ k * (α (φ s) ^ n * κ c) at hk
    obtain ⟨a0, ha1, ha2⟩ := hsurj (φ s ^ (k + m) * r) (ψ s ^ (k + n) * c) (by
      rw [map_mul, map_pow, map_mul, map_pow, hu, pow_add, pow_add, mul_assoc, mul_assoc]; exact hk)
    refine ⟨IsLocalization.mk' LA a0 (⟨s ^ (n + k + m), n + k + m, rfl⟩ : Submonoid.powers s), ?_, ?_⟩
    · rw [map_mk'_of_comp φ Φ hΦ (Submonoid.powers s) (Submonoid.powers (φ s)) a0 _
        ⟨φ s ^ (n + k + m), _, rfl⟩ (by simp), IsLocalization.mk'_eq_iff_eq]
      congr 1
      change φ s ^ n * φ a0 = φ s ^ (n + k + m) * r
      rw [ha1]; ring
    · rw [map_mk'_of_comp ψ Ψ hΨ (Submonoid.powers s) (Submonoid.powers (ψ s)) a0 _
        ⟨ψ s ^ (n + k + m), _, rfl⟩ (by simp), IsLocalization.mk'_eq_iff_eq]
      congr 1
      change ψ s ^ m * ψ a0 = ψ s ^ (n + k + m) * c
      rw [ha2]; ring
end GlobalTheory.QuotientMapComposition
