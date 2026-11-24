-- Prove2me | solution 1 for GlobalTheory.SympMod.exists_pair_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:02:40.664405+00:00
-- url     : https://prove2.me/submissions/e3422715-506c-48bb-b53f-30c9bc4ab4d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsStdSympZmod
import Theorems.Thm_GlobalTheory_exists_pair_dvd_of_bilinForm
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.SympMod
namespace GlobalTheory.SympMod
theorem _root_.solution {M g : ℕ} [NeZero M] {V : Type*} [AddCommGroup V] [Module (ZMod M) V]
    {B : LinearMap.BilinForm (ZMod M) V} (N : Submodule (ZMod M) V)
    (hN : ∀ x ∈ N, (∀ y ∈ N, B x y = 0) → x = 0)
    (hc : ∀ d, d ∣ M → Nat.card {x : V // x ∈ N ∧ d • x = 0} = d ^ (2 * (g + 1))) :
    ∃ e ∈ N, ∃ f ∈ N, B e f = 1 := by
  have : IsPrincipalIdealRing (ZMod M) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod M)) (ZMod.ringHom_surjective _)
  obtain ⟨e, he, f, hf, h₁, h₂, h₃⟩ := exists_pair_dvd_of_bilinForm B N
  have hall : ∀ x ∈ N, ∀ y ∈ N, B e f ∣ B x y := by
    intro x hx y hy
    obtain ⟨b, hb⟩ := h₁ y hy
    obtain ⟨a, ha⟩ := h₂ x hx
    have k₁ : B (x - a • e) f = 0 := by simp [ha, mul_comm]
    have k := h₃ (x - a • e) (N.sub_mem hx (N.smul_mem _ he)) (y - b • f)
      (N.sub_mem hy (N.smul_mem _ hf)) (by simp [hb, mul_comm]) k₁
    rw [map_sub, map_smul, k₁, smul_zero, sub_zero] at k
    have : B x y = B (x - a • e) y + a * B e y := by simp
    rw [this]
    exact dvd_add k (Dvd.dvd.mul_left (h₁ y hy) a)
  have hu : IsUnit (B e f) := by
    by_contra hnu
    obtain ⟨m, hm⟩ := ZMod.natCast_zmod_surjective (B e f)
    rw [← hm, ZMod.isUnit_iff_coprime, Nat.Prime.not_coprime_iff_dvd] at hnu
    obtain ⟨p, hp, ⟨c, rfl⟩, ⟨q, hq⟩⟩ := hnu
    have hkill : ∀ x ∈ N, q • x = 0 := by
      intro x hx
      refine hN _ (N.toAddSubgroup.nsmul_mem hx q) fun y hy => ?_
      obtain ⟨r, hr⟩ := hall x hx y hy
      rw [map_nsmul, LinearMap.smul_apply, hr, ← hm, nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, ← mul_assoc,
        mul_comm q p, ← hq, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_mul]
    have hM : ∀ x : V, M • x = 0 := fun x => by
      rw [← Nat.cast_smul_eq_nsmul (ZMod M), ZMod.natCast_self, zero_smul]
    have k₁ := hc q ⟨p, by rw [hq, mul_comm]⟩
    have k₂ := hc M dvd_rfl
    have k₃ : Nat.card {x : V // x ∈ N ∧ q • x = 0} = Nat.card {x : V // x ∈ N ∧ M • x = 0} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x =>
        ⟨fun h => ⟨h.1, hM x⟩, fun h => ⟨h.1, hkill x h.1⟩⟩)
    rw [k₁, k₂] at k₃
    have k₄ : q = M := Nat.pow_left_injective (by omega) k₃
    have k₅ := NeZero.pos M
    have := hp.two_le
    nlinarith
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  exact ⟨e, he, u • f, N.smul_mem _ hf, by simpa using hu⟩
end GlobalTheory.SympMod
