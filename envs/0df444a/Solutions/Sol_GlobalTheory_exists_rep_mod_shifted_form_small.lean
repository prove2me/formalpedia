-- Prove2me | solution 1 for GlobalTheory.exists_rep_mod_shifted_form_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:37:52.09134+00:00
-- url     : https://prove2.me/submissions/2505a612-70e5-4095-bdd2-8b4b59f8518e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSmulEqBilinOfAnisotropic
import Theorems.Thm_GlobalTheory_exists_smul_eq_bilin_of_anisotropic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Q : X → ℤ) (B : X →+ X →+ ℤ), (∀ a b, Q (a + b) = Q a + Q b + B a b) → (∀ a, 2 * Q a = B a a) → (∀ a, a ≠ 0 → 1 ≤ Q a) → ∀ (l : X →+ ℚ) (k : ℕ), 1 ≤ k → ∀ y : X, ∃ z : X, ∀ m : X, |(B (y + k • z) m : ℚ) - l m| ≤ k * Q m := by
  intro X _ _ _ Q B hadd h2 hpos l k hk y
  have hQ0 : ∀ a, 0 ≤ Q a := by
    intro a
    by_cases ha : a = 0
    · have := h2 a
      rw [ha] at this ⊢
      simp at this
      omega
    · have := hpos a ha
      omega
  have hsm : ∀ (n : ℤ) a, Q (n • a) = n * n * Q a := by
    intro n a
    have e1 := h2 (n • a)
    have e2 := h2 a
    rw [map_zsmul, map_zsmul, AddMonoidHom.zsmul_apply, ← e2] at e1
    simp only [smul_eq_mul] at e1
    linarith
  obtain ⟨M, x, hM, hx⟩ := exists_smul_eq_bilin_of_anisotropic B (fun a ha => by
    by_contra h
    have := hpos a h
    have := h2 a
    omega) l
  let F : X → ℕ := fun z => (Q (M • (y + k • z) - x)).toNat
  obtain ⟨z, hz⟩ : ∃ z, ∀ z', F z ≤ F z' :=
    ⟨Function.argmin F, fun z' => Function.argmin_le F z'⟩
  refine ⟨z, fun m => ?_⟩
  have hz' : ∀ z', Q (M • (y + k • z) - x) ≤ Q (M • (y + k • z') - x) := by
    intro z'
    have := hz z'
    have a := hQ0 (M • (y + k • z) - x)
    have b := hQ0 (M • (y + k • z') - x)
    simp only [F] at this
    omega
  have key : ∀ s : ℤ, 0 ≤ (M * k * s) * (M * k * s) * Q m
      + (M * k * s) * (M * B (y + k • z) m - B x m) := by
    intro s
    have h := hz' (z + s • m)
    have e : M • (y + k • (z + s • m)) - x = (M • (y + k • z) - x) + (M * k * s) • m := by
      module
    rw [e, hadd, hsm, map_zsmul, map_sub, map_zsmul, AddMonoidHom.sub_apply,
      AddMonoidHom.zsmul_apply] at h
    simp only [smul_eq_mul] at h
    linarith
  have k1 : (0 : ℚ) ≤ ((M * k * 1) * (M * k * 1) * Q m
      + (M * k * 1) * (M * B (y + k • z) m - B x m) : ℤ) := by exact_mod_cast key 1
  have k2 : (0 : ℚ) ≤ ((M * k * (-1)) * (M * k * (-1)) * Q m
      + (M * k * (-1)) * (M * B (y + k • z) m - B x m) : ℤ) := by exact_mod_cast key (-1)
  push_cast at k1 k2
  rw [hx] at k1 k2
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have hp : (0 : ℚ) < M * M * k := by positivity
  set β : ℚ := ((B (y + k • z) m : ℤ) : ℚ)
  rw [abs_le]
  constructor
  · have : (0 : ℚ) ≤ M * M * k * (k * Q m + (β - l m)) := by linarith
    have := (mul_nonneg_iff_of_pos_left hp).1 this
    linarith
  · have : (0 : ℚ) ≤ M * M * k * (k * Q m - (β - l m)) := by linarith
    have := (mul_nonneg_iff_of_pos_left hp).1 this
    linarith
end GlobalTheory
