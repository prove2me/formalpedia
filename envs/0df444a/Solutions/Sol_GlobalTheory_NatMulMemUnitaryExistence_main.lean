-- Prove2me | solution 1 for GlobalTheory.NatMulMemUnitaryExistence.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:32.958342+00:00
-- url     : https://prove2.me/submissions/2dd2ed6c-e33e-447c-9db5-17e995d097b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulMem
import Theorems.Thm_GlobalTheory_NatMulMemUnitaryExistence_exists_nat_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatMulMemUnitaryExistence
open NumberField
namespace GlobalTheory.NatMulMemUnitaryExistence
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by simpa using hy⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, Nat.mul_pos hd₁ hd₂, ?_⟩
    have e : (d₁ * d₂) • (y + z) = d₂ • (d₁ • y) + d₁ • (d₂ • z) := by
      rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_of_tower_mem d₂ h₁) (L.smul_of_tower_mem d₁ h₂)
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨k, hk, a, ha⟩ := exists_nat_mul_mem c
    refine ⟨k * d, Nat.mul_pos hk hd, ?_⟩
    have e : (k * d) • (c • y) = a • (d • y) := by
      funext i
      simp only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul]
      rw [Algebra.smul_def, show algebraMap (𝓞 E) E a = (a : E) from rfl, ha]
      simp only [Pi.mul_apply, Pi.natCast_apply]
      push_cast; ring
    rw [e]
    exact L.smul_mem a h
end GlobalTheory.NatMulMemUnitaryExistence
