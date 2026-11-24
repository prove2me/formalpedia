-- Prove2me | solution 1 for GlobalTheory.CoordinateBasisBounds.basis_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:58:35.179502+00:00
-- url     : https://prove2.me/submissions/9a2f798e-9658-4f8a-b52f-66e433a6cff9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatMulIntegral
import Theorems.Thm_GlobalTheory_CoordinateBasisBounds_nat_mul_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CoordinateBasisBounds
open NumberField
namespace GlobalTheory.CoordinateBasisBounds
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ (d : E) • y ∈ L := by
  have hy : y ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hspan]; trivial
  induction hy using Submodule.span_induction with
  | mem v hv => exact ⟨1, one_pos, by simpa using hv⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    have e : ((a * b : ℕ) : E) • (x + y) = b • ((a : E) • x) + a • ((b : E) • y) := by
      rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, smul_smul, smul_add]
      push_cast; ring_nf
    rw [e]
    exact L.add_mem (nsmul_mem hax b) (nsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨d, hd, hdx⟩ := hx
    obtain ⟨m, hm, o, ho⟩ := nat_mul_integral c
    refine ⟨m * d, Nat.mul_pos hm hd, ?_⟩
    have e : ((m * d : ℕ) : E) • (c • x) = o • ((d : E) • x) := by
      rw [← algebraMap_smul E o, ← ho, smul_smul, smul_smul]; push_cast; ring_nf
    rw [e]
    exact L.smul_mem o hdx
end GlobalTheory.CoordinateBasisBounds
