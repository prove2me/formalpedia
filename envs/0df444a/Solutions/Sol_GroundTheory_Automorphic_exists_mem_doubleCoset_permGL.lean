-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_mem_doubleCoset_permGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:09:48.442484+00:00
-- url     : https://prove2.me/submissions/21358e6f-a8d3-424b-ba8e-08b80e526a14

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Theorems.Thm_GroundTheory_Automorphic_rowsReduced_step
import Theorems.Thm_GroundTheory_Automorphic_exists_eq_mul_permGL_of_rowsReduced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset
variable {n : ℕ} {k : Type*} [Field k]
namespace GroundTheory.Automorphic
theorem _root_.solution (g : GL (Fin n) k) :
    ∃ σ : Equiv.Perm (Fin n), g ∈ doubleCoset (permGL k σ) (borel n k) (borel n k) := by
  have key : ∀ d, d ≤ n → ∃ b₁ ∈ borel n k, ∃ b₂ ∈ borel n k,
      RowsReduced ((b₁ * g * b₂ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (n - d) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨1, (borel n k).one_mem, 1, (borel n k).one_mem, id, fun i hi => ?_⟩
      have := i.isLt
      omega
    | succ d ih =>
      intro hd
      obtain ⟨b₁, hb₁, b₂, hb₂, hred⟩ := ih (by omega)
      have ht : n - (d + 1) + 1 = n - d := by omega
      rw [← ht] at hred
      obtain ⟨c₁, hc₁, c₂, hc₂, hred'⟩ := rowsReduced_step _ (n - (d + 1)) (by omega) hred
      refine ⟨c₁ * b₁, (borel n k).mul_mem hc₁ hb₁, b₂ * c₂, (borel n k).mul_mem hb₂ hc₂, ?_⟩
      simpa only [mul_assoc] using hred'
  obtain ⟨b₁, hb₁, b₂, hb₂, hred⟩ := key n le_rfl
  rw [Nat.sub_self] at hred
  obtain ⟨σ, b, hb, hgb⟩ := exists_eq_mul_permGL_of_rowsReduced _ hred
  refine ⟨σ, mem_doubleCoset.mpr ⟨b₁⁻¹ * b, (borel n k).mul_mem ((borel n k).inv_mem hb₁) hb,
    b₂⁻¹, (borel n k).inv_mem hb₂, ?_⟩⟩
  rw [mul_assoc b₁⁻¹, ← hgb]
  group
end GroundTheory.Automorphic
