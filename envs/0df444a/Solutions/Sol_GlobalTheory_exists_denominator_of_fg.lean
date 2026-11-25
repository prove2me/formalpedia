-- Prove2me | solution 1 for GlobalTheory.exists_denominator_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:03:30.428555+00:00
-- url     : https://prove2.me/submissions/a09f43ef-6900-4530-b9e7-014a1502b362

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDenominatorOfFg
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {V : Type} [AddCommGroup V] (B : V →ₗ[ℤ] V →ₗ[ℤ] ℚ)
    (M : Submodule ℤ V) (hM : M.FG) :
    ∃ d : ℕ, 0 < d ∧ ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, (d : ℚ) * B x y = n := by
  obtain ⟨s, hs⟩ := Submodule.FG.map₂ B hM hM
  refine ⟨∏ a ∈ s, a.den, Finset.prod_pos fun a _ => a.den_pos, ?_⟩
  have key : ∀ r ∈ Submodule.span ℤ (s : Set ℚ), ∃ n : ℤ, ((∏ a ∈ s, a.den : ℕ) : ℚ) * r = n := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun a : ℚ => a.den) (Finset.mem_coe.mp ha)
      refine ⟨c * a.num, ?_⟩
      rw [hc]
      push_cast
      rw [← Rat.den_mul_eq_num]; ring
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨m, hm⟩ := ha
      obtain ⟨n, hn⟩ := hb
      exact ⟨m + n, by rw [mul_add, hm, hn]; push_cast; ring⟩
    | smul c a _ ha =>
      obtain ⟨m, hm⟩ := ha
      exact ⟨c * m, by rw [zsmul_eq_mul, mul_left_comm, hm]; push_cast; ring⟩
  intro x hx y hy
  exact key _ (hs ▸ Submodule.apply_mem_map₂ B hx hy)
end GlobalTheory
