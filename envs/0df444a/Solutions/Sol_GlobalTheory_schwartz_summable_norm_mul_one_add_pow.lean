-- Prove2me | solution 1 for GlobalTheory.schwartz_summable_norm_mul_one_add_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:05.328227+00:00
-- url     : https://prove2.me/submissions/da8e3956-5733-4bd2-b67a-5bd2b3373c45

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeDualFourierExpansionSchwartz
import Theorems.Thm_GroundTheory_Global_exists_norm_le_inv_one_add_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open scoped RealInnerProductSpace FourierTransform SchwartzMap
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ]
    (h : 𝓢(V, ℂ)) (N : ℕ) : Summable fun l : Λ => ‖h l‖ * (1 + ‖(l : V)‖) ^ N := by
  set k := finrank ℤ Λ + 1
  obtain ⟨C, hC, hg⟩ := GroundTheory.Global.exists_norm_le_inv_one_add_pow h (k + N)
  have hs : Summable fun l : Λ => C * ((1 + ‖l‖) ^ k)⁻¹ := by
    apply Summable.mul_left
    have hs := ZLattice.summable_norm_pow_inv (L := Λ) k (by omega)
    refine Summable.of_norm_bounded_eventually hs ?_
    filter_upwards [(Set.finite_singleton (0 : Λ)).compl_mem_cofinite] with l hl
    have hpos : 0 < ‖l‖ := norm_pos_iff.mpr hl
    rw [Real.norm_of_nonneg (by positivity), inv_pow]
    gcongr
    linarith
  refine hs.of_nonneg_of_le (fun _ => by positivity) fun l => ?_
  have hp : 0 < 1 + ‖(l : V)‖ := by positivity
  calc ‖h l‖ * (1 + ‖(l : V)‖) ^ N
      ≤ C * ((1 + ‖(l : V)‖) ^ (k + N))⁻¹ * (1 + ‖(l : V)‖) ^ N := by
        gcongr
        exact hg _
    _ = C * ((1 + ‖(l : V)‖) ^ k)⁻¹ := by
        rw [pow_add]
        field_simp
    _ = C * ((1 + ‖l‖) ^ k)⁻¹ := rfl
end GlobalTheory
