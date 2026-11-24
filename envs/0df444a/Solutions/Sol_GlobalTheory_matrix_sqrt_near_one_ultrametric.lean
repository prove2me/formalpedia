-- Prove2me | solution 1 for GlobalTheory.matrix_sqrt_near_one_ultrametric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:19:55.415734+00:00
-- url     : https://prove2.me/submissions/9db0647f-1476-4b0a-ab6d-e24c1aff6449

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatrixSqrtNearOneUltrametric
import Theorems.Thm_GlobalTheory_MatSqrtNearOne_exists_sqrt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] (n : ℕ) (σ : K →+* K), Continuous σ →
      ∃ W ∈ nhds (1 : Matrix (Fin n) (Fin n) K), ∀ s ∈ W, ∃ r : Matrix (Fin n) (Fin n) K,
        r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) K, a * s = s * a → a * r = r * a) ∧
        ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by
  intro K _ _ _ _ n σ hσ
  have h4 : (4 : K) ≠ 0 := by norm_num
  refine ⟨{s | ∀ i j, ‖s i j - (1 : Matrix (Fin n) (Fin n) K) i j‖ < ‖(4 : K)‖}, ?_, ?_⟩
  · refine IsOpen.mem_nhds ?_ (by simp [h4])
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt ((continuous_id.matrix_elem i j).sub continuous_const).norm continuous_const
  · intro s hs
    exact MatSqrtNearOne.exists_sqrt σ hσ s hs
end GlobalTheory
