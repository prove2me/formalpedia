-- Prove2me | solution 1 for GlobalTheory.tail_sum_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:43:12.887783+00:00
-- url     : https://prove2.me/submissions/39464a32-eebf-4b81-b2fc-3fd984efcc46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TailSumLtOne

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
theorem _root_.solution {ι : Type*} (idx : ι → ℕ) (ρ n : ℕ) (hn : 4 * ρ + 4 ≤ n) (h2 : ∀ i, 2 ≤ idx i)
    (hc : ∀ m, {i | idx i = m}.Finite ∧ {i | idx i = m}.ncard ≤ m ^ (2 * ρ)) (c : ι → ℂ) (hcb : ∀ i, ‖c i‖ ≤ (idx i : ℝ) ^ (-(n : ℝ) / 2)) :
    Summable (fun i => ‖c i‖) ∧ ∑' i, ‖c i‖ ≤ 0.65 := by
  classical
  have hterm : ∀ i, ‖c i‖ ≤ 1 / ((idx i : ℝ) ^ (2 * ρ) * (idx i : ℝ) ^ 2) := by
    intro i
    have h1 : (1 : ℝ) ≤ idx i := by exact_mod_cast (le_trans (by norm_num) (h2 i))
    refine (hcb i).trans ?_
    have hn' : (4 * ρ + 4 : ℝ) ≤ n := by exact_mod_cast hn
    have hle : -(n : ℝ) / 2 ≤ -((2 * ρ + 2 : ℕ) : ℝ) := by push_cast; linarith
    refine (Real.rpow_le_rpow_of_exponent_le h1 hle).trans (le_of_eq ?_)
    rw [Real.rpow_neg (by linarith), Real.rpow_natCast, pow_add, one_div]
  have hz := hasSum_zeta_two
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, ‖c i‖ ≤ 0.65 := by
    intro s
    rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image idx) (g := idx)
      (fun i hi => Finset.mem_image_of_mem _ hi)]
    have hfib : ∀ m ∈ s.image idx, ∑ i ∈ s with idx i = m, ‖c i‖ ≤ 1 / (m : ℝ) ^ 2 := by
      intro m hm
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hm
      have hpos : (0 : ℝ) < idx j := by exact_mod_cast (lt_of_lt_of_le (by norm_num) (h2 j))
      have hcard : ((s.filter (fun i => idx i = idx j)).card : ℝ) ≤ (idx j : ℝ) ^ (2 * ρ) := by
        have h3 : (s.filter (fun i => idx i = idx j)).card ≤ {i | idx i = idx j}.ncard := by
          rw [← Set.ncard_coe_finset]
          refine Set.ncard_le_ncard ?_ (hc _).1
          intro i hi
          simpa using (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
        exact_mod_cast h3.trans (hc _).2
      calc ∑ i ∈ s with idx i = idx j, ‖c i‖
          ≤ (s.filter (fun i => idx i = idx j)).card •
              (1 / ((idx j : ℝ) ^ (2 * ρ) * (idx j : ℝ) ^ 2)) := by
            refine Finset.sum_le_card_nsmul _ _ _ ?_
            intro i hi
            have := hterm i
            rwa [(Finset.mem_filter.1 hi).2] at this
        _ ≤ (idx j : ℝ) ^ (2 * ρ) * (1 / ((idx j : ℝ) ^ (2 * ρ) * (idx j : ℝ) ^ 2)) := by
            rw [nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 1 / (idx j : ℝ) ^ 2 := by field_simp
    refine (Finset.sum_le_sum hfib).trans ?_
    have h1 : 1 ∉ s.image idx := by
      intro h
      obtain ⟨j, -, hj⟩ := Finset.mem_image.1 h
      have := h2 j
      omega
    have h4 := sum_le_hasSum (insert 1 (s.image idx)) (fun m _ => by positivity) hz
    rw [Finset.sum_insert h1] at h4
    have hpi := Real.pi_lt_d4
    have hpi0 := Real.pi_pos
    have h5 : Real.pi ^ 2 ≤ 3.1416 ^ 2 := by gcongr
    norm_num at h4 h5 ⊢
    linarith
  have hs : Summable (fun i => ‖c i‖) := summable_of_sum_le (fun i => norm_nonneg _) hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩
end GlobalTheory
