-- Prove2me | solution 1 for GlobalTheory.PlaceModel.mem_of_finite_cosets
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:24.737768+00:00
-- url     : https://prove2.me/submissions/e96895e8-c0ba-411c-b92d-6970ad357837

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Theorems.Thm_GlobalTheory_PlaceModel_trans_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PlaceModel
variable {G : Type} [AddCommGroup G]
variable {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}
namespace GlobalTheory.PlaceModel
theorem _root_.solution {K : AddSubgroup G} (hK : ind K ∈ waveSpan χ X Y L) (P : Finset G) :
    ∀ Φ : G → ℂ, (∀ t, Φ t ≠ 0 → t ∈ X) → (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) →
      (∀ t, Φ t ≠ 0 → ∃ s ∈ P, ∃ u ∈ K, t = s + u) → Φ ∈ waveSpan χ X Y L := by
  classical
  refine Finset.induction_on P ?_ ?_
  · intro Φ _ _ hP
    have hz : Φ = 0 := by
      funext t
      by_contra ht
      obtain ⟨s, hs, -⟩ := hP t ht
      simp at hs
    rw [hz]
    exact zero_mem _
  · intro s P0 hsP0 ih Φ hΦX hinv hP
    by_cases hex : ∃ u ∈ K, Φ (s + u) ≠ 0
    · obtain ⟨u0, hu0, hw⟩ := hex
      have hwX : s + u0 ∈ X := hΦX _ hw

      have hconst : ∀ t, t + -(s + u0) ∈ K → Φ t = Φ (s + u0) := by
        intro t ht
        have h1 := hinv _ ht (s + u0)
        rwa [show s + u0 + (t + -(s + u0)) = t by abel] at h1
      have hΨeq : ∀ t, Φ t - Φ (s + u0) * ind K (t + -(s + u0)) =
          if t + -(s + u0) ∈ K then 0 else Φ t := by
        intro t
        by_cases ht : t + -(s + u0) ∈ K
        · rw [if_pos ht, hconst t ht]
          unfold ind
          rw [if_pos ht, mul_one, sub_self]
        · rw [if_neg ht]
          unfold ind
          rw [if_neg ht, mul_zero, sub_zero]
      have hΨ : (fun t => Φ t - Φ (s + u0) * ind K (t + -(s + u0))) ∈ waveSpan χ X Y L := by
        refine ih _ ?_ ?_ ?_
        · intro t ht
          rw [hΨeq] at ht
          split_ifs at ht with h1
          · exact absurd rfl ht
          · exact hΦX t ht
        · intro u hu t
          simp only [hΨeq]
          have hiff : t + u + -(s + u0) ∈ K ↔ t + -(s + u0) ∈ K := by
            rw [show t + u + -(s + u0) = t + -(s + u0) + u by abel]
            exact K.add_mem_cancel_right hu
          rw [if_congr hiff rfl (hinv u hu t)]
        · intro t ht
          rw [hΨeq] at ht
          split_ifs at ht with h1
          · exact absurd rfl ht
          · obtain ⟨s', hs', u, hu, rfl⟩ := hP _ ht
            rcases Finset.mem_insert.mp hs' with rfl | hs'0
            · exact absurd (by
                rw [show s' + u + -(s' + u0) = u + -u0 by abel]
                exact K.add_mem hu (K.neg_mem hu0)) h1
            · exact ⟨s', hs'0, u, hu, rfl⟩
      have htr := trans_mem hK (X.neg_mem hwX)
      have hsum := add_mem hΨ (Submodule.smul_mem _ (Φ (s + u0)) htr)
      convert hsum using 1
      funext t
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · push Not at hex
      refine ih Φ hΦX hinv fun t ht => ?_
      obtain ⟨s', hs', u, hu, rfl⟩ := hP t ht
      rcases Finset.mem_insert.mp hs' with rfl | hs'0
      · exact absurd (hex u hu) ht
      · exact ⟨s', hs'0, u, hu, rfl⟩
end GlobalTheory.PlaceModel
