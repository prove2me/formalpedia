-- Prove2me | solution 1 for GlobalTheory.CharSeriesCoef.exists_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:26:25.462921+00:00
-- url     : https://prove2.me/submissions/9cc67b65-a99c-4f10-a45b-ad84cd51c121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousAtCharSeriesCoefZero
import Theorems.Thm_GlobalTheory_CharSeriesCoef_norm_avg_le_one_of
import Theorems.Thm_GlobalTheory_CharSeriesCoef_avg_prod
import Theorems.Thm_GlobalTheory_CharSeriesCoef_geom_avg_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CharSeriesCoef
namespace GlobalTheory.CharSeriesCoef
theorem _root_.solution {Y Ξ : Type} [AddCommGroup Y] [Zero Ξ] (e : Ξ → AddChar Y ℂ)
    (hn : ∀ a y, ‖e a y‖ = 1) (hne : ∀ a, a ≠ 0 → ∃ y, e a y ≠ 1)
    (δ : ℝ) (hδ : 0 < δ) (T : Finset Ξ) (h0 : (0:Ξ) ∉ T) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (w : ι → Y),
      ∀ b ∈ T, ‖avg w (e b)‖ ≤ δ := by
  classical
  revert h0
  refine Finset.induction_on T ?_ ?_
  · intro _
    exact ⟨Unit, inferInstance, inferInstance, fun _ => 0, by simp⟩
  · intro a T ha ih h0
    have ha0 : a ≠ 0 := fun h => h0 (by simp [h])
    have hT0 : (0:Ξ) ∉ T := fun h => h0 (Finset.mem_insert_of_mem h)
    obtain ⟨ι, _, _, w, hw⟩ := ih hT0
    obtain ⟨y, hy⟩ := hne a ha0
    have hz : 0 < ‖e a y - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy)
    obtain ⟨K, hK⟩ := exists_nat_gt (2 / (δ * ‖e a y - 1‖))
    have hK0 : (0:ℝ) < K := lt_trans (by positivity) hK
    have hKn : 0 < K := by exact_mod_cast hK0
    haveI : Nonempty (Fin K) := ⟨⟨0, hKn⟩⟩
    refine ⟨ι × Fin K, inferInstance, inferInstance,
      fun ik => w ik.1 + (ik.2 : ℕ) • y, ?_⟩
    intro b hb
    rw [avg_prod, norm_mul]
    have hA : ‖avg w (e b)‖ ≤ 1 := norm_avg_le_one_of _ (fun i => (hn b _).le)
    have hG : ‖(K:ℂ)⁻¹ * ∑ k : Fin K, e b y ^ (k:ℕ)‖ ≤ 1 := by
      have := norm_avg_le_one_of (ι := Fin K) (fun k => e b y ^ (k:ℕ))
        (fun k => by rw [norm_pow, hn]; simp)
      simpa using this
    rcases Finset.mem_insert.mp hb with rfl | hbT
    · have hg := geom_avg_le hy (hn b y) K hKn
      have : 2 / (K * ‖e b y - 1‖) ≤ δ := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ (by positivity)] at hK
        nlinarith
      calc ‖avg w (e b)‖ * ‖(K:ℂ)⁻¹ * ∑ k : Fin K, e b y ^ (k:ℕ)‖ ≤ 1 * δ := by
            gcongr
            exact hg.trans this
        _ = δ := one_mul δ
    · calc ‖avg w (e b)‖ * ‖(K:ℂ)⁻¹ * ∑ k : Fin K, e b y ^ (k:ℕ)‖ ≤ δ * 1 := by
            gcongr
            exact hw b hbT
        _ = δ := mul_one δ
end GlobalTheory.CharSeriesCoef
