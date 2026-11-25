-- Prove2me | solution 1 for GlobalTheory.HeckeSplitAll.Approx.strong_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:52:39.576858+00:00
-- url     : https://prove2.me/submissions/9a661760-e878-4f70-aabd-769555ee303a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFinsetNormOne
import Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_norm_alg_inf
import Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_norm_le_one_iff_int
import Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_norm_int_le_one
import Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_nat_ne_zero_fin
import Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_exists_int_near
import Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_exists_small_elt
import Theorems.Thm_PI_UnipApproxD_IntegersDenseFiniteAdeles_exists_approx_adele


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology Filter
open GlobalTheory GlobalTheory.HeckeSplitAll GlobalTheory.HeckeSplitAll.Approx
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeSplitAll.Approx
theorem _root_.solution (v₀ : HeightOneSpectrum (𝓞 F)) (t : InfiniteAdeleRing F) (s : FiniteAdeleRing (𝓞 F) F)
    (M : ℕ) (hM : M ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : F, c ≠ 0 ∧ (∀ w : InfinitePlace F, ‖algebraMap F w.Completion c - t w‖ < ε) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ →
        ‖algebraMap F (v.adicCompletion F) c - s v‖ ≤ ‖(M : v.adicCompletion F)‖ := by
  have hMF : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hMR : (0 : ℝ) < M := Nat.cast_pos.2 (Nat.pos_of_ne_zero hM)
  obtain ⟨u, hu⟩ := PI.UnipApproxD.IntegersDenseFiniteAdeles.exists_approx_adele
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (M : F)⁻¹ * s)
  obtain ⟨C, hC, hCt⟩ := exists_int_near F
  obtain ⟨x, hx0, hxw, hxv⟩ := exists_small_elt v₀ (ε / (M * (C + 1))) (by positivity)
  obtain ⟨o, ho⟩ := hCt fun w => (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x)
  have key : ∀ o' : 𝓞 F, (∀ w : InfinitePlace F, ‖algebraMap F w.Completion (o' : F) -
      (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x)‖ < C + 1) →
      (∀ w : InfinitePlace F, ‖algebraMap F w.Completion (M * u + M * x * o') - t w‖ < ε) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ →
        ‖algebraMap F (v.adicCompletion F) (M * u + M * x * o') - s v‖ ≤ ‖(M : v.adicCompletion F)‖ := by
    intro o' ho'
    refine ⟨fun w => ?_, fun v hv => ?_⟩
    · have h0 : algebraMap F w.Completion (M * x) ≠ 0 := (map_ne_zero _).2 (mul_ne_zero hMF hx0)
      have e : algebraMap F w.Completion (M * u + M * x * o') - t w = algebraMap F w.Completion (M * x) *
          (algebraMap F w.Completion (o' : F) -
            (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x)) := by
        rw [map_add, map_mul _ (M * x), mul_sub, mul_div_cancel₀ _ h0]; ring
      rw [e, norm_mul, norm_alg_inf, map_mul, InfinitePlace.map_natCast]
      calc _ ≤ (M * w x) * (C + 1) := mul_le_mul_of_nonneg_left (ho' w).le (by positivity)
        _ < (M * (ε / (M * (C + 1)))) * (C + 1) := by gcongr; exact hxw w
        _ = ε := by field_simp
    · have h0 := nat_ne_zero_fin v hM
      have hu' : ‖algebraMap F (v.adicCompletion F) (M : F)⁻¹ * s v - algebraMap F (v.adicCompletion F) u‖ ≤ 1 :=
        (norm_le_one_iff_int v _).2 (hu v)
      have e : algebraMap F (v.adicCompletion F) (M * u + M * x * o') - s v = (M : v.adicCompletion F) *
          (-(algebraMap F (v.adicCompletion F) (M : F)⁻¹ * s v - algebraMap F (v.adicCompletion F) u) +
            algebraMap F (v.adicCompletion F) x * algebraMap F (v.adicCompletion F) (o' : F)) := by
        simp only [map_add, map_mul, map_inv₀, map_natCast]
        field_simp
        ring
      rw [e, norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_))
      · rwa [norm_neg]
      · rw [norm_mul]; exact mul_le_one₀ (hxv v hv) (norm_nonneg _) (norm_int_le_one v o')
  by_cases hc : (M : F) * u + M * x * o = 0
  · refine ⟨M * u + M * x * (o + 1 : 𝓞 F), ?_, key (o + 1) fun w => ?_⟩
    · have : (M : F) * u + M * x * (o + 1 : 𝓞 F) = M * x := by push_cast; linear_combination hc
      rw [this]; exact mul_ne_zero hMF hx0
    · have h1 := norm_add_le (1 : w.Completion) (algebraMap F w.Completion (o : F) -
        (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x))
      have e : ((o + 1 : 𝓞 F) : F) = 1 + o := by push_cast; ring
      rw [e, map_add, map_one, add_sub_assoc]
      rw [norm_one] at h1
      linarith [ho w]
  · exact ⟨_, hc, key o fun w => (ho w).trans (lt_add_one C)⟩
end GlobalTheory.HeckeSplitAll.Approx
