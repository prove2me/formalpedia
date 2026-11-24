-- Prove2me | solution 1 for GlobalTheory.WeilM.eventually_char_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:16:53.101649+00:00
-- url     : https://prove2.me/submissions/a80874e7-d777-4fc9-a622-e1f2762c30ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsLocallyConstantSplitOm
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_cball_mem_nhds
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_subset
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_eq_one_of_valuation_eq_one
import Theorems.Thm_GlobalTheory_WeilM_eq_one_of_forall_pow_near


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel Filter
open scoped NNReal Topology Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.WeilM
theorem _root_.solution (μ : Fˣ →* Circle) (hμ : Continuous μ) :
    ∀ᶠ t in 𝓝 (1 : Fˣ), μ t = 1 ∧ distribHaarChar F t = 1 := by
  have h0 : {t : Fˣ | ‖(μ t : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Fˣ) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨U, hU, hUV⟩ := h0
  have h1 : (fun x : F => 1 + x) ⁻¹' U ∈ 𝓝 (0 : F) :=
    (Continuous.tendsto' (by fun_prop) _ _ (by simp) : Tendsto (fun x : F => 1 + x) (𝓝 0) (𝓝 ((1 : Fˣ) : F))) hU
  have h2 : {x : F | valuation F x < 1} ∈ 𝓝 (0 : F) := (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun _ h => h⟩
  obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset (inter_mem h1 h2)
  have h3 : Tendsto (fun t : Fˣ => (t : F) - 1) (𝓝 1) (𝓝 0) := Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [h3.eventually (SplitWeil.cball_mem_nhds s)] with t ht
  have hv : valuation F (t : F) = 1 := by simpa using (valuation F).map_one_add_of_lt (hs ht).2
  have hn : ∀ n : ℕ, (t : F) ^ n - 1 ∈ SplitWeil.cball s := fun n => by
    induction n with
    | zero => simp [SplitWeil.cball]
    | succ n ih =>
      rw [show (t : F) ^ (n + 1) - 1 = t * (t ^ n - 1) + (t - 1) by ring]
      refine SplitWeil.add_mem_cball ?_ ht
      show valuation F ((t : F) * ((t : F) ^ n - 1)) ≤ valuation F (s : F)
      rw [map_mul, hv, one_mul]
      exact ih
  refine ⟨Circle.coe_eq_one.mp (eq_one_of_forall_pow_near fun n => ?_),
    NNReal.coe_injective (SplitWeil.nabs_eq_one_of_valuation_eq_one hv)⟩
  have : t ^ n ∈ Units.val ⁻¹' U := by simpa using (hs (hn n)).1
  simpa using hUV this
end GlobalTheory.WeilM
