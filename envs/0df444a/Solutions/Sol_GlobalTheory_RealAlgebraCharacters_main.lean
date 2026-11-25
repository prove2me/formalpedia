-- Prove2me | solution 1 for GlobalTheory.RealAlgebraCharacters.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:07:43.823492+00:00
-- url     : https://prove2.me/submissions/270ab85a-119f-4218-88e1-2d9a721b2d94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealAlgSep
import Theorems.Thm_GlobalTheory_RealAlgebraCharacters_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RealAlgebraCharacters
open Filter Topology
namespace GlobalTheory.RealAlgebraCharacters
theorem _root_.solution {X : Type} [PseudoMetricSpace X] [ProperSpace X] (x₀ : X) {B : Type}
    [AddCommGroup B] (χ : B → X → ℂ) (hc : ∀ b, Continuous (χ b))
    (hadd : ∀ (a b : B) (x : X), χ (a + b) x = χ a x * χ b x)
    (h0 : ∀ x, χ 0 x = 1) (hn : ∀ (a : B) (x : X), ‖χ a x‖ = 1)
    (hs : ∀ x y : X, x ≠ y → ∃ b, χ b x ≠ χ b y) (β : X → ℝ) (hβ : Continuous β)
    (hβ1 : ∀ u, 0 ≤ β u ∧ β u ≤ 1) :
    ∃ (s : ℕ → Finset B) (c : ℕ → B → ℂ),
      (∀ (n : ℕ) (x : X), ‖∑ b ∈ s n, c n b * χ b x‖ ≤ 2) ∧
      ∀ x : X, Tendsto (fun n : ℕ => ∑ b ∈ s n, c n b * χ b x) atTop (𝓝 (β x : ℂ)) := by
  have key : ∀ n : ℕ, ∃ (s : Finset B) (c : B → ℂ), (∀ x, ‖∑ b ∈ s, c b * χ b x‖ ≤ 2) ∧
      ∀ x ∈ Metric.closedBall x₀ (n : ℝ),
        ‖∑ b ∈ s, c b * χ b x - (β x : ℂ)‖ ≤ 2 * (1 / ((n : ℝ) + 1)) := by
    intro n
    refine step χ hc hadd h0 hn hs β hβ hβ1 (isCompact_closedBall x₀ n)
      Nat.one_div_pos_of_nat ?_
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  choose s c h1 h2 using key
  refine ⟨s, c, h1, fun x => ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (dist x x₀)]
    with n hn'
  exact h2 n x hn'
end GlobalTheory.RealAlgebraCharacters
