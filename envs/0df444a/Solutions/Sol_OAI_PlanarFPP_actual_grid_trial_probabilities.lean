-- Prove2me | solution 1 for OAI.PlanarFPP.actual_grid_trial_probabilities
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:42:11.162313+00:00
-- url     : https://prove2.me/submissions/29856e06-8e3c-4d30-8b7a-e1f068bf59a7

import Mathlib
import Definitions.Def_PlanarFirstPassage
import Definitions.Def_OAISPf002
import Theorems.Thm_OAI_PlanarFPP_exponential_characteristic_lengths_exist
import Theorems.Thm_OAI_PlanarFPP_exponential_characteristic_lengths_ratio

section
-- module Solutions.OAIS_PlanarFPP.Compat
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CharacteristicLengths
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology

theorem firstDyadicExponent_le (p : ℕ → ℝ) (q : ℝ) (j : ℕ) (hj : p j ≤ q) :
    firstDyadicExponent p q ≤ j := by
  have h : ∃ j, p j ≤ q := ⟨j,hj⟩
  simpa only [firstDyadicExponent,dite_eq_left h] using Nat.find_min' h hj

theorem firstDyadicExponent_min (p : ℕ → ℝ) (q : ℝ) (j : ℕ)
    (hj : j < firstDyadicExponent p q) : q < p j := by
  by_contra hh
  exact (not_le_of_gt hj) (firstDyadicExponent_le p q j (le_of_not_gt hh))

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (τ : Edge → Ω → ℝ)

variable {P τ}

theorem characteristicLength_minimal (μ : Plane → ℝ) (b q : ℝ) (k j : ℕ)
    (hj : (2 : ℤ)^j < characteristicLength P τ μ b q k) :
    q < sourceDyadicCrossingProbability P τ μ b k j := by
  have hj' : j < characteristicExponent P τ μ b q k := by
    by_contra hh
    have he := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (le_of_not_gt hh)
    exact (not_le_of_gt hj) he
  exact firstDyadicExponent_min _ _ _ hj'

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridMeshes
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter Set MeasureTheory
open scoped Topology

lemma gridMesh_pos (m j : ℕ) : 0 < gridMesh m j := by unfold gridMesh; positivity

lemma gridMesh_level_bound (m k j : ℕ) (hm : m ≤ 3*k) (hj : j ≤ gridLastLevel m) :
    4*(k-j)+3 ≥ k := by
  unfold gridLastLevel at hj
  omega

lemma gridMesh_below_record_length (L : ℕ → ℤ) (k m j : ℕ)
    (hL : L k=(2 : ℤ)^m)
    (hrec : (1/16 : ℝ)^j*(L k : ℝ) ≤ (L (k-j) : ℝ))
    (hunit : 1 < L (k-j)) : gridMesh m j < L (k-j) := by
  by_cases hsmall : m ≤ 4*j+1
  · simpa [gridMesh,gridMeshExponent,Nat.sub_eq_zero_of_le hsmall] using hunit
  · have he : m=gridMeshExponent m j+(4*j+1) := by unfold gridMeshExponent; omega
    have hr : (1/16 : ℝ)^j*((2 : ℤ)^m : ℝ) = 2*(gridMesh m j : ℝ) := by
      simp only [Int.cast_pow,Int.cast_ofNat,gridMesh]
      conv_lhs => rw [he,pow_add]
      rw [pow_add,pow_one,show (2 : ℝ)^(4*j)=(16 : ℝ)^j by rw [pow_mul]; norm_num]
      have hh : (1/16 : ℝ)^j*16^j=1 := by rw [← mul_pow]; norm_num
      calc
        _ = (2 : ℝ)^gridMeshExponent m j*((1/16 : ℝ)^j*16^j)*2 := by ring
        _ = _ := by rw [hh]; ring
    rw [hL] at hrec
    simp only [Int.cast_pow,Int.cast_ofNat] at hrec hr
    rw [hr] at hrec
    have hp : (0 : ℝ) < gridMesh m j := by exact_mod_cast gridMesh_pos m j
    exact_mod_cast (show (gridMesh m j : ℝ) < L (k-j) by linarith)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem actual_grid_trial_probabilities_oai (henv : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b q₀ : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) :
    ∀ᶠ k : ℕ in atTop, ∀ j : ℕ,
      j ≤ gridLastLevel (characteristicExponent P τ μ b q₀ k) →
      ((1/16 : ℝ)^j*(characteristicLength P τ μ b q₀ k : ℝ) ≤
        (characteristicLength P τ μ b q₀ (k-j) : ℝ)) →
      q₀ < P.real {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b))
        (sourceCrossingK μ b) (gridWidth k j) (gridMesh (characteristicExponent P τ μ b q₀ k) j) 0} := by
  have hlarge := (exponential_characteristic_lengths_ratio henv μ hμ ht b q₀ hb hq hq1).eventually
    (eventually_gt_atTop (1 : ℝ))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hlarge
  filter_upwards [eventually_ge_atTop (4*N+4),
    exponential_characteristic_lengths_exist henv μ hμ ht b q₀ hb hq] with k hk hex
  intro j hj hrec
  have hlev := gridMesh_level_bound (characteristicExponent P τ μ b q₀ k) k j hex.1 hj
  have hjk : j ≤ k := by unfold gridLastLevel at hj; omega
  have hNk : N ≤ k-j := by omega
  have hunit : 1 < characteristicLength P τ μ b q₀ (k-j) := by
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2^(k-j))).mp (hN (k-j) hNk)
    have hp : (1 : ℝ) ≤ 2^(k-j) := one_le_pow₀ (by norm_num)
    exact_mod_cast (show (1 : ℝ) < characteristicLength P τ μ b q₀ (k-j) by linarith)
  have hmesh := gridMesh_below_record_length (characteristicLength P τ μ b q₀) k
    (characteristicExponent P τ μ b q₀ k) j rfl hrec hunit
  have hp := characteristicLength_minimal μ b q₀ (k-j)
    (gridMeshExponent (characteristicExponent P τ μ b q₀ k) j) hmesh
  simpa only [sourceDyadicCrossingProbability,gridWidth,gridMesh,Int.cast_pow,Int.cast_ofNat] using hp

end PlanarFPP

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PlanarFPP.actual_grid_trial_probabilities_oai.{u_1} := @OAI.PlanarFPP.actual_grid_trial_probabilities_oai.{u_1}
