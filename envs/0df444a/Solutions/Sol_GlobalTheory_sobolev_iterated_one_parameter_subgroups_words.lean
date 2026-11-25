-- Prove2me | solution 1 for GlobalTheory.sobolev_iterated_one_parameter_subgroups_words
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:56:51.305892+00:00
-- url     : https://prove2.me/submissions/ed2ec569-f630-4560-8506-8f6e606990b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SobolevIteratedOneParameterSubgroups
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SobolevIteratedOneParameterSubgroupsWords
import Theorems.Thm_GlobalTheory_sobolev_iterated_one_parameter_subgroups


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : ℕ) (c : Fin N → ℝ → G) (s : ℝ), 0 < s → (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) → ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : List (Fin N) → G → ℂ), (∀ l, Continuous (F l)) → (∀ l i x, HasDerivAt (fun t => F l (x * c i t)) (F (i :: l) x) 0) → ∀ (y : G) (M : ℝ), (∀ l : List (Fin N), l.length ≤ N → ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖F l (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2 ≤ M) → ‖F [] y‖ ^ 2 ≤ C * M := by
  intro G _ _ _ N c s hs hc
  obtain ⟨enc, hinj, h1, h2⟩ : ∃ enc : List (Fin N) → ℝ, Function.Injective enc ∧
      (∀ l, 1 ≤ ‖enc l‖) ∧ ∀ l, ‖enc l‖ ≤ 2 := by
    have hpos : ∀ l : List (Fin N), (0 : ℝ) < 1 / ((Encodable.encode l : ℝ) + 1) := fun l => by
      positivity
    have hle : ∀ l : List (Fin N), 1 / ((Encodable.encode l : ℝ) + 1) ≤ 1 := fun l => by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (Encodable.encode l : ℝ) := Nat.cast_nonneg _
      linarith
    refine ⟨fun l => 1 + 1 / ((Encodable.encode l : ℝ) + 1), ?_, fun l => ?_, fun l => ?_⟩
    · intro a b hab
      have h : (1 : ℝ) / ((Encodable.encode a : ℝ) + 1) = 1 / ((Encodable.encode b : ℝ) + 1) :=
        add_left_cancel hab
      rw [one_div, one_div, inv_inj, add_left_inj, Nat.cast_inj] at h
      exact Encodable.encode_injective h
    · have := hpos l
      rw [Real.norm_of_nonneg (by linarith)]
      linarith
    · have := hpos l
      have := hle l
      rw [Real.norm_of_nonneg (by linarith)]
      linarith
  have hdec : ∀ l, Function.invFun enc (enc l) = l := Function.leftInverse_invFun hinj
  have hK : 0 ≤ (2 / s + 2 * s * 2 ^ 2) ^ N := by positivity
  refine ⟨(2 / s + 2 * s * 2 ^ 2) ^ N * 4, by positivity, ?_⟩
  intro F hF hD y M hM
  have hM0 : 0 ≤ M :=
    le_trans (integral_nonneg fun t => by positivity) (hM [] (Nat.zero_le _))
  have main := sobolev_iterated_one_parameter_subgroups G ℝ ℂ N 0 c
    (fun p => enc '' {l | l.length ≤ p}) (fun i u => enc (i :: Function.invFun enc u))
    (fun u => F (Function.invFun enc u)) s 2 M y hs (by norm_num) hM0 hc
    (fun p q hpq => Set.image_mono fun l hl => le_trans hl hpq) ?_ ?_ ?_ (enc [])
    ⟨[], Nat.le_refl 0, rfl⟩
  · rw [hdec] at main
    have h4 : ‖enc []‖ ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (h2 _) 2
    calc _ ≤ _ := main
      _ ≤ (2 / s + 2 * s * 2 ^ 2) ^ N * M * 2 ^ 2 :=
        mul_le_mul_of_nonneg_left h4 (mul_nonneg hK hM0)
      _ = _ := by ring
  · rintro p _ ⟨l, hl, rfl⟩
    simp only [hdec]
    exact ⟨hF l, fun i => ⟨⟨i :: l, Nat.succ_le_succ hl, rfl⟩, hD l i⟩⟩
  · rintro p _ _ ⟨l, hl, rfl⟩ i
    have := h1 l
    have := h2 (i :: Function.invFun enc (enc l))
    linarith
  · rintro _ ⟨l, hl, rfl⟩
    simp only [hdec]
    have hl' : l.length ≤ N := by simpa using hl
    exact (hM l hl').trans (le_mul_of_one_le_right hM0 (one_le_pow₀ (h1 l)))
end GlobalTheory
