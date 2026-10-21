-- Prove2me | solution 1 for ModernOnlineLearning.Adaptive.implicit_bound
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T17:02:42.844997+00:00
-- url     : https://prove2.me/submissions/0a918624-34cc-467d-a279-ea87f8fcb542

import Definitions.Def_ModernOnlineLearning_Adaptive_Defs
import Theorems.Thm_ModernOnlineLearning_Adaptive_theorem_4_14

set_option autoImplicit false
open scoped BigOperators
open ModernOnlineLearning.Adaptive

private lemma run_mem {d : ℕ} (V : Set (Vec d)) (ℓ : ℕ → Vec d → ℝ)
    (D : ℝ) (T : ℕ) (x g : ℕ → Vec d) (hrun : IsAdaptiveOSDRun V ℓ D T x g) :
    ∀ n, n ≤ T → x (n + 1) ∈ V := by
  intro n
  induction n with
  | zero => intro _; exact hrun.2.2.2.2.2.1
  | succ n ih =>
    intro hn
    have ht : n + 1 ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨by omega, hn⟩
    have hs := hrun.2.2.2.2.2.2 (n + 1) ht
    by_cases hg : g (n + 1) = 0
    · rw [hs.2.2.1 hg]
      exact ih (by omega)
    · exact (hs.2.2.2 hg).1

theorem solution {d : ℕ} (V : Set (Vec d)) (ℓ : ℕ → Vec d → ℝ)
    (D s : ℝ) (T : ℕ) (x g : ℕ → Vec d)
    (hT : 1 ≤ T) (hs : 0 ≤ s) (hVne : V.Nonempty)
    (hVclosed : IsClosed V) (hVconv : Convex ℝ V)
    (hdiam : ∀ a ∈ V, ∀ b ∈ V, ‖a - b‖ ≤ D)
    (hconv : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ Set.univ (ℓ t))
    (hnonneg : ∀ t ∈ Finset.Icc 1 T, ∀ z : Vec d, 0 ≤ ℓ t z)
    (hself : ∀ t ∈ Finset.Icc 1 T, IsSelfBounded V s (ℓ t))
    (hrun : IsAdaptiveOSDRun V ℓ D T x g) :
    ∀ u ∈ V, regret ℓ x u T ≤
      2 * D * Real.sqrt (s * (∑ t ∈ Finset.Icc 1 T, ℓ t (x t))) := by
  have hD : 0 < D := hrun.2.2.2.1
  have henergy : gradientEnergy g T ≤ 2 * s * ∑ t ∈ Finset.Icc 1 T, ℓ t (x t) := by
    rw [gradientEnergy, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    have ht' := Finset.mem_Icc.mp ht
    have hxt : x t ∈ V := by
      have hm := run_mem V ℓ D T x g hrun (t - 1) (by omega)
      simpa [Nat.sub_add_cancel ht'.1] using hm
    have hinf : 0 ≤ sInf (Set.range (ℓ t)) := by
      apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨z, rfl⟩
      exact hnonneg t ht z
    have h := (hself t ht).2.2 (x t) hxt (g t) (hrun.2.2.2.2.2.2 t ht).2.1
    nlinarith [mul_nonneg hs hinf]
  intro u hu
  have hreg := (ModernOnlineLearning.Adaptive.theorem_4_14 V ℓ D T x g hT
    hVne hVclosed hVconv hdiam hconv hrun).1 u hu
  calc
    regret ℓ x u T ≤ D * Real.sqrt (2 * gradientEnergy g T) := hreg
    _ ≤ D * Real.sqrt (4 * (s * (∑ t ∈ Finset.Icc 1 T, ℓ t (x t)))) := by
      apply mul_le_mul_of_nonneg_left _ hD.le
      apply Real.sqrt_le_sqrt
      nlinarith
    _ = 2 * D * Real.sqrt (s * (∑ t ∈ Finset.Icc 1 T, ℓ t (x t))) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
      ring

