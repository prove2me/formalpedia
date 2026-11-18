-- Prove2me | solution 1 for IAFTRL.proposition_G_1_anc
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-17T13:49:37.689236+00:00
-- url     : https://prove2.me/submissions/eae3ceb1-ef84-4a45-a99a-dd8b53894591

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_GTerms
import Theorems.Thm_IAFTRL_lemma_G_master
import Theorems.Thm_IAFTRL_lemma_G_1
import Theorems.Thm_IAFTRL_lemma_G_4
import Theorems.Thm_IAFTRL_lemma_G_5
import Theorems.Thm_IAFTRL_lemma_G_9
import Theorems.Thm_IAFTRL_lemma_G_12

open MeasureTheory

namespace IAFTRL

lemma anc_atom_pos {d : ℕ} {ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {m : ℕ}
    (hm : m ∈ Jset ℬ e) {a : Fin d → ℝ} (ha : cand ℬ e m = a) : 0 < refMu ℬ e {a} := by
  classical
  have h1 : muDisc ℬ e {a} ≤ refMu ℬ e {a} := by
    unfold refMu; rw [Measure.add_apply]; exact le_self_add
  refine lt_of_lt_of_le ?_ h1
  unfold muDisc
  rw [Measure.sum_apply _ (measurableSet_singleton a)]
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum m)
  rw [if_pos hm, Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton a), ha]
  simp only [Set.indicator_of_mem (Set.mem_singleton a), Pi.one_apply, smul_eq_mul, mul_one]
  exact ENNReal.ofReal_pos.2 (Real.exp_pos _)

theorem _root_.solution {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (he : Function.Surjective e) (θ astar : Fin d → ℝ) (hθ : setNorm 𝒜 θ ≤ 1)
    (hastar : astar ∈ 𝒜) (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ)
    (hsharp : IsSharp 𝒜 θ astar) :
    ∃ J : ℝ, ∀ n : Measure (Fin d → ℝ), IsCtrAlloc ℬ θ astar n →
      ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (T : ℕ) (C : ℝ) (R : GRun d Ω), 1 ≤ T → 0 ≤ C →
        IsGIAFTRLRun P 𝒜 ℬ e T R → IsCorruptedG P 𝒜 θ C T R →
        gRegretVs P T R astar ≤
          16 * gB d * 64 ^ 4 * ctrCost θ astar n * Real.log (Real.exp 1 * T) + M +
            J * Real.sqrt C * Real.log (Real.exp 1 + C) := by
  obtain ⟨m, hm, hcand⟩ := lemma_G_12 𝒜 ℬ e h𝒜 hℬ hgen hball hspan he θ astar hastar huniq hsharp
  have hatom := anc_atom_pos hm hcand
  obtain ⟨M1, J1, h1⟩ := lemma_G_1 hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan hk he θ astar hθ hastar huniq
    hsharp
  obtain ⟨M4, J4, h4⟩ := lemma_G_4 hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan hk he θ astar hθ hastar huniq
    hsharp
  obtain ⟨J5, h5⟩ := lemma_G_5 hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan hk he θ astar hθ hastar huniq
    hsharp
  refine ⟨J1 + J4 + J5 + 32 * d, fun n hn => ?_⟩
  obtain ⟨M5, h5n⟩ := h5 n hn
  refine ⟨M1 + M4 + M5, ?_⟩
  intro Ω _ P _ T C R hT hC hR hcor
  have hmaster := lemma_G_master hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan hk P T R hT hR θ astar hatom
  have i1 := h1 P T C R hT hC hR hcor
  have i4 := h4 P T C R hT hC hR hcor
  have i5 := h5n P T C R hT hC hR hcor
  have i9 := lemma_G_9 hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan hk θ P T C R hT hC hR hcor
  have hL : 1 ≤ Real.log (Real.exp 1 + C) := by
    rw [Real.le_log_iff_exp_le (by positivity)]; linarith
  have hs : Real.sqrt C ≤ Real.sqrt C * Real.log (Real.exp 1 + C) :=
    le_mul_of_one_le_right (Real.sqrt_nonneg _) hL
  have hd0 : (0 : ℝ) ≤ 32 * d := by positivity
  have h9 : 32 * (d : ℝ) * Real.sqrt C ≤ 32 * d * (Real.sqrt C * Real.log (Real.exp 1 + C)) :=
    mul_le_mul_of_nonneg_left hs hd0
  nlinarith

end IAFTRL
