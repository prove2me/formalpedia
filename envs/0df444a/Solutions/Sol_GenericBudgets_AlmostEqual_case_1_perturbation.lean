-- Prove2me | solution 1 for GenericBudgets.AlmostEqual.case_1_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:58:43.189237+00:00
-- url     : https://prove2.me/submissions/cd24a2fd-95e2-4744-828d-c3ca4b71f8fb

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

open GenericBudgets.AlmostEqual in
theorem solution {m : ℕ} (v : Fin 2 → Finset (Fin m) → ℝ)
    (σ : Fin m → Fin 2) (p : Fin m → ℝ) (hCE : IsCE v (fun _ => 1 / 2) σ p) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      IsCE v ![(1 / 2 + ε) / (1 + ε), 1 - (1 / 2 + ε) / (1 + ε)] σ (fun j => p j / (1 + ε)) := by
  obtain ⟨hp0, hD⟩ := hCE
  set F := Finset.univ.filter (fun T : Finset (Fin m) => v 0 (bundle σ 0) < v 0 T) with hF
  have hpos : ∀ T ∈ F, 0 < price p T - 1 / 2 := fun T hT => by
    have : (1 / 2 : ℝ) < price p T := (hD 0).2 T (Finset.mem_filter.1 hT).2
    linarith
  refine ⟨if h : F.Nonempty then F.inf' h (fun T => price p T - 1 / 2) else 1, ?_, ?_⟩
  · split_ifs with h
    · exact (Finset.lt_inf'_iff h).2 hpos
    · norm_num
  · intro ε hε hεδ
    have h1ε : 0 < 1 + ε := by linarith
    have hprice : ∀ S, price (fun j => p j / (1 + ε)) S = price p S / (1 + ε) := fun S => by
      unfold price; rw [Finset.sum_div]
    refine ⟨fun j => div_nonneg (hp0 j) h1ε.le, fun i => ?_⟩
    fin_cases i
    · show IsDemanded (v 0) ((1 / 2 + ε) / (1 + ε)) (fun j => p j / (1 + ε)) (bundle σ 0)
      have hA : price p (bundle σ 0) ≤ 1 / 2 := (hD 0).1
      constructor
      · rw [hprice, div_le_div_iff_of_pos_right h1ε]; linarith
      · intro T hT
        have hTF : T ∈ F := Finset.mem_filter.2 ⟨Finset.mem_univ _, hT⟩
        have hne : F.Nonempty := ⟨T, hTF⟩
        rw [dif_pos hne] at hεδ
        have := Finset.inf'_le (fun T => price p T - 1 / 2) hTF
        rw [hprice, div_lt_div_iff_of_pos_right h1ε]
        linarith
    · show IsDemanded (v 1) (1 - (1 / 2 + ε) / (1 + ε)) (fun j => p j / (1 + ε)) (bundle σ 1)
      have hb1 : 1 - (1 / 2 + ε) / (1 + ε) = (1 / 2) / (1 + ε) := by field_simp; ring
      rw [hb1]
      have hA : price p (bundle σ 1) ≤ 1 / 2 := (hD 1).1
      constructor
      · rw [hprice, div_le_div_iff_of_pos_right h1ε]; exact hA
      · intro T hT
        have : (1 / 2 : ℝ) < price p T := (hD 1).2 T hT
        rw [hprice, div_lt_div_iff_of_pos_right h1ε]
        exact this
