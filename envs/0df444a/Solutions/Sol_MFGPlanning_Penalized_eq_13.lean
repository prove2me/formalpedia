-- Prove2me | solution 1 for MFGPlanning.Penalized.eq_13
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T14:58:08.350984+00:00
-- url     : https://prove2.me/submissions/1e12ec75-4d27-4d65-a775-8db47c3dc9d9

import Mathlib
import Definitions.Def_MFGPlanning_Penalized_Grid
import Definitions.Def_MFGPlanning_Penalized_Hyp

namespace MFGPlanning.Penalized.Eq13Aux

open MFGPlanning.Penalized

theorem dh0 (d : Data) (U : Pt d → ℝ) (p : Pt d) : Dh d U p 0 = D1 d U p := by
  simp [Dh]

theorem dh1 (d : Data) (U : Pt d → ℝ) (p : Pt d) :
    Dh d U (p.1 + 1, p.2) 1 = D1 d U p := by
  simp [Dh]

theorem dh2 (d : Data) (U : Pt d → ℝ) (p : Pt d) : Dh d U p 2 = D2 d U p := by
  simp [Dh]

theorem dh3 (d : Data) (U : Pt d → ℝ) (p : Pt d) :
    Dh d U (p.1, p.2 + 1) 3 = D2 d U p := by
  simp [Dh]

theorem caseD1 (d : Data) (R L0 L1 S : ℝ)
    (h0 : ∀ (p : Pt d) (q : Fin 4 → ℝ), q 0 ≤ -L0 → R * |q 0| ≤ d.g p q)
    (h1 : ∀ (p : Pt d) (q : Fin 4 → ℝ), L1 ≤ q 1 → R * q 1 ≤ d.g p q)
    (U : Pt d → ℝ) (p : Pt d) (hS : |D1 d U p| = S) (hL0 : L0 ≤ S) (hL1 : L1 ≤ S) :
    ∃ p' : Pt d, R * S ≤ d.g p' (Dh d U p') := by
  rcases le_or_gt (D1 d U p) 0 with hv | hv
  · refine ⟨p, ?_⟩
    have habs : |D1 d U p| = - D1 d U p := abs_of_nonpos hv
    have := h0 p (Dh d U p) (by rw [dh0]; linarith)
    rw [dh0, hS] at this
    exact this
  · refine ⟨(p.1 + 1, p.2), ?_⟩
    have habs : |D1 d U p| = D1 d U p := abs_of_pos hv
    have := h1 (p.1 + 1, p.2) (Dh d U (p.1 + 1, p.2)) (by rw [dh1]; linarith)
    rw [dh1, ← habs, hS] at this
    exact this

theorem caseD2 (d : Data) (R L2 L3 S : ℝ)
    (h2 : ∀ (p : Pt d) (q : Fin 4 → ℝ), q 2 ≤ -L2 → R * |q 2| ≤ d.g p q)
    (h3 : ∀ (p : Pt d) (q : Fin 4 → ℝ), L3 ≤ q 3 → R * |q 3| ≤ d.g p q)
    (U : Pt d → ℝ) (p : Pt d) (hS : |D2 d U p| = S) (hL2 : L2 ≤ S) (hL3 : L3 ≤ S) :
    ∃ p' : Pt d, R * S ≤ d.g p' (Dh d U p') := by
  rcases le_or_gt (D2 d U p) 0 with hv | hv
  · refine ⟨p, ?_⟩
    have habs : |D2 d U p| = - D2 d U p := abs_of_nonpos hv
    have := h2 p (Dh d U p) (by rw [dh2]; linarith)
    rw [dh2, hS] at this
    exact this
  · refine ⟨(p.1, p.2 + 1), ?_⟩
    have habs : |D2 d U p| = D2 d U p := abs_of_pos hv
    have := h3 (p.1, p.2 + 1) (Dh d U (p.1, p.2 + 1)) (by rw [dh3]; linarith)
    rw [dh3, hS] at this
    exact this

theorem dh1' (d : Data) (U : Pt d → ℝ) (p : Pt d) :
    Dh d U p 1 = D1 d U (p.1 - 1, p.2) := by
  simp [Dh]

theorem dh3' (d : Data) (U : Pt d → ℝ) (p : Pt d) :
    Dh d U p 3 = D2 d U (p.1, p.2 - 1) := by
  simp [Dh]

end MFGPlanning.Penalized.Eq13Aux

open MFGPlanning.Penalized in
theorem solution (d : Data) (hG5 : G5 d) :
    ∀ R : ℝ, ∃ L : ℝ, ∀ U : Pt d → ℝ, L ≤ supNormDh d U →
      ∃ p : Pt d, R * supNormDh d U ≤ d.g p (Dh d U p) := by
  intro R
  obtain ⟨⟨L0, h0⟩, ⟨L1, h1⟩, ⟨L2, h2⟩, ⟨L3, h3⟩⟩ :=
    And.intro (hG5.1 R) (And.intro (hG5.2.1 R) (And.intro (hG5.2.2.1 R) (hG5.2.2.2 R)))
  refine ⟨max (max L0 L1) (max L2 L3), ?_⟩
  intro U hL
  have hL0 : L0 ≤ supNormDh d U := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL1 : L1 ≤ supNormDh d U := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL2 : L2 ≤ supNormDh d U := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hL3 : L3 ≤ supNormDh d U := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Pt d × Fin 4))
    (fun x : Pt d × Fin 4 => |Dh d U x.1 x.2|)
  have hS : supNormDh d U = |Dh d U x.1 x.2| := hx
  obtain ⟨p, k⟩ := x
  simp only at hS
  fin_cases k
  · exact Eq13Aux.caseD1 d R L0 L1 _ h0 h1 U p (by rw [hS]; rfl) hL0 hL1
  · exact Eq13Aux.caseD1 d R L0 L1 _ h0 h1 U (p.1 - 1, p.2) (by rw [hS]; rfl) hL0 hL1
  · exact Eq13Aux.caseD2 d R L2 L3 _ h2 h3 U p (by rw [hS]; rfl) hL2 hL3
  · exact Eq13Aux.caseD2 d R L2 L3 _ h2 h3 U (p.1, p.2 - 1) (by rw [hS]; rfl) hL2 hL3
