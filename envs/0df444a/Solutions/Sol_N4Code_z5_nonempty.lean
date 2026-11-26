-- Prove2me | solution 1 for N4Code.z5_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:03.131098+00:00
-- url     : https://prove2.me/submissions/3bacb8ed-1642-4a56-8a4e-85769d059c55

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_hammingDist_row1_row2_eq
import Theorems.Thm_N4Code_count_pos_of_colVal
import Theorems.Thm_N4Code_z5_nonempty_of_table
import Theorems.Thm_N4Code_odd_of_not_even


set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C)
    (hcase :
      (Odd (count C 2) ∧ Odd (count C 3) ∧ Odd (count C 5) ∧ Even (count C 4)) ∨
        (Even (count C 2) ∧ Even (count C 3) ∧ Even (count C 5) ∧ Odd (count C 4)) ∨
        (Even (hammingDist (row1 C) (row2 C)) ∧
          ¬ (Even (count C 2) ∧ Even (count C 4) ∧ Odd (count C 3) ∧ Odd (count C 5)))) :
    ∃ y : Word n, Z5 C t₁ t₂ y := by
  have hc1 : 1 ≤ count C 1 := count_pos_of_colVal C t₁ (by rw [h1]; decide)
  have hc7 : 1 ≤ count C 7 := count_pos_of_colVal C t₂ (by rw [h7]; decide)
  rcases hcase with hcase | hcase | hcase
  · -- case 7: |2|,|3|,|5| odd, |4| even
    rcases hcase with ⟨h2o, h3o, h5o, h4e⟩
    rcases h2o with ⟨p2, hp2⟩
    rcases h3o with ⟨p3, hp3⟩
    rcases h4e with ⟨p4, hp4⟩
    rcases h5o with ⟨p5, hp5⟩
    refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 (p2 + 1) p3 p4 (p5 + 1)
      (count C 6) (count C 7 - 1) 1 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rfl
    · omega
    · omega
    · omega
    · omega
  · -- case 8: |2|,|3|,|5| even, |4| odd
    rcases hcase with ⟨h2e, h3e, h5e, h4o⟩
    rcases h2e with ⟨p2, hp2⟩
    rcases h3e with ⟨p3, hp3⟩
    rcases h4o with ⟨p4, hp4⟩
    rcases h5e with ⟨p5, hp5⟩
    refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 p3 (p4 + 1) p5
      (count C 6) (count C 7 - 1) 1 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rfl
    · omega
    · rw [hp2, hp3, hp4, hp5]
      omega
    · rw [hp2, hp3]
      omega
    · rw [hp2, hp5]
      omega
  · -- cases 9-15: w(c2⊕c3) even, not case 16
    rcases hcase with ⟨heven, hnot16⟩
    have heven' : Even (count C 2 + count C 3 + count C 4 + count C 5) := by
      rw [← hammingDist_row1_row2_eq C h07]
      exact heven
    by_cases h2e : Even (count C 2)
    · by_cases h3e : Even (count C 3)
      · by_cases h4e : Even (count C 4)
        · by_cases h5e : Even (count C 5)
          · -- case 9: all even
            rcases h2e with ⟨p2, hp2⟩
            rcases h3e with ⟨p3, hp3⟩
            rcases h4e with ⟨p4, hp4⟩
            rcases h5e with ⟨p5, hp5⟩
            refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 p3 p4 p5
              (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · rfl
            · omega
            · omega
            · omega
            · omega
          · -- (E,E,E,O): odd sum, impossible
            exfalso
            rcases heven' with ⟨m, hm⟩
            rcases h2e with ⟨a, ha⟩
            rcases h3e with ⟨b, hb⟩
            rcases h4e with ⟨c, hc⟩
            have h5o : Odd (count C 5) := odd_of_not_even h5e
            rcases h5o with ⟨d, hd⟩
            omega
        · by_cases h5e : Even (count C 5)
          · -- (E,E,O,E): odd sum, impossible
            exfalso
            rcases heven' with ⟨m, hm⟩
            rcases h2e with ⟨a, ha⟩
            rcases h3e with ⟨b, hb⟩
            have h4o : Odd (count C 4) := odd_of_not_even h4e
            rcases h4o with ⟨c, hc⟩
            rcases h5e with ⟨d, hd⟩
            omega
          · -- case 14: (E,E,O,O), |4|,|5| odd
            rcases h2e with ⟨p2, hp2⟩
            rcases h3e with ⟨p3, hp3⟩
            have h4o : Odd (count C 4) := odd_of_not_even h4e
            rcases h4o with ⟨p4, hp4⟩
            have h5o : Odd (count C 5) := odd_of_not_even h5e
            rcases h5o with ⟨p5, hp5⟩
            refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 p3 (p4 + 1) p5
              (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · rfl
            · omega
            · omega
            · omega
            · omega
      · by_cases h4e : Even (count C 4)
        · by_cases h5e : Even (count C 5)
          · -- (E,O,E,E): odd sum, impossible
            exfalso
            rcases heven' with ⟨m, hm⟩
            rcases h2e with ⟨a, ha⟩
            have h3o : Odd (count C 3) := odd_of_not_even h3e
            rcases h3o with ⟨b, hb⟩
            rcases h4e with ⟨c, hc⟩
            rcases h5e with ⟨d, hd⟩
            omega
          · -- case 16: (E,O,E,O), excluded
            exfalso
            exact hnot16 ⟨h2e, h4e, odd_of_not_even h3e, odd_of_not_even h5e⟩
        · by_cases h5e : Even (count C 5)
          · -- case 12: (E,O,O,E)
            rcases h2e with ⟨p2, hp2⟩
            have h3o : Odd (count C 3) := odd_of_not_even h3e
            rcases h3o with ⟨p3, hp3⟩
            have h4o : Odd (count C 4) := odd_of_not_even h4e
            rcases h4o with ⟨p4, hp4⟩
            rcases h5e with ⟨p5, hp5⟩
            refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 (p3 + 1) (p4 + 1) p5
              (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · rfl
            · omega
            · omega
            · omega
            · omega
          · -- (E,O,O,O): odd sum, impossible
            exfalso
            rcases heven' with ⟨m, hm⟩
            rcases h2e with ⟨a, ha⟩
            have h3o : Odd (count C 3) := odd_of_not_even h3e
            rcases h3o with ⟨b, hb⟩
            have h4o : Odd (count C 4) := odd_of_not_even h4e
            rcases h4o with ⟨c, hc⟩
            have h5o : Odd (count C 5) := odd_of_not_even h5e
            rcases h5o with ⟨d, hd⟩
            omega
    · by_cases h3e : Even (count C 3)
      · by_cases h4e : Even (count C 4)
        · by_cases h5e : Even (count C 5)
          · -- (O,E,E,E): odd sum, impossible
            exfalso
            rcases heven' with ⟨m, hm⟩
            have h2o : Odd (count C 2) := odd_of_not_even h2e
            rcases h2o with ⟨a, ha⟩
            rcases h3e with ⟨b, hb⟩
            rcases h4e with ⟨c, hc⟩
            rcases h5e with ⟨d, hd⟩
            omega
          · -- case 11: (O,E,E,O)
            have h2o : Odd (count C 2) := odd_of_not_even h2e
            rcases h2o with ⟨p2, hp2⟩
            rcases h3e with ⟨p3, hp3⟩
            rcases h4e with ⟨p4, hp4⟩
            have h5o : Odd (count C 5) := odd_of_not_even h5e
            rcases h5o with ⟨p5, hp5⟩
            refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 (p2 + 1) p3 p4 (p5 + 1)
              (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · rfl
            · omega
            · omega
            · omega
            · omega
        · by_cases h5e : Even (count C 5)
          · -- case 13: (O,E,O,E)
            have h2o : Odd (count C 2) := odd_of_not_even h2e
            rcases h2o with ⟨p2, hp2⟩
            rcases h3e with ⟨p3, hp3⟩
            have h4o : Odd (count C 4) := odd_of_not_even h4e
            rcases h4o with ⟨p4, hp4⟩
            rcases h5e with ⟨p5, hp5⟩
            refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 (p2 + 1) p3 (p4 + 1) p5
              (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · rfl
            · omega
            · omega
            · omega
            · omega
          · -- (O,E,O,O): odd sum, impossible
            exfalso
            rcases heven' with ⟨m, hm⟩
            have h2o : Odd (count C 2) := odd_of_not_even h2e
            rcases h2o with ⟨a, ha⟩
            rcases h3e with ⟨b, hb⟩
            have h4o : Odd (count C 4) := odd_of_not_even h4e
            rcases h4o with ⟨c, hc⟩
            have h5o : Odd (count C 5) := odd_of_not_even h5e
            rcases h5o with ⟨d, hd⟩
            omega
      · by_cases h4e : Even (count C 4)
        · by_cases h5e : Even (count C 5)
          · -- case 10: (O,O,E,E)
            have h2o : Odd (count C 2) := odd_of_not_even h2e
            rcases h2o with ⟨p2, hp2⟩
            have h3o : Odd (count C 3) := odd_of_not_even h3e
            rcases h3o with ⟨p3, hp3⟩
            rcases h4e with ⟨p4, hp4⟩
            rcases h5e with ⟨p5, hp5⟩
            refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 (p2 + 1) p3 p4 p5
              (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · rfl
            · omega
            · omega
            · omega
            · omega
          · -- (O,O,E,O): odd sum, impossible
            exfalso
            rcases heven' with ⟨m, hm⟩
            have h2o : Odd (count C 2) := odd_of_not_even h2e
            rcases h2o with ⟨a, ha⟩
            have h3o : Odd (count C 3) := odd_of_not_even h3e
            rcases h3o with ⟨b, hb⟩
            rcases h4e with ⟨c, hc⟩
            have h5o : Odd (count C 5) := odd_of_not_even h5e
            rcases h5o with ⟨d, hd⟩
            omega
        · by_cases h5e : Even (count C 5)
          · -- (O,O,O,E): odd sum, impossible
            exfalso
            rcases heven' with ⟨m, hm⟩
            have h2o : Odd (count C 2) := odd_of_not_even h2e
            rcases h2o with ⟨a, ha⟩
            have h3o : Odd (count C 3) := odd_of_not_even h3e
            rcases h3o with ⟨b, hb⟩
            have h4o : Odd (count C 4) := odd_of_not_even h4e
            rcases h4o with ⟨c, hc⟩
            rcases h5e with ⟨d, hd⟩
            omega
          · -- case 15: all odd
            have h2o : Odd (count C 2) := odd_of_not_even h2e
            rcases h2o with ⟨p2, hp2⟩
            have h3o : Odd (count C 3) := odd_of_not_even h3e
            rcases h3o with ⟨p3, hp3⟩
            have h4o : Odd (count C 4) := odd_of_not_even h4e
            rcases h4o with ⟨p4, hp4⟩
            have h5o : Odd (count C 5) := odd_of_not_even h5e
            rcases h5o with ⟨p5, hp5⟩
            refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 (p2 + 1) p3 (p4 + 1) p5
              (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · rfl
            · omega
            · omega
            · omega
            · omega
end N4Code
