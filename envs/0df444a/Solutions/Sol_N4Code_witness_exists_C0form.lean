-- Prove2me | solution 1 for N4Code.witness_exists_C0form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:12.053222+00:00
-- url     : https://prove2.me/submissions/d69e0e5f-cd99-4b59-8e72-2fd684d45123

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_witness_from_k
import Theorems.Thm_N4Code_tableK_0
import Theorems.Thm_N4Code_tableK_03
import Theorems.Thm_N4Code_tableK_815
import Theorems.Thm_N4Code_odd_of_not_even
import Theorems.Thm_N4Code_tableK_bounds_47
import Theorems.Thm_N4Code_C0form_iff_Columns07
import Theorems.Thm_N4Code_use_witness

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (h07 : Columns07 C)
    (hcnt0 : 1 ≤ count C 0) (hWeven : Even (count C 4 + count C 5 + count C 6 + count C 7))
    (hnotC0 : ¬ C0form C) :
    ∃ t : Fin n, C t = col0 ∧ ∃ y : Word n, Y3c C col5 colZeros_col5_nonempty
      colOnes_col5_nonempty t y := by
  by_cases h4 : Even (count C 4)
  · by_cases h5 : Even (count C 5)
    · by_cases h6 : Even (count C 6)
      · by_cases h7 : Even (count C 7)
        · -- case 1: all even — w = (|4|,|5|,|6|,|7|)/2
          rcases h4 with ⟨a, h4a⟩
          rcases h5 with ⟨b, h5b⟩
          rcases h6 with ⟨c, h6c⟩
          rcases h7 with ⟨d, h7d⟩
          let k : ℕ → ℕ := tableK a b c d
          have hk4 : k 4 = a := by simp [k, tableK]
          have hk5 : k 5 = b := by simp [k, tableK]
          have hk6 : k 6 = c := by simp [k, tableK]
          have hk7 : k 7 = d := by simp [k, tableK]
          have hb4 : a ≤ count C 4 := by omega
          have hb5 : b ≤ count C 5 := by omega
          have hb6 : c ≤ count C 6 := by omega
          have hb7 : d ≤ count C 7 := by omega
          have hmid : 2 * (k 4 + k 5 + k 6 + k 7) = count C 4 + count C 5 + count C 6 + count C 7 := by
            rw [hk4, hk5, hk6, hk7]
            omega
          have hge2 : 2 * k 6 + 2 * k 7 ≤ count C 2 + count C 3 + count C 6 + count C 7 := by
            rw [hk6, hk7]
            omega
          have hge3 : 2 * k 5 + 2 * k 7 ≤ count C 1 + count C 3 + count C 5 + count C 7 := by
            rw [hk5, hk7]
            omega
          exact witness_from_k C h07 k hcnt0 (tableK_0 a b c d) (tableK_03 a b c d)
            (by simpa [k] using tableK_bounds_47 C a b c d hcnt0 hb4 hb5 hb6 hb7)
            (tableK_815 a b c d) hmid hge2 hge3
        · -- (E,E,E,O): one odd — impossible since W even
          exfalso
          rcases hWeven with ⟨m, hm⟩
          rcases h4 with ⟨a, h4a⟩
          rcases h5 with ⟨b, h5b⟩
          rcases h6 with ⟨c, h6c⟩
          have h7o : Odd (count C 7) := (odd_of_not_even h7)
          rcases h7o with ⟨d, h7d⟩
          omega
      · by_cases h7 : Even (count C 7)
        · -- (E,E,O,E): one odd — impossible
          exfalso
          rcases hWeven with ⟨m, hm⟩
          rcases h4 with ⟨a, h4a⟩
          rcases h5 with ⟨b, h5b⟩
          have h6o : Odd (count C 6) := (odd_of_not_even h6)
          rcases h6o with ⟨c, h6c⟩
          rcases h7 with ⟨d, h7d⟩
          omega
        · -- case 7: (E,E,O,O) — w = (0,0,1/2,-1/2)
          rcases h4 with ⟨a, h4a⟩
          rcases h5 with ⟨b, h5b⟩
          have h6o : Odd (count C 6) := (odd_of_not_even h6)
          rcases h6o with ⟨c, h6c⟩
          have h7o : Odd (count C 7) := (odd_of_not_even h7)
          rcases h7o with ⟨d, h7d⟩
          have hb4 : a ≤ count C 4 := by omega
          have hb5 : b ≤ count C 5 := by omega
          have hb6 : c + 1 ≤ count C 6 := by omega
          have hb7 : d ≤ count C 7 := by omega
          have hmid : 2 * (a + b + (c + 1) + d) = count C 4 + count C 5 + count C 6 + count C 7 := by omega
          have hge2 : 2 * (c + 1) + 2 * d ≤ count C 2 + count C 3 + count C 6 + count C 7 := by omega
          have hge3 : 2 * b + 2 * d ≤ count C 1 + count C 3 + count C 5 + count C 7 := by omega
          exact use_witness C h07 hcnt0 a b (c + 1) d hb4 hb5 hb6 hb7 hmid hge2 hge3
    · by_cases h6 : Even (count C 6)
      · by_cases h7 : Even (count C 7)
        · -- (E,O,E,E): one odd — impossible
          exfalso
          rcases hWeven with ⟨m, hm⟩
          rcases h4 with ⟨a, h4a⟩
          have h5o : Odd (count C 5) := (odd_of_not_even h5)
          rcases h5o with ⟨b, h5b⟩
          rcases h6 with ⟨c, h6c⟩
          rcases h7 with ⟨d, h7d⟩
          omega
        · -- case 6: (E,O,E,O) — w = (0,1/2,0,-1/2)
          rcases h4 with ⟨a, h4a⟩
          have h5o : Odd (count C 5) := (odd_of_not_even h5)
          rcases h5o with ⟨b, h5b⟩
          rcases h6 with ⟨c, h6c⟩
          have h7o : Odd (count C 7) := (odd_of_not_even h7)
          rcases h7o with ⟨d, h7d⟩
          have hb4 : a ≤ count C 4 := by omega
          have hb5 : b + 1 ≤ count C 5 := by omega
          have hb6 : c ≤ count C 6 := by omega
          have hb7 : d ≤ count C 7 := by omega
          have hmid : 2 * (a + (b + 1) + c + d) = count C 4 + count C 5 + count C 6 + count C 7 := by omega
          have hge2 : 2 * c + 2 * d ≤ count C 2 + count C 3 + count C 6 + count C 7 := by omega
          have hge3 : 2 * (b + 1) + 2 * d ≤ count C 1 + count C 3 + count C 5 + count C 7 := by omega
          exact use_witness C h07 hcnt0 a (b + 1) c d hb4 hb5 hb6 hb7 hmid hge2 hge3
      · by_cases h7 : Even (count C 7)
        · -- (E,O,O,E): cases 5a, 5b, or the exceptional table-2 case
          by_cases h4pos : 0 < count C 4
          · -- case 5a: w = (|4|/2+1, (|5|-1)/2, (|6|-1)/2, |7|/2)
            rcases h4 with ⟨a, h4a⟩
            have h5o : Odd (count C 5) := (odd_of_not_even h5)
            rcases h5o with ⟨b, h5b⟩
            have h6o : Odd (count C 6) := (odd_of_not_even h6)
            rcases h6o with ⟨c, h6c⟩
            rcases h7 with ⟨d, h7d⟩
            have hb4 : a + 1 ≤ count C 4 := by omega
            have hb5 : b ≤ count C 5 := by omega
            have hb6 : c ≤ count C 6 := by omega
            have hb7 : d ≤ count C 7 := by omega
            have hmid : 2 * ((a + 1) + b + c + d) = count C 4 + count C 5 + count C 6 + count C 7 := by omega
            have hge2 : 2 * c + 2 * d ≤ count C 2 + count C 3 + count C 6 + count C 7 := by omega
            have hge3 : 2 * b + 2 * d ≤ count C 1 + count C 3 + count C 5 + count C 7 := by omega
            exact use_witness C h07 hcnt0 (a + 1) b c d hb4 hb5 hb6 hb7 hmid hge2 hge3
          · by_cases h7pos : 0 < count C 7
            · -- case 5b: w = (|4|/2, (|5|+1)/2, (|6|+1)/2, |7|/2−1)
              rcases h4 with ⟨a, h4a⟩
              have h5o : Odd (count C 5) := (odd_of_not_even h5)
              rcases h5o with ⟨b, h5b⟩
              have h6o : Odd (count C 6) := (odd_of_not_even h6)
              rcases h6o with ⟨c, h6c⟩
              rcases h7 with ⟨d, h7d⟩
              have hb4 : a ≤ count C 4 := by omega
              have hb5 : b + 1 ≤ count C 5 := by omega
              have hb6 : c + 1 ≤ count C 6 := by omega
              have hb7 : d - 1 ≤ count C 7 := by omega
              have hmid : 2 * (a + (b + 1) + (c + 1) + (d - 1)) =
                  count C 4 + count C 5 + count C 6 + count C 7 := by omega
              have hge2 : 2 * (c + 1) + 2 * (d - 1) ≤ count C 2 + count C 3 + count C 6 + count C 7 := by omega
              have hge3 : 2 * (b + 1) + 2 * (d - 1) ≤ count C 1 + count C 3 + count C 5 + count C 7 := by omega
              exact use_witness C h07 hcnt0 a (b + 1) (c + 1) (d - 1) hb4 hb5 hb6 hb7 hmid hge2 hge3
            · -- exceptional: |4| = 0, |7| = 0, |5|,|6| odd → Table 2
              have h40 : count C 4 = 0 := by omega
              have h70 : count C 7 = 0 := by omega
              have h5o : Odd (count C 5) := (odd_of_not_even h5)
              have h6o : Odd (count C 6) := (odd_of_not_even h6)
              rcases h5o with ⟨b, h5b⟩
              rcases h6o with ⟨c, h6c⟩
              -- not C0-form → at least one of |1|,|2|,|3| is positive
              have h123 : 0 < count C 1 + count C 2 + count C 3 := by
                by_contra h
                have hsum0 : count C 1 = 0 ∧ count C 2 = 0 ∧ count C 3 = 0 := by omega
                have hC0 : C0form C := (C0form_iff_Columns07 C h07).mpr
                  ⟨hsum0.1, hsum0.2.1, hsum0.2.2, h40, h70, odd_of_not_even h5, odd_of_not_even h6⟩
                exact hnotC0 hC0
              by_cases h1pos : 0 < count C 1
              · -- Table 2, |1| > 0: w5 = (|5|+1)/2, w6 = (|6|-1)/2
                have hb4 : (0 : ℕ) ≤ count C 4 := by omega
                have hb5 : b + 1 ≤ count C 5 := by omega
                have hb6 : c ≤ count C 6 := by omega
                have hb7 : (0 : ℕ) ≤ count C 7 := by omega
                have hmid : 2 * ((0 : ℕ) + (b + 1) + c + 0) =
                    count C 4 + count C 5 + count C 6 + count C 7 := by omega
                have hge2 : 2 * c + 2 * 0 ≤ count C 2 + count C 3 + count C 6 + count C 7 := by omega
                have hge3 : 2 * (b + 1) + 2 * 0 ≤ count C 1 + count C 3 + count C 5 + count C 7 := by omega
                exact use_witness C h07 hcnt0 0 (b + 1) c 0 hb4 hb5 hb6 hb7 hmid hge2 hge3
              · by_cases h2pos : 0 < count C 2
                · -- Table 2, |2| > 0: w5 = (|5|-1)/2, w6 = (|6|+1)/2
                  have hb4 : (0 : ℕ) ≤ count C 4 := by omega
                  have hb5 : b ≤ count C 5 := by omega
                  have hb6 : c + 1 ≤ count C 6 := by omega
                  have hb7 : (0 : ℕ) ≤ count C 7 := by omega
                  have hmid : 2 * ((0 : ℕ) + b + (c + 1) + 0) =
                      count C 4 + count C 5 + count C 6 + count C 7 := by omega
                  have hge2 : 2 * (c + 1) + 2 * 0 ≤ count C 2 + count C 3 + count C 6 + count C 7 := by omega
                  have hge3 : 2 * b + 2 * 0 ≤ count C 1 + count C 3 + count C 5 + count C 7 := by omega
                  exact use_witness C h07 hcnt0 0 b (c + 1) 0 hb4 hb5 hb6 hb7 hmid hge2 hge3
                · -- Table 2, |3| > 0 (must hold since |1|,|2| = 0 and sum > 0)
                  have h3pos : 0 < count C 3 := by omega
                  have hb4 : (0 : ℕ) ≤ count C 4 := by omega
                  have hb5 : b + 1 ≤ count C 5 := by omega
                  have hb6 : c ≤ count C 6 := by omega
                  have hb7 : (0 : ℕ) ≤ count C 7 := by omega
                  have hmid : 2 * ((0 : ℕ) + (b + 1) + c + 0) =
                      count C 4 + count C 5 + count C 6 + count C 7 := by omega
                  have hge2 : 2 * c + 2 * 0 ≤ count C 2 + count C 3 + count C 6 + count C 7 := by omega
                  have hge3 : 2 * (b + 1) + 2 * 0 ≤ count C 1 + count C 3 + count C 5 + count C 7 := by omega
                  exact use_witness C h07 hcnt0 0 (b + 1) c 0 hb4 hb5 hb6 hb7 hmid hge2 hge3
        · -- (E,O,O,O): three odds — impossible
          exfalso
          rcases hWeven with ⟨m, hm⟩
          rcases h4 with ⟨a, h4a⟩
          have h5o : Odd (count C 5) := (odd_of_not_even h5)
          rcases h5o with ⟨b, h5b⟩
          have h6o : Odd (count C 6) := (odd_of_not_even h6)
          rcases h6o with ⟨c, h6c⟩
          have h7o : Odd (count C 7) := (odd_of_not_even h7)
          rcases h7o with ⟨d, h7d⟩
          omega
  · by_cases h5 : Even (count C 5)
    · by_cases h6 : Even (count C 6)
      · by_cases h7 : Even (count C 7)
        · -- (O,E,E,E): one odd — impossible
          exfalso
          rcases hWeven with ⟨m, hm⟩
          have h4o : Odd (count C 4) := (odd_of_not_even h4)
          rcases h4o with ⟨a, h4a⟩
          rcases h5 with ⟨b, h5b⟩
          rcases h6 with ⟨c, h6c⟩
          rcases h7 with ⟨d, h7d⟩
          omega
        · -- case 4: (O,E,E,O) — w = (1/2,0,0,-1/2)
          have h4o : Odd (count C 4) := (odd_of_not_even h4)
          rcases h4o with ⟨a, h4a⟩
          rcases h5 with ⟨b, h5b⟩
          rcases h6 with ⟨c, h6c⟩
          have h7o : Odd (count C 7) := (odd_of_not_even h7)
          rcases h7o with ⟨d, h7d⟩
          let k : ℕ → ℕ := tableK (a + 1) b c d
          exact witness_from_k C h07 k hcnt0 (tableK_0 (a + 1) b c d) (tableK_03 (a + 1) b c d)
            (tableK_bounds_47 C (a + 1) b c d hcnt0 (by omega) (by omega) (by omega) (by omega))
            (tableK_815 (a + 1) b c d)
            (by simp [k, tableK]; omega)
            (by simp [k, tableK]; omega)
            (by simp [k, tableK]; omega)
      · by_cases h7 : Even (count C 7)
        · -- case 3: (O,E,O,E) — w = (1/2,0,-1/2,0)
          have h4o : Odd (count C 4) := (odd_of_not_even h4)
          rcases h4o with ⟨a, h4a⟩
          rcases h5 with ⟨b, h5b⟩
          have h6o : Odd (count C 6) := (odd_of_not_even h6)
          rcases h6o with ⟨c, h6c⟩
          rcases h7 with ⟨d, h7d⟩
          let k : ℕ → ℕ := tableK (a + 1) b c d
          exact witness_from_k C h07 k hcnt0 (tableK_0 (a + 1) b c d) (tableK_03 (a + 1) b c d)
            (tableK_bounds_47 C (a + 1) b c d hcnt0 (by omega) (by omega) (by omega) (by omega))
            (tableK_815 (a + 1) b c d)
            (by simp [k, tableK]; omega)
            (by simp [k, tableK]; omega)
            (by simp [k, tableK]; omega)
        · -- (O,E,O,O): three odds — impossible
          exfalso
          rcases hWeven with ⟨m, hm⟩
          have h4o : Odd (count C 4) := (odd_of_not_even h4)
          rcases h4o with ⟨a, h4a⟩
          rcases h5 with ⟨b, h5b⟩
          have h6o : Odd (count C 6) := (odd_of_not_even h6)
          rcases h6o with ⟨c, h6c⟩
          have h7o : Odd (count C 7) := (odd_of_not_even h7)
          rcases h7o with ⟨d, h7d⟩
          omega
    · by_cases h6 : Even (count C 6)
      · by_cases h7 : Even (count C 7)
        · -- case 2: (O,O,E,E) — w = (1/2,-1/2,0,0)
          have h4o : Odd (count C 4) := (odd_of_not_even h4)
          rcases h4o with ⟨a, h4a⟩
          have h5o : Odd (count C 5) := (odd_of_not_even h5)
          rcases h5o with ⟨b, h5b⟩
          rcases h6 with ⟨c, h6c⟩
          rcases h7 with ⟨d, h7d⟩
          let k : ℕ → ℕ := tableK (a + 1) b c d
          exact witness_from_k C h07 k hcnt0 (tableK_0 (a + 1) b c d) (tableK_03 (a + 1) b c d)
            (tableK_bounds_47 C (a + 1) b c d hcnt0 (by omega) (by omega) (by omega) (by omega))
            (tableK_815 (a + 1) b c d)
            (by simp [k, tableK]; omega)
            (by simp [k, tableK]; omega)
            (by simp [k, tableK]; omega)
        · -- (O,O,E,O): three odds — impossible
          exfalso
          rcases hWeven with ⟨m, hm⟩
          have h4o : Odd (count C 4) := (odd_of_not_even h4)
          rcases h4o with ⟨a, h4a⟩
          have h5o : Odd (count C 5) := (odd_of_not_even h5)
          rcases h5o with ⟨b, h5b⟩
          rcases h6 with ⟨c, h6c⟩
          have h7o : Odd (count C 7) := (odd_of_not_even h7)
          rcases h7o with ⟨d, h7d⟩
          omega
      · by_cases h7 : Even (count C 7)
        · -- (O,O,O,E): three odds — impossible
          exfalso
          rcases hWeven with ⟨m, hm⟩
          have h4o : Odd (count C 4) := (odd_of_not_even h4)
          rcases h4o with ⟨a, h4a⟩
          have h5o : Odd (count C 5) := (odd_of_not_even h5)
          rcases h5o with ⟨b, h5b⟩
          have h6o : Odd (count C 6) := (odd_of_not_even h6)
          rcases h6o with ⟨c, h6c⟩
          rcases h7 with ⟨d, h7d⟩
          omega
        · -- case 8: (O,O,O,O) — w = (1/2,1/2,-1/2,-1/2)
          have h4o : Odd (count C 4) := (odd_of_not_even h4)
          rcases h4o with ⟨a, h4a⟩
          have h5o : Odd (count C 5) := (odd_of_not_even h5)
          rcases h5o with ⟨b, h5b⟩
          have h6o : Odd (count C 6) := (odd_of_not_even h6)
          rcases h6o with ⟨c, h6c⟩
          have h7o : Odd (count C 7) := (odd_of_not_even h7)
          rcases h7o with ⟨d, h7d⟩
          let k : ℕ → ℕ := tableK (a + 1) (b + 1) c d
          exact witness_from_k C h07 k hcnt0 (tableK_0 (a + 1) (b + 1) c d) (tableK_03 (a + 1) (b + 1) c d)
            (tableK_bounds_47 C (a + 1) (b + 1) c d hcnt0 (by omega) (by omega) (by omega) (by omega))
            (tableK_815 (a + 1) (b + 1) c d)
            (by simp [k, tableK]; omega)
            (by simp [k, tableK]; omega)
            (by simp [k, tableK]; omega)
end N4Code
