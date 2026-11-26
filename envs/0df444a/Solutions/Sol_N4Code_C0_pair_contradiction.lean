-- Prove2me | solution 1 for N4Code.C0_pair_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:46.145835+00:00
-- url     : https://prove2.me/submissions/d6453068-386f-4b08-9a12-f0476931f959

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_dRow_C0_formula

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n)
    (hC : ∀ u : Fin n, colVal (C u) = 0 ∨ colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h5 : Odd (count C 5)) (h6 : Odd (count C 6)) (y : Word n) :
    (dRow C 0 y ≠ dRow C 2 y) ∧
    (dRow C 0 y ≠ dRow C 3 y) ∧
    (dRow C 1 y ≠ dRow C 2 y) ∧
    (dRow C 1 y ≠ dRow C 3 y) ∧
    (¬ (dRow C 0 y = dRow C 1 y ∧ dRow C 0 y ≤ dRow C 2 y ∧ dRow C 0 y ≤ dRow C 3 y)) ∧
    (¬ (dRow C 2 y = dRow C 3 y ∧ dRow C 2 y ≤ dRow C 0 y ∧ dRow C 2 y ≤ dRow C 1 y)) := by
  rcases dRow_C0_formula C hC y with ⟨h0, h1, h2, h3⟩
  constructor
  · intro h
    have hsum : dRow C 0 y + dRow C 2 y = 2 * w_i C 0 y + 2 * w_i C 5 y + count C 6 := by
      rw [h0, h2]
      omega
    have hodd : Odd (dRow C 0 y + dRow C 2 y) := by
      rw [hsum]
      exact Even.add_odd ⟨w_i C 0 y + w_i C 5 y, by ring⟩ h6
    have hev : Even (dRow C 0 y + dRow C 2 y) := by
      exact ⟨dRow C 0 y, by rw [← h]⟩
    rcases hodd with ⟨k, hk⟩
    rcases hev with ⟨r, hr⟩
    omega
  · constructor
    · intro h
      have hsum : dRow C 0 y + dRow C 3 y = 2 * w_i C 0 y + count C 5 + 2 * w_i C 6 y := by
        rw [h0, h3]
        omega
      have hodd : Odd (dRow C 0 y + dRow C 3 y) := by
        rw [hsum]
        have hre : 2 * w_i C 0 y + count C 5 + 2 * w_i C 6 y =
            (2 * w_i C 0 y + 2 * w_i C 6 y) + count C 5 := by ring
        rw [hre]
        exact Even.add_odd ⟨w_i C 0 y + w_i C 6 y, by ring⟩ h5
      have hev : Even (dRow C 0 y + dRow C 3 y) := by
        exact ⟨dRow C 0 y, by rw [← h]⟩
      rcases hodd with ⟨k, hk⟩
      rcases hev with ⟨r, hr⟩
      omega
    · constructor
      · intro h
        have hsum : dRow C 1 y + dRow C 2 y = 2 * w_i C 0 y + count C 5 + 2 * (count C 6 - w_i C 6 y) := by
          rw [h1, h2]
          omega
        have hodd : Odd (dRow C 1 y + dRow C 2 y) := by
          rw [hsum]
          have hre : 2 * w_i C 0 y + count C 5 + 2 * (count C 6 - w_i C 6 y) =
              (2 * w_i C 0 y + 2 * (count C 6 - w_i C 6 y)) + count C 5 := by ring
          rw [hre]
          exact Even.add_odd ⟨w_i C 0 y + (count C 6 - w_i C 6 y), by ring⟩ h5
        have hev : Even (dRow C 1 y + dRow C 2 y) := by
          exact ⟨dRow C 1 y, by rw [← h]⟩
        rcases hodd with ⟨k, hk⟩
        rcases hev with ⟨r, hr⟩
        omega
      · constructor
        · intro h
          have hsum : dRow C 1 y + dRow C 3 y = 2 * w_i C 0 y + 2 * (count C 5 - w_i C 5 y) + count C 6 := by
            rw [h1, h3]
            omega
          have hodd : Odd (dRow C 1 y + dRow C 3 y) := by
            rw [hsum]
            exact Even.add_odd ⟨w_i C 0 y + (count C 5 - w_i C 5 y), by ring⟩ h6
          have hev : Even (dRow C 1 y + dRow C 3 y) := by
            exact ⟨dRow C 1 y, by rw [← h]⟩
          rcases hodd with ⟨k, hk⟩
          rcases hev with ⟨r, hr⟩
          omega
        · constructor
          · rintro ⟨h, hle2, hle3⟩
            have htwo : count C 5 = 2 * w_i C 5 y := by
              rw [h0, h1] at h
              rw [h0, h2] at hle2
              rw [h0, h3] at hle3
              omega
            rcases h5 with ⟨k5, hk5⟩
            omega
          · rintro ⟨h, hle0, hle1⟩
            have htwo : count C 5 = 2 * w_i C 5 y := by
              rw [h2, h3] at h
              rw [h2, h0] at hle0
              rw [h2, h1] at hle1
              omega
            rcases h5 with ⟨k5, hk5⟩
            omega
end N4Code
