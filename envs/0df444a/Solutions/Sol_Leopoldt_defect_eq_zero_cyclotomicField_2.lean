-- Prove2me | solution 2 for Leopoldt.defect_eq_zero_cyclotomicField
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:23:41.57718+00:00
-- url     : https://prove2.me/submissions/54d9a9b5-b9d9-4fee-a0b3-dc22371bfd3a

import Definitions.Def_LeopoldtDefect
import Theorems.Thm_Leopoldt_defect_pos_of_defect_pos
import Theorems.Thm_Leopoldt_defect_eq_zero_cyclotomicField_of_dvd
import Theorems.Thm_Leopoldt_units_rank_cyclotomicField
import Theorems.Thm_Leopoldt_defect_le_units_rank_sub_one
import Theorems.Thm_NumberField_nonempty_algHom_cyclotomicField_of_dvd

open NumberField Leopoldt

theorem solution (p : ℕ) [Fact p.Prime] (n : ℕ) :
    defect p (CyclotomicField n ℚ) = 0 := by
  by_cases hn : n = 0
  · subst n
    have h1 := defect_le_units_rank_sub_one p (CyclotomicField 0 ℚ)
    have h2 := units_rank_cyclotomicField 0
    have h3 : (0 : ℕ).totient / 2 - 1 ≤ 1 := by decide
    omega
  · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
    have : NeZero n := ⟨hn⟩
    have hp0 : 0 < p := (Fact.out : p.Prime).pos
    let m := 4 * p * n
    have hm0 : 0 < m := by dsimp [m]; positivity
    have : NeZero m := ⟨Nat.ne_of_gt hm0⟩
    have hdvd : n ∣ m := by dsimp [m]; exact ⟨4 * p, by ring⟩
    let f : CyclotomicField n ℚ →ₐ[ℚ] CyclotomicField m ℚ :=
      Classical.choice (NumberField.nonempty_algHom_cyclotomicField_of_dvd hn0 hm0 hdvd)
    let _ : Algebra (CyclotomicField n ℚ) (CyclotomicField m ℚ) := f.toRingHom.toAlgebra
    have : IsScalarTower ℚ (CyclotomicField n ℚ) (CyclotomicField m ℚ) :=
      IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
    have : FiniteDimensional (CyclotomicField n ℚ) (CyclotomicField m ℚ) :=
      FiniteDimensional.right ℚ _ _
    by_contra h
    have hpos : 0 < defect p (CyclotomicField n ℚ) := Nat.pos_of_ne_zero h
    have hpos' := defect_pos_of_defect_pos p (CyclotomicField n ℚ) (CyclotomicField m ℚ) hpos
    have hzero : defect p (CyclotomicField m ℚ) = 0 :=
      defect_eq_zero_cyclotomicField_of_dvd p m hm0 (by dsimp [m]; exact ⟨n, rfl⟩)
    omega
