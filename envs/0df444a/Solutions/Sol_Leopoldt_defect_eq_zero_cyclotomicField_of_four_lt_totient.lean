-- Prove2me | solution 1 for Leopoldt.defect_eq_zero_cyclotomicField_of_four_lt_totient
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:43:33.491438+00:00
-- url     : https://prove2.me/submissions/fb050a5b-85c0-4451-b692-f8f1ee9fed43
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Leopoldt_defect_pos_of_defect_pos
import Theorems.Thm_Leopoldt_defect_eq_zero_cyclotomicField_of_dvd

open NumberField Polynomial Leopoldt

theorem solution (p : ℕ) [Fact p.Prime] (n : ℕ)
    (hn : 4 < n.totient) :
    defect p (CyclotomicField n ℚ) = 0 := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have : NeZero n := ⟨hn0⟩
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set m := 4 * p * n with hmdef
  have hm0 : m ≠ 0 := by positivity
  have : NeZero m := ⟨hm0⟩
  have hcyc : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
    CyclotomicField.isCyclotomicExtension m ℚ
  have hcyc2 : IsCyclotomicExtension ({m} ∪ {n}) ℚ (CyclotomicField m ℚ) :=
    IsCyclotomicExtension.of_union_of_dvd (n := n) (S := {m}) (A := ℚ)
      (B := CyclotomicField m ℚ) ⟨m, rfl, hm0, Dvd.intro_left (4 * p) rfl⟩
  have hsplit : Splits ((cyclotomic n ℚ).map (algebraMap ℚ (CyclotomicField m ℚ))) :=
    IsCyclotomicExtension.splits_cyclotomic (n := n) (S := {m} ∪ {n}) (K := ℚ)
      (L := CyclotomicField m ℚ) (by simp)
  let f : CyclotomicField n ℚ →ₐ[ℚ] CyclotomicField m ℚ := SplittingField.lift _ hsplit
  let _ : Algebra (CyclotomicField n ℚ) (CyclotomicField m ℚ) := f.toRingHom.toAlgebra
  have : IsScalarTower ℚ (CyclotomicField n ℚ) (CyclotomicField m ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  have : FiniteDimensional (CyclotomicField n ℚ) (CyclotomicField m ℚ) :=
    FiniteDimensional.right ℚ _ _
  by_contra h
  have hpos : 0 < defect p (CyclotomicField n ℚ) := Nat.pos_of_ne_zero h
  have := defect_pos_of_defect_pos p (CyclotomicField n ℚ) (CyclotomicField m ℚ) hpos
  rw [defect_eq_zero_cyclotomicField_of_dvd p m (Nat.pos_of_ne_zero hm0)
    (Dvd.intro n rfl)] at this
  exact lt_irrefl 0 this

