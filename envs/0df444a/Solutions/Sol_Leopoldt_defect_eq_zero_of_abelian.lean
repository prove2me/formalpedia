-- Prove2me | solution 1 for Leopoldt.defect_eq_zero_of_abelian
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-09T15:35:50.979013+00:00
-- url     : https://prove2.me/submissions/f63a3605-cd97-49f5-aa58-7bdb966628f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Leopoldt_defect_pos_of_defect_pos
import Theorems.Thm_Leopoldt_defect_eq_zero_cyclotomicField
import Theorems.Thm_Leopoldt_exists_algHom_cyclotomicField

open NumberField

/-- Brumer's theorem for abelian fields, reduced to the cyclotomic case: by Kronecker-Weber an
abelian field embeds into a cyclotomic field, and by Remark 1.A a vanishing Leopoldt defect is
inherited by subfields. -/
theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    [IsMulCommutative (K ≃ₐ[ℚ] K)] :
    Leopoldt.defect p K = 0 := by
  -- Kronecker-Weber: `K` embeds into a cyclotomic field `ℚ(ζ_n)`.
  obtain ⟨n, -, ⟨f⟩⟩ := Leopoldt.exists_algHom_cyclotomicField K
  letI : Algebra K (CyclotomicField n ℚ) := f.toRingHom.toAlgebra
  have : IsScalarTower ℚ K (CyclotomicField n ℚ) :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  have : FiniteDimensional K (CyclotomicField n ℚ) :=
    FiniteDimensional.right ℚ K (CyclotomicField n ℚ)
  -- Brumer for cyclotomic fields.
  have hL : Leopoldt.defect p (CyclotomicField n ℚ) = 0 :=
    Leopoldt.defect_eq_zero_cyclotomicField p n
  -- Remark 1.A: a positive defect for `K` would force one for `ℚ(ζ_n)`.
  by_contra h
  have hpos := Leopoldt.defect_pos_of_defect_pos p K (CyclotomicField n ℚ) (Nat.pos_of_ne_zero h)
  omega
