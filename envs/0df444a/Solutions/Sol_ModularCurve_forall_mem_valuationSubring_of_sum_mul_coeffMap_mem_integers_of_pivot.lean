-- Prove2me | solution 1 for ModularCurve.forall_mem_valuationSubring_of_sum_mul_coeffMap_mem_integers_of_pivot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/36ba92ae-6388-53e8-900e-64bfcc99ff39

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_forall_mem_valuationSubring_of_sum_mul_coeffMap_mem_integers_of_pivot

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    {n : ℕ} (c : Fin n → AlgebraicClosure ℚ) (y : Fin n → LaurentSeries ↥A)
    (hy : ∀ i, coeffMap A.subtype (y i) ∈ modularFunctionFieldBar M')
    (p : Fin n → ℤ) (hpiv : ∀ i j, (y j).coeff (p i) = if i = j then 1 else 0)
    (hf : (∑ i, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (c i) *
        (⟨coeffMap A.subtype (y i), hy i⟩ : ↥(modularFunctionFieldBar M'))) ∈ R₀.integers) :
    ∀ i, c i ∈ A := by
  classical
  by_contra hnot
  push_neg at hnot
  obtain ⟨i₁, hi₁⟩ := hnot

  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i₁, Finset.mem_univ _⟩
  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => A.valuation (c i)) hne
  have hmax' : ∀ i, A.valuation (c i) ≤ A.valuation (c i₀) := fun i => hmax i (Finset.mem_univ _)
  have hc₀ : c i₀ ∉ A := by
    intro h
    apply hi₁
    rw [← A.valuation_le_one_iff] at h ⊢
    exact (hmax' i₁).trans h
  have hc0 : c i₀ ≠ 0 := by rintro h; exact hc₀ (h ▸ A.zero_mem)

  have hratio : ∀ i, c i * (c i₀)⁻¹ ∈ A := by
    intro i
    rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
    have h0 : A.valuation (c i₀) ≠ 0 := by
      rw [ne_eq, map_eq_zero]; exact hc0
    calc A.valuation (c i) * (A.valuation (c i₀))⁻¹ ≤ A.valuation (c i₀) * (A.valuation (c i₀))⁻¹ :=
          mul_le_mul_left (hmax' i) _
      _ = 1 := mul_inv_cancel₀ h0
  have hinvA : (c i₀)⁻¹ ∈ A := (A.mem_or_inv_mem _).resolve_left hc₀
  have hinv_max : (⟨(c i₀)⁻¹, hinvA⟩ : A) ∈ maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff A ⟨_, hinvA⟩]
    show A.valuation (c i₀)⁻¹ < 1
    rw [map_inv₀]
    have hgt : 1 < A.valuation (c i₀) := lt_of_not_ge fun h => hc₀ ((A.valuation_le_one_iff _).mp h)
    exact inv_lt_one_of_one_lt₀ hgt
  have hres0 : IsLocalRing.residue A ⟨(c i₀)⁻¹, hinvA⟩ = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hinv_max

  let Y : LaurentSeries ↥A := ∑ i, HahnSeries.C (⟨c i * (c i₀)⁻¹, hratio i⟩ : A) * y i
  have hYcoe : coeffMap A.subtype Y =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c i₀)⁻¹ *
        ∑ i, algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c i) * coeffMap A.subtype (y i) := by
    simp only [Y, map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [HahnSeries.C_apply, coeffMap_single, algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single,
      ← mul_assoc, HahnSeries.single_mul_single, zero_add, mul_comm ((c i₀)⁻¹)]
    rfl

  set f : ↥(modularFunctionFieldBar M') := ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (c i) *
      (⟨coeffMap A.subtype (y i), hy i⟩ : ↥(modularFunctionFieldBar M')) with hfdef
  have hfcoe : (f : LaurentSeries (AlgebraicClosure ℚ)) =
      ∑ i, algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c i) * coeffMap A.subtype (y i) := by
    rw [hfdef, AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MulMemClass.coe_mul]; rfl
  have hYmem : coeffMap A.subtype Y ∈ modularFunctionFieldBar M' := by
    rw [hYcoe, ← hfcoe]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) f.2

  have hg_eq : (⟨coeffMap A.subtype Y, hYmem⟩ : ↥(modularFunctionFieldBar M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') ((⟨(c i₀)⁻¹, hinvA⟩ : A) : AlgebraicClosure ℚ) * f := by
    apply Subtype.ext
    show coeffMap A.subtype Y = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c i₀)⁻¹ * (f : LaurentSeries _)
    rw [hYcoe, hfcoe]
  obtain ⟨hYO, hYres⟩ := hR₀ Y hYmem
  have hcO : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') ((⟨(c i₀)⁻¹, hinvA⟩ : A) : AlgebraicClosure ℚ) ∈
      R₀.integers := (R₀.algebraMap_mem_iff _).mpr hinvA
  have hres_g : R₀.residue ⟨_, hYO⟩ = 0 := by
    have : (⟨_, hYO⟩ : R₀.integers) = ⟨_, hcO⟩ * ⟨f, hf⟩ := Subtype.ext hg_eq
    rw [this, map_mul, R₀.residue_algebraMap, hres0, map_zero, zero_mul]

  have hcoeff : Y.coeff (p i₀) = 1 := by
    simp only [Y, HahnSeries.coeff_sum]
    rw [Finset.sum_eq_single i₀]
    · rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul, hpiv, if_pos rfl, mul_one]
      apply Subtype.ext
      show c i₀ * (c i₀)⁻¹ = 1
      exact mul_inv_cancel₀ hc0
    · intro j _ hj
      rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul, hpiv, if_neg (Ne.symm hj), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have : (coeffMap (IsLocalRing.residue ↥A) Y).coeff (p i₀) = 1 := by
    rw [coeffMap_coeff, hcoeff, map_one]
  rw [← hYres, hres_g] at this
  simp at this

end

end S_ModularCurve_forall_mem_valuationSubring_of_sum_mul_coeffMap_mem_integers_of_pivot
end P2MW
export P2MW.S_ModularCurve_forall_mem_valuationSubring_of_sum_mul_coeffMap_mem_integers_of_pivot (solution)
