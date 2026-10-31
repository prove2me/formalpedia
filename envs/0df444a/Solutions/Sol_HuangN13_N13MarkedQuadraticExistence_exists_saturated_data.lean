-- Prove2me | solution 1 for HuangN13.N13MarkedQuadraticExistence.exists_saturated_data
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T15:11:15.293754+00:00
-- url     : https://prove2.me/submissions/acf041c9-a316-4ff2-be3d-aa98b1b890d4

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Theorems.Thm_HuangN13_N13MarkedQuadraticExistence_exists_saturated_data_of_distinct_split
import Theorems.Thm_HuangN13_N13MarkedQuadraticExistence_exists_saturated_data_of_irreducible
import Theorems.Thm_HuangN13_N13MarkedQuadraticExistence_exists_saturated_data_of_repeated_root

set_option autoImplicit false

section
section
set_option autoImplicit false
namespace MazurProof.N13MarkedQuadraticExistence
noncomputable section
open Polynomial N13InfinityChartMarking
open N13SplitQuadraticPicardRealization N13SplitQuadraticSpecialRestriction
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem exists_saturated_data
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          Model
          (N13Infinity.positiveInfinityOrder Q₂)
          D ∧
      N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      HasInfinityMultiplicities R.charts 0 0 := by
  by_cases hirr : Irreducible D.u
  · exact HuangN13.N13MarkedQuadraticExistence.exists_saturated_data_of_irreducible D hdeg hirr
  obtain ⟨c₁, c₂, hc₀, hc₁⟩ :=
    (D.u_monic.not_irreducible_iff_exists_add_mul_eq_coeff hdeg).mp
      hirr
  let x₁ : Q₂ := -c₁
  let x₂ : Q₂ := -c₂
  have hfactor :
      D.u = (X - C x₁) * (X - C x₂) := by
    have hc₂ : D.u.coeff 2 = 1 := by
      calc
        D.u.coeff 2 = D.u.coeff D.u.natDegree :=
          congrArg D.u.coeff hdeg.symm
        _ = 1 := D.u_monic.coeff_natDegree
    simp only [x₁, x₂, C_neg, sub_neg_eq_add]
    rw [D.u.as_sum_range_C_mul_X_pow, hdeg,
      Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, hc₂, hc₀, hc₁, C_mul, C_add, C_1]
    ring
  by_cases hneq : x₁ ≠ x₂
  · exact
      HuangN13.N13MarkedQuadraticExistence.exists_saturated_data_of_distinct_split
        D hdeg x₁ x₂ hfactor hneq
  · have heq : x₂ = x₁ := by
      apply not_ne_iff.mp
      exact fun h ↦ hneq h.symm
    have hfactorSquare :
        D.u = (X - C x₁) ^ 2 := by
      rw [heq] at hfactor
      simpa only [pow_two] using hfactor
    exact
      HuangN13.N13MarkedQuadraticExistence.exists_saturated_data_of_repeated_root
        D x₁ hfactorSquare
end
end MazurProof.N13MarkedQuadraticExistence
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem solution
    (D : MazurProof.SexticMumford.Mumford MazurProof.N13MarkedQuadraticExistence.Model)
    (hdeg : D.u.natDegree = 2) :
    ∃ R : MazurProof.N13TwoChartPicardRealization.Data,
      MazurProof.N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        MazurProof.SexticMumford.mumfordRaw MazurProof.N13MarkedQuadraticExistence.Model D ∧
      R.toGenericPic =
        MazurProof.SexticMumford.classOf
          MazurProof.N13MarkedQuadraticExistence.Model
          (MazurProof.N13Infinity.positiveInfinityOrder MazurProof.N13MarkedQuadraticExistence.Q₂)
          D ∧
      MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities R.charts 0 0 := by
  exact MazurProof.N13MarkedQuadraticExistence.exists_saturated_data D hdeg
