-- Prove2me | solution 1 for HuangN13.N13MarkedQuadraticExistence.exists_reciprocal_saturated_data
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:59:22.715626+00:00
-- url     : https://prove2.me/submissions/fe928824-12e8-4603-85a2-f1785b1eb318

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Theorems.Thm_HuangN13_N13IrreducibleQuadraticSpread_exists_reciprocalGraphClosure_or_verticalGraph
import Theorems.Thm_HuangN13_N13MarkedQuadraticExistence_ReciprocalGraphClosure_exists_saturated_data
import Theorems.Thm_HuangN13_N13MarkedQuadraticExistence_verticalGraph_exists_saturated_data

set_option autoImplicit false

section
section
set_option autoImplicit false
namespace MazurProof.N13MarkedQuadraticExistence
noncomputable section
open Polynomial N13InfinityChartMarking
open N13SplitQuadraticPicardRealization N13SplitQuadraticSpecialRestriction
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem exists_reciprocal_saturated_data
    (D : SexticMumford.Mumford
      N13IrreducibleQuadraticSpread.Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : N13IrreducibleQuadraticSpread.R₂)
    (hm :
      (X ^ 2 +
          C (a : N13IrreducibleQuadraticSpread.Q₂) * X +
          C (b : N13IrreducibleQuadraticSpread.Q₂) :
        N13IrreducibleQuadraticSpread.Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw
          N13IrreducibleQuadraticSpread.Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          N13IrreducibleQuadraticSpread.Model
          (N13Infinity.positiveInfinityOrder
            N13TwoChartPicardRealization.Q₂)
          D ∧
      N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      HasInfinityMultiplicities R.charts 0 0 := by
  rcases
      HuangN13.N13IrreducibleQuadraticSpread.exists_reciprocalGraphClosure_or_verticalGraph
        D hdeg h0 a b hm with
    hhorizontal | ⟨E, hmDegree, hI⟩
  · obtain ⟨E⟩ := hhorizontal
    exact
      HuangN13.N13MarkedQuadraticExistence.ReciprocalGraphClosure.exists_saturated_data
        E hdeg h0 hm
  · exact
      HuangN13.N13MarkedQuadraticExistence.verticalGraph_exists_saturated_data
        hdeg h0 hm E hmDegree hI
end
end MazurProof.N13MarkedQuadraticExistence
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem solution
    (D : MazurProof.SexticMumford.Mumford
      MazurProof.N13IrreducibleQuadraticSpread.Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : MazurProof.N13IrreducibleQuadraticSpread.R₂)
    (hm :
      (X ^ 2 +
          C (a : MazurProof.N13IrreducibleQuadraticSpread.Q₂) * X +
          C (b : MazurProof.N13IrreducibleQuadraticSpread.Q₂) :
        MazurProof.N13IrreducibleQuadraticSpread.Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    ∃ R : MazurProof.N13TwoChartPicardRealization.Data,
      MazurProof.N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        MazurProof.SexticMumford.mumfordRaw
          MazurProof.N13IrreducibleQuadraticSpread.Model D ∧
      R.toGenericPic =
        MazurProof.SexticMumford.classOf
          MazurProof.N13IrreducibleQuadraticSpread.Model
          (MazurProof.N13Infinity.positiveInfinityOrder
            MazurProof.N13TwoChartPicardRealization.Q₂)
          D ∧
      MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities R.charts 0 0 := by
  exact MazurProof.N13MarkedQuadraticExistence.exists_reciprocal_saturated_data D hdeg h0 a b hm
