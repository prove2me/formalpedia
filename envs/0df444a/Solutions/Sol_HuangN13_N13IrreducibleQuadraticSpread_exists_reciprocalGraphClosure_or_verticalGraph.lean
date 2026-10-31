-- Prove2me | solution 1 for HuangN13.N13IrreducibleQuadraticSpread.exists_reciprocalGraphClosure_or_verticalGraph
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:36:09.062353+00:00
-- url     : https://prove2.me/submissions/e49550e6-b728-4a62-b846-78f3ac4f94ce

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_InfinityGraphLineCore
import Theorems.Thm_HuangN13_N13ReciprocalInfinityContraction_exists_horizontal_or_vertical_recovery

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IrreducibleQuadraticSpread
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The canonical direct-kernel construction closes the horizontal
reciprocal branch outright.  Its only alternative is the literal vertical
rank-two graph on the infinity chart. -/
theorem exists_reciprocalGraphClosure_or_verticalGraph
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : R₂)
    (hm :
      (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    Nonempty (ReciprocalGraphClosure D a b) ∨
      (∃ E :
          N13IntegralInfinityVerticalGraphJacobian.VerticalGraph,
        E.m.natDegree = 2 ∧
        N13ReciprocalInfinityContraction.integralInfinityIdeal
            D hdeg h0 =
          E.ideal) := by
  rcases
      HuangN13.N13ReciprocalInfinityContraction.exists_horizontal_or_vertical_recovery
        D hdeg h0 a b hm with
    ⟨E, hu, _huMonic, _huDegree, hvDegree, hwDegree, _hI,
      hordinate⟩ |
    hvertical
  · left
    exact
      ⟨{
        data := E
        data_u := hu
        v_degree := hvDegree.trans (by omega)
        w_degree := hwDegree
        generic_ordinate := hordinate
      }⟩
  · exact Or.inr hvertical
end
end MazurProof.N13IrreducibleQuadraticSpread
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem solution
    (D : MazurProof.SexticMumford.Mumford MazurProof.N13IrreducibleQuadraticSpread.Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : MazurProof.N13IrreducibleQuadraticSpread.R₂)
    (hm :
      (X ^ 2 + C (a : MazurProof.N13IrreducibleQuadraticSpread.Q₂) * X + C (b : MazurProof.N13IrreducibleQuadraticSpread.Q₂) : MazurProof.N13IrreducibleQuadraticSpread.Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    Nonempty (MazurProof.N13IrreducibleQuadraticSpread.ReciprocalGraphClosure D a b) ∨
      (∃ E :
          MazurProof.N13IntegralInfinityVerticalGraphJacobian.VerticalGraph,
        E.m.natDegree = 2 ∧
        MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal
            D hdeg h0 =
          E.ideal) := by
  exact MazurProof.N13IrreducibleQuadraticSpread.exists_reciprocalGraphClosure_or_verticalGraph D hdeg h0 a b hm
