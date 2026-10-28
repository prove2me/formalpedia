-- Prove2me | solution 1 for OAI.Kadison.commutator_column_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:15:32.996+00:00
-- url     : https://prove2.me/submissions/23621d22-339c-49bf-bb6c-33cf88143db9

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C022
import Definitions.Def_OAIQ039C030
import Theorems.Thm_OAI_Kadison_RectangularColumn_column_bound
import Theorems.Thm_OAI_Kadison_commutatorSeminorm_nonneg

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicMatrix
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.CyclicColumns

variable {A H F ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

lemma columnNorm_nonneg (v : ι → A) : 0 ≤ columnNorm v := norm_nonneg _

end Kadison.CyclicColumns

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MainMatrix
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

universe u

open scoped InnerProductSpace BigOperators ComplexOrder

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma innerDerivation_norm_le (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) :
    ‖innerDerivation P Y‖ ≤ commutatorSeminorm P Y :=
  ContinuousLinearMap.opNorm_le_bound _ (commutatorSeminorm_nonneg P Y)
    (fun a => commutator_bound P Y a.property)

lemma innerDerivation_mul (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) (a b : P) :
    innerDerivation P Y (a*b)=(innerDerivation P Y a).comp (b:K →L[ℂ] K)+
      (a:K →L[ℂ] K).comp (innerDerivation P Y b) := by
  change Y*((a:K →L[ℂ] K)*b)-(a:K →L[ℂ] K)*b*Y=
    (Y*a-(a:K →L[ℂ] K)*Y)*b+(a:K →L[ℂ] K)*(Y*b-(b:K →L[ℂ] K)*Y)
  noncomm_ring

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProperlyInfinite
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma commutator_column_bound_oai (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K)
    (h : ℕ) (a : Fin h → P) (ha : CyclicColumns.columnNorm a≤1) :
    ‖operatorColumn h (fun i => Y*(a i : K →L[ℂ] K)-(a i : K →L[ℂ] K)*Y)‖ ≤
      4*commutatorSeminorm P Y := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [commutatorSeminorm_nonneg P Y])
  intro ξ
  let : StarOrderedRing P.toStarSubalgebra := VonNeumannCStar.starOrderedRing P
  have hb := RectangularColumn.column_bound P.toStarSubalgebra.subtype P.toStarSubalgebra.subtype
    (innerDerivation P Y) (innerDerivation_mul P Y) a ξ
  have he : operatorColumn h (fun i => Y*(a i : K →L[ℂ] K)-(a i : K →L[ℂ] K)*Y) ξ =
      WithLp.toLp 2 (fun i => innerDerivation P Y (a i) ξ) := by ext i; rfl
  rw [he]
  refine hb.trans ?_
  have hn := innerDerivation_norm_le P Y
  have hp := CyclicColumns.columnNorm_nonneg a
  have hm := (mul_le_mul hn ha hp (commutatorSeminorm_nonneg P Y)).trans_eq (mul_one _)
  calc
    (4*‖innerDerivation P Y‖)*CyclicColumns.columnNorm a*‖ξ‖ =
      4*(‖innerDerivation P Y‖*CyclicColumns.columnNorm a)*‖ξ‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num)) (norm_nonneg ξ)

end Kadison

end

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.Kadison.commutator_column_bound_oai.{u} := @OAI.Kadison.commutator_column_bound_oai.{u}
