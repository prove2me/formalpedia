-- Prove2me | solution 1 for OAI.Kadison.MatrixTower.exists_matrix_freeCornerPosition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:30:35.679829+00:00
-- url     : https://prove2.me/submissions/b0af2814-83d3-4087-8d41-4bfe64354ee7

import Mathlib
import Definitions.Def_OAIQ039C067
import Definitions.Def_OAIQ039C068
import Definitions.Def_OAIQ039C073
import Theorems.Thm_OAI_Kadison_MatrixGNS_trace_mul
import Theorems.Thm_OAI_Kadison_MatrixGNS_trace_one
import Theorems.Thm_OAI_Kadison_MatrixTower_generated_factor
import Theorems.Thm_OAI_Kadison_OperatorAmplification_amplifiedStage_in_relative
import Theorems.Thm_OAI_Kadison_OperatorAmplification_amplifiedStage_irreducible
import Theorems.Thm_OAI_Kadison_OperatorAmplification_amplifiedStage_monotone
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixTrace_faithful
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixTrace_normal
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixTrace_tracial
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrix_diffuse_of_stages
import Theorems.Thm_OAI_Kadison_TracialSequence_exists_freeCornerPosition_of_equiv_stages

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixNormalTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder Topology

open ContinuousLinearMapWOT

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_1
variable (τ : M →ₚ[ℂ] ℂ)

lemma matrixTrace_equiv (X : CStarMatrix ι ι M) :
    matrixTrace ι i₀ M τ (matrixEquiv ι i₀ M X)=MatrixGNS.trace (ι:=ι) τ X := by
  change MatrixGNS.trace (ι:=ι) τ ((matrixEquiv ι i₀ M).symm (matrixEquiv ι i₀ M X))=_
  rw [StarAlgEquiv.symm_apply_apply]

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixDiffuseTransfer
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.matrixDiffuseTransferIndexDecidableEq
lemma entry_diagonal (a : H →L[ℂ] H) (i : ι) :
    entry ι (diagonal (H:=H) ι a) i i=a := by
  ext x
  simp only [entry_apply,diagonal_single,single_apply,ite_true]

lemma diagonalHom_injective : Function.Injective (diagonalHom ι i₀ M) := by
  intro a b h
  apply Subtype.ext
  have he := congrArg (fun T : matrixVonNeumann ι i₀ M =>
    entry ι (T:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i₀ i₀) h
  simpa only [coe_diagonalHom,entry_diagonal] using he

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AmplifiedTowerGeometry
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace Kadison.OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

variable (E : ℕ → MatrixTower.Stage M)

attribute [local instance] OAI.Kadison.OperatorAmplification.amplifiedTowerGeometryIndexDecidableEq
lemma amplifiedStage_size (n : ℕ) :
    Fintype.card (amplifiedStage ι i₀ M (E n)).I=Fintype.card ι*Fintype.card (E n).I :=
  Fintype.card_prod ι (E n).I

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixFreePositionProducer
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification TracialSequence

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H) [Nontrivial M]

attribute [local instance] OAI.Kadison.MatrixTower.matrixFreePositionProducerDecidableEq
variable (E : ℕ → Stage M) (τ : M →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

theorem exists_matrix_freeCornerPosition_oai [TopologicalSpace.SeparableSpace τ.GNS]
    (hE : Monotone (fun n => (E n).hom.range))
    (hsize : ∀ n,n+1 ≤ Fintype.card (E n).I)
    (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (hω : (ω : Filter ℕ) ≤ atTop) :
    Nonempty (FreeCornerPosition (MatrixGNS.trace (ι:=ι) τ) ω
      (matrixVonNeumann ι i₀ (generated M E))
      (matrixInclusion ι i₀ M (generated M E) (generated_le M E))) := by
  let : Nonempty ι := ⟨i₀⟩
  let P := matrixVonNeumann ι i₀ M
  let R := generated M E
  let Q := matrixVonNeumann ι i₀ R
  let σ := matrixTrace ι i₀ M τ
  let F := fun n => amplifiedStage ι i₀ M (E n)
  let : Nontrivial P := (diagonalHom_injective ι i₀ M).nontrivial
  let U := standardMatrixUnitary ι i₀ M τ
  let : TopologicalSpace.SeparableSpace σ.GNS :=
    U.symm.surjective.denseRange.separableSpace U.symm.continuous
  have hQP : Q ≤ P := matrixVonNeumann_mono ι i₀ (generated_le M E)
  have hj (q : Q) : matrixEquiv ι i₀ M
      (matrixInclusion ι i₀ M R (generated_le M E) q)=NormalSubalgebra.inclusion P Q hQP q := by
    change matrixEquiv ι i₀ M ((matrixEquiv ι i₀ M).symm _)=_
    rw [StarAlgEquiv.apply_symm_apply]
    rfl
  have hQdiff : DiffuseProjection.HasNoMinimalProjections Q := by
    let ρ := NormalSubalgebra.trace M R (generated_le M E) τ
    apply matrix_diffuse_of_stages ι i₀ R (generated_factor M E hirr) ρ
      (NormalSubalgebra.tracial M R (generated_le M E) τ hτ)
      (NormalSubalgebra.faithful M R (generated_le M E) τ hfaith)
      (NormalSubalgebra.one M R (generated_le M E) τ h1) (generatedStage M E)
    intro N
    exact ⟨N,lt_of_lt_of_le (Nat.lt_succ_self N) (hsize N)⟩
  apply exists_freeCornerPosition_of_equiv_stages P Q hQP (matrixEquiv ι i₀ M)
    (matrixInclusion ι i₀ M R (generated_le M E)) hj (MatrixGNS.trace (ι:=ι) τ) σ ω F
    (amplifiedStage_monotone ι i₀ M E hE)
    (matrixTrace_equiv ι i₀ M τ) (MatrixGNS.trace_mul τ hτ)
    (matrixTrace_tracial ι i₀ M τ hτ) hω (matrixTrace_normal ι i₀ M τ hnormal)
    (matrixTrace_faithful ι i₀ M τ hfaith) (MatrixGNS.trace_one τ h1)
    (amplifiedStage_irreducible ι i₀ M E hirr) _ _ hQdiff
  · intro n a
    apply amplifiedStage_in_relative ι i₀ M E R _ n a
    intro k b
    exact stage_mem M E k b
  · apply tendsto_atTop_mono (f := fun n : ℕ => (n:ℝ)) _ tendsto_natCast_atTop_atTop
    intro n
    have hc : 1 ≤ Fintype.card ι := Fintype.card_pos
    have hcard : n ≤ Fintype.card (F n).I := by
      rw [amplifiedStage_size]
      exact (Nat.le_succ n).trans ((hsize n).trans (Nat.le_mul_of_pos_left _ hc))
    exact_mod_cast hcard

end Kadison.MatrixTower

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.MatrixTower.exists_matrix_freeCornerPosition_oai := @OAI.Kadison.MatrixTower.exists_matrix_freeCornerPosition_oai
