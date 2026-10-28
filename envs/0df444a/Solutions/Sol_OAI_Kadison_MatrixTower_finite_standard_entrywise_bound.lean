-- Prove2me | solution 1 for OAI.Kadison.MatrixTower.finite_standard_entrywise_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:36:20.437005+00:00
-- url     : https://prove2.me/submissions/e9169db5-620f-4234-980f-d93812bff896

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C063
import Definitions.Def_OAIQ039C067
import Definitions.Def_OAIQ039C073
import Theorems.Thm_OAI_Kadison_MatrixTower_finiteStandard_range
import Theorems.Thm_OAI_Kadison_MatrixTower_finite_standard_gauge_bound

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteStandardRepresented
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification TracialSequence CyclicColumns HilbertPadding

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type) [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ] (k₀ : κ)

local instance finiteStandardRepresentedIndexDecidableEq_rcf3c43_1 : DecidableEq ι := Classical.decEq ι
local instance finiteStandardRepresentedColumnDecidableEq_rcf3c43_1 : DecidableEq κ := Classical.decEq κ
local instance finiteStandardRepresentedSumDecidableEq_rcf3c43_1 : DecidableEq (κ⊕ι) := Classical.decEq _
attribute [local instance] OAI.Kadison.MatrixTower.finiteStandardRepresentedDoubledSumDecidableEq
variable (M : VonNeumannAlgebra H) [Nontrivial M] (E : ℕ → Stage M)

variable (τ : M →ₚ[ℂ] ℂ) (hnormal : NormalGNS.BoundedWOTContinuous M τ)

variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)

variable (F : FreeCornerPosition (MatrixGNS.trace (ι:=(Fin 2)×(κ⊕ι)) τ) ω
  (matrixVonNeumann ((Fin 2)×(κ⊕ι)) (0,Sum.inl k₀) (generated M E))
  (matrixInclusion ((Fin 2)×(κ⊕ι)) (0,Sum.inl k₀) M (generated M E) (generated_le M E)))

include hnormal hω F in
theorem finite_standard_entrywise_bound_oai
    (hE : Monotone (fun n => (E n).hom.range))
    (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (X : Matrix κ κ (SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι))
    (hX : ∀ i j,X i j∈finiteStandardAlgebra ι M τ) :
    ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) κ Y*matrixAction X-
      matrixAction X*diagonal (H:=SumSpace (H:=τ.GNS) ι) κ Y‖ ≤
      (3122*commutatorSeminorm (finiteStandardAlgebra ι M τ) Y)*‖matrixAction X‖ := by
  have hlift (i j : κ) := (finiteStandard_range ι M τ hτ hnormal (X i j)).mp (hX i j)
  let A : CStarMatrix κ κ M := CStarMatrix.ofMatrix (fun i j => Classical.choose (hlift i j))
  have hA (i j : κ) : diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (A i j))=X i j :=
    Classical.choose_spec (hlift i j)
  have hrep : matrixRepresentation ((diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom) A=matrixAction X := by
    apply ContinuousLinearMap.ext
    intro v
    apply PiLp.ext
    intro i
    simp only [CyclicSpatial.represented_matrix_apply,StarAlgHom.comp_apply,hA]
    exact (CyclicColumns.matrixAction_apply X v i).symm
  have gauge := finite_standard_gauge_bound ι κ k₀ M E τ hnormal ω hω
  change _ at gauge F
  delta finiteStandardGaugeDoubledSumDecidableEq finiteStandardRepresentedDoubledSumDecidableEq at gauge F
  have hb := gauge F hE hirr hτ hfaith h1 Y A
  simpa only [hrep] using hb

end Kadison.MatrixTower

end

end OAI
end

theorem solution : type_of% @OAI.Kadison.MatrixTower.finite_standard_entrywise_bound_oai := @OAI.Kadison.MatrixTower.finite_standard_entrywise_bound_oai
