-- Prove2me | solution 1 for OAI.Kadison.MatrixTower.finite_standard_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:33:26.992976+00:00
-- url     : https://prove2.me/submissions/c9814d6c-4161-4518-bc55-666dc50c6c25

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C063
import Definitions.Def_OAIQ039C067
import Definitions.Def_OAIQ039C073
import Theorems.Thm_OAI_Kadison_MatrixTower_exists_irreducible_stage_tower
import Theorems.Thm_OAI_Kadison_MatrixTower_exists_matrix_freeCornerPosition
import Theorems.Thm_OAI_Kadison_MatrixTower_finite_standard_entrywise_bound

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteStandardMainInterface
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

variable (ι : Type) [Fintype ι] [Nonempty ι] (h : ℕ) (hh : 1 ≤ h)

local instance finiteStandardMainInterfaceIndexDecidableEq_r176609_1 : DecidableEq ι := Classical.decEq ι
local instance finiteStandardMainInterfaceColumnDecidableEq_r176609_1 : DecidableEq (Fin h) := Classical.decEq (Fin h)
local instance finiteStandardMainInterfaceSumDecidableEq_r176609_1 : DecidableEq (Fin h⊕ι) := Classical.decEq _
attribute [local instance] OAI.Kadison.MatrixTower.finiteStandardMainInterfaceDoubledSumDecidableEq
variable (M : VonNeumannAlgebra H) [Nontrivial M] (E : ℕ → Stage M)

variable (τ : M →ₚ[ℂ] ℂ) (hnormal : NormalGNS.BoundedWOTContinuous M τ)

variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)

variable (F : FreeCornerPosition (MatrixGNS.trace (ι:=(Fin 2)×(Fin h⊕ι)) τ) ω
  (matrixVonNeumann ((Fin 2)×(Fin h⊕ι)) (0,Sum.inl (⟨0,lt_of_lt_of_le Nat.zero_lt_one hh⟩ : Fin h)) (generated M E))
  (matrixInclusion ((Fin 2)×(Fin h⊕ι)) (0,Sum.inl (⟨0,lt_of_lt_of_le Nat.zero_lt_one hh⟩ : Fin h)) M (generated M E) (generated_le M E)))

include hnormal hω F in
theorem finite_standard_matrixOperator_bound
    (hE : Monotone (fun n => (E n).hom.range))
    (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (X : Matrix (Fin h) (Fin h) (SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι))
    (hX : ∀ i j,X i j∈finiteStandardAlgebra ι M τ) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖ ≤
      (3122*commutatorSeminorm (finiteStandardAlgebra ι M τ) Y)*‖matrixOperator h X‖ := by
  let k₀ : Fin h := ⟨0,lt_of_lt_of_le Nat.zero_lt_one hh⟩
  let : Nonempty (Fin h) := ⟨k₀⟩
  have represented := finite_standard_entrywise_bound ι (Fin h) k₀ M E τ hnormal ω hω
  change _ at represented F
  delta finiteStandardRepresentedDoubledSumDecidableEq
    finiteStandardMainInterfaceDoubledSumDecidableEq at represented F
  exact represented F hE hirr hτ hfaith h1 Y X hX

end Kadison.MatrixTower

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteStandardUnconditional
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator Topology

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification TracialSequence CyclicColumns HilbertPadding

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) [Nontrivial M]

variable (τ : M →ₚ[ℂ] ℂ)

variable (ι : Type) [Fintype ι] [Nonempty ι]

local instance finiteStandardUnconditionalIndexDecidableEq_r176609_1 : DecidableEq ι := Classical.decEq ι
theorem finite_standard_bound_oai [TopologicalSpace.SeparableSpace τ.GNS]
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)
    (h : ℕ) (hh : 1 ≤ h)
    (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (X : Matrix (Fin h) (Fin h) (SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι))
    (hX : ∀ i j,X i j∈finiteStandardAlgebra ι M τ) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖ ≤
      (3122*commutatorSeminorm (finiteStandardAlgebra ι M τ) Y)*‖matrixOperator h X‖ := by
  obtain ⟨E,hE,hsize,hirr⟩ := exists_irreducible_stage_tower M τ hτ hnormal hfaith hone hfac hdiffuse
  let k₀ : Fin h := ⟨0,lt_of_lt_of_le Nat.zero_lt_one hh⟩
  let i₀ : (Fin 2)×(Fin h⊕ι) := (0,Sum.inl k₀)
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨F⟩ := exists_matrix_freeCornerPosition ((Fin 2)×(Fin h⊕ι)) i₀ M E τ ω
    hE hsize hirr hτ hnormal hfaith hone hω
  have bound := finite_standard_matrixOperator_bound ι h hh M E τ hnormal ω hω
  change _ at bound F
  delta finiteStandardMainInterfaceDoubledSumDecidableEq
    matrixFreePositionProducerDecidableEq at bound F
  exact bound F hE hirr hτ hfaith hone Y X hX

end Kadison.MatrixTower

end

end OAI
end

theorem solution : type_of% @OAI.Kadison.MatrixTower.finite_standard_bound_oai := @OAI.Kadison.MatrixTower.finite_standard_bound_oai
