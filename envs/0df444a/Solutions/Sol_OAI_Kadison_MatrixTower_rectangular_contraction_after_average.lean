-- Prove2me | solution 1 for OAI.Kadison.MatrixTower.rectangular_contraction_after_average
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:41:20.197525+00:00
-- url     : https://prove2.me/submissions/30341c0a-d8ec-4baf-a664-d20cebc3a45d

import Mathlib
import Definitions.Def_OAIQ039C031
import Definitions.Def_OAIQ039C063
import Definitions.Def_OAIQ039C067
import Definitions.Def_OAIQ039C073
import Theorems.Thm_OAI_Kadison_HilbertPadding_amplified_extension_commutator_norm
import Theorems.Thm_OAI_Kadison_HilbertPadding_matrix_padding_commutator_norm
import Theorems.Thm_OAI_Kadison_HilbertPadding_norm_padMatrix_le
import Theorems.Thm_OAI_Kadison_HilbertPadding_rightCopies_commutator_norm
import Theorems.Thm_OAI_Kadison_HilbertPadding_rightCopies_diagonal
import Theorems.Thm_OAI_Kadison_MatrixTower_square_contraction_after_average

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteRectangularContraction
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

variable (ι κ : Type) [Fintype ι] [Fintype κ] [Nonempty κ] (k₀ : κ)

local instance finiteRectangularContractionIndexDecidableEq_r8e9ab8_1 : DecidableEq ι := Classical.decEq ι
local instance finiteRectangularContractionColumnDecidableEq_r8e9ab8_1 : DecidableEq κ := Classical.decEq κ
local instance finiteRectangularContractionSumDecidableEq_r8e9ab8_1 : DecidableEq (κ⊕ι) := Classical.decEq _
attribute [local instance] OAI.Kadison.MatrixTower.finiteRectangularContractionDoubledSumDecidableEq
omit [Nonempty κ] in
private lemma rectangular_contraction_norm_eq
    {A K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (Y : SumSpace (H:=K) ι →L[ℂ] SumSpace (H:=K) ι)
    (X : CStarMatrix κ κ A) :
    ‖diagonal (H:=SumSpace (H:=K) ι) κ Y *
        matrixRepresentation ((diagonal (H:=K) ι).comp π) X -
      matrixRepresentation ((diagonal (H:=K) ι).comp π) X *
        diagonal (H:=SumSpace (H:=K) ι) κ Y‖ =
    ‖diagonal (H:=SumSpace (H:=K) (κ⊕ι)) (κ⊕ι)
        (extend (rightCopies (H:=K) ι κ) Y) *
        matrixRepresentation ((diagonal (H:=K) (κ⊕ι)).comp π) (padMatrix κ ι X) -
      matrixRepresentation ((diagonal (H:=K) (κ⊕ι)).comp π) (padMatrix κ ι X) *
        diagonal (H:=SumSpace (H:=K) (κ⊕ι)) (κ⊕ι)
          (extend (rightCopies (H:=K) ι κ) Y)‖ := by
  let ρ := (diagonal (H:=K) ι).comp π
  let σ := (diagonal (H:=K) (κ⊕ι)).comp π
  let Z := extend (rightCopies (H:=K) ι κ) Y
  have hp := matrix_padding_commutator_norm κ ι σ Z X
  have hreduce (a : A) := rightCopies_diagonal ι κ (π a)
  have hr := amplified_extension_commutator_norm κ (rightCopies (H:=K) ι κ) ρ σ hreduce Y X
  exact (hp.trans hr).symm

variable (M : VonNeumannAlgebra H) [Nontrivial M] (E : ℕ → Stage M)

variable (τ : M →ₚ[ℂ] ℂ) (hnormal : NormalGNS.BoundedWOTContinuous M τ)

variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)

variable (F : FreeCornerPosition (MatrixGNS.trace (ι:=(Fin 2)×(κ⊕ι)) τ) ω
  (matrixVonNeumann ((Fin 2)×(κ⊕ι)) (0,Sum.inl k₀) (generated M E))
  (matrixInclusion ((Fin 2)×(κ⊕ι)) (0,Sum.inl k₀) M (generated M E) (generated_le M E)))

include hnormal hω F in
theorem rectangular_contraction_after_average_oai
    (hE : Monotone (fun n => (E n).hom.range))
    (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hY : ∀ a : M,‖Y*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Y‖ ≤ δ*‖a‖)
    (X : CStarMatrix κ κ M) (hX : ‖X‖≤1) :
    ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) κ Y*
        matrixRepresentation ((diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom) X-
      matrixRepresentation ((diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom) X*
        diagonal (H:=SumSpace (H:=τ.GNS) ι) κ Y‖ ≤ 3122*δ := by
  let J := κ⊕ι
  let Z := extend (rightCopies (H:=τ.GNS) ι κ) Y
  have hZ (a : M) :=
    (rightCopies_commutator_norm ι κ Y (τ.gnsStarAlgHom a)).le.trans (hY a)
  have preF := square_contraction_after_average (H:=H) J (Sum.inl k₀) M E τ hnormal ω hω
  -- Normalize index dictionaries before comparing the matrix algebra parameters.
  change _ at preF F
  dsimp (config := {instances := true}) only
    [J, finiteSquareContractionDoubledIndexDecidableEq] at preF
  dsimp (config := {instances := true}) only [rectangular_index_decidable_eq ι κ] at F
  have withF := preF F
  have withData := withF hE hirr hτ hfaith h1
  have withY := withData Z hδ hZ
  have hbound := withY (padMatrix κ ι X) ((norm_padMatrix_le κ ι X).trans hX)
  have h := rectangular_contraction_norm_eq ι κ τ.gnsStarAlgHom Y X
  exact h.le.trans hbound

end Kadison.MatrixTower

end

end OAI
end

theorem solution : type_of% @OAI.Kadison.MatrixTower.rectangular_contraction_after_average_oai := @OAI.Kadison.MatrixTower.rectangular_contraction_after_average_oai
