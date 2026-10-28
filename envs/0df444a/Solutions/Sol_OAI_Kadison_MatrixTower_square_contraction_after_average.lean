-- Prove2me | solution 1 for OAI.Kadison.MatrixTower.square_contraction_after_average
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:43:51.556319+00:00
-- url     : https://prove2.me/submissions/63525026-a1c8-4af4-8abc-a164e8fca01f

import Mathlib
import Definitions.Def_OAIQ039C031
import Definitions.Def_OAIQ039C063
import Definitions.Def_OAIQ039C067
import Definitions.Def_OAIQ039C073
import Theorems.Thm_OAI_Kadison_HilbertPadding_amplified_extension_commutator_norm
import Theorems.Thm_OAI_Kadison_HilbertPadding_doubleCopies_commutator_norm
import Theorems.Thm_OAI_Kadison_HilbertPadding_doubleCopies_diagonal
import Theorems.Thm_OAI_Kadison_MatrixGNS_flatBalancedUnitary_sq
import Theorems.Thm_OAI_Kadison_MatrixGNS_flatBalancedUnitary_trace
import Theorems.Thm_OAI_Kadison_MatrixGNS_flatBalanced_commutator_dominates
import Theorems.Thm_OAI_Kadison_MatrixTower_square_symmetry_after_average

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteSquareContraction
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

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι)

local instance instDecidableEq_solutions_rc8370b_1 : DecidableEq ι := Classical.decEq ι
attribute [local instance] OAI.Kadison.MatrixTower.finiteSquareContractionDoubledIndexDecidableEq
omit [Nonempty ι] in
private lemma square_contraction_norm_le
    {A K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (Y : SumSpace (H:=K) ι →L[ℂ] SumSpace (H:=K) ι)
    (X : CStarMatrix ι ι A) (hX : ‖X‖ ≤ 1) :
    ‖diagonal (H:=SumSpace (H:=K) ι) ι Y*
        matrixRepresentation ((diagonal (H:=K) ι).comp π) X-
      matrixRepresentation ((diagonal (H:=K) ι).comp π) X*
        diagonal (H:=SumSpace (H:=K) ι) ι Y‖ ≤
    ‖diagonal (H:=SumSpace (H:=K) ((Fin 2)×ι)) ((Fin 2)×ι)
        (extend (doubleCopies (H:=K) ι) Y)*
        matrixRepresentation ((diagonal (H:=K) ((Fin 2)×ι)).comp π)
          (MatrixGNS.flatBalancedUnitary ι X hX)-
      matrixRepresentation ((diagonal (H:=K) ((Fin 2)×ι)).comp π)
          (MatrixGNS.flatBalancedUnitary ι X hX)*
        diagonal (H:=SumSpace (H:=K) ((Fin 2)×ι)) ((Fin 2)×ι)
          (extend (doubleCopies (H:=K) ι) Y)‖ := by
  let ρ := (diagonal (H:=K) ι).comp π
  let σ := (diagonal (H:=K) ((Fin 2)×ι)).comp π
  let Z := extend (doubleCopies (H:=K) ι) Y
  have hd := MatrixGNS.flatBalanced_commutator_dominates ι σ Z X hX
  have hreduce (a : A) := doubleCopies_diagonal ι (π a)
  have hr := amplified_extension_commutator_norm ι (doubleCopies (H:=K) ι) ρ σ hreduce Y X
  rw [hr] at hd
  exact hd

variable (M : VonNeumannAlgebra H) [Nontrivial M] (E : ℕ → Stage M)

variable (τ : M →ₚ[ℂ] ℂ) (hnormal : NormalGNS.BoundedWOTContinuous M τ)

variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)

variable (F : FreeCornerPosition (MatrixGNS.trace (ι:=(Fin 2)×ι) τ) ω
  (matrixVonNeumann ((Fin 2)×ι) (0,i₀) (generated M E))
  (matrixInclusion ((Fin 2)×ι) (0,i₀) M (generated M E) (generated_le M E)))

include hnormal hω F in
theorem square_contraction_after_average_oai
    (hE : Monotone (fun n => (E n).hom.range))
    (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hY : ∀ a : M,‖Y*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Y‖ ≤ δ*‖a‖)
    (X : CStarMatrix ι ι M) (hX : ‖X‖≤1) :
    ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) ι Y*MatrixGNS.representation τ X-
      MatrixGNS.representation τ X*diagonal (H:=SumSpace (H:=τ.GNS) ι) ι Y‖ ≤ 3122*δ := by
  let J := (Fin 2)×ι
  let Z := extend (doubleCopies (H:=τ.GNS) ι) Y
  have hZ (a : M) :=
    (doubleCopies_commutator_norm ι Y (τ.gnsStarAlgHom a)).le.trans (hY a)
  have boundRule := square_symmetry_after_average J (0,i₀) M E τ hnormal ω hω
  change _ at boundRule F
  dsimp (config := { instances := true }) only [J, finiteSquareConditionalBoundDecidableEq] at boundRule
  dsimp (config := { instances := true }) only
    [square_index_decidable_eq ι] at F
  have positioned := boundRule F
  have towerBound := positioned hE hirr hτ hfaith h1
  have forZ := towerBound Z hδ hZ
  have hbound := forZ
    (MatrixGNS.flatBalancedUnitary ι X hX)
    (MatrixGNS.flatBalancedUnitary_trace ι τ hτ X hX)
    (MatrixGNS.flatBalancedUnitary_sq ι X hX)
  have h := square_contraction_norm_le ι τ.gnsStarAlgHom Y X hX
  exact h.trans hbound

end Kadison.MatrixTower

end

end OAI
end

theorem solution : type_of% @OAI.Kadison.MatrixTower.square_contraction_after_average_oai := @OAI.Kadison.MatrixTower.square_contraction_after_average_oai
