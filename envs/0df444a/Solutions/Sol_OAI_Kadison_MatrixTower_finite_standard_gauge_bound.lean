-- Prove2me | solution 1 for OAI.Kadison.MatrixTower.finite_standard_gauge_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:36:21.67321+00:00
-- url     : https://prove2.me/submissions/1e965b5e-f6d3-4fa5-a55a-c5369dd2cc0f

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C063
import Definitions.Def_OAIQ039C067
import Definitions.Def_OAIQ039C073
import Theorems.Thm_OAI_Kadison_CyclicSpatial_matrixRepresentation_norm_eq
import Theorems.Thm_OAI_Kadison_MatrixTower_rectangular_bound_after_average
import Theorems.Thm_OAI_Kadison_TracialGNS_left_faithful
import Theorems.Thm_OAI_Kadison_commutatorSeminorm_nonneg

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteStandardGauge
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

local instance finiteStandardGaugeIndexDecidableEq_r040b4e_1 : DecidableEq ι := Classical.decEq ι
attribute [local instance] OAI.Kadison.MatrixTower.finiteStandardGaugeColumnDecidableEq
local instance finiteStandardGaugeSumDecidableEq_r040b4e_1 : DecidableEq (κ⊕ι) := Classical.decEq _
attribute [local instance] OAI.Kadison.MatrixTower.finiteStandardGaugeDoubledSumDecidableEq
omit [Nonempty κ] in
private theorem finite_standard_representation_estimates
    {A K : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (hπ : Function.Injective π)
    (Y : SumSpace (H:=K) ι →L[ℂ] SumSpace (H:=K) ι)
    (X : CStarMatrix κ κ A) :
    ‖matrixRepresentation ((diagonal (H:=K) ι).comp π) X‖ = ‖X‖ ∧
      ∀ a : A,
        ‖Y * ((diagonal (H:=K) ι).comp π) a - ((diagonal (H:=K) ι).comp π) a * Y‖ ≤
          commutatorSeminorm (NormalGNS.bicommutant (((diagonal (H:=K) ι).comp π).range)) Y * ‖a‖ := by
  let ρ := (diagonal (H:=K) ι).comp π
  let P := NormalGNS.bicommutant ρ.range
  have hdiag : Function.Injective (diagonal (H:=K) ι) := by
    intro a b hab
    ext x
    let i : ι := Classical.choice (inferInstance : Nonempty ι)
    have hh := congrArg (fun T : SumSpace (H:=K) ι →L[ℂ] SumSpace (H:=K) ι =>
      T (single ι i x) i) hab
    simpa only [diagonal_apply,single_apply,ite_true] using hh
  constructor
  · exact CyclicSpatial.matrixRepresentation_norm_eq ρ (hdiag.comp hπ) X
  · intro a
    have hmem : ρ a ∈ P := NormalGNS.subset_bicommutant ρ.range ⟨a,rfl⟩
    exact (commutator_bound P Y hmem).trans
      (mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le ρ a)
        (commutatorSeminorm_nonneg P Y))

variable (M : VonNeumannAlgebra H) [Nontrivial M] (E : ℕ → Stage M)

variable (τ : M →ₚ[ℂ] ℂ) (hnormal : NormalGNS.BoundedWOTContinuous M τ)

variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)

variable (F : FreeCornerPosition (MatrixGNS.trace (ι:=(Fin 2)×(κ⊕ι)) τ) ω
  (matrixVonNeumann ((Fin 2)×(κ⊕ι)) (0,Sum.inl k₀) (generated M E))
  (matrixInclusion ((Fin 2)×(κ⊕ι)) (0,Sum.inl k₀) M (generated M E) (generated_le M E)))

include hnormal hω F in
theorem finite_standard_gauge_bound_oai
    (hE : Monotone (fun n => (E n).hom.range))
    (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (X : CStarMatrix κ κ M) :
    ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) κ Y*
        matrixRepresentation ((diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom) X-
      matrixRepresentation ((diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom) X*
        diagonal (H:=SumSpace (H:=τ.GNS) ι) κ Y‖ ≤
      (3122*commutatorSeminorm (finiteStandardAlgebra ι M τ) Y)*
        ‖matrixRepresentation ((diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom) X‖ := by
  have estimates := finite_standard_representation_estimates ι κ τ.gnsStarAlgHom
    (TracialGNS.left_faithful τ hfaith) Y X
  have hδ := commutatorSeminorm_nonneg (finiteStandardAlgebra ι M τ) Y
  have preF := rectangular_bound_after_average ι κ k₀ M E τ hnormal ω hω
  change _ at preF F
  delta finiteRectangularBoundDoubledSumDecidableEq finiteStandardGaugeDoubledSumDecidableEq at preF F
  have withF := preF F
  have withData := withF hE hirr hτ hfaith h1
  have withY := withData Y hδ estimates.2
  exact (withY X).trans_eq (congrArg
    (fun r : ℝ => (3122 * commutatorSeminorm (finiteStandardAlgebra ι M τ) Y) * r)
    estimates.1.symm)

end Kadison.MatrixTower

end

end OAI
end

theorem solution : type_of% @OAI.Kadison.MatrixTower.finite_standard_gauge_bound_oai := @OAI.Kadison.MatrixTower.finite_standard_gauge_bound_oai
