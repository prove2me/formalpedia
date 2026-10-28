-- Prove2me | solution 1 for OAI.Kadison.HilbertPadding.amplified_extension_commutator_norm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:23:45.606307+00:00
-- url     : https://prove2.me/submissions/ab559dde-7f63-4f65-84d9-6a9354cd29ca

import Mathlib
import Definitions.Def_OAIQ039C022
import Definitions.Def_OAIQ039C027
import Theorems.Thm_OAI_Kadison_HilbertPadding_norm_extend_commutator

section
-- module Solutions.OAIQ039_CM.Commutator_AmplificationIsometry
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

namespace Kadison.HilbertPadding

open OperatorAmplification CyclicColumns

variable {A H K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (ι : Type*) [Fintype ι]

local instance instDecidableEq_solutions_2_r499259_1 : DecidableEq ι := Classical.decEq ι
lemma amplifyIsometry_adjoint (E : H →ₗᵢ[ℂ] K) (v : SumSpace (H:=K) ι) :
    (amplifyIsometry ι E).toContinuousLinearMap.adjoint v=
      WithLp.toLp 2 (fun i => E.toContinuousLinearMap.adjoint (v i)) := by
  apply ext_inner_left ℂ
  intro w
  rw [adjoint_inner_right]
  simp only [PiLp.inner_apply,amplifyIsometry_apply,adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap]

lemma diagonal_extend (E : H →ₗᵢ[ℂ] K) (Y : H →L[ℂ] H) :
    diagonal (H:=K) ι (extend E Y)=extend (amplifyIsometry ι E) (diagonal (H:=H) ι Y) := by
  ext v i
  simp [extend,amplifyIsometry_adjoint]

lemma amplifyIsometry_matrix_intertwines (E : H →ₗᵢ[ℂ] K)
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hE : ∀ a,(σ a).comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp (ρ a))
    (X : CStarMatrix ι ι A) :
    (matrixRepresentation σ X).comp (amplifyIsometry ι E).toContinuousLinearMap=
      (amplifyIsometry ι E).toContinuousLinearMap.comp (matrixRepresentation ρ X) := by
  ext v i
  change matrixAction (fun i j => σ (X i j)) (amplifyIsometry ι E v) i=
    E (matrixAction (fun i j => ρ (X i j)) v i)
  simp only [matrixAction_apply,amplifyIsometry_apply,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun T : H →L[ℂ] K => T (v j)) (hE (X i j))

lemma amplifyIsometry_adjoint_matrix_intertwines (E : H →ₗᵢ[ℂ] K)
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hE : ∀ a,(σ a).comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp (ρ a))
    (X : CStarMatrix ι ι A) :
    (amplifyIsometry ι E).toContinuousLinearMap.adjoint.comp (matrixRepresentation σ X)=
      (matrixRepresentation ρ X).comp (amplifyIsometry ι E).toContinuousLinearMap.adjoint := by
  have h := congrArg (fun T => T.adjoint) (amplifyIsometry_matrix_intertwines ι E ρ σ hE (star X))
  simpa only [adjoint_comp,←star_eq_adjoint,←map_star,star_star] using h

theorem amplified_extension_commutator_norm_oai (E : H →ₗᵢ[ℂ] K)
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hE : ∀ a,(σ a).comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp (ρ a))
    (Y : H →L[ℂ] H) (X : CStarMatrix ι ι A) :
    ‖diagonal (H:=K) ι (extend E Y)*matrixRepresentation σ X-
      matrixRepresentation σ X*diagonal (H:=K) ι (extend E Y)‖=
    ‖diagonal (H:=H) ι Y*matrixRepresentation ρ X-
      matrixRepresentation ρ X*diagonal (H:=H) ι Y‖ := by
  rw [diagonal_extend]
  exact norm_extend_commutator _ _ _ _ (amplifyIsometry_matrix_intertwines ι E ρ σ hE X)
    (amplifyIsometry_adjoint_matrix_intertwines ι E ρ σ hE X)

end Kadison.HilbertPadding

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Kadison.HilbertPadding.amplified_extension_commutator_norm_oai.{u_1, u_2, u_3, u_4} := @OAI.Kadison.HilbertPadding.amplified_extension_commutator_norm_oai.{u_1, u_2, u_3, u_4}
