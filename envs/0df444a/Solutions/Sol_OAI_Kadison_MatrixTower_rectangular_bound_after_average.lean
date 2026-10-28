-- Prove2me | solution 1 for OAI.Kadison.MatrixTower.rectangular_bound_after_average
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:38:29.641428+00:00
-- url     : https://prove2.me/submissions/c00ae015-adda-428b-bb58-5608bd480de4

import Mathlib
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C031
import Definitions.Def_OAIQ039C063
import Definitions.Def_OAIQ039C067
import Definitions.Def_OAIQ039C073
import Theorems.Thm_OAI_Kadison_MatrixTower_rectangular_contraction_after_average

section
-- module Solutions.OAIQ039_CM.Commutator_HomogeneousBound
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

lemma linear_norm_bound_from_unitball (f : V →ₗ[ℂ] W) (C : ℝ)
    (h : ∀ x : V,‖x‖≤1 → ‖f x‖≤C) (x : V) : ‖f x‖≤C*‖x‖ := by
  by_cases hx : x=0
  · simp [hx]
  have hp : 0<‖x‖ := norm_pos_iff.mpr hx
  let z : ℂ := ((‖x‖⁻¹ : ℝ) : ℂ)
  have hz : ‖z‖=‖x‖⁻¹ := by simp [z]
  have hu : ‖z • x‖≤1 := by
    rw [norm_smul,hz,inv_mul_cancel₀ hp.ne']
  have hb : ‖x‖⁻¹*‖f x‖≤C := by
    simpa only [map_smul,norm_smul,hz] using h (z • x) hu
  have hb' := (inv_mul_le_iff₀ hp).mp hb
  simpa only [mul_comm] using hb'

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteRectangularBound
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

local instance finiteRectangularBoundIndexDecidableEq_r906b38_1 : DecidableEq ι := Classical.decEq ι
attribute [local instance] OAI.Kadison.MatrixTower.finiteRectangularBoundColumnDecidableEq
local instance finiteRectangularBoundSumDecidableEq_r906b38_1 : DecidableEq (κ⊕ι) := Classical.decEq _
attribute [local instance] OAI.Kadison.MatrixTower.finiteRectangularBoundDoubledSumDecidableEq
omit [Nonempty κ] in
private lemma rectangular_bound_from_unitball
    {A K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (Y : SumSpace (H:=K) ι →L[ℂ] SumSpace (H:=K) ι)
    (C : ℝ)
    (h : ∀ X : CStarMatrix κ κ A, ‖X‖ ≤ 1 →
      ‖diagonal (H:=SumSpace (H:=K) ι) κ Y *
          matrixRepresentation ((diagonal (H:=K) ι).comp π) X -
        matrixRepresentation ((diagonal (H:=K) ι).comp π) X *
          diagonal (H:=SumSpace (H:=K) ι) κ Y‖ ≤ C)
    (X : CStarMatrix κ κ A) :
    ‖diagonal (H:=SumSpace (H:=K) ι) κ Y *
        matrixRepresentation ((diagonal (H:=K) ι).comp π) X -
      matrixRepresentation ((diagonal (H:=K) ι).comp π) X *
        diagonal (H:=SumSpace (H:=K) ι) κ Y‖ ≤ C * ‖X‖ := by
  let ρ := (diagonal (H:=K) ι).comp π
  let f := representedCommutator (matrixRepresentation (ι:=κ) ρ)
    (diagonal (H:=SumSpace (H:=K) ι) κ Y)
  exact linear_norm_bound_from_unitball f C h X

variable (M : VonNeumannAlgebra H) [Nontrivial M] (E : ℕ → Stage M)

variable (τ : M →ₚ[ℂ] ℂ) (hnormal : NormalGNS.BoundedWOTContinuous M τ)

variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)

variable (F : FreeCornerPosition (MatrixGNS.trace (ι:=(Fin 2)×(κ⊕ι)) τ) ω
  (matrixVonNeumann ((Fin 2)×(κ⊕ι)) (0,Sum.inl k₀) (generated M E))
  (matrixInclusion ((Fin 2)×(κ⊕ι)) (0,Sum.inl k₀) M (generated M E) (generated_le M E)))

include hnormal hω F in
theorem rectangular_bound_after_average_oai
    (hE : Monotone (fun n => (E n).hom.range))
    (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hY : ∀ a : M,‖Y*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Y‖ ≤ δ*‖a‖)
    (X : CStarMatrix κ κ M) :
    ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) κ Y*
        matrixRepresentation ((diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom) X-
      matrixRepresentation ((diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom) X*
        diagonal (H:=SumSpace (H:=τ.GNS) ι) κ Y‖ ≤ (3122*δ)*‖X‖ := by
  have preF := rectangular_contraction_after_average ι κ k₀ M E τ hnormal ω hω
  change _ at preF F
  delta finiteRectangularContractionDoubledSumDecidableEq at preF
  delta finiteRectangularBoundDoubledSumDecidableEq at F
  have withF := preF F
  have withData := withF hE hirr hτ hfaith h1
  have withY := withData Y hδ hY
  exact rectangular_bound_from_unitball ι κ τ.gnsStarAlgHom Y (3122*δ) withY X

end Kadison.MatrixTower

end

end OAI
end

theorem solution : type_of% @OAI.Kadison.MatrixTower.rectangular_bound_after_average_oai := @OAI.Kadison.MatrixTower.rectangular_bound_after_average_oai
