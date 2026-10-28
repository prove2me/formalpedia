-- Prove2me | solution 1 for OAI.Kadison.CentralSpectral.stable_model_center
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T15:23:46.34893+00:00
-- url     : https://prove2.me/submissions/0856cf0d-249e-491f-8d1b-7e02ccd30c21

import Mathlib
import Definitions.Def_OAIQ039C027
import Definitions.Def_OAIQ039C031
import Definitions.Def_OAIQ039C037
import Definitions.Def_OAIQ039C054
import Theorems.Thm_OAI_Kadison_InfiniteAmplification_stable_center_range

section
-- module Solutions.OAIQ039_CM.Commutator_L2InfiniteSumCoordinates
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped InnerProductSpace Topology ENNReal

namespace Kadison.Decomposable

open InfiniteAmplification

local instance l2InfiniteSumCoordinatesDecidableEq_r29ab29_1 {α : Sort*} : DecidableEq α := Classical.decEq α
variable {Ω H ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [Countable ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [TopologicalSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

lemma scalarVectorMultiplier_ae (f : C(Ω,ℂ)) (v : Lp H 2 μ) :
    scalarVectorMultiplier μ f v=ᵐ[μ] fun x => f x • v x := operator_ae ..

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StableScalarGeometry
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

open InfiniteAmplification

variable {Ω H ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [Countable ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [TopologicalSpace Ω] [T2Space Ω] [CompactSpace Ω] [BorelSpace Ω]

omit [T2Space Ω] in
lemma scalarVectorMultiplier_commutes_constant (f : C(Ω,ℂ)) (C : H →L[ℂ] H) :
    Commute (operator μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall (fun _ => le_rfl))) (scalarVectorMultiplier μ f) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [operator_ae μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
    (Eventually.of_forall (fun _ => le_rfl)) (scalarVectorMultiplier μ f v),
    scalarVectorMultiplier_ae μ f v,
    scalarVectorMultiplier_ae μ f (operator μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall (fun _ => le_rfl)) v),
    operator_ae μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall (fun _ => le_rfl)) v] with x h₁ h₂ h₃ h₄
  change operator μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
    (Eventually.of_forall (fun _ => le_rfl)) (scalarVectorMultiplier μ f v) x=
    scalarVectorMultiplier μ f (operator μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
    (Eventually.of_forall (fun _ => le_rfl)) v) x
  rw [h₁,h₂,h₃,h₄]
  exact C.map_smul _ _

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CentralSpectralGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open MeasureTheory Filter

open scoped Topology InnerProductSpace ComplexOrder

namespace Kadison.CentralSpectral

open CyclicSpectral Decomposable InfiniteAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (μ : Measure (Spectrum M))

variable (U : Space ℕ H ≃ₗᵢ[ℂ] Lp (Space ℕ ℂ) 2 μ)

variable (hU : ∀ (a : CentralCorner.center M) (v : Space ℕ H),
  U (map (a : H →L[ℂ] H) v)=scalarVectorMultiplier μ (gelfandStarTransform _ a) (U v))

include hU

lemma conjugate_center (a : CentralCorner.center M) :
    U.conjStarAlgEquiv (map a.val)=scalarVectorMultiplier μ (gelfandStarTransform _ a) := by
  apply ContinuousLinearMap.ext
  intro v
  change U (map a.val (U.symm v))=scalarVectorMultiplier μ (gelfandStarTransform _ a) v
  rw [hU,U.apply_symm_apply]

lemma center_commutes_constant
    (Z : Lp (Space ℕ ℂ) 2 μ →L[ℂ] Lp (Space ℕ ℂ) 2 μ)
    (hZ : Z∈CentralCorner.center (UnitaryTransport.algebra U (algebra M)))
    (C : Space ℕ ℂ →L[ℂ] Space ℕ ℂ) :
    Commute (operator μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall (fun _ => le_rfl))) Z := by
  obtain ⟨a,ha⟩ := stable_center_range M U Z hZ
  rw [←ha,conjugate_center M μ U hU a]
  exact scalarVectorMultiplier_commutes_constant μ _ C

end Kadison.CentralSpectral

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StableModelBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open MeasureTheory Filter

open scoped Topology InnerProductSpace ComplexOrder

namespace Kadison.CentralSpectral

open CyclicSpectral Decomposable InfiniteAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (μ : Measure (Spectrum M))

variable (U : Space ℕ H ≃ₗᵢ[ℂ] Lp (Space ℕ ℂ) 2 μ)

variable (hU : ∀ (a : CentralCorner.center M) (v : Space ℕ H),
  U (map (a : H →L[ℂ] H) v)=scalarVectorMultiplier μ (gelfandStarTransform _ a) (U v))

variable (hind : ∀ (s : Set (Spectrum M)) (hs : MeasurableSet s),
  ∃ a : CentralCorner.center M,
    scalarMultiplier μ (gelfandStarTransform _ a)=indicatorOperator μ s hs)

include hU hind

omit hind in
lemma stable_model_center_oai [IsFiniteMeasure μ] (Z : Lp (Space ℕ ℂ) 2 μ →L[ℂ] Lp (Space ℕ ℂ) 2 μ)
    (hZ : Z∈UnitaryTransport.algebra U (algebra M))
    (hZc : Z∈(UnitaryTransport.algebra U (algebra M)).commutant)
    (C : Space ℕ ℂ →L[ℂ] Space ℕ ℂ) :
    Commute (operator μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall (fun _ => le_rfl))) Z :=
  center_commutes_constant M μ U hU Z ⟨hZ,hZc⟩ C

end Kadison.CentralSpectral

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.CentralSpectral.stable_model_center_oai := @OAI.Kadison.CentralSpectral.stable_model_center_oai
