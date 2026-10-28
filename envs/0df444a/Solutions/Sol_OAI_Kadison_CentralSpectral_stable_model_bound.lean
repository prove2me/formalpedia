-- Prove2me | solution 1 for OAI.Kadison.CentralSpectral.stable_model_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T15:23:45.759108+00:00
-- url     : https://prove2.me/submissions/07641aff-8a18-4502-97a8-fb42b8087efa

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C027
import Definitions.Def_OAIQ039C031
import Definitions.Def_OAIQ039C037
import Definitions.Def_OAIQ039C054
import Theorems.Thm_OAI_Kadison_CentralSpectral_stable_model_center
import Theorems.Thm_OAI_Kadison_Decomposable_uniform_commutator_in_central_spectral_model_nonzero
import Theorems.Thm_OAI_Kadison_Decomposable_vector_indicator_of_scalar
import Theorems.Thm_OAI_Kadison_InfiniteAmplification_separable_space
import Theorems.Thm_OAI_Kadison_UnitaryTransport_bound_of_conjugate_bound
import Theorems.Thm_OAI_Kadison_commutatorSeminorm_nonneg

section
-- module Solutions.OAIQ039_CM.Commutator_InfiniteCenter
attribute [-instance] _root_.OAI.Kadison.CentralSpectral.centerCommCStar _root_.OAI.Kadison.CentralSpectral.spectrumBorel _root_.OAI.Kadison.CentralSpectral.spectrumMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

namespace Kadison.InfiniteAmplification

local instance infiniteCenterDecidableEq_r1cd4c1_1 {α : Sort*} : DecidableEq α := Classical.decEq α
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma map_injective : Function.Injective (map (ι:=ℕ) (H:=H) (G:=H)) := by
  intro S T h
  ext x
  have he := congrArg (fun R : Space ℕ H →L[ℂ] Space ℕ H => R (lp.single 2 0 x) 0) h
  simpa only [map_apply,lp.single_apply,Pi.single_eq_same] using he

lemma map_mem_algebra (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) (ha : a∈M) :
    map (ι:=ℕ) a∈algebra M := ⟨⟨a,ha⟩,rfl⟩

lemma map_mem_center (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    map (ι:=ℕ) a∈CentralCorner.center (algebra M) ↔ a∈CentralCorner.center M := by
  rw [CentralCorner.mem_center,CentralCorner.mem_center]
  constructor
  · rintro ⟨⟨b,hb⟩,hc⟩
    have hba : (b:H →L[ℂ] H)=a := map_injective hb
    refine ⟨hba ▸ b.property,?_⟩
    intro c hc'
    apply map_injective
    change diagonal (ι:=ℕ) (H:=H) (c*a)=diagonal (ι:=ℕ) (H:=H) (a*c)
    rw [map_mul,map_mul]
    exact hc (map c) (map_mem_algebra M c hc')
  · rintro ⟨ha,hc⟩
    refine ⟨map_mem_algebra M a ha,?_⟩
    rintro _ ⟨b,rfl⟩
    change diagonal (ι:=ℕ) (H:=H) b.val*diagonal (ι:=ℕ) (H:=H) a=
      diagonal (ι:=ℕ) (H:=H) a*diagonal (ι:=ℕ) (H:=H) b.val
    rw [←map_mul,←map_mul,hc b b.property]

end Kadison.InfiniteAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryCenterTransport
attribute [-instance] _root_.OAI.Kadison.CentralSpectral.centerCommCStar _root_.OAI.Kadison.CentralSpectral.spectrumBorel _root_.OAI.Kadison.CentralSpectral.spectrumMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

namespace Kadison.UnitaryTransport

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (U : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)

lemma mem_center_algebra (a : H →L[ℂ] H) :
    U.conjStarAlgEquiv a∈CentralCorner.center (algebra U M) ↔ a∈CentralCorner.center M := by
  rw [CentralCorner.mem_center,CentralCorner.mem_center,mem_algebra]
  constructor
  · rintro ⟨ha,hc⟩
    refine ⟨ha,?_⟩
    intro b hb
    apply U.conjStarAlgEquiv.injective
    rw [map_mul,map_mul]
    exact hc _ ((mem_algebra U M b).mpr hb)
  · rintro ⟨ha,hc⟩
    refine ⟨ha,?_⟩
    rintro _ ⟨b,hb,rfl⟩
    change U.conjStarAlgEquiv b*U.conjStarAlgEquiv a=U.conjStarAlgEquiv a*U.conjStarAlgEquiv b
    rw [←map_mul,←map_mul,hc b hb]

end Kadison.UnitaryTransport

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

lemma central_indicators
    (hind : ∀ (s : Set (Spectrum M)) (hs : MeasurableSet s),
      ∃ a : CentralCorner.center M,
        scalarMultiplier μ (gelfandStarTransform _ a)=indicatorOperator μ s hs)
    (s : Set (Spectrum M)) (hs : MeasurableSet s) :
    indicatorOperator (H:=Space ℕ ℂ) μ s hs ∈
      CentralCorner.center (UnitaryTransport.algebra U (algebra M)) := by
  obtain ⟨a,ha⟩ := hind s hs
  rw [←vector_indicator_of_scalar μ _ s hs ha,←conjugate_center M μ U hU a]
  exact (UnitaryTransport.mem_center_algebra U (algebra M) (map a.val)).mpr
    ((map_mem_center M a.val).mpr a.property)

end Kadison.CentralSpectral

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CentralSpectralModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology

namespace Kadison.Decomposable

variable {Ω H : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp H 2 μ)]

theorem uniform_commutator_in_central_spectral_model
    (P : VonNeumannAlgebra (Lp H 2 μ))
    (hdiag : ∀ (s : Set Ω) (hs : MeasurableSet s),
      indicatorOperator (H:=H) μ s hs∈P ∧
      indicatorOperator (H:=H) μ s hs∈Set.centralizer (P : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)))
    (hcenter : ∀ (Z : Lp H 2 μ →L[ℂ] Lp H 2 μ),Z∈P → Z∈P.commutant →
      ∀ C : H →L[ℂ] H,Commute
        (operator μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
          (Eventually.of_forall (fun _ => le_rfl))) Z)
    (Y : Lp H 2 μ →L[ℂ] Lp H 2 μ) (h : ℕ) (hh : 1≤h)
    (X : Matrix (Fin h) (Fin h) (Lp H 2 μ →L[ℂ] Lp H 2 μ)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖≤
      9368*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  by_cases hz : μ=0
  · have hY : Y=0 := by
      apply ContinuousLinearMap.ext
      intro f
      apply Lp.ext
      simp only [hz,MeasureTheory.ae_zero]
      exact Filter.eventually_bot
    have hd : diagonalAmplification h Y=0 := by
      ext f i
      simp [hY,diagonalAmplification_apply]
    rw [hd,zero_mul,mul_zero,sub_self,norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (commutatorSeminorm_nonneg P Y)) (norm_nonneg _)
  · let : NeZero μ := ⟨hz⟩
    exact uniform_commutator_in_central_spectral_model_nonzero μ P hdiag hcenter Y h hh X hX

end Kadison.Decomposable

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

lemma stable_model_indicators [IsFiniteMeasure μ] (s : Set (Spectrum M)) (hs : MeasurableSet s) :
    indicatorOperator (H:=Space ℕ ℂ) μ s hs∈UnitaryTransport.algebra U (algebra M) ∧
    indicatorOperator (H:=Space ℕ ℂ) μ s hs∈Set.centralizer
      (UnitaryTransport.algebra U (algebra M) : Set _) :=
  (CentralCorner.mem_center _ _).mp (central_indicators M μ U hU hind s hs)

variable [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace (Lp (Space ℕ ℂ) 2 μ)]

lemma stable_model_bound_oai (Y : Space ℕ H →L[ℂ] Space ℕ H)
    (h : ℕ) (hh : 1≤h) (X : Matrix (Fin h) (Fin h) (Space ℕ H →L[ℂ] Space ℕ H))
    (hX : ∀ i j,X i j∈algebra M) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      9368*commutatorSeminorm (algebra M) Y*‖matrixOperator h X‖ := by
  let : TopologicalSpace.SeparableSpace (Space ℕ ℂ) := separable_space
  apply UnitaryTransport.bound_of_conjugate_bound U (algebra M) Y h X 9368
  exact uniform_commutator_in_central_spectral_model μ (UnitaryTransport.algebra U (algebra M))
    (stable_model_indicators M μ U hU hind) (stable_model_center M μ U hU)
    (U.conjStarAlgEquiv Y) h hh (fun i j => U.conjStarAlgEquiv (X i j))
    (fun i j => (UnitaryTransport.mem_algebra U (algebra M) _).mpr (hX i j))

end Kadison.CentralSpectral

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.CentralSpectral.stable_model_bound_oai := @OAI.Kadison.CentralSpectral.stable_model_bound_oai
