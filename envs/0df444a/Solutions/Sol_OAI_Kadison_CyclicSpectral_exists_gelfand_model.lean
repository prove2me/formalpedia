-- Prove2me | solution 1 for OAI.Kadison.CyclicSpectral.exists_gelfand_model
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:35:39.734811+00:00
-- url     : https://prove2.me/submissions/c11d69c5-6b83-4feb-aecd-0a4c648250bc

import Mathlib
import Definitions.Def_OAIQ039C033

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicSpectralUnitary
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

namespace Kadison.CyclicSpectral

variable {Ω H : Type*} [TopologicalSpace Ω] [T2Space Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma unitary_toLp (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hd : DenseRange (orbitMap ρ ξ)) (f : C(Ω,ℂ)) :
    unitary ρ ξ hd (ContinuousMap.toLp 2 (measure ρ ξ) ℂ f)=ρ f ξ := by
  exact LinearEquiv.extendOfIsometry_eq ..

variable (μ : Measure Ω)

omit [T2Space Ω] in
lemma scalarMultiplier_ae (f : C(Ω,ℂ)) (v : Lp ℂ 2 μ) :
    scalarMultiplier μ f v=ᵐ[μ] fun x => f x*v x :=
  Decomposable.operator_ae ..

omit [T2Space Ω] in
lemma scalarMultiplier_toLp [IsFiniteMeasure μ] (f g : C(Ω,ℂ)) :
    scalarMultiplier μ f (ContinuousMap.toLp 2 μ ℂ g)=ContinuousMap.toLp 2 μ ℂ (f*g) := by
  apply Lp.ext
  filter_upwards [scalarMultiplier_ae μ f (ContinuousMap.toLp 2 μ ℂ g),
    ContinuousMap.coeFn_toLp (𝕜:=ℂ) (p:=2) μ g,ContinuousMap.coeFn_toLp (𝕜:=ℂ) (p:=2) μ (f*g)] with x hx hg hfg
  rw [hx,hg,hfg]
  rfl

lemma unitary_intertwines (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hd : DenseRange (orbitMap ρ ξ)) (f : C(Ω,ℂ)) (v : Lp ℂ 2 (measure ρ ξ)) :
    unitary ρ ξ hd (scalarMultiplier (measure ρ ξ) f v)=ρ f (unitary ρ ξ hd v) := by
  apply (ContinuousMap.toLp_denseRange ℂ (measure ρ ξ) ℂ (p:=2) (by norm_num)).induction_on v
    (p:=fun v => unitary ρ ξ hd (scalarMultiplier (measure ρ ξ) f v)=ρ f (unitary ρ ξ hd v))
  · apply isClosed_eq
    · exact (unitary ρ ξ hd).continuous.comp (scalarMultiplier (measure ρ ξ) f).continuous
    · exact (ρ f).continuous.comp (unitary ρ ξ hd).continuous
  · intro g
    rw [scalarMultiplier_toLp,unitary_toLp,unitary_toLp,map_mul]
    rfl

end Kadison.CyclicSpectral

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicGelfandModel
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory

open scoped Topology

namespace Kadison.CyclicSpectral

variable {A H : Type*} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [MeasurableSpace (spectrumSpace (A:=A))] [BorelSpace (spectrumSpace (A:=A))]

omit [MeasurableSpace (spectrumSpace (A:=A))] [BorelSpace (spectrumSpace (A:=A))] in
lemma gelfandRepresentation_dense (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hd : DenseRange (fun a : A => ρ a ξ)) :
    DenseRange (orbitMap (gelfandRepresentation ρ) ξ) := by
  apply hd.mono
  rintro y ⟨a,rfl⟩
  refine ⟨gelfandStarTransform A a,?_⟩
  change ρ ((gelfandStarTransform A).symm (gelfandStarTransform A a)) ξ=ρ a ξ
  rw [(gelfandStarTransform A).symm_apply_apply]

theorem exists_gelfand_model_oai (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hd : DenseRange (fun a : A => ρ a ξ)) :
    ∃ μ : Measure (spectrumSpace (A:=A)), IsFiniteMeasure μ ∧
      ∃ U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] H,
        ∀ (a : A) (v : Lp ℂ 2 μ), U (scalarMultiplier μ (gelfandStarTransform A a) v)=ρ a (U v) := by
  let σ := gelfandRepresentation ρ
  let μ := measure σ ξ
  let U := unitary σ ξ (gelfandRepresentation_dense ρ ξ hd)
  refine ⟨μ,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)),U,?_⟩
  intro a v
  have h := unitary_intertwines σ ξ (gelfandRepresentation_dense ρ ξ hd)
    (gelfandStarTransform A a) v
  have he : σ (gelfandStarTransform A a)=ρ a := by
    change ρ ((gelfandStarTransform A).symm (gelfandStarTransform A a))=ρ a
    rw [(gelfandStarTransform A).symm_apply_apply]
  rw [he] at h
  exact h

end Kadison.CyclicSpectral

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.CyclicSpectral.exists_gelfand_model_oai.{u_1, u_2} := @OAI.Kadison.CyclicSpectral.exists_gelfand_model_oai.{u_1, u_2}
