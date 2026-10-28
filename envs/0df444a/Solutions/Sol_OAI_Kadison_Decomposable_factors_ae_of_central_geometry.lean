-- Prove2me | solution 1 for OAI.Kadison.Decomposable.factors_ae_of_central_geometry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:34:24.066738+00:00
-- url     : https://prove2.me/submissions/4465112a-2bb6-4079-9f51-b3f9e67c88be

import Mathlib
import Definitions.Def_OAIQ039C059

section
-- module Solutions.OAIQ039_CM.Commutator_DecomposableAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma operator_sub (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ : H,AEStronglyMeasurable (fun a => S a ξ) μ)
    {b c : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖ ≤ c) :
    operator μ T hT hb-operator μ S hS hc=
      operator μ (fun a => T a-S a) (sub_measurable μ T S hT hS) (sub_bound μ T S hb hc) := by
  apply operator_eq_of_ae_apply
  intro f
  filter_upwards [operator_ae μ T hT hb f,operator_ae μ S hS hc f,
    Lp.coeFn_sub (operator μ T hT hb f) (operator μ S hS hc f)] with a h1 h2 h3
  change (operator μ T hT hb f-operator μ S hS hc f) a=_
  rw [h3]
  exact congrArg₂ (·-·) h1 h2

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FieldUniqueness
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

lemma field_eq_ae_of_operator_eq (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ,AEStronglyMeasurable (fun a => S a ξ) μ)
    {b c : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖ ≤ c)
    (he : operator μ T hT hb=operator μ S hS hc) : T=ᵐ[μ]S := by
  have hz : operator μ (fun a => T a-S a) (sub_measurable μ T S hT hS)
      (sub_bound μ T S hb hc)=0 := by
    rw [←operator_sub μ T S hT hS hb hc,he,sub_self]
  have hn := (operator_norm_le_iff_ae μ (fun a => T a-S a)
    (sub_measurable μ T S hT hS) (sub_bound μ T S hb hc) (by norm_num : (0:ℝ)≤0)).mp
    (by rw [hz]; simp)
  filter_upwards [hn] with a ha
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm ha (norm_nonneg _)))

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RankOneFactor
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma scalar_of_commutes_rankOne (Z : H →L[ℂ] H)
    (hz : ∀ x y : H,Commute Z (InnerProductSpace.rankOne ℂ x y)) :
    ∃ c : ℂ,Z=c • (1:H →L[ℂ] H) := by
  rcases subsingleton_or_nontrivial H with hH|hH
  · let := hH
    exact ⟨0,Subsingleton.elim _ _⟩
  · let := hH
    obtain ⟨e,he⟩ := exists_ne (0:H)
    have hee : inner ℂ e e≠0 := inner_self_ne_zero.mpr he
    refine ⟨((inner ℂ e e)⁻¹*inner ℂ e (Z e)),?_⟩
    apply ContinuousLinearMap.ext
    intro x
    have hc := congrArg (fun A : H →L[ℂ] H => A e) (hz x e).eq
    change Z (inner ℂ e e • x)=inner ℂ e (Z e) • x at hc
    rw [map_smul] at hc
    have hc' := congrArg (fun y : H => (inner ℂ e e)⁻¹ • y) hc
    simpa only [smul_smul,inv_mul_cancel₀ hee,one_smul,
      smul_apply,one_apply_eq_self] using hc'

omit [CompleteSpace H] in
lemma scalar_of_dense_rankOne_tests (v : ℕ → H) (hv : DenseRange v)
    (Z : H →L[ℂ] H)
    (hz : ∀ i j,Commute Z (InnerProductSpace.rankOne ℂ (v i) (v j))) :
    ∃ c : ℂ,Z=c • (1:H →L[ℂ] H) := by
  have ht (i j : ℕ) (e : H) :
      inner ℂ (v j) e • Z (v i)=inner ℂ (v j) (Z e) • v i := by
    have h := congrArg (fun A : H →L[ℂ] H => A e) (hz i j).eq
    change Z (inner ℂ (v j) e • v i)=inner ℂ (v j) (Z e) • v i at h
    simpa only [map_smul] using h
  have hy (i : ℕ) (y e : H) :
      inner ℂ y e • Z (v i)=inner ℂ y (Z e) • v i := by
    exact hv.induction_on y
      (isClosed_eq ((continuous_id.inner continuous_const).smul continuous_const)
        ((continuous_id.inner continuous_const).smul continuous_const))
      (fun j => ht i j e)
  have hx (x y e : H) : inner ℂ y e • Z x=inner ℂ y (Z e) • x := by
    exact hv.induction_on x
      (isClosed_eq (continuous_const.smul Z.continuous)
        (continuous_const.smul continuous_id)) (fun i => hy i y e)
  apply scalar_of_commutes_rankOne Z
  intro x y
  change Z*InnerProductSpace.rankOne ℂ x y=InnerProductSpace.rankOne ℂ x y*Z
  apply ContinuousLinearMap.ext
  intro e
  change Z (inner ℂ y e • x)=inner ℂ y (Z e) • x
  rw [map_smul]
  exact hx x y e

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiberFactorProducer
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
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

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

omit [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
lemma fieldMember_mono {Q R : Ω → VonNeumannAlgebra H}
    (hQR : ∀ᵐ a ∂μ,Q a≤R a) {A : Lp H 2 μ →L[ℂ] Lp H 2 μ}
    (hA : FieldMember μ Q A) : FieldMember μ R A := by
  obtain ⟨T,hm,b,hb,hb0,he,hmem⟩ := hA
  refine ⟨T,hm,b,hb,hb0,he,?_⟩
  filter_upwards [hQR,hmem] with a ha hm
  exact ha hm

omit [TopologicalSpace.SeparableSpace H] in
lemma le_fiberJoin_left (Q R : VonNeumannAlgebra H) : Q≤fiberJoin Q R := by
  intro A hA
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro Z hZ
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hZ.1 A hA).symm

omit [TopologicalSpace.SeparableSpace H] in
lemma le_fiberJoin_right (Q R : VonNeumannAlgebra H) : R≤fiberJoin Q R := by
  intro A hA
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro Z hZ
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hZ.2 A hA).symm

omit [TopologicalSpace.SeparableSpace H] in
lemma factor_of_rankOne_mem_join (Q R : VonNeumannAlgebra H)
    (hRQ : R≤Q.commutant) (v : ℕ → H) (hv : DenseRange v)
    (hmem : ∀ i j,InnerProductSpace.rankOne ℂ (v i) (v j)∈fiberJoin Q R) :
    FactorCorner.IsFactor Q := by
  intro Z hZ hZc
  apply scalar_of_dense_rankOne_tests v hv Z
  intro i j
  apply VonNeumannAlgebra.mem_commutant_iff.mp (hmem i j) Z
  exact ⟨VonNeumannAlgebra.mem_commutant_iff.mpr hZc,
    VonNeumannAlgebra.mem_commutant_iff.mpr (fun B hB =>
      (VonNeumannAlgebra.mem_commutant_iff.mp (hRQ hB) Z hZ).symm)⟩

theorem factors_ae_of_central_geometry_oai
    (P : VonNeumannAlgebra (Lp H 2 μ)) (Q R : Ω → VonNeumannAlgebra H)
    (hP : ∀ A,A∈P → FieldMember μ Q A)
    (hPc : ∀ A,A∈P.commutant → FieldMember μ R A)
    (hRQ : ∀ᵐ a ∂μ,R a≤(Q a).commutant)
    (hcenter : ∀ (Z : Lp H 2 μ →L[ℂ] Lp H 2 μ),Z∈P → Z∈P.commutant →
      ∀ B : H →L[ℂ] H,Commute
        (operator μ (fun _ => B) (fun _ => aestronglyMeasurable_const)
          (Eventually.of_forall (fun _ => le_rfl))) Z) :
    ∀ᵐ a ∂μ,FactorCorner.IsFactor (Q a) := by
  let J : Ω → VonNeumannAlgebra H := fun a => fiberJoin (Q a) (R a)
  let N := fieldVonNeumann μ J
  have hPN : P≤N := fun A hA => fieldMember_mono μ
    (Eventually.of_forall (fun a => le_fiberJoin_left (Q a) (R a))) (hP A hA)
  have hPcN : P.commutant≤N := fun A hA => fieldMember_mono μ
    (Eventually.of_forall (fun a => le_fiberJoin_right (Q a) (R a))) (hPc A hA)
  have hconstant (B : H →L[ℂ] H) : ∀ᵐ a ∂μ,B∈J a := by
    let C := operator μ (fun _ => B) (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall (fun _ => le_rfl))
    have hCN : C∈N := by
      change C∈N.carrier
      rw [←N.centralizer_centralizer']
      intro Z hZ
      have hZc : Z∈P.commutant :=
        VonNeumannAlgebra.mem_commutant_iff.mpr (fun A hA => hZ A (hPN hA))
      have hZP : Z∈P := by
        change Z∈P.carrier
        rw [←P.centralizer_centralizer']
        intro A hA
        exact hZ A (hPcN (VonNeumannAlgebra.mem_commutant_iff.mpr hA))
      exact (hcenter Z hZP hZc B).eq.symm
    obtain ⟨T,hm,b,hb,_,he,hmem⟩ := hCN
    have heae := field_eq_ae_of_operator_eq μ T (fun _ => B) hm
      (fun _ => aestronglyMeasurable_const) hb
      (Eventually.of_forall (fun _ => le_rfl)) he.symm
    filter_upwards [heae,hmem] with a ha hm
    rwa [ha] at hm
  let v : ℕ → H := TopologicalSpace.denseSeq H
  filter_upwards [hRQ,ae_all_iff.mpr (fun i => ae_all_iff.mpr
    (fun j => hconstant (InnerProductSpace.rankOne ℂ (v i) (v j))))] with a ha hm
  exact factor_of_rankOne_mem_join (Q a) (R a) ha v
    (TopologicalSpace.denseRange_denseSeq H) hm

end Kadison.Decomposable

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.Decomposable.factors_ae_of_central_geometry_oai.{u_1, u_2} := @OAI.Kadison.Decomposable.factors_ae_of_central_geometry_oai.{u_1, u_2}
