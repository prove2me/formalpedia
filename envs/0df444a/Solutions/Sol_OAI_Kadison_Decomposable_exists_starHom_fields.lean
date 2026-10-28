-- Prove2me | solution 1 for OAI.Kadison.Decomposable.exists_starHom_fields
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:36:04.626992+00:00
-- url     : https://prove2.me/submissions/49feb2d6-d2ed-44b9-8379-eb429086a357

import Mathlib
import Definitions.Def_OAIQ039C043
import Definitions.Def_OAIQ039C044

section
-- module Solutions.OAIQ039_CM.Commutator_DecomposableAlgebra
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
-- module Solutions.OAIQ039_CM.Commutator_StarHomFieldRaw
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

open scoped Topology

namespace Kadison.Decomposable

variable {Ω H A : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ]
  [CStarAlgebra A]

theorem exists_starHom_fields_oai
    (ρ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (hcomm : ∀ a (s : Set Ω) (hs : MeasurableSet s),
      Commute (ρ a) (indicatorOperator (H:=H) μ s hs)) :
    ∃ (T : A → Ω → H →L[ℂ] H)
      (hm : ∀ a ξ,AEStronglyMeasurable (fun x => T a x ξ) μ)
      (hb : ∀ a,∀ᵐ x ∂μ,‖T a x‖≤‖a‖),
      (∀ a,ρ a=operator μ (T a) (hm a) (hb a)) ∧
      (∀ a b,∀ᵐ x ∂μ,T (a+b) x=T a x+T b x) ∧
      (∀ a b,∀ᵐ x ∂μ,T (a*b) x=T a x*T b x) ∧
      (∀ a,∀ᵐ x ∂μ,T (star a) x=star (T a x)) ∧
      (∀ z : ℂ,∀ᵐ x ∂μ,T (z • (1:A)) x=z • (1:H →L[ℂ] H)) := by
  choose T hm hbn he using fun a => exists_field_of_commutes_indicator μ (ρ a) (hcomm a)
  have hb : ∀ a,∀ᵐ x ∂μ,‖T a x‖≤‖a‖ := fun a =>
    (hbn a).mono (fun _ hx => hx.trans (NonUnitalStarAlgHom.norm_apply_le ρ a))
  have he' (a : A) : ρ a=operator μ (T a) (hm a) (hb a) := by
    apply operator_eq_of_ae_apply
    intro f
    rw [he a]
    exact operator_ae μ (T a) (hm a) (hbn a) f
  refine ⟨T,hm,hb,he',?_,?_,?_,?_⟩
  · intro a b
    apply field_eq_ae_of_operator_eq μ (T (a+b)) (fun x => T a x+T b x)
      (hm (a+b)) (add_measurable μ _ _ (hm a) (hm b)) (hb (a+b))
      (add_field_bound μ _ _ (hb a) (hb b))
    rw [operator_add μ _ _ (hm a) (hm b) (hb a) (hb b),←he',←he',←he',map_add]
  · intro a b
    apply field_eq_ae_of_operator_eq μ (T (a*b)) (fun x => T a x*T b x)
      (hm (a*b)) (mul_measurable μ _ _ (hm a) (hm b)) (hb (a*b))
      (mul_bound μ _ _ (norm_nonneg a) (hb a) (hb b))
    rw [←operator_mul μ _ _ (hm a) (hm b) (norm_nonneg a) (hb a) (hb b),
      ←he',←he',←he',map_mul]
  · intro a
    exact adjoint_ae μ (T a) (T (star a)) (hm a) (hm (star a)) (hb a) (hb (star a))
      (by rw [←he',←he',map_star]; rfl)
  · intro z
    have hc : (z • (1 : Lp H 2 μ →L[ℂ] Lp H 2 μ))=
        operator μ (fun _ => z • (1:H →L[ℂ] H))
          (fun _ => aestronglyMeasurable_const) (Eventually.of_forall (fun _ => le_rfl)) := by
      apply operator_eq_of_ae_apply
      intro f
      exact Lp.coeFn_smul z f
    apply field_eq_ae_of_operator_eq μ (T (z • (1:A))) (fun _ => z • (1:H →L[ℂ] H))
      (hm _) (fun _ => aestronglyMeasurable_const) (hb _)
      (Eventually.of_forall (fun _ => le_rfl))
    rw [←he',←hc,map_smul,map_one]

end Kadison.Decomposable

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.Decomposable.exists_starHom_fields_oai := @OAI.Kadison.Decomposable.exists_starHom_fields_oai
