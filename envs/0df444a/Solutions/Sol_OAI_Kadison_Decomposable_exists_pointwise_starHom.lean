-- Prove2me | solution 1 for OAI.Kadison.Decomposable.exists_pointwise_starHom
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:36:02.767668+00:00
-- url     : https://prove2.me/submissions/5d0a10eb-425d-4833-a790-9c77582ae122

import Mathlib
import Definitions.Def_OAIQ039C044
import Theorems.Thm_OAI_Kadison_Decomposable_exists_starHom_fields
import Theorems.Thm_OAI_Kadison_Decomposable_homomorphisms_ae_of_countable_relations

section
-- module Solutions.OAIQ039_CM.Commutator_CountablyGeneratedCStar
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

namespace Kadison

lemma countable_submonoidClosure {A : Type*} [Monoid A] {s : Set A} (hs : s.Countable) :
    (Submonoid.closure s : Set A).Countable := by
  let := hs.to_subtype
  rw [Submonoid.closure_eq_mrange,MonoidHom.coe_mrange]
  exact Set.countable_range _

end Kadison

end

end
end

end OAI
end

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
-- module Solutions.OAIQ039_CM.Commutator_DenseRationalStar
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

namespace Kadison.DenseRationalStar

variable (A : Type*) [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]

attribute [local instance] OAI.Kadison.DenseRationalStar.denseRationalStarNormedAlgebra
attribute [local instance] OAI.Kadison.DenseRationalStar.denseRationalStarStarModule
theorem exists_dense_countable : ∃ S : StarSubalgebra ℚ A,
    Countable S ∧ DenseRange (fun a : S => (a:A)) ∧ Complex.I • (1:A)∈S := by
  let s : Set A := Set.range (TopologicalSpace.denseSeq A) ∪ {Complex.I • (1:A)}
  have hs : s.Countable := (Set.countable_range _).union (Set.countable_singleton _)
  let S := StarAlgebra.adjoin ℚ s
  have hms : (Submonoid.closure (s∪star s) : Set A).Countable :=
    countable_submonoidClosure (hs.union (by simpa only [Set.image_star] using hs.image star))
  let M := Submonoid.closure (s∪star s)
  let : Countable M := hms.to_subtype
  have hc : (Submodule.span ℚ (M:Set A) : Set A).Countable := by
    have hr : Set.range (fun a : M => (a:A))=(M:Set A) := by ext a; simp
    have : Countable (Submodule.span ℚ (Set.range (fun a : M => (a:A)))) := inferInstance
    rw [←hr]
    exact Set.countable_coe_iff.mp inferInstance
  have he : (S:Set A)=(Submodule.span ℚ (M:Set A) : Set A) :=
    congrArg (fun N : Submodule ℚ A => (N:Set A)) (StarAlgebra.adjoin_eq_span (R:=ℚ) s)
  have hsc : Countable S := Set.countable_coe_iff.mpr (by rw [he]; exact hc)
  refine ⟨S,hsc,?_,StarAlgebra.subset_adjoin ℚ s (Or.inr (Set.mem_singleton _))⟩
  apply denseRange_subtype_val.mpr
  apply (TopologicalSpace.denseRange_denseSeq A).mono
  intro a ha
  exact StarAlgebra.subset_adjoin ℚ s (Or.inl ha)

end Kadison.DenseRationalStar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StarHomFieldLip
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

variable {Ω H A : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ] [CStarAlgebra A]

lemma representation_field_diff_bound
    (ρ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (T : A → Ω → H →L[ℂ] H)
    (hm : ∀ a ξ,AEStronglyMeasurable (fun x => T a x ξ) μ)
    (hb : ∀ a,∀ᵐ x ∂μ,‖T a x‖≤‖a‖)
    (he : ∀ a,ρ a=operator μ (T a) (hm a) (hb a)) (a b : A) :
    ∀ᵐ x ∂μ,‖T a x-T b x‖≤‖a-b‖ := by
  apply (operator_norm_le_iff_ae μ (fun x => T a x-T b x)
    (sub_measurable μ _ _ (hm a) (hm b)) (sub_bound μ _ _ (hb a) (hb b))
    (norm_nonneg (a-b))).mp
  rw [←operator_sub μ _ _ (hm a) (hm b) (hb a) (hb b),←he a,←he b,←map_sub]
  exact NonUnitalStarAlgHom.norm_apply_le ρ (a-b)

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PointwiseStarHom
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology CStarAlgebra

namespace Kadison.Decomposable

variable {Ω H A : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ] [NeZero μ]
  [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]

local instance pointwiseStarHomNormedAlgebra_r065f3d_1 : NormedAlgebra ℚ A :=
  NormedAlgebra.restrictScalars ℚ ℂ A
local instance pointwiseStarHomStarModule_r065f3d_1 : StarModule ℚ A where
  star_smul r a := by
    change star ((r:ℂ) • a)=((star r:ℚ):ℂ) • star a
    simp
theorem exists_pointwise_starHom_oai
    (ρ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (hcomm : ∀ a (s : Set Ω) (hs : MeasurableSet s),
      Commute (ρ a) (indicatorOperator (H:=H) μ s hs)) :
    ∃ σ : Ω → A →⋆ₐ[ℂ] (H →L[ℂ] H),
      (∀ a ξ,AEStronglyMeasurable (fun x => σ x a ξ) μ) ∧
      (∀ a (f : Lp H 2 μ),ρ a f =ᵐ[μ] fun x => σ x a (f x)) := by
  classical
  obtain ⟨T,hm,hb,he,ha,hmu,hst,hsc⟩ := exists_starHom_fields μ ρ hcomm
  obtain ⟨S,hcount,hd,hI⟩ := DenseRationalStar.exists_dense_countable A
  let : Countable S := hcount
  have hg := homomorphisms_ae_of_countable_relations μ S hd hI T hb ha hmu hst hsc
  obtain ⟨x₀,hx₀⟩ := hg.exists
  obtain ⟨Φ₀,hΦ₀⟩ := hx₀
  have hex (x : Ω) : ∃ Φ : A →⋆ₐ[ℂ] (H →L[ℂ] H),
      (∃ Ψ : A →⋆ₐ[ℂ] (H →L[ℂ] H),∀ a : S,Ψ (a:A)=T (a:A) x) →
        ∀ a : S,Φ (a:A)=T (a:A) x := by
    by_cases hx : ∃ Ψ : A →⋆ₐ[ℂ] (H →L[ℂ] H),∀ a : S,Ψ (a:A)=T (a:A) x
    · obtain ⟨Ψ,hΨ⟩ := hx
      exact ⟨Ψ,fun _ => hΨ⟩
    · exact ⟨Φ₀,fun h => (hx h).elim⟩
  choose σ hσ using hex
  have hσg : ∀ᵐ x ∂μ,∀ a : S,σ x (a:A)=T (a:A) x :=
    hg.mono (fun x hx => hσ x hx)
  have hσae (a : A) : (fun x => σ x a)=ᵐ[μ]T a := by
    obtain ⟨s,hs,hl⟩ := mem_closure_iff_seq_limit.mp (hd a)
    choose b hbs using hs
    have hbl : Tendsto (fun n => (b n:A)) atTop (𝓝 a) := by
      have heq : (fun n => (b n:A))=s := funext hbs
      rwa [heq]
    filter_upwards [hσg,ae_all_iff.mpr (fun n =>
      representation_field_diff_bound μ ρ T hm hb he (b n:A) a)] with x hx hxb
    have ht : Tendsto (fun n => T (b n:A) x) atTop (𝓝 (T a x)) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      exact squeeze_zero (fun _ => norm_nonneg _) hxb
        (by simpa using (hbl.sub_const a).norm)
    have hc : Continuous (σ x : A → (H →L[ℂ] H)) :=
      map_continuous (σ x)
    have hlim := (hc.tendsto a).comp hbl
    have heq : (fun n => σ x (b n:A))=(fun n => T (b n:A) x) := funext (fun n => hx (b n))
    change Tendsto (fun n => σ x (b n:A)) atTop (𝓝 (σ x a)) at hlim
    rw [heq] at hlim
    exact tendsto_nhds_unique hlim ht
  refine ⟨σ,?_,?_⟩
  · intro a ξ
    apply (hm a ξ).congr
    filter_upwards [hσae a] with x hx
    exact congrArg (fun U : H →L[ℂ] H => U ξ) hx.symm
  · intro a f
    rw [he a]
    filter_upwards [operator_ae μ (T a) (hm a) (hb a) f,hσae a] with x hx hs
    rw [hx,hs]

end Kadison.Decomposable

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.Decomposable.exists_pointwise_starHom_oai := @OAI.Kadison.Decomposable.exists_pointwise_starHom_oai
