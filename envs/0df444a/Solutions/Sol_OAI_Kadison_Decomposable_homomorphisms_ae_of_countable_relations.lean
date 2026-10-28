-- Prove2me | solution 1 for OAI.Kadison.Decomposable.homomorphisms_ae_of_countable_relations
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:23:00.953994+00:00
-- url     : https://prove2.me/submissions/43fabb7f-5fba-4273-9e5c-e9e6c28f84ed

import Mathlib
import Definitions.Def_OAIQ039C023
import Definitions.Def_OAIQ039C029

section
-- module Solutions.OAIQ039_CM.Commutator_RationalStarExtension
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

namespace Kadison.RationalStarExtension

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

attribute [local instance] OAI.Kadison.RationalStarExtension.instNormedAlgebraRat_solutions
attribute [local instance] OAI.Kadison.RationalStarExtension.instNormedAlgebraRat_solutions_1
local instance instStarModuleRat_solutions_rb3033a_1 : StarModule ℚ A where
  star_smul r a := by
    change star ((r:ℂ) • a)=((star r:ℚ):ℂ) • star a
    simp
attribute [local instance] OAI.Kadison.RationalStarExtension.instStarModuleRat_solutions_1
variable (S : StarSubalgebra ℚ A)
  (hd : DenseRange (fun a : S => (a:A)))
  (φ : S →⋆ₐ[ℚ] B) (hb : ∀ a : S,‖φ a‖≤‖(a:A)‖)

include hd in
lemma lift_subtype (a : S) : lift S φ hb (a:A)=φ a :=
  ContinuousLinearMap.extend_eq _ hd isUniformEmbedding_subtype_val.isUniformInducing a

include hd in
lemma lift_norm (a : A) : ‖lift S φ hb a‖≤‖a‖ := by
  refine hd.induction_on (p:=fun x => ‖lift S φ hb x‖≤‖x‖) a
    (isClosed_le (lift S φ hb).continuous.norm continuous_norm) ?_
  intro b
  rw [lift_subtype S hd φ hb]
  exact hb b

include hd hb in
theorem exists_complex_extension (hI : Complex.I • (1:A)∈S)
    (hφI : φ ⟨Complex.I • (1:A),hI⟩=Complex.I • (1:B)) :
    ∃ Φ : A →⋆ₐ[ℂ] B,(∀ a : S,Φ (a:A)=φ a) ∧ (∀ a : A,‖Φ a‖≤‖a‖) := by
  let L := realLift S φ hb
  have hsub (a : S) : L (a:A)=φ a := lift_subtype S hd φ hb a
  have hLI (a : A) : L (Complex.I • a)=Complex.I • L a := by
    refine hd.induction_on (p:=fun x => L (Complex.I • x)=Complex.I • L x) a (isClosed_eq
      (L.continuous.comp (continuous_const.smul continuous_id))
      (continuous_const.smul L.continuous)) ?_
    intro a
    let i : S := ⟨Complex.I • (1:A),hI⟩
    have he : Complex.I • (a:A)=((i*a:S):A) := by simp [i]
    rw [he,hsub,map_mul,hsub]
    change φ ⟨Complex.I • (1:A),hI⟩*φ a=Complex.I • φ a
    rw [hφI]
    simp
  have hsmul (z : ℂ) (a : A) : L (z • a)=z • L a := by
    rw [←Complex.re_add_im z,add_smul,map_add,add_smul,mul_smul,mul_smul]
    have hr (r : ℝ) (x : A) : L ((r:ℂ) • x)=(r:ℂ) • L x := by
      change L (r • x)=r • L x
      exact map_smul L r x
    rw [hr,hr,hLI]
  have hmul (a b : A) : L (a*b)=L a*L b := by
    refine hd.induction_on (p:=fun x => L (x*b)=L x*L b) a
      (isClosed_eq (L.continuous.comp (continuous_id.mul continuous_const))
        (L.continuous.mul continuous_const)) ?_
    intro a
    refine hd.induction_on (p:=fun x => L ((a:A)*x)=L (a:A)*L x) b
      (isClosed_eq (L.continuous.comp (continuous_const.mul continuous_id))
        (continuous_const.mul L.continuous)) ?_
    intro b
    change L ((a*b:S):A)=L (a:A)*L (b:A)
    rw [hsub,hsub,hsub,map_mul]
  have hstar (a : A) : L (star a)=star (L a) := by
    refine hd.induction_on (p:=fun x => L (star x)=star (L x)) a
      (isClosed_eq (L.continuous.comp continuous_star) L.continuous.star) ?_
    intro a
    change L ((star a:S):A)=star (L (a:A))
    rw [hsub,hsub,map_star]
  have hone : L (1:A)=1 := by
    change L ((1:S):A)=1
    rw [hsub,map_one]
  let Φ : A →⋆ₐ[ℂ] B :=
    { toAlgHom :=
      { toFun := L
        map_one' := hone
        map_mul' := hmul
        map_zero' := map_zero L
        map_add' := map_add L
        commutes' := by
          intro z
          change L (algebraMap ℂ A z)=algebraMap ℂ B z
          rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one,hsmul,hone] }
      map_star' := hstar }
  exact ⟨Φ,hsub,lift_norm S hd φ hb⟩

end Kadison.RationalStarExtension

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CountableFieldHom
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
  [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ] [CStarAlgebra A]

attribute [local instance] OAI.Kadison.Decomposable.instNormedAlgebraRat_solutions
attribute [local instance] OAI.Kadison.Decomposable.instNormedAlgebraRatContinuousLinearMapComplexId_solutions
attribute [local instance] OAI.Kadison.Decomposable.instStarModuleRat_solutions
local instance instStarModuleRatContinuousLinearMapComplexId_solutions_rb3033a_1 : StarModule ℚ (H →L[ℂ] H) where
  star_smul r a := by
    change star ((r:ℂ) • a)=((star r:ℚ):ℂ) • star a
    simp
omit [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ] in
theorem homomorphisms_ae_of_countable_relations_oai
    (S : StarSubalgebra ℚ A) [Countable S]
    (hd : DenseRange (fun a : S => (a:A))) (hI : Complex.I • (1:A)∈S)
    (T : A → Ω → H →L[ℂ] H)
    (hb : ∀ a,∀ᵐ x ∂μ,‖T a x‖≤‖a‖)
    (ha : ∀ a b,∀ᵐ x ∂μ,T (a+b) x=T a x+T b x)
    (hm : ∀ a b,∀ᵐ x ∂μ,T (a*b) x=T a x*T b x)
    (hst : ∀ a,∀ᵐ x ∂μ,T (star a) x=star (T a x))
    (hsc : ∀ z : ℂ,∀ᵐ x ∂μ,T (z • (1:A)) x=z • (1:H →L[ℂ] H)) :
    ∀ᵐ x ∂μ,∃ Φ : A →⋆ₐ[ℂ] (H →L[ℂ] H),∀ a : S,Φ (a:A)=T (a:A) x := by
  filter_upwards [ae_all_iff.mpr (fun a : S => hb (a:A)),
    ae_all_iff.mpr (fun a : S => ae_all_iff.mpr (fun b : S => ha (a:A) (b:A))),
    ae_all_iff.mpr (fun a : S => ae_all_iff.mpr (fun b : S => hm (a:A) (b:A))),
    ae_all_iff.mpr (fun a : S => hst (a:A)),
    ae_all_iff.mpr (fun r : ℚ => hsc (r:ℂ)),hsc Complex.I] with x hx ha hm hs hc hi
  let φ : S →⋆ₐ[ℚ] (H →L[ℂ] H) :=
    { toAlgHom :=
      { toFun := fun a => T (a:A) x
        map_one' := by simpa using hc (1:ℚ)
        map_zero' := by simpa using hc (0:ℚ)
        map_add' := fun a b => ha a b
        map_mul' := fun a b => hm a b
        commutes' := by
          intro r
          change T (algebraMap ℚ A r) x=algebraMap ℚ (H →L[ℂ] H) r
          rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one]
          exact hc r }
      map_star' := fun a => hs a }
  obtain ⟨Φ,hΦ,hnb⟩ := RationalStarExtension.exists_complex_extension S hd φ hx hI hi
  exact ⟨Φ,hΦ⟩

end Kadison.Decomposable

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.Decomposable.homomorphisms_ae_of_countable_relations_oai := @OAI.Kadison.Decomposable.homomorphisms_ae_of_countable_relations_oai
