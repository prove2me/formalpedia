-- Prove2me | solution 1 for OAI.Kadison.uniform_commutator_separable_factor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:52:05.08922+00:00
-- url     : https://prove2.me/submissions/71cf6718-7670-4695-9d34-23f46223bab1

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C064
import Theorems.Thm_OAI_Kadison_NormalRepresentation_separable_traced_factor_bound
import Theorems.Thm_OAI_Kadison_OrbitStateHull_exists_tracial_hull_of_norm_separable
import Theorems.Thm_OAI_Kadison_OrbitStateHull_hull_norm_separable
import Theorems.Thm_OAI_Kadison_OrbitStateHull_hull_projectionContinuousAtOne
import Theorems.Thm_OAI_Kadison_PositiveWOT_mem_predual
import Theorems.Thm_OAI_Kadison_TraceDimension_faithful
import Theorems.Thm_OAI_Kadison_commutatorSeminorm_nonneg
import Theorems.Thm_OAI_Kadison_uniform_commutator_atomic_factor
import Theorems.Thm_OAI_Kadison_uniform_commutator_nonfinite_factor

section
-- module Solutions.OAIQ039_CM.Commutator_WeakDualHull
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology ComplexOrder

namespace Kadison.WeakDualHull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

attribute [local instance] OAI.Kadison.WeakDualHull.instAddCommGroupWeakDualComplex_solutions
attribute [local instance] OAI.Kadison.WeakDualHull.instModuleRealWeakDualComplex_solutions
lemma eval_eq {S : Set (WeakDual ℂ E)} (a : E) (c : ℂ)
    (h : ∀ f∈S,f a=c) {f : WeakDual ℂ E} (hf : f∈hull S) : f a=c := by
  have hc : IsClosed {f : WeakDual ℂ E | f a=c} :=
    isClosed_eq (WeakDual.eval_continuous a) continuous_const
  have hv : Convex ℝ {f : WeakDual ℂ E | f a=c} := by
    intro g hg k hk s t _ _ hst
    change (s • g a+t • k a)=c
    rw [hg,hk,←add_smul,hst,one_smul]
  exact closure_minimal (convexHull_min h hv) hc hf

end Kadison.WeakDualHull

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_OrbitStateHull
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.OrbitStateHull

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

lemma hull_one (x : H) {f : WeakDual ℂ M} (hf : f∈hull M x) :
    f 1=(‖x‖^2 : ℝ) := by
  apply WeakDualHull.eval_eq (1 : M) ((‖x‖^2 : ℝ) : ℂ) _ hf
  rintro g ⟨u,_,rfl⟩
  change inner ℂ ((u : H →L[ℂ] H) x) ((u : H →L[ℂ] H) x)=_
  rw [inner_self_eq_norm_sq_to_K,Unitary.norm_map,Complex.ofReal_pow]
  rfl

end Kadison.OrbitStateHull

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalPredual
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter ContinuousLinearMapWOT

open scoped Topology InnerProductSpace

namespace Kadison.NormalPredual

open FiniteStrongTest

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma coefficient_normal (M : VonNeumannAlgebra H) (v : ℕ → H) (N : ℕ)
    (y : PiLp 2 (fun _ : Fin N => H)) : BoundedWOTContinuous M (coefficient M v N y) := by
  intro C
  change Continuous (fun a : {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} =>
    inner ℂ y (testMap M v N ⟨a.val.toCLM,a.property.1⟩))
  simp_rw [PiLp.inner_apply,testMap_apply]
  apply continuous_finsetSum
  intro j _
  exact ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val (v j) (y j)

theorem normal_of_mem_closure (M : VonNeumannAlgebra H) (v : ℕ → H)
    {f : StrongDual ℂ M} (hf : f∈closure (finiteTests M v)) : BoundedWOTContinuous M f := by
  obtain ⟨g,hg,hlim⟩ := mem_closure_iff_seq_limit.mp hf
  intro C
  let D := {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C}
  let a (T : D) : M := ⟨T.val.toCLM,T.property.1⟩
  have hn : Tendsto (fun n => ‖g n-f‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hlim.sub (tendsto_const_nhds (x:=f))).norm
  have hu : TendstoUniformly (fun n (T:D) => g n (a T)) (fun T => f (a T)) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have hev := hn.eventually_lt_const (by positivity : (0:ℝ)<ε/(|C|+1))
    filter_upwards [hev] with n hn
    intro T
    have ha : ‖a T‖≤|C|+1 := (show ‖a T‖≤C from T.property.2).trans
      (by linarith [le_abs_self C])
    have hb : ‖(g n-f) (a T)‖≤‖g n-f‖*(|C|+1) :=
      ((g n-f).le_opNorm (a T)).trans (mul_le_mul_of_nonneg_left ha (norm_nonneg _))
    have hh : ‖g n-f‖*(|C|+1)<ε := (lt_div_iff₀ (by positivity : (0:ℝ)< |C|+1)).mp hn
    rw [dist_eq_norm,norm_sub_rev]
    exact hb.trans_lt hh
  apply hu.continuous
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨N,y,hy⟩ := Set.mem_iUnion.mp (hg n)
  rw [←hy]
  exact coefficient_normal M v N y C

end Kadison.NormalPredual

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionNormalBridge
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem boundedWOTContinuous [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) (hf : ProjectionContinuousAtOne M f) :
    NormalPredual.BoundedWOTContinuous M (strongFunctional M f) :=
  NormalPredual.normal_of_mem_closure M (TopologicalSpace.denseSeq H) (mem_predual M f hf)

end Kadison.PositiveWOT

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteFactorTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.OrbitStateHull

open PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfac hd hfin

theorem hull_normal (x : H) {f : WeakDual ℂ M} (hf : f∈hull M x) :
    NormalGNS.BoundedWOTContinuous M (positive M x f hf) :=
  PositiveWOT.boundedWOTContinuous M (positive M x f hf)
    (hull_projectionContinuousAtOne M hfac hd hfin x hf)

theorem exists_faithful_normal_trace :
    ∃ τ : M →ₚ[ℂ] ℂ,(∀ a b : M,τ (a*b)=τ (b*a)) ∧
      NormalGNS.BoundedWOTContinuous M τ ∧ (∀ a : M,τ (star a*a)=0 → a=0) ∧ τ 1=1 := by
  obtain ⟨x,hx⟩ := exists_norm_eq H (show (0:ℝ)≤1 from zero_le_one)
  obtain ⟨f,hf,htr⟩ := exists_tracial_hull_of_norm_separable M x (hull_norm_separable M hfac hd hfin x)
  let τ := positive M x f hf
  have ht : ∀ a b : M,τ (a*b)=τ (b*a) := htr
  have hone : τ 1=1 := by
    change f 1=1
    rw [hull_one M x hf,hx]
    norm_num
  exact ⟨τ,ht,hull_normal M hfac hd hfin x hf,
    TraceDimension.faithful M τ ht hfac hd hfin hone,hone⟩

end Kadison.OrbitStateHull

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SeparableFactorMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem uniform_commutator_separable_factor_oai (P : VonNeumannAlgebra H)
    (hfac : FactorCorner.IsFactor P) (Y : H →L[ℂ] H) (h : ℕ) (hh : 1≤h)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖ ≤
      3122*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  classical
  rcases subsingleton_or_nontrivial H with hH|hH
  · let := hH
    have hz : diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y=0 := by
      ext x i
      exact Subsingleton.elim _ _
    rw [hz,norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (commutatorSeminorm_nonneg P Y)) (norm_nonneg _)
  · let := hH
    have hc : 9*commutatorSeminorm P Y*‖matrixOperator h X‖≤
        3122*commutatorSeminorm P Y*‖matrixOperator h X‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num : (9:ℝ)≤3122)
        (commutatorSeminorm_nonneg P Y)) (norm_nonneg _)
    by_cases hd : DiffuseProjection.HasNoMinimalProjections P
    · by_cases hf : PartialIsometryOrder.IsFiniteAlgebra P
      · obtain ⟨τ,htr,hnormal,hfaith,hone⟩ :=
          OrbitStateHull.exists_faithful_normal_trace P hfac hd hf
        exact NormalRepresentation.separable_traced_factor_bound P τ htr hnormal hfaith hone
          hfac hd h hh Y X hX
      · exact (uniform_commutator_nonfinite_factor P hfac hf Y h X hX).trans hc
    · exact (uniform_commutator_atomic_factor P hfac hd Y h X hX).trans hc

end Kadison

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.uniform_commutator_separable_factor_oai := @OAI.Kadison.uniform_commutator_separable_factor_oai
