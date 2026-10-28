-- Prove2me | solution 1 for OAI.Kadison.CentralAverage.exists_center_average
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:17:49.314001+00:00
-- url     : https://prove2.me/submissions/62ab29a9-b4d7-4b2b-b8c2-ca15625f9d77

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C048
import Theorems.Thm_OAI_Kadison_CentralAverage_exists_finite_average
import Theorems.Thm_OAI_Kadison_commutatorSeminorm_nonneg

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteDimensionalAverage
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap MeasureTheory

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma unitary_conjugate_distance (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) (v : unitary P) :
    ‖CompactAverage.conjugate (algebraUnitaryRepresentation P) Y v-Y‖ ≤ commutatorSeminorm P Y := by
  let w : unitary (K →L[ℂ] K) := algebraUnitaryLift P v
  have he : CompactAverage.conjugate (algebraUnitaryRepresentation P) Y v-Y=
      (((w:K →L[ℂ] K)*Y-Y*(w:K →L[ℂ] K))*star (w:K →L[ℂ] K)) := by
    change (w:K →L[ℂ] K)*Y*star (w:K →L[ℂ] K)-Y=_
    rw [sub_mul,mul_assoc Y (w:K →L[ℂ] K) (star (w:K →L[ℂ] K)),w.property.2,mul_one]
  rw [he]
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem w.property), norm_sub_rev]
  apply commutator_bound_unitball P Y (v:P).property
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(w:K →L[ℂ] K) x‖≤1*‖x‖
  rw [one_mul]
  exact (Unitary.norm_map w x).le

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryOrbitHull
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.UnitaryOrbit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

lemma hull_distance {Y T : H →L[ℂ] H} (hT : T∈hull M Y) :
    ‖T-Y‖ ≤ commutatorSeminorm M Y := by
  have hs : Set.range (fun v : unitary M => conjugate M v Y) ⊆
      Metric.closedBall Y (commutatorSeminorm M Y) := by
    rintro _ ⟨v,rfl⟩
    rw [Metric.mem_closedBall,dist_eq_norm]
    exact unitary_conjugate_distance M Y v
  simpa only [Metric.mem_closedBall,dist_eq_norm] using
    (convexHull_min hs (convex_closedBall Y _) hT)

lemma hull_norm {Y T : H →L[ℂ] H} (hT : T∈hull M Y) :
    ‖T‖ ≤ commutatorSeminorm M Y+‖Y‖ := by
  calc
    ‖T‖=‖T-Y+Y‖ := by rw [sub_add_cancel]
    _≤‖T-Y‖+‖Y‖ := norm_add_le _ _
    _ ≤ commutatorSeminorm M Y+‖Y‖ := by linarith [hull_distance M hT]

end Kadison.UnitaryOrbit

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MainCommutantDistance
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

open ContinuousLinearMap

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
lemma operator_commutator_norm_le (Y Z : K →L[ℂ] K) : ‖Y*Z-Z*Y‖≤2*‖Y‖*‖Z‖ := by
  calc
    _ ≤ ‖Y*Z‖+‖Z*Y‖ := norm_sub_le _ _
    _ ≤ ‖Y‖*‖Z‖+‖Z‖*‖Y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CommutatorPerturbation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma commutatorSeminorm_le (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) (C : ℝ)
    (hC : ∀ a : H →L[ℂ] H,a∈P → ‖a‖≤1 → ‖Y*a-a*Y‖≤C) :
    commutatorSeminorm P Y≤C := by
  apply csSup_le
  · exact ⟨0,0,P.zero_mem,by simp,by simp⟩
  · rintro r ⟨a,ha,hna,rfl⟩
    exact hC a ha hna

lemma commutatorSeminorm_perturb (P : VonNeumannAlgebra H) (Y Z : H →L[ℂ] H) :
    commutatorSeminorm P Z ≤ commutatorSeminorm P Y+2*‖Z-Y‖ := by
  apply commutatorSeminorm_le
  intro a ha hna
  have he : Z*a-a*Z=(Y*a-a*Y)+((Z-Y)*a-a*(Z-Y)) := by
    simp only [sub_mul,mul_sub]; abel
  rw [he]
  calc
    _ ≤ ‖Y*a-a*Y‖+‖(Z-Y)*a-a*(Z-Y)‖ := norm_add_le _ _
    _ ≤ commutatorSeminorm P Y+2*‖Z-Y‖*‖a‖ :=
      add_le_add (commutator_bound_unitball P Y ha hna) (operator_commutator_norm_le _ _)
    _ ≤ commutatorSeminorm P Y+2*‖Z-Y‖ := by nlinarith [norm_nonneg (Z-Y)]

lemma commutatorSeminorm_three (P : VonNeumannAlgebra H) (Y Z : H →L[ℂ] H)
    (hZ : ‖Z-Y‖ ≤ commutatorSeminorm P Y) : commutatorSeminorm P Z≤3*commutatorSeminorm P Y := by
  have hh := commutatorSeminorm_perturb P Y Z
  linarith

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionCommutant
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commutes_algebra_of_commutes_projections (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (hT : ∀ p∈M,IsStarProjection p → T*p=p*T) :
    ∀ a∈M,T*a=a*T := by
  have hself : ∀ a∈M,IsSelfAdjoint a → T*a=a*T := by
    intro a ha hsa
    have hclosed : IsClosed {b : H →L[ℂ] H | T*b=b*T} := isClosed_eq
      (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
    apply hclosed.closure_subset
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n,p,c,hp,_,he⟩ := Polar.exists_selfadjoint_spectral_sum M ha hsa hε
    refine ⟨∑ i,c i • p i,?_,?_⟩
    · change T*(∑ i,c i • p i)=(∑ i,c i • p i)*T
      simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]
      exact Finset.sum_congr rfl (fun i _ => congrArg (fun z : H →L[ℂ] H => c i • z)
        (hT (p i) (hp i).1 (hp i).2))
    · simpa only [dist_eq_norm] using he
  intro a ha
  let b : M := ⟨a,ha⟩
  have hR := hself (((realPart b):M):H →L[ℂ] H) ((realPart b):M).property
    ((realPart b).property.map M.toStarSubalgebra.subtype)
  have hI := hself (((imaginaryPart b):M):H →L[ℂ] H) ((imaginaryPart b):M).property
    ((imaginaryPart b).property.map M.toStarSubalgebra.subtype)
  have hid : (((realPart b):M):H →L[ℂ] H)+
      Complex.I • (((imaginaryPart b):M):H →L[ℂ] H)=a :=
    congrArg (fun x : M => (x:H →L[ℂ] H)) (realPart_add_I_smul_imaginaryPart b)
  rw [←hid,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,hR,hI]

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WeakOperatorLimit
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

open Filter

namespace Kadison.WeakOperatorLimit

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem norm_le_of_tendsto {l : Filter ι} [l.NeBot] {T : ι → E →L[ℂ] F}
    {V : E →L[ℂ] F} (hlim : ∀ x y, Tendsto (fun i => inner ℂ (T i x) y) l
      (𝓝 (inner ℂ (V x) y))) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ᶠ i in l, ‖T i‖ ≤ C) : ‖V‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound V hC
  intro x
  have hi : ‖inner ℂ (V x) (V x)‖ ≤ C*‖x‖*‖V x‖ := by
    apply le_of_tendsto (hlim x (V x)).norm
    filter_upwards [hT] with i hi
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (((T i).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hi (norm_nonneg x))) (norm_nonneg _))
  rw [← inner_self_re_eq_norm,inner_self_eq_norm_mul_norm] at hi
  by_cases hv : ‖V x‖=0
  · rw [hv]; positivity
  · have hp : 0 < ‖V x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    exact (mul_le_mul_iff_left₀ hp).mp (by simpa [pow_two,mul_comm,mul_left_comm,mul_assoc] using hi)

end Kadison.WeakOperatorLimit

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CentralAverage
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

open scoped InnerProductSpace Topology

namespace Kadison.CentralAverage

open UnitaryOrbit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_center_average_oai (M : VonNeumannAlgebra H) (Y : H →L[ℂ] H) :
    ∃ Y₁ : H →L[ℂ] H,
      (∀ a∈M,a∈Set.centralizer (M : Set (H →L[ℂ] H)) → Y₁*a=a*Y₁) ∧
      ‖Y₁-Y‖ ≤ commutatorSeminorm M Y ∧
      commutatorSeminorm M Y₁≤3*commutatorSeminorm M Y := by
  classical
  choose T hT hcomm using exists_finite_average M Y
  let ω : Ultrafilter (Finset (CentralProjection M)) := Ultrafilter.of atTop
  have hω : (ω : Filter (Finset (CentralProjection M)))≤atTop := Ultrafilter.of_le atTop
  obtain ⟨Y₁,_,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω T
    (commutatorSeminorm M Y+‖Y‖) (add_nonneg (commutatorSeminorm_nonneg M Y) (norm_nonneg Y))
    (fun s => hull_norm M (hT s))
  have hd : ‖Y₁-Y‖ ≤ commutatorSeminorm M Y := by
    apply WeakOperatorLimit.norm_le_of_tendsto (l := (ω : Filter (Finset (CentralProjection M))))
      (T := fun s => T s-Y)
      (fun x y => ?_) (commutatorSeminorm_nonneg M Y)
      (Filter.Eventually.of_forall fun s => hull_distance M (hT s))
    simpa only [sub_apply,inner_sub_left] using
      (hlim x y).sub_const (inner ℂ (Y x) y)
  have hc (p : CentralProjection M) : Y₁*p.val=p.val*Y₁ := by
    apply WeakOperatorLimit.intertwine hlim p.val p.val
    have he := (Filter.eventually_ge_atTop ({p} : Finset (CentralProjection M))).filter_mono hω
    filter_upwards [he] with s hs
    exact hcomm s p (hs (Finset.mem_singleton_self p))
  refine ⟨Y₁,?_,hd,?_⟩
  · intro a ha haz
    apply commutes_algebra_of_commutes_projections (vonNeumannIntersection M M.commutant) Y₁
      (fun p hp hpp => hc ⟨p,hp.1,hpp,by
        simpa only [VonNeumannAlgebra.coe_toStarSubalgebra,VonNeumannAlgebra.coe_commutant] using hp.2⟩) a
    exact ⟨ha,by
      simpa only [VonNeumannAlgebra.coe_toStarSubalgebra,VonNeumannAlgebra.coe_commutant] using haz⟩
  · exact commutatorSeminorm_three M Y Y₁ hd

end Kadison.CentralAverage

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.CentralAverage.exists_center_average_oai.{u_1} := @OAI.Kadison.CentralAverage.exists_center_average_oai.{u_1}
