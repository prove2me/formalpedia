-- Prove2me | solution 1 for OAI.Kadison.PartialIsometryOrder.nonfinite_two_isometries
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:23:05.914893+00:00
-- url     : https://prove2.me/submissions/2a8a6acd-4707-479d-a434-9d4a0b84b4a6

import Mathlib
import Definitions.Def_OAIQ039C051
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_PartialDecomposition_countable
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_exists_partialDecomposition

section
-- module Solutions.OAIQ039_CM.Commutator_PartialDecomposition
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

universe u

namespace Kadison.PartialIsometryOrder

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace PartialDecomposition

variable {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (D : PartialDecomposition M p)

lemma support_projection (s : Finset D.I) : IsStarProjection (D.support s) := by
  classical
  constructor
  · change D.support s*D.support s=D.support s
    rw [support,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum,Finset.sum_eq_single_of_mem i hi]
    · exact (D.v i).final_projection.isIdempotentElem.eq
    · intro j hj hne
      change ((D.v i).val*star (D.v i).val)*((D.v j).val*star (D.v j).val)=0
      calc
        _=((D.v i).val*(star (D.v i).val*(D.v j).val))*star (D.v j).val := by noncomm_ring
        _=0 := by rw [D.cross i j hne.symm,mul_zero,zero_mul]
  · change star (D.support s)=D.support s
    rw [support,star_sum]
    exact Finset.sum_congr rfl (fun i _ => (D.v i).final_projection.isSelfAdjoint.star_eq)

lemma support_norm_le (s : Finset D.I) : ‖D.support s‖≤1 :=
  (D.support_projection s).norm_le _

lemma support_tendsto (x : H) : Tendsto (fun s : Finset D.I => D.support s x) atTop (𝓝 x) :=
  D.strong x

lemma eq_zero_of_coefficients_zero {a : H →L[ℂ] H}
    (ha : ∀ i j,star (D.v i).val*a*(D.v j).val=0) : a=0 := by
  have hleft (i : D.I) : star (D.v i).val*a=0 := by
    ext x
    have he (s : Finset D.I) : (star (D.v i).val*a) (D.support s x)=0 := by
      have ht : (star (D.v i).val*a)*D.support s=0 := by
        rw [support,Finset.mul_sum]
        apply Finset.sum_eq_zero
        intro j hj
        change (star (D.v i).val*a)*((D.v j).val*star (D.v j).val)=0
        rw [←mul_assoc,ha i j,zero_mul]
      exact congrArg (fun T : H →L[ℂ] H => T x) ht
    exact tendsto_nhds_unique
      (((star (D.v i).val*a).continuous.tendsto x).comp (D.support_tendsto x))
      (by simpa only [Function.comp_def,he,zero_apply] using
        (tendsto_const_nhds : Tendsto (fun _ : Finset D.I => (0:H)) atTop (𝓝 0)))
  ext x
  have he (s : Finset D.I) : D.support s (a x)=0 := by
    have ht : D.support s*a=0 := by
      rw [support,Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro i hi
      change ((D.v i).val*star (D.v i).val)*a=0
      rw [mul_assoc,hleft i,mul_zero]
    exact congrArg (fun T : H →L[ℂ] H => T x) ht
  exact tendsto_nhds_unique (D.support_tendsto (a x))
    (by simpa only [Function.comp_def,he,zero_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : Finset D.I => (0:H)) atTop (𝓝 0)))

lemma eq_of_coefficients_eq {a b : H →L[ℂ] H}
    (h : ∀ i j,star (D.v i).val*a*(D.v j).val=star (D.v i).val*b*(D.v j).val) : a=b := by
  apply sub_eq_zero.mp
  apply D.eq_zero_of_coefficients_zero
  intro i j
  rw [mul_sub,sub_mul,h i j,sub_self]

end PartialDecomposition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProperIsometryReplicas
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem nonfinite_replicas (M : VonNeumannAlgebra H) (hfin : ¬IsFiniteAlgebra M) :
    ∃ r,r∈M ∧ IsStarProjection r ∧ r≠0 ∧ Nonempty (Replicas M r) := by
  classical
  simp only [IsFiniteAlgebra,not_forall] at hfin
  obtain ⟨v,hvM,hvi,hvn⟩ := hfin
  have hq : IsStarProjection (v*star v) := by
    constructor
    · change (v*star v)*(v*star v)=v*star v
      calc
        _=v*(star v*v)*star v := by noncomm_ring
        _=v*star v := by rw [hvi,mul_one]
    · exact IsSelfAdjoint.mul_star_self v
  let r : H →L[ℂ] H := 1-v*star v
  have hr : IsStarProjection r := hq.one_sub
  have hrn : r≠0 := by
    intro h
    exact hvn (sub_eq_zero.mp h).symm
  have hsvr : star v*r=0 := by
    change star v*(1-v*star v)=0
    rw [mul_sub,mul_one,←mul_assoc,hvi,one_mul,sub_self]
  have hrvs : r*v=0 := by
    simpa only [star_mul,hr.isSelfAdjoint.star_eq,star_star,star_zero] using congrArg star hsvr
  have hwords (n m : ℕ) : star (v^n*r)*(v^m*r)=if n=m then r else 0 := by
    induction n generalizing m with
    | zero =>
      cases m with
      | zero => simpa [hr.isSelfAdjoint.star_eq] using hr.isIdempotentElem.eq
      | succ m =>
        simp only [pow_zero,one_mul,pow_succ',Nat.zero_ne_add_one,ite_false,hr.isSelfAdjoint.star_eq]
        rw [show r*(v*v^m*r)=(r*v)*(v^m*r) by noncomm_ring,hrvs,zero_mul]
    | succ n ih =>
      cases m with
      | zero =>
        simp only [pow_zero,one_mul,pow_succ',Nat.add_one_ne_zero,ite_false,star_mul]
        rw [show star r*(star (v^n)*star v)*r=star r*star (v^n)*(star v*r) by noncomm_ring,hsvr,mul_zero]
      | succ m =>
        rw [pow_succ',pow_succ',star_mul,star_mul]
        rw [show star r*(star (v^n)*star v)*(v*v^m*r)=star (v^n*r)*(star v*v)*(v^m*r) by
          rw [star_mul]; noncomm_ring,hvi,mul_one,ih]
        simp
  refine ⟨r,M.sub_mem M.one_mem (M.mul_mem hvM (M.star_mem' hvM)),hr,hrn,
    ⟨⟨fun n => v^n*r,?_,?_,?_,?_⟩⟩⟩
  · intro n
    exact M.mul_mem (M.pow_mem hvM n) (M.sub_mem M.one_mem (M.mul_mem hvM (M.star_mem' hvM)))
  · intro n
    simpa using hwords n n
  · intro n m hnm
    simpa only [ite_eq_right hnm] using hwords n m
  · intro n
    rw [mul_assoc,hr.isIdempotentElem.eq]

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ReplicaPacking
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace PartialDecomposition

variable {M : VonNeumannAlgebra H} {r : H →L[ℂ] H}

variable (D : PartialDecomposition M r) (R : Replicas M r) (hr : IsStarProjection r)

include hr in
lemma finitePacking_star_mul (f : D.I → ℕ) (hf : Function.Injective f) (s : Finset D.I) :
    star (D.finitePacking R f s)*D.finitePacking R f s=D.support s := by
  classical
  rw [finitePacking,star_sum,Finset.sum_mul,support]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum,Finset.sum_eq_single_of_mem i hi]
  · simp only [star_mul,star_star]
    calc
      _=((D.v i).val*(star (R.a (f i))*R.a (f i)))*star (D.v i).val := by noncomm_ring
      _=(D.v i).final := by rw [R.initial,(D.v i).mul_source hr]; rfl
  · intro j hj hne
    simp only [star_mul,star_star]
    calc
      _=((D.v i).val*(star (R.a (f i))*R.a (f j)))*star (D.v j).val := by noncomm_ring
      _=0 := by rw [R.cross (f i) (f j) (fun h => hne (hf h).symm),mul_zero,zero_mul]

include hr in
lemma finitePacking_norm_le (f : D.I → ℕ) (hf : Function.Injective f) (s : Finset D.I) :
    ‖D.finitePacking R f s‖≤1 := by
  have he := D.support_norm_le s
  rw [←D.finitePacking_star_mul R hr f hf s,CStarRing.norm_star_mul_self] at he
  nlinarith [norm_nonneg (D.finitePacking R f s)]

lemma finitePacking_mul_val (f : D.I → ℕ) (s : Finset D.I) {i : D.I} (hi : i∈s) :
    D.finitePacking R f s*(D.v i).val=R.a (f i)*(D.v i).initial := by
  classical
  rw [finitePacking,Finset.sum_mul,Finset.sum_eq_single_of_mem i hi,mul_assoc]
  · rfl
  · intro j hj hne
    rw [mul_assoc,D.cross j i hne,mul_zero]

include hr in
theorem exists_packing (f : D.I → ℕ) (hf : Function.Injective f) :
    ∃ W : H →L[ℂ] H,W∈M ∧ ∀ i,W*(D.v i).val=R.a (f i)*(D.v i).initial := by
  classical
  let ω : Ultrafilter (Finset D.I) := Ultrafilter.of atTop
  have hω : (ω : Filter (Finset D.I))≤atTop := Ultrafilter.of_le _
  obtain ⟨W,hW,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω (D.finitePacking R f) 1
    (by norm_num) (D.finitePacking_norm_le R hr f hf)
  have hWM : W∈M := WeakOperatorLimit.mem_vonNeumann hlim M
    (Eventually.of_forall fun s => M.sum_mem (fun i _ =>
      M.mul_mem (R.mem (f i)) (M.star_mem' (D.v i).mem)))
  refine ⟨W,hWM,?_⟩
  intro i
  apply WeakOperatorLimit.right_eq hlim (D.v i).val (R.a (f i)*(D.v i).initial)
  filter_upwards [hω (eventually_ge_atTop ({i}:Finset D.I))] with s hs
  exact D.finitePacking_mul_val R f s (i:=i) (hs (Finset.mem_singleton_self i))

include hr in
lemma packing_isometry (f : D.I → ℕ) (hf : Function.Injective f)
    {W : H →L[ℂ] H} (hW : ∀ i,W*(D.v i).val=R.a (f i)*(D.v i).initial) : star W*W=1 := by
  apply D.eq_of_coefficients_eq
  intro i j
  calc
    star (D.v i).val*(star W*W)*(D.v j).val=star (W*(D.v i).val)*(W*(D.v j).val) := by
      rw [star_mul]; noncomm_ring
    _=star (R.a (f i)*(D.v i).initial)*(R.a (f j)*(D.v j).initial) := by rw [hW i,hW j]
    _=star (D.v i).val*(D.v j).val := by
      rw [star_mul,(D.v i).initial_projection.isSelfAdjoint.star_eq]
      rw [show (D.v i).initial*star (R.a (f i))*(R.a (f j)*(D.v j).initial)=
        (D.v i).initial*(star (R.a (f i))*R.a (f j))*(D.v j).initial by noncomm_ring]
      by_cases hij : i=j
      · subst j
        rw [R.initial,((D.v i).initial_projection.le_iff_mul_eq_left hr).mp (D.v i).source_le,
          (D.v i).initial_projection.isIdempotentElem.eq]
        rfl
      · rw [R.cross (f i) (f j) (fun h => hij (hf h)),mul_zero,zero_mul,D.cross i j hij]
    _=star (D.v i).val*1*(D.v j).val := by rw [mul_one]

lemma packings_orthogonal (f g : D.I → ℕ) (hfg : ∀ i j,f i≠g j)
    {W V : H →L[ℂ] H} (hW : ∀ i,W*(D.v i).val=R.a (f i)*(D.v i).initial)
    (hV : ∀ i,V*(D.v i).val=R.a (g i)*(D.v i).initial) : star W*V=0 := by
  apply D.eq_zero_of_coefficients_zero
  intro i j
  calc
    _=star (W*(D.v i).val)*(V*(D.v j).val) := by rw [star_mul]; noncomm_ring
    _=star (R.a (f i)*(D.v i).initial)*(R.a (g j)*(D.v j).initial) := by rw [hW i,hV j]
    _=star (D.v i).initial*(star (R.a (f i))*R.a (g j))*(D.v j).initial := by
      rw [star_mul]; noncomm_ring
    _=0 := by rw [R.cross _ _ (hfg i j),mul_zero,zero_mul]

end PartialDecomposition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NonfiniteFactor
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem nonfinite_two_isometries_oai (M : VonNeumannAlgebra H)
    (hfac : FactorCorner.IsFactor M) (hfin : ¬IsFiniteAlgebra M) :
    ∃ s t : M,star s*s=1 ∧ star t*t=1 ∧ star s*t=0 := by
  classical
  obtain ⟨r,hrM,hr,hrn,⟨R⟩⟩ := nonfinite_replicas M hfin
  obtain ⟨D⟩ := exists_partialDecomposition M hfac hrM hr hrn
  let := D.countable
  obtain ⟨e,he⟩ := Countable.exists_injective_nat (D.I × Bool)
  let f : D.I → ℕ := fun i => e (i,false)
  let g : D.I → ℕ := fun i => e (i,true)
  have hf : Function.Injective f := fun i j h => (Prod.mk.inj (he h)).1
  have hg : Function.Injective g := fun i j h => (Prod.mk.inj (he h)).1
  have hfg : ∀ i j,f i≠g j := by
    intro i j hij
    have := (Prod.mk.inj (he hij)).2
    contradiction
  obtain ⟨s,hs,hsv⟩ := D.exists_packing R hr f hf
  obtain ⟨t,ht,htv⟩ := D.exists_packing R hr g hg
  refine ⟨⟨s,hs⟩,⟨t,ht⟩,?_,?_,?_⟩
  · apply Subtype.ext
    exact D.packing_isometry R hr f hf hsv
  · apply Subtype.ext
    exact D.packing_isometry R hr g hg htv
  · apply Subtype.ext
    exact D.packings_orthogonal R f g hfg hsv htv

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.PartialIsometryOrder.nonfinite_two_isometries_oai.{u_1} := @OAI.Kadison.PartialIsometryOrder.nonfinite_two_isometries_oai.{u_1}
