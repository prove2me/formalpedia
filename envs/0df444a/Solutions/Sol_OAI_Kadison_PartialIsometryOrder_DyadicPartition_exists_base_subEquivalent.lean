-- Prove2me | solution 1 for OAI.Kadison.PartialIsometryOrder.DyadicPartition.exists_base_subEquivalent
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:43:25.396771+00:00
-- url     : https://prove2.me/submissions/37e1cbad-fe9d-4ab5-8999-c85d8c994f20

import Mathlib
import Definitions.Def_OAIQ039C058
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
-- module Solutions.OAIQ039_CM.Commutator_FiniteNoReplicas
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
  [TopologicalSpace.SeparableSpace H]

theorem finite_no_replicas (M : VonNeumannAlgebra H)
    (hfac : FactorCorner.IsFactor M) (hfin : IsFiniteAlgebra M)
    {r : H →L[ℂ] H} (hrM : r∈M) (hr : IsStarProjection r) (hrn : r≠0)
    (R : Replicas M r) : False := by
  classical
  obtain ⟨D⟩ := exists_partialDecomposition M hfac hrM hr hrn
  have := D.countable
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
  have hsi : star s*s=1 := D.packing_isometry R hr f hf hsv
  have hti : star t*t=1 := D.packing_isometry R hr g hg htv
  have hst : star s*t=0 := D.packings_orthogonal R f g hfg hsv htv
  have hsf : s*star s=1 := hfin s hs hsi
  have htz : t=0 := by
    calc
      t=(s*star s)*t := by rw [hsf,one_mul]
      _=0 := by rw [mul_assoc,hst,mul_zero]
  have hone : (1 : H →L[ℂ] H)=0 := by simpa only [htz,mul_zero] using hti.symm
  exact hrn (by simpa only [mul_one,mul_zero] using congrArg (fun z : H →L[ℂ] H => r*z) hone)

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionEquivalence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

lemma factor_subEquivalent_total (M : VonNeumannAlgebra H)
    (hfac : FactorCorner.IsFactor M) {e f : H →L[ℂ] H}
    (heM : e∈M) (hfM : f∈M) (he : IsStarProjection e) (hf : IsStarProjection f) :
    SubEquivalent M e f ∨ SubEquivalent M f e := by
  obtain ⟨v,hv⟩ := factor_comparison M hfac heM hfM he hf
  rcases hv with hv|hv
  · exact Or.inl ⟨v,hv⟩
  · exact Or.inr ⟨v.adjoint,by simpa using hv⟩

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DyadicCuts
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

namespace DyadicCuts

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
    (hd : DiffuseProjection.HasNoMinimalProjections M)

lemma side_projection (n : ℕ) : IsStarProjection (side M hfac hd n) :=
  (link M hfac hd n).final_projection

lemma side_le (n : ℕ) : side M hfac hd n≤(cut M hfac hd n).val :=
  (link M hfac hd n).target_le

lemma cut_antitone : Antitone (fun n => (cut M hfac hd n).val) := by
  apply antitone_nat_of_succ_le
  intro n
  exact (link M hfac hd n).source_le

lemma side_mul_cut_succ (n : ℕ) :
    side M hfac hd n*(cut M hfac hd (n+1)).val=0 := by
  have h := (link M hfac hd n).initial_mul_final_eq_zero
    (half_square M hfac hd (cut M hfac hd n))
  change (cut M hfac hd (n+1)).val*side M hfac hd n=0 at h
  simpa only [star_mul,(side_projection M hfac hd n).isSelfAdjoint.star_eq,
    (cut M hfac hd (n+1)).projection.isSelfAdjoint.star_eq,star_zero] using congrArg star h

lemma side_mul_side_of_lt {n m : ℕ} (hnm : n < m) : side M hfac hd n*side M hfac hd m=0 := by
  have hle : side M hfac hd m≤(cut M hfac hd (n+1)).val :=
    (side_le M hfac hd m).trans (cut_antitone M hfac hd (Nat.succ_le_of_lt hnm))
  have he := ((side_projection M hfac hd m).le_iff_mul_eq_right
    (cut M hfac hd (n+1)).projection).mp hle
  calc
    _=side M hfac hd n*((cut M hfac hd (n+1)).val*side M hfac hd m) := by rw [he]
    _=0 := by rw [←mul_assoc,side_mul_cut_succ,zero_mul]

lemma side_cross (n m : ℕ) (hne : n≠m) : side M hfac hd n*side M hfac hd m=0 := by
  rcases lt_or_gt_of_ne hne with h|h
  · exact side_mul_side_of_lt M hfac hd h
  · simpa only [star_mul,(side_projection M hfac hd n).isSelfAdjoint.star_eq,
      (side_projection M hfac hd m).isSelfAdjoint.star_eq,star_zero] using
      congrArg star (side_mul_side_of_lt M hfac hd h)

theorem exists_subEquivalent [TopologicalSpace.SeparableSpace H]
    (hfin : IsFiniteAlgebra M) {e : H →L[ℂ] H}
    (heM : e∈M) (he : IsStarProjection e) (hen : e≠0) :
    ∃ n,SubEquivalent M (cut M hfac hd n).val e := by
  classical
  by_contra hn
  push Not at hn
  have hrev (n : ℕ) : SubEquivalent M e (cut M hfac hd n).val := by
    exact (factor_subEquivalent_total M hfac heM (cut M hfac hd n).mem
      he (cut M hfac hd n).projection).resolve_right (hn n)
  choose v hv using hrev
  let b (n : ℕ) : Link M (cut M hfac hd (n+1)).val (side M hfac hd n) :=
    ⟨(link M hfac hd n).val,(link M hfac hd n).mem,(link M hfac hd n).triple,le_rfl,le_rfl⟩
  let a (n : ℕ) : Link M e (side M hfac hd n) :=
    (b n).compFull (v (n+1)) he (cut M hfac hd (n+1)).projection (hv (n+1)) rfl
  have hai (n : ℕ) : (a n).initial=e :=
    (b n).compFull_initial (v (n+1)) he (cut M hfac hd (n+1)).projection (hv (n+1)) rfl
  have hac (n m : ℕ) (hne : n≠m) : star (a n).val*(a m).val=0 := by
    have hl : star (a n).val*side M hfac hd n=star (a n).val := by
      simpa only [star_mul,(side_projection M hfac hd n).isSelfAdjoint.star_eq] using
        congrArg star ((a n).target_mul (side_projection M hfac hd n))
    calc
      _=(star (a n).val*side M hfac hd n)*(side M hfac hd m*(a m).val) := by
        rw [hl,(a m).target_mul (side_projection M hfac hd m)]
      _=star (a n).val*(side M hfac hd n*side M hfac hd m)*(a m).val := by noncomm_ring
      _=0 := by rw [side_cross M hfac hd n m hne,mul_zero,zero_mul]
  exact finite_no_replicas M hfac hfin heM he hen
    ⟨fun n => (a n).val,fun n => (a n).mem,hai,hac,fun n => (a n).mul_source he⟩

end DyadicCuts

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DyadicPartition
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace DyadicPartition

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M)

lemma base_eq_cut (n : ℕ) : (partition M hfac hd n).base=(DyadicCuts.cut M hfac hd n).val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (DyadicCuts.half M hfac hd ⟨(partition M hfac hd n).base,_,_⟩).initial=_
    have he : (⟨(partition M hfac hd n).base,(partition M hfac hd n).base_mem,
      (partition M hfac hd n).base_projection⟩ : ProjectionIn M)=DyadicCuts.cut M hfac hd n := by
      cases h : DyadicCuts.cut M hfac hd n
      simp only [h] at ih
      cases ih
      rfl
    rw [he]
    rfl

lemma exists_base_subEquivalent_oai [TopologicalSpace.SeparableSpace H]
    (hfin : IsFiniteAlgebra M) {e : H →L[ℂ] H}
    (heM : e∈M) (he : IsStarProjection e) (hen : e≠0) :
    ∃ n,SubEquivalent M (partition M hfac hd n).base e := by
  obtain ⟨n,hn⟩ := DyadicCuts.exists_subEquivalent M hfac hd hfin heM he hen
  exact ⟨n,by rwa [base_eq_cut]⟩

end DyadicPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.PartialIsometryOrder.DyadicPartition.exists_base_subEquivalent_oai.{u_1} := @OAI.Kadison.PartialIsometryOrder.DyadicPartition.exists_base_subEquivalent_oai.{u_1}
