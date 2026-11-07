-- Prove2me | solution 1 for HordijkKallenbergLP.Correspondence.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T09:32:57.4857+00:00
-- url     : https://prove2.me/submissions/4d83373a-47c5-4e63-8b05-1c3eb611b041

import Mathlib
import Definitions.Def_HordijkKallenbergLP_Correspondence_Representative

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section ThmSevenPart
attribute [-instance] HordijkKallenbergLP.Correspondence.instFintypePair

-- Begin Canonical
section ModuleScope_Canonical

end ModuleScope_Canonical
-- End Canonical

-- Begin ConeReduction
section ModuleScope_ConeReduction

open scoped BigOperators

namespace HordijkKallenbergLP.SingleLP.Proof

variable {I E : Type*} [AddCommGroup E] [Module ℝ E]

lemma positive_dependence (v : I → E) (s : Finset I)
    (h : ¬ LinearIndepOn ℝ v (s : Set I)) :
    ∃ g : I → ℝ, (∑ i ∈ s, g i • v i) = 0 ∧ ∃ i ∈ s, 0 < g i := by
  obtain ⟨g, hg, i, hi, hgi⟩ := not_linearIndepOn_finset_iff.mp h
  rcases lt_or_gt_of_ne hgi with hneg | hpos
  · refine ⟨fun j => -g j, ?_, i, hi, neg_pos.mpr hneg⟩
    simpa only [neg_smul, Finset.sum_neg_distrib, neg_zero] using congrArg Neg.neg hg
  · exact ⟨g, hg, i, hi, hpos⟩

lemma conical_support_reduction (v : I → E) (s : Finset I) (c : I → ℝ)
    (hc : ∀ i ∈ s, 0 < c i) (h : ¬ LinearIndepOn ℝ v (s : Set I)) :
    ∃ t : Finset I, t ⊂ s ∧ ∃ d : I → ℝ,
      (∀ i ∈ t, 0 < d i) ∧ (∑ i ∈ t, d i • v i) = ∑ i ∈ s, c i • v i := by
  classical
  obtain ⟨g, hg, i, hi, hgi⟩ := positive_dependence v s h
  let p := s.filter fun j => 0 < g j
  have hp : p.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  obtain ⟨j, hj, hmin⟩ := p.exists_min_image (fun j => c j / g j) hp
  have hjs : j ∈ s := (Finset.mem_filter.mp hj).1
  have hgj : 0 < g j := (Finset.mem_filter.mp hj).2
  let a := c j / g j
  have ha : 0 < a := div_pos (hc j hjs) hgj
  let d := fun k => c k - a * g k
  have hd : ∀ k ∈ s, 0 ≤ d k := by
    intro k hk
    by_cases hgk : 0 < g k
    · have hh := hmin k (Finset.mem_filter.mpr ⟨hk, hgk⟩)
      have hh' : a * g k ≤ c k := (le_div_iff₀ hgk).mp hh
      exact sub_nonneg.mpr hh'
    · have hh : g k ≤ 0 := le_of_not_gt hgk
      have := mul_nonpos_of_nonneg_of_nonpos ha.le hh
      dsimp [d]
      linarith [hc k hk]
  have hdj : d j = 0 := by dsimp [d, a]; field_simp; ring
  let t := s.filter fun k => 0 < d k
  have hts : t ⊆ s := Finset.filter_subset _ _
  have hjt : j ∉ t := by simp [t, hdj]
  refine ⟨t, Finset.ssubset_iff_subset_ne.mpr ⟨hts, ?_⟩, d, ?_, ?_⟩
  · intro heq
    exact hjt (heq.symm ▸ hjs)
  · intro k hk
    exact (Finset.mem_filter.mp hk).2
  · have heq : (∑ k ∈ t, d k • v k) = ∑ k ∈ s, d k • v k := by
      apply Finset.sum_subset hts
      intro k hk hkt
      have hle : d k ≤ 0 := by simpa [t, hk] using hkt
      rw [le_antisymm hle (hd k hk), zero_smul]
    rw [heq]
    simp_rw [d, sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, hg,
      smul_zero, sub_zero]

lemma conical_independent_representation (v : I → E) (s : Finset I) (c : I → ℝ)
    (hc : ∀ i ∈ s, 0 < c i) :
    ∃ t : Finset I, t ⊆ s ∧ LinearIndepOn ℝ v (t : Set I) ∧ ∃ d : I → ℝ,
      (∀ i ∈ t, 0 < d i) ∧ (∑ i ∈ t, d i • v i) = ∑ i ∈ s, c i • v i := by
  classical
  induction s using Finset.strongInductionOn generalizing c with
  | _ s ih =>
    by_cases hs : LinearIndepOn ℝ v (s : Set I)
    · exact ⟨s, subset_rfl, hs, c, hc, rfl⟩
    · obtain ⟨t, ht, d, hd, heq⟩ := conical_support_reduction v s c hc hs
      obtain ⟨u, hu, hi, e, he, heq'⟩ := ih t ht d hd
      exact ⟨u, hu.trans (Finset.ssubset_iff_subset_ne.mp ht).1, hi, e, he, heq'.trans heq⟩

end HordijkKallenbergLP.SingleLP.Proof
end ModuleScope_ConeReduction
-- End ConeReduction

-- Begin ConeClosed
section ModuleScope_ConeClosed

open scoped BigOperators

namespace HordijkKallenbergLP.SingleLP.Proof

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def finiteCone (v : I → E) : Set E :=
  {x | ∃ c : I → ℝ, (∀ i, 0 ≤ c i) ∧ ∑ i, c i • v i = x}

def supportedCone (v : I → E) (s : Finset I) : Set E :=
  (Fintype.linearCombination ℝ (fun i : s => v i)) '' {c : s → ℝ | ∀ i, 0 ≤ c i}

omit [DecidableEq I] in
lemma supportedCone_closed (v : I → E) (s : Finset I)
    (hs : LinearIndepOn ℝ v (s : Set I)) : IsClosed (supportedCone v s) := by
  have hinj := hs.fintypeLinearCombination_injective
  have he := LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  apply he.isClosedMap _
  have hh : IsClosed (⋂ i : s, {c : s → ℝ | 0 ≤ c i}) :=
    isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have heq : {c : s → ℝ | ∀ i, 0 ≤ c i} = ⋂ i : s, {c : s → ℝ | 0 ≤ c i} := by
    ext c
    simp
  rw [heq]
  exact hh

omit [Fintype I] [DecidableEq I] in
lemma supportedCone_mem (v : I → E) (s : Finset I) {x : E} :
    x ∈ supportedCone v s ↔ ∃ c : s → ℝ, (∀ i, 0 ≤ c i) ∧ ∑ i, c i • v i = x := by
  rfl

lemma finiteCone_union (v : I → E) :
    finiteCone v = ⋃ s : Finset I, ⋃ (_ : LinearIndepOn ℝ v (s : Set I)), supportedCone v s := by
  classical
  ext x
  constructor
  · rintro ⟨c, hc, hcx⟩
    let s := Finset.univ.filter fun i => 0 < c i
    have hcs : ∀ i ∈ s, 0 < c i := fun i hi => (Finset.mem_filter.mp hi).2
    obtain ⟨t, _, ht, d, hd, heq⟩ := conical_independent_representation v s c hcs
    apply Set.mem_iUnion.mpr
    refine ⟨t, Set.mem_iUnion.mpr ⟨ht, ?_⟩⟩
    apply (supportedCone_mem v t).mpr
    refine ⟨fun i => d i, fun i => (hd i i.2).le, ?_⟩
    rw [← Finset.sum_attach] at heq
    change (∑ i ∈ t.attach, d i • v i) = x
    rw [heq]
    rw [← hcx]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hz : c i = 0 := le_antisymm (by simpa [s] using hi) (hc i)
    simp [hz]
  · intro hx
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
    obtain ⟨_, hx⟩ := Set.mem_iUnion.mp hs
    obtain ⟨c, hc, hcx⟩ := (supportedCone_mem v s).mp hx
    refine ⟨fun i => if hi : i ∈ s then c ⟨i, hi⟩ else 0, ?_, ?_⟩
    · intro i
      dsimp only
      split_ifs with hi
      · exact hc ⟨i, hi⟩
      · exact le_rfl
    · have hh := Finset.sum_attach_eq_sum_dite s (fun i : s => c i • v i)
      simpa only [dite_smul, zero_smul] using hh.symm.trans hcx

lemma finiteCone_closed (v : I → E) : IsClosed (finiteCone v) := by
  rw [finiteCone_union]
  exact isClosed_iUnion_of_finite fun s => isClosed_iUnion_of_finite fun hs =>
    supportedCone_closed v s hs

end HordijkKallenbergLP.SingleLP.Proof
end ModuleScope_ConeClosed
-- End ConeClosed

-- Begin ConeSeparation
section ModuleScope_ConeSeparation

open scoped BigOperators
namespace HordijkKallenbergLP.SingleLP.Proof

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

omit [DecidableEq I] [DecidableEq V] in
lemma finiteCone_zero (a : I → V → ℝ) : (0 : V → ℝ) ∈ finiteCone a := by
  exact ⟨0, by simp, by simp⟩

omit [DecidableEq I] [DecidableEq V] in
lemma finiteCone_add (a : I → V → ℝ) {x y : V → ℝ}
    (hx : x ∈ finiteCone a) (hy : y ∈ finiteCone a) : x+y ∈ finiteCone a := by
  obtain ⟨c,hc,rfl⟩ := hx
  obtain ⟨d,hd,rfl⟩ := hy
  refine ⟨c+d, fun i => add_nonneg (hc i) (hd i), ?_⟩
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

omit [DecidableEq I] [DecidableEq V] in
lemma finiteCone_smul (a : I → V → ℝ) {x : V → ℝ} (hx : x ∈ finiteCone a)
    {r : ℝ} (hr : 0≤r) : r • x ∈ finiteCone a := by
  obtain ⟨c,hc,rfl⟩ := hx
  refine ⟨fun i => r*c i, fun i => mul_nonneg hr (hc i), ?_⟩
  simp only [mul_smul, Finset.smul_sum]

omit [DecidableEq V] in
lemma finiteCone_generator (a : I → V → ℝ) (i : I) : a i ∈ finiteCone a := by
  refine ⟨Pi.single i 1, ?_, ?_⟩
  · intro j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · simp

noncomputable def finiteProperCone (a : I → V → ℝ) : ProperCone ℝ (V → ℝ) where
  carrier := finiteCone a
  zero_mem' := finiteCone_zero a
  add_mem' := finiteCone_add a
  smul_mem' r _ hx := finiteCone_smul a hx r.property
  isClosed' := finiteCone_closed a

lemma finiteCone_separate (a : I → V → ℝ) {c : V → ℝ} (hc : c ∉ finiteCone a) :
    ∃ h : V → ℝ, (∀ i, ∑ j, a i j * h j ≤ 0) ∧ 0 < ∑ j, c j * h j := by
  obtain ⟨f,hf,hfc⟩ := (finiteProperCone a).hyperplane_separation_point hc
  let h : V → ℝ := fun j => -f (Pi.single j 1)
  have heq (v : V → ℝ) : (∑ j, v j * h j) = -f v := by
    have hv : (∑ j, v j • (Pi.single j 1 : V → ℝ)) = v := by
      ext k
      simp [Pi.single_apply]
    calc
      (∑ j, v j * h j) = -(∑ j, v j*f (Pi.single j 1)) := by
        simp [h,mul_neg,Finset.sum_neg_distrib]
      _ = -f (∑ j, v j • (Pi.single j 1 : V → ℝ)) := by simp
      _ = -f v := by rw [hv]
  refine ⟨h, fun i => ?_, ?_⟩
  · rw [heq]
    exact neg_nonpos.mpr (hf _ (finiteCone_generator a i))
  · rw [heq]
    exact neg_pos.mpr hfc

end HordijkKallenbergLP.SingleLP.Proof
end ModuleScope_ConeSeparation
-- End ConeSeparation

-- Begin FiniteSlack
section ModuleScope_FiniteSlack

open Filter Topology
namespace HordijkKallenbergLP.SingleLP.Proof

variable {V : Type*} [Fintype V]

lemma positive_slack (z h : V → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ∀ i, 0 < z i → 0 < z i + t*h i := by
  have he : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 < z i → 0 < z i + t*h i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : 0 < z i
    · have hc : ContinuousAt (fun t : ℝ => z i+t*h i) 0 := by fun_prop
      have hh := hc.eventually (lt_mem_nhds (by simpa using hi : 0 < z i+0*h i))
      exact hh.mono fun t ht _ => ht
    · exact Filter.Eventually.of_forall fun _ h => (hi h).elim
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp he
  exact ⟨ε,hε,fun t ht => hball (by simpa [Real.dist_eq] using ht)⟩

lemma nonnegative_step {z h : V → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hzero : ∀ i, z i=0 → 0≤h i) :
    ∃ ε : ℝ, 0<ε ∧ ∀ i, 0≤z i+ε*h i := by
  obtain ⟨ε,hε,hh⟩ := positive_slack z h
  refine ⟨ε/2,by positivity,fun i => ?_⟩
  rcases eq_or_lt_of_le (hz i) with hi | hi
  · rw [← hi,zero_add]
    exact mul_nonneg (by positivity) (hzero i hi.symm)
  · exact (hh (ε/2) (by rw [abs_of_pos (by positivity)]; linarith) i hi).le

lemma supported_two_steps {z h : V → ℝ} (hz : ∀ i, 0≤z i)
    (hzero : ∀ i, z i=0 → h i=0) :
    ∃ ε : ℝ, 0<ε ∧ (∀ i, 0≤z i+ε*h i) ∧ (∀ i, 0≤z i-ε*h i) := by
  obtain ⟨ε,hε,hh⟩ := positive_slack z h
  refine ⟨ε/2,by positivity,?_,?_⟩
  · intro i
    rcases eq_or_lt_of_le (hz i) with hi | hi
    · simp [← hi,hzero i hi.symm]
    · exact (hh (ε/2) (by rw [abs_of_pos (by positivity)]; linarith) i hi).le
  · intro i
    rcases eq_or_lt_of_le (hz i) with hi | hi
    · simp [← hi,hzero i hi.symm]
    · have hs := hh (-(ε/2)) (by rw [abs_neg,abs_of_pos (by positivity)]; linarith) i hi
      linarith

lemma extreme_direction_zero {E : Type*} [AddCommGroup E] [Module ℝ E]
    {C : Set E} {z h : E} (hz : z ∈ C.extremePoints ℝ) {ε : ℝ} (hε : 0<ε)
    (hp : z+ε•h ∈ C) (hm : z-ε•h ∈ C) : h=0 := by
  have hs : z ∈ openSegment ℝ (z+ε•h) (z-ε•h) := by
    refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
    module
  have he := hz.2 hp hm hs
  have hh : ε•h=0 := add_left_cancel (he.trans (add_zero z).symm)
  exact (smul_eq_zero.mp hh).resolve_left hε.ne'

end HordijkKallenbergLP.SingleLP.Proof
end ModuleScope_FiniteSlack
-- End FiniteSlack

-- Begin NormalCone
section ModuleScope_NormalCone

open scoped BigOperators
namespace HordijkKallenbergLP.SingleLP.Proof
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

noncomputable def normalGenerator (A : I → V → ℝ) (z : V → ℝ) :
    (I ⊕ I) ⊕ {v : V // z v=0} → V → ℝ :=
  Sum.elim (Sum.elim A (fun i => -A i)) (fun v => -Pi.single v.1 1)

lemma normal_multiplier (A : I → V → ℝ) (z c : V → ℝ)
    (hz : ∀ v, 0≤z v)
    (hopt : ∀ w : V → ℝ, (∀ v,0≤w v) →
      (∀ i, ∑ v,A i v*w v=∑ v,A i v*z v) → ∑ v,c v*w v≤∑ v,c v*z v) :
    ∃ l : I → ℝ, ∃ s : V → ℝ, (∀ v,0 ≤ s v) ∧
      (∀ v,0<z v → s v=0) ∧ ∀ v,c v=(∑ i,l i*A i v)-s v := by
  classical
  have hmem : c ∈ finiteCone (normalGenerator A z) := by
    by_contra hc
    obtain ⟨h,hh,hcpos⟩ := finiteCone_separate (normalGenerator A z) hc
    have hAh (i : I) : ∑ v,A i v*h v=0 := by
      have hp := hh (Sum.inl (Sum.inl i))
      have hm := hh (Sum.inl (Sum.inr i))
      simp only [normalGenerator,Sum.elim_inl,Sum.elim_inr,Pi.neg_apply,
        neg_mul,Finset.sum_neg_distrib] at hp hm
      linarith
    have hhzero (v : V) (hv : z v=0) : 0≤h v := by
      have hs := hh (Sum.inr ⟨v,hv⟩)
      simpa [normalGenerator,Pi.single_apply] using hs
    obtain ⟨ε,hε,hstep⟩ := nonnegative_step hz hhzero
    have hfeas (i : I) : (∑ v,A i v*(z v+ε*h v))=∑ v,A i v*z v := by
      simp_rw [mul_add,Finset.sum_add_distrib,← mul_assoc, mul_comm (A i _ ) ε,
        mul_assoc,← Finset.mul_sum,hAh,mul_zero,add_zero]
    have ho := hopt (fun v=>z v+ε*h v) hstep hfeas
    have he : (∑ v,c v*(z v+ε*h v))=(∑ v,c v*z v)+ε*(∑ v,c v*h v) := by
      simp_rw [mul_add,Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    rw [he] at ho
    have := mul_pos hε hcpos
    linarith
  obtain ⟨d,hd,heq⟩ := hmem
  let l : I → ℝ := fun i=>d (Sum.inl (Sum.inl i))-d (Sum.inl (Sum.inr i))
  let s : V → ℝ := fun v=>∑ j : {v : V // z v=0}, d (Sum.inr j)*(if j.1=v then 1 else 0)
  refine ⟨l,s,?_,?_,?_⟩
  · intro v
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hd _) (by split_ifs <;> norm_num)
  · intro v hv
    apply Finset.sum_eq_zero
    intro j _
    have hj : j.1≠v := by intro he; have := j.2; rw [he] at this; linarith
    simp [hj]
  · intro v
    have he := congrFun heq v
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Fintype.sum_sum_type,
      normalGenerator,Sum.elim_inl,Sum.elim_inr,Pi.neg_apply] at he
    have hu : (∑ j : {v : V // z v=0},d (Sum.inr j)* -((Pi.single j.1 (1 : ℝ) : V → ℝ) v)) = -s v := by
      simp only [s,mul_neg,Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simp [Pi.single_apply,eq_comm]
    rw [hu] at he
    simp only [l,sub_mul,Finset.sum_sub_distrib,s] at *
    simp only [mul_neg,Finset.sum_neg_distrib] at he
    linarith

end HordijkKallenbergLP.SingleLP.Proof
end ModuleScope_NormalCone
-- End NormalCone

-- Begin NativeLPBasic
section ModuleScope_NativeLPBasic

open scoped BigOperators
open MarkovDecisionProcesses
namespace HordijkKallenbergLP.SingleLP.Proof
variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

noncomputable def deltaTrans (M : StationaryMDP S A) (p : Pair M) (j : S) : ℝ :=
  (if p.1.1=j then 1 else 0)-M.trans p.1.1 p.1.2 j

noncomputable def stateVec (M : StationaryMDP S A) (x : Pair M → ℝ) (j : S) : ℝ :=
  ∑ p, (if p.1.1=j then 1 else 0)*x p

lemma stateVec_eq (M : StationaryMDP S A) (x : Pair M → ℝ) (j : S) :
    stateVec M x j=stateSum M x j := by
  simp only [stateVec,stateSum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp

omit [DecidableEq A] in
lemma delta_pairing (M : StationaryMDP S A) (p : Pair M) (u : S → ℝ) :
    (∑ j,deltaTrans M p j*u j)=u p.1.1-∑ j,M.trans p.1.1 p.1.2 j*u j := by
  simp [deltaTrans,sub_mul,Finset.sum_sub_distrib,ite_mul,eq_comm]

noncomputable def lpRows (M : StationaryMDP S A) : (S⊕S) → (Pair M⊕Pair M) → ℝ :=
  Sum.elim (fun j=>Sum.elim (fun p=>deltaTrans M p j) (fun _=>0))
    (fun j=>Sum.elim (fun p=>if p.1.1=j then 1 else 0) (fun p=>deltaTrans M p j))

noncomputable def lpCost (M : StationaryMDP S A) : (Pair M⊕Pair M) → ℝ :=
  Sum.elim (fun p=>M.reward p.1.1 p.1.2) (fun _=>0)

lemma lp_rows_first (M : StationaryMDP S A) (w : (Pair M⊕Pair M)→ℝ) (j : S) :
    (∑ p,lpRows M (.inl j) p*w p)=∑ p,deltaTrans M p j*w (.inl p) := by
  simp [lpRows,Fintype.sum_sum_type]

lemma lp_rows_second (M : StationaryMDP S A) (w : (Pair M⊕Pair M)→ℝ) (j : S) :
    (∑ p,lpRows M (.inr j) p*w p)=stateSum M (fun p=>w (.inl p)) j+
      ∑ p,deltaTrans M p j*w (.inr p) := by
  simp only [lpRows,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  rw [← stateVec_eq]
  rfl

omit [DecidableEq S] in
lemma lp_cost_eq (M : StationaryMDP S A) (w : (Pair M⊕Pair M)→ℝ) :
    (∑ p,lpCost M p*w p)=dualObjective M (fun p=>w (.inl p)) := by
  simp [lpCost,Fintype.sum_sum_type,dualObjective]

omit [DecidableEq A] in
lemma lp_column_first (M : StationaryMDP S A) (l : S⊕S→ℝ) (p : Pair M) :
    (∑ i,l i*lpRows M i (.inl p))=
    l (.inr p.1.1)+l (.inl p.1.1)-∑ j,M.trans p.1.1 p.1.2 j*l (.inl j) := by
  have hd:=delta_pairing M p (fun j=>l (.inl j))
  simp only [lpRows,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  simp only [mul_comm (l _) (deltaTrans M p _)]
  rw [hd]
  simp [mul_ite,eq_comm]
  ring

omit [DecidableEq A] in
lemma lp_column_second (M : StationaryMDP S A) (l : S⊕S→ℝ) (p : Pair M) :
    (∑ i,l i*lpRows M i (.inr p))=
    l (.inr p.1.1)-∑ j,M.trans p.1.1 p.1.2 j*l (.inr j) := by
  simp only [lpRows,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,mul_zero,
    Finset.sum_const_zero,zero_add]
  simpa only [mul_comm (l _) (deltaTrans M p _)] using delta_pairing M p (fun j=>l (.inr j))

end HordijkKallenbergLP.SingleLP.Proof
end ModuleScope_NativeLPBasic
-- End NativeLPBasic

-- Begin NativeCertificate
section ModuleScope_NativeCertificate

open scoped BigOperators
open MarkovDecisionProcesses
namespace HordijkKallenbergLP.SingleLP.Proof
variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

lemma native_certificate (M : StationaryMDP S A) (β : S→ℝ)
    (z : (Pair M→ℝ)×(Pair M→ℝ)) (hopt : IsDualOptimal M β z) :
    ∃ φ u : S→ℝ, Superharmonic M φ u ∧
      (∀ p : Pair M,0<z.1 p → φ p.1.1+u p.1.1=
        M.reward p.1.1 p.1.2+∑ j,M.trans p.1.1 p.1.2 j*u j) ∧
      (∀ p : Pair M,0<z.2 p → φ p.1.1=∑ j,M.trans p.1.1 p.1.2 j*φ j) := by
  classical
  let v : Pair M⊕Pair M→ℝ := Sum.elim z.1 z.2
  have hv : ∀ p,0≤v p := by
    intro p
    cases p with
    | inl p => exact (hopt.1.2.2 p).1
    | inr p => exact (hopt.1.2.2 p).2
  have ho : ∀ w : Pair M⊕Pair M→ℝ, (∀ p,0≤w p) →
      (∀ i,∑ p,lpRows M i p*w p=∑ p,lpRows M i p*v p) →
      (∑ p,lpCost M p*w p)≤∑ p,lpCost M p*v p := by
    intro w hw he
    have hf : (fun p=>w (.inl p),fun p=>w (.inr p)) ∈ dualFeasible M β := by
      refine ⟨?_,?_,fun p=>⟨hw (.inl p),hw (.inr p)⟩⟩
      · intro j
        have hj:=he (.inl j)
        rw [lp_rows_first,lp_rows_first] at hj
        exact hj.trans (hopt.1.1 j)
      · intro j
        have hj:=he (.inr j)
        rw [lp_rows_second,lp_rows_second] at hj
        exact hj.trans (hopt.1.2.1 j)
    simpa only [lp_cost_eq,v,Sum.elim_inl] using hopt.2 _ hf
  obtain ⟨l,s,hs,hzero,hc⟩ := normal_multiplier (lpRows M) v (lpCost M) hv ho
  let φ : S→ℝ := fun j=>l (.inr j)
  let u : S→ℝ := fun j=>l (.inl j)
  have hx (p : Pair M) : M.reward p.1.1 p.1.2=
      φ p.1.1+u p.1.1-(∑ j,M.trans p.1.1 p.1.2 j*u j)-s (.inl p) := by
    simpa only [lpCost,Sum.elim_inl,lp_column_first,φ,u] using hc (.inl p)
  have hy (p : Pair M) : 0=φ p.1.1-(∑ j,M.trans p.1.1 p.1.2 j*φ j)-s (.inr p) := by
    simpa only [lpCost,Sum.elim_inr,lp_column_second,φ] using hc (.inr p)
  refine ⟨φ,u,?_,?_,?_⟩
  · intro i a ha
    have hxp:=hx ⟨(i,a),ha⟩
    have hyp:=hy ⟨(i,a),ha⟩
    have hsx:=hs (.inl ⟨(i,a),ha⟩)
    have hsy:=hs (.inr ⟨(i,a),ha⟩)
    dsimp only at hxp hyp
    constructor <;> linarith
  · intro p hp
    have hz:=hzero (.inl p) hp
    have hh:=hx p
    rw [hz] at hh
    linarith
  · intro p hp
    have hz:=hzero (.inr p) hp
    have hh:=hy p
    rw [hz] at hh
    linarith

end HordijkKallenbergLP.SingleLP.Proof
end ModuleScope_NativeCertificate
-- End NativeCertificate

-- Begin NativeExtreme
section ModuleScope_NativeExtreme

open scoped BigOperators
open MarkovDecisionProcesses
namespace HordijkKallenbergLP.SingleLP.Proof
variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

lemma feasible_y_add (M : StationaryMDP S A) (β : S→ℝ)
    (z : (Pair M→ℝ)×(Pair M→ℝ)) (hz : z∈dualFeasible M β)
    (h : Pair M→ℝ) (hh : ∀ j,∑ p,deltaTrans M p j*h p=0)
    (t : ℝ) (hn : ∀ p,0≤z.2 p+t*h p) :
    (z.1,fun p=>z.2 p+t*h p)∈dualFeasible M β := by
  refine ⟨hz.1,?_,fun p=>⟨(hz.2.2 p).1,hn p⟩⟩
  intro j
  change stateSum M z.1 j+(∑ p,deltaTrans M p j*(z.2 p+t*h p))=β j
  have he : (∑ p,deltaTrans M p j*(z.2 p+t*h p))=
      (∑ p,deltaTrans M p j*z.2 p)+t*(∑ p,deltaTrans M p j*h p) := by
    simp_rw [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he,hh,mul_zero,add_zero]
  exact hz.2.1 j

lemma extreme_y_kernel (M : StationaryMDP S A) (β : S→ℝ)
    (z : (Pair M→ℝ)×(Pair M→ℝ)) (hext : z∈(dualFeasible M β).extremePoints ℝ)
    (h : Pair M→ℝ) (hh : ∀ j,∑ p,deltaTrans M p j*h p=0)
    (hsupp : ∀ p,z.2 p=0 → h p=0) : h=0 := by
  obtain ⟨ε,hε,hp,hm⟩ := supported_two_steps (fun p=>(hext.1.2.2 p).2) hsupp
  have hplus : z+ε•(0,h) ∈ dualFeasible M β := by
    convert feasible_y_add M β z hext.1 h hh ε hp using 1
    apply Prod.ext
    · simp
    · rfl
  have hminus : z-ε•(0,h) ∈ dualFeasible M β := by
    convert feasible_y_add M β z hext.1 h hh (-ε)
      (by simpa [sub_eq_add_neg] using hm) using 1
    apply Prod.ext
    · simp
    · funext p
      change z.2 p-ε*h p=z.2 p+(-ε)*h p
      ring
  have he := extreme_direction_zero hext hε hplus hminus
  exact congrArg Prod.snd he

noncomputable def selectedPair (M : StationaryMDP S A) (f : S→A)
    (hf : ∀ i,f i∈M.admissible i) (i : S) : Pair M := ⟨(i,f i),hf i⟩

omit [DecidableEq S] [DecidableEq A] in
lemma selectedPair_injective (M : StationaryMDP S A) (f : S→A)
    (hf : ∀ i,f i∈M.admissible i) : Function.Injective (selectedPair M f hf) := by
  intro i j he
  exact congrArg (fun p : Pair M=>p.1.1) he

noncomputable def liftSelected (M : StationaryMDP S A) (f : S→A)
    (hf : ∀ i,f i∈M.admissible i) (C : Finset S) (w : C→ℝ) : Pair M→ℝ :=
  ∑ i : C,w i • Pi.single (selectedPair M f hf i) 1

lemma liftSelected_at (M : StationaryMDP S A) (f : S→A)
    (hf : ∀ i,f i∈M.admissible i) (C : Finset S) (w : C→ℝ) (j : C) :
    liftSelected M f hf C w (selectedPair M f hf j)=w j := by
  simp only [liftSelected,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
  have he (i : C) : selectedPair M f hf j=selectedPair M f hf i ↔ i=j := by
    rw [(selectedPair_injective M f hf).eq_iff]
    exact ⟨fun h=>Subtype.ext h.symm,fun h=>by cases h; rfl⟩
  simp_rw [he]
  simp

lemma liftSelected_balance (M : StationaryMDP S A) (f : S→A)
    (hf : ∀ i,f i∈M.admissible i) (C : Finset S) (w : C→ℝ) (j : S) :
    (∑ p,deltaTrans M p j*liftSelected M f hf C w p)=
      ∑ i : C,w i*deltaTrans M (selectedPair M f hf i) j := by
  simp only [liftSelected,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [Pi.single_apply,mul_ite,mul_comm]

end HordijkKallenbergLP.SingleLP.Proof
end ModuleScope_NativeExtreme
-- End NativeExtreme

-- Begin ClosedKernel
section ModuleScope_ClosedKernel

open scoped BigOperators
open MarkovDecisionProcesses Matrix
namespace HordijkKallenbergLP.SingleLP.Proof
variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

omit [DecidableEq A] in
lemma closed_selected_kernel (M : StationaryMDP S A) (f : S→A)
    (hf : ∀ i,f i∈M.admissible i) (C : Finset S) (hC : C.Nonempty)
    (hclosed : ∀ i∈C,∀ j∉C,M.trans i (f i) j=0) :
    ∃ w : C→ℝ, w≠0 ∧ ∀ j : S,
      ∑ i : C,w i*deltaTrans M (selectedPair M f hf i) j=0 := by
  classical
  let Q : Matrix C C ℝ := fun i j=>deltaTrans M (selectedPair M f hf i) j
  have hone : (fun _ : C=>(1:ℝ))≠0 := by
    obtain ⟨i,hi⟩:=hC
    intro he
    have := congrFun he ⟨i,hi⟩
    norm_num at this
  have hrow (i : C) : ∑ j : C,M.trans i (f i) j=1 := by
    rw [Finset.sum_coe_sort]
    calc
      (∑ j∈C,M.trans i (f i) j) = ∑ j,M.trans i (f i) j := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        exact hclosed i i.2 j hj
      _ = 1 := M.trans_sum _ _
  have hQone : Q*ᵥ(fun _=>1)=0 := by
    funext i
    simp only [mulVec,dotProduct,Q,deltaTrans,selectedPair,mul_one,
      Finset.sum_sub_distrib]
    have he : (∑ j : C,if (i:S)=(j:S) then (1:ℝ) else 0)=1 := by
      simp only [Subtype.val_inj]
      simp
    change (∑ j : C,if (i:S)=(j:S) then (1:ℝ) else 0) - (∑ j : C,M.trans i (f i) j)=0
    rw [he,hrow,sub_self]
  have hn : ¬Function.Injective Q.vecMul := by
    intro hi
    have hj := Matrix.mulVec_injective_of_isUnit (Matrix.vecMul_injective_iff_isUnit.mp hi)
    have he : (fun _ : C=>(1:ℝ))=0 := hj (hQone.trans (Matrix.mulVec_zero Q).symm)
    exact hone he
  obtain ⟨a,b,hab,hne⟩ := Function.not_injective_iff.mp hn
  let w : C→ℝ := a-b
  have hw : w≠0 := sub_ne_zero.mpr hne
  have hwQ : w ᵥ* Q=0 := by
    dsimp only [w]
    rw [Matrix.sub_vecMul,hab,sub_self]
  refine ⟨w,hw,fun j=>?_⟩
  by_cases hj : j∈C
  · exact congrFun hwQ ⟨j,hj⟩
  · apply Finset.sum_eq_zero
    intro i _
    have hij : (i:S)≠j := by intro he; exact hj (he ▸ i.2)
    simp [deltaTrans,selectedPair,hij,hclosed i i.2 j hj]

lemma no_closed_outside (M : StationaryMDP S A) (β : S→ℝ)
    (z : (Pair M→ℝ)×(Pair M→ℝ)) (hext : z∈(dualFeasible M β).extremePoints ℝ)
    (f : S→A) (hf : ∀ i,f i∈M.admissible i) (hsel : IsSelection M z.1 z.2 f hf) :
    ∀ C : Set S, C.Nonempty → C⊆(Ex M z.1)ᶜ →
      (∀ i∈C,∀ j∉C,M.trans i (f i) j=0) → False := by
  classical
  intro C hC hsub hclosed
  let D : Finset S := C.toFinite.toFinset
  have hD : D.Nonempty := by simpa [D] using hC
  obtain ⟨w,hw,hbal⟩ := closed_selected_kernel M f hf D hD
    (by simpa [D] using hclosed)
  let h := liftSelected M f hf D w
  have hsupport : ∀ p : Pair M,z.2 p=0 → h p=0 := by
    intro p hp
    dsimp only [h,liftSelected]
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hine : (i:S)∉Ex M z.1 := hsub (by simpa [D] using i.2)
    have hy := (hsel i).2 hine
    have hne : p≠selectedPair M f hf i := by
      intro he
      rw [he] at hp
      exact hy.ne' hp
    simp [Pi.smul_apply,hne]
  have he : h=0 := extreme_y_kernel M β z hext h
    (fun j=>(liftSelected_balance M f hf D w j).trans (hbal j)) hsupport
  apply hw
  funext i
  have hh := congrFun he (selectedPair M f hf i)
  simpa only [h,liftSelected_at,Pi.zero_apply] using hh

end HordijkKallenbergLP.SingleLP.Proof
end ModuleScope_ClosedKernel
-- End ClosedKernel

-- Begin SelectedStructure
section ModuleScope_SelectedStructure

open scoped BigOperators
open MarkovDecisionProcesses
namespace HordijkKallenbergLP.SingleLP.Proof
variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

lemma balance_pairing_zero (M : StationaryMDP S A) (x : Pair M→ℝ)
    (hbal : ∀ j,∑ p,deltaTrans M p j*x p=0) (φ : S→ℝ) :
    (∑ p,x p*(φ p.1.1-∑ j,M.trans p.1.1 p.1.2 j*φ j))=0 := by
  simp_rw [← delta_pairing,Finset.mul_sum]
  rw [Finset.sum_comm]
  have he (j : S) : (∑ p,x p*(deltaTrans M p j*φ j))=
      (∑ p,deltaTrans M p j*x p)*φ j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    ring
  simp_rw [he,hbal,zero_mul,Finset.sum_const_zero]

lemma selected_closed (M : StationaryMDP S A) (β : S→ℝ)
    (z : (Pair M→ℝ)×(Pair M→ℝ)) (hz : z∈dualFeasible M β)
    (f : S→A) (hf : ∀ i,f i∈M.admissible i) (hsel : IsSelection M z.1 z.2 f hf) :
    ∀ i∈Ex M z.1,∀ j∉Ex M z.1,M.trans i (f i) j=0 := by
  intro i hi j hj
  have hsnn : 0 ≤ stateSum M z.1 j := Finset.sum_nonneg fun p _=>(hz.2.2 p).1
  have hsz : stateSum M z.1 j=0 := le_antisymm (not_lt.mp hj) hsnn
  have hb:=hz.1 j
  have he : (∑ p : Pair M,deltaTrans M p j*z.1 p)=
      stateSum M z.1 j-∑ p : Pair M,M.trans p.1.1 p.1.2 j*z.1 p := by
    simp_rw [deltaTrans,sub_mul,Finset.sum_sub_distrib]
    rw [← stateVec_eq]
    rfl
  change (∑ p : Pair M,deltaTrans M p j*z.1 p)=0 at hb
  rw [he,hsz,zero_sub] at hb
  have hin : (∑ p : Pair M,M.trans p.1.1 p.1.2 j*z.1 p)=0 := neg_eq_zero.mp hb
  have hp := (Finset.sum_eq_zero_iff_of_nonneg
    (fun p (_ : p∈Finset.univ)=>mul_nonneg (M.trans_nonneg _ _ _) (hz.2.2 p).1)).mp hin
  have hprod:=hp (selectedPair M f hf i) (Finset.mem_univ _)
  exact (mul_eq_zero.mp hprod).resolve_right ((hsel i).1 hi).ne'

lemma selected_structure (M : StationaryMDP S A) (β : S→ℝ)
    (z : (Pair M→ℝ)×(Pair M→ℝ)) (hext : z∈(dualFeasible M β).extremePoints ℝ)
    (hopt : IsDualOptimal M β z) (f : S→A) (hf : ∀ i,f i∈M.admissible i)
    (hsel : IsSelection M z.1 z.2 f hf) :
    ∃ φ u : S→ℝ, Superharmonic M φ u ∧
      (∀ i,∑ j,M.trans i (f i) j*φ j=φ i) ∧
      (∀ i∈Ex M z.1,M.reward i (f i)=φ i+u i-∑ j,M.trans i (f i) j*u j) ∧
      (∀ i∈Ex M z.1,∀ j∉Ex M z.1,M.trans i (f i) j=0) ∧
      (∀ C : Set S,C.Nonempty → C⊆(Ex M z.1)ᶜ →
        (∀ i∈C,∀ j∉C,M.trans i (f i) j=0) → False) := by
  obtain ⟨φ,u,hsh,hx,hy⟩ := native_certificate M β z hopt
  have hgap (p : Pair M) : 0≤φ p.1.1-∑ j,M.trans p.1.1 p.1.2 j*φ j :=
    sub_nonneg.mpr (hsh p.1.1 p.1.2 p.2).1
  have hzero:=balance_pairing_zero M z.1 hopt.1.1 φ
  have hterm:=(Finset.sum_eq_zero_iff_of_nonneg
    (fun p (_ : p∈Finset.univ)=>mul_nonneg (hopt.1.2.2 p).1 (hgap p))).mp hzero
  refine ⟨φ,u,hsh,?_,?_,selected_closed M β z hopt.1 f hf hsel,
    no_closed_outside M β z hext f hf hsel⟩
  · intro i
    by_cases hi : i∈Ex M z.1
    · have hh:=hterm (selectedPair M f hf i) (Finset.mem_univ _)
      have hz:=(mul_eq_zero.mp hh).resolve_left ((hsel i).1 hi).ne'
      exact (sub_eq_zero.mp hz).symm
    · exact (hy (selectedPair M f hf i) ((hsel i).2 hi)).symm
  · intro i hi
    have hh:=hx (selectedPair M f hf i) ((hsel i).1 hi)
    dsimp only [selectedPair] at hh
    linarith

end HordijkKallenbergLP.SingleLP.Proof
end ModuleScope_SelectedStructure
-- End SelectedStructure

-- Begin Substochastic
section ModuleScope_Substochastic

open scoped BigOperators

namespace HordijkKallenbergLP.SingleLP.Proof

variable {I : Type*} [Fintype I]

lemma substochastic_fixed_nonpos (Q : I → I → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hs : ∀ i, ∑ j, Q i j ≤ 1)
    (hclosed : ∀ C : Set I, C.Nonempty →
      (∀ i ∈ C, (∑ j, Q i j = 1) ∧ ∀ j ∉ C, Q i j = 0) → False)
    (w : I → ℝ) (hw : ∀ i, ∑ j, Q i j * w j = w i) : ∀ i, w i ≤ 0 := by
  classical
  by_contra! hh
  obtain ⟨i, hi⟩ := hh
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ w ⟨i, Finset.mem_univ i⟩
  have ham (j : I) : w j ≤ w a := ha j (Finset.mem_univ j)
  have hap : 0 < w a := hi.trans_le (ham i)
  apply hclosed {j | w j = w a} ⟨a, rfl⟩
  intro j hj
  change w j = w a at hj
  have hle : ∑ k, Q j k * w k ≤ (∑ k, Q j k) * w a := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (ham k) (hQ j k)
  have hrow : ∑ k, Q j k = 1 := by rw [hw, hj] at hle; nlinarith [hs j]
  refine ⟨hrow, ?_⟩
  have hz : ∑ k, Q j k * (w a - w k) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hrow, hw, hj]; ring
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k (_ : k ∈ Finset.univ) => mul_nonneg (hQ j k) (sub_nonneg.mpr (ham k)))).mp hz
  intro k hk
  have hk' : w k ≠ w a := hk
  exact (mul_eq_zero.mp (hterm k (Finset.mem_univ k))).resolve_right
    (sub_ne_zero.mpr hk'.symm)

lemma substochastic_fixed_zero (Q : I → I → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hs : ∀ i, ∑ j, Q i j ≤ 1)
    (hclosed : ∀ C : Set I, C.Nonempty →
      (∀ i ∈ C, (∑ j, Q i j = 1) ∧ ∀ j ∉ C, Q i j = 0) → False)
    (w : I → ℝ) (hw : ∀ i, ∑ j, Q i j * w j = w i) : w = 0 := by
  have hneg : ∀ i, ∑ j, Q i j * (-w j) = -w i := by
    intro i
    simpa only [mul_neg, Finset.sum_neg_distrib] using congrArg Neg.neg (hw i)
  have h1 := substochastic_fixed_nonpos Q hQ hs hclosed w hw
  have h2 := substochastic_fixed_nonpos Q hQ hs hclosed (fun i => -w i) hneg
  funext i
  exact le_antisymm (h1 i) (neg_nonpos.mp (h2 i))

lemma substochastic_poisson_nonneg (Q : I → I → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hs : ∀ i, ∑ j, Q i j ≤ 1)
    (v : I → ℝ) (hv : ∀ i, v i - ∑ j, Q i j * v j = 1) : ∀ i, 0 ≤ v i := by
  classical
  by_contra! hh
  obtain ⟨i, hi⟩ := hh
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ v ⟨i, Finset.mem_univ i⟩
  have ham (j : I) : v a ≤ v j := ha j (Finset.mem_univ j)
  have han : v a < 0 := (ham i).trans_lt hi
  have hle : (∑ j, Q a j) * v a ≤ ∑ j, Q a j * v j := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ham j) (hQ a j)
  have hle' : v a ≤ (∑ j, Q a j) * v a := by nlinarith [hs a]
  linarith [hv a]

end HordijkKallenbergLP.SingleLP.Proof
end ModuleScope_Substochastic
-- End Substochastic

-- Begin PoissonVector
section ModuleScope_PoissonVector

open scoped BigOperators

namespace HordijkKallenbergLP.SingleLP.Proof

variable {I : Type*} [Fintype I]

lemma exists_poisson_vector (Q : I → I → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hs : ∀ i, ∑ j, Q i j ≤ 1)
    (hclosed : ∀ C : Set I, C.Nonempty →
      (∀ i ∈ C, (∑ j, Q i j = 1) ∧ ∀ j ∉ C, Q i j = 0) → False) :
    ∃ v : I → ℝ, (∀ i, 0 ≤ v i) ∧ ∀ i, v i - ∑ j, Q i j * v j = 1 := by
  let L : (I → ℝ) →ₗ[ℝ] (I → ℝ) := LinearMap.id - Matrix.mulVecLin Q
  have hker : LinearMap.ker L = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    apply (injective_iff_map_eq_zero L).mpr
    intro w hw
    apply substochastic_fixed_zero Q hQ hs hclosed w
    intro i
    have hh := congrFun hw i
    change w i - ∑ j, Q i j * w j = 0 at hh
    linarith
  have hsurj : Function.Surjective L :=
    LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp hker)
  obtain ⟨v, hv⟩ := hsurj (fun _ => 1)
  have heq (i : I) : v i - ∑ j, Q i j * v j = 1 := congrFun hv i
  exact ⟨v, substochastic_poisson_nonneg Q hQ hs v heq, heq⟩

end HordijkKallenbergLP.SingleLP.Proof
end ModuleScope_PoissonVector
-- End PoissonVector

-- Begin Lyapunov
section ModuleScope_Lyapunov

open scoped BigOperators

namespace HordijkKallenbergLP.SingleLP.Proof

variable {I : Type*} [Fintype I]

lemma exists_lyapunov (P : I → I → ℝ) (E : Set I) [DecidablePred (· ∈ E)]
    (hP : ∀ i j, 0 ≤ P i j) (hs : ∀ i, ∑ j, P i j = 1)
    (hE : ∀ i ∈ E, ∀ j ∉ E, P i j = 0)
    (hclosed : ∀ C : Set I, C.Nonempty → C ⊆ Eᶜ →
      (∀ i ∈ C, ∀ j ∉ C, P i j = 0) → False) :
    ∃ v : I → ℝ, (∀ i, 0 ≤ v i) ∧
      ∀ i, v i - ∑ j, P i j * v j = if i ∈ E then 0 else 1 := by
  classical
  let Q : I → I → ℝ := fun i j => if i ∈ E then 0 else P i j
  have hQ : ∀ i j, 0 ≤ Q i j := by intro i j; dsimp [Q]; split_ifs; positivity; exact hP i j
  have hQs : ∀ i, ∑ j, Q i j ≤ 1 := by
    intro i
    by_cases hi : i ∈ E <;> simp [Q, hi, hs]
  have hQc : ∀ C : Set I, C.Nonempty →
      (∀ i ∈ C, (∑ j, Q i j = 1) ∧ ∀ j ∉ C, Q i j = 0) → False := by
    intro C hC hc
    have hCE : C ⊆ Eᶜ := by
      intro i hi
      change i ∉ E
      intro hie
      have hh := (hc i hi).1
      simp [Q, hie] at hh
    apply hclosed C hC hCE
    intro i hi j hj
    have hn : i ∉ E := hCE hi
    simpa [Q, hn] using (hc i hi).2 j hj
  obtain ⟨v, hv, heq⟩ := exists_poisson_vector Q hQ hQs hQc
  have hone (i : I) : 1 ≤ v i := by
    have hh := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => mul_nonneg (hQ i j) (hv j)
    linarith [heq i]
  have hvE (i : I) (hi : i ∈ E) : v i = 1 := by simpa [Q, hi] using heq i
  refine ⟨fun i => v i - 1, fun i => sub_nonneg.mpr (hone i), ?_⟩
  intro i
  change v i - 1 - ∑ j, P i j * (v j - 1) = _
  by_cases hi : i ∈ E
  · rw [if_pos hi, hvE i hi, sub_self]
    have hz : ∑ j, P i j * (v j - 1) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j ∈ E
      · rw [hvE j hj, sub_self, mul_zero]
      · rw [hE i hi j hj, zero_mul]
    rw [hz, sub_zero]
  · have hh : v i - ∑ j, P i j * v j = 1 := by simpa [Q, hi] using heq i
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [hs i, if_neg hi]
    linarith

end HordijkKallenbergLP.SingleLP.Proof
end ModuleScope_Lyapunov
-- End Lyapunov

-- Begin RewardBounds
section ModuleScope_RewardBounds

open scoped BigOperators
open MarkovDecisionProcesses

namespace HordijkKallenbergLP.SingleLP.Proof

variable {S A : Type*} [Fintype S] [Fintype A] {M : StationaryMDP S A}

lemma reward_upper (R : AvgHRPolicy M) (φ u : S → ℝ) (b : ℝ)
    (hb : ∀ i, b ≤ u i)
    (hφ : ∀ i a, a ∈ M.admissible i → ∑ j, M.trans i a j * φ j ≤ φ i)
    (hu : ∀ i a, a ∈ M.admissible i →
      M.reward i a + ∑ j, M.trans i a j * u j ≤ φ i + u i) :
    ∀ (N : ℕ) t h i, totalReward R N t h i ≤ (N : ℝ) * φ i + u i - b := by
  intro N
  induction N with
  | zero => intro t h i; simpa [totalReward] using sub_nonneg.mpr (hb i)
  | succ N ih =>
    intro t h i
    rw [totalReward]
    have hterm (a : A) (ha : a ∈ M.admissible i) :
        M.reward i a + ∑ j, M.trans i a j * totalReward R N (t+1) (h ++ [(i,a)]) j ≤
        ((N+1 : ℕ) : ℝ) * φ i + u i - b := by
      have hcont := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
        mul_le_mul_of_nonneg_left (ih (t+1) (h ++ [(i,a)]) j) (M.trans_nonneg i a j)
      have hid : (∑ j, M.trans i a j * ((N : ℝ) * φ j + u j - b)) =
          (N : ℝ) * (∑ j, M.trans i a j * φ j) + (∑ j, M.trans i a j * u j) - b := by
        simp_rw [mul_sub, mul_add, ← mul_assoc, mul_comm _ (N : ℝ), mul_assoc,
          Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        rw [M.trans_sum, one_mul]
      rw [hid] at hcont
      have hn := mul_le_mul_of_nonneg_left (hφ i a ha) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      push_cast
      linarith [hu i a ha]
    calc
      _ ≤ ∑ a ∈ M.admissible i, R.q t h i a * (((N+1 : ℕ) : ℝ) * φ i + u i - b) :=
        Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hterm a ha) (R.nonneg t h i a)
      _ = _ := by rw [← Finset.sum_mul, R.sum_one, one_mul]

lemma reward_lower (R : AvgHRPolicy M) (φ u : S → ℝ) (b : ℝ)
    (hb : ∀ i, u i ≤ b)
    (hφ : ∀ t h i a, a ∈ M.admissible i → 0 < R.q t h i a → φ i ≤ ∑ j, M.trans i a j * φ j)
    (hu : ∀ t h i a, a ∈ M.admissible i → 0 < R.q t h i a →
      φ i + u i ≤ M.reward i a + ∑ j, M.trans i a j * u j) :
    ∀ (N : ℕ) t h i, (N : ℝ) * φ i + u i - b ≤ totalReward R N t h i := by
  intro N
  induction N with
  | zero => intro t h i; simpa [totalReward] using sub_nonpos.mpr (hb i)
  | succ N ih =>
    intro t h i
    rw [totalReward]
    have hterm (a : A) (ha : a ∈ M.admissible i) (hq : 0 < R.q t h i a) :
        ((N+1 : ℕ) : ℝ) * φ i + u i - b ≤
        M.reward i a + ∑ j, M.trans i a j * totalReward R N (t+1) (h ++ [(i,a)]) j := by
      have hcont := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
        mul_le_mul_of_nonneg_left (ih (t+1) (h ++ [(i,a)]) j) (M.trans_nonneg i a j)
      have hid : (∑ j, M.trans i a j * ((N : ℝ) * φ j + u j - b)) =
          (N : ℝ) * (∑ j, M.trans i a j * φ j) + (∑ j, M.trans i a j * u j) - b := by
        simp_rw [mul_sub, mul_add, ← mul_assoc, mul_comm _ (N : ℝ), mul_assoc,
          Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        rw [M.trans_sum, one_mul]
      rw [hid] at hcont
      have hn := mul_le_mul_of_nonneg_left (hφ t h i a ha hq) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      push_cast
      linarith [hu t h i a ha hq]
    calc
      _ = ∑ a ∈ M.admissible i, R.q t h i a * (((N+1 : ℕ) : ℝ) * φ i + u i - b) := by
        rw [← Finset.sum_mul, R.sum_one, one_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro a ha
        by_cases hq : 0 < R.q t h i a
        · exact mul_le_mul_of_nonneg_left (hterm a ha hq) hq.le
        · have hz : R.q t h i a = 0 := le_antisymm (le_of_not_gt hq) (R.nonneg t h i a)
          rw [hz, zero_mul, zero_mul]

end HordijkKallenbergLP.SingleLP.Proof
end ModuleScope_RewardBounds
-- End RewardBounds

-- Begin RewardLimit
section ModuleScope_RewardLimit

open scoped BigOperators
open MarkovDecisionProcesses Filter Topology

namespace HordijkKallenbergLP.SingleLP.Proof

variable {S A : Type*} [Fintype S] [Fintype A] {M : StationaryMDP S A}

lemma reward_averages_bounded_below (R : AvgHRPolicy M) (i : S) :
    atTop.IsBoundedUnder (· ≥ ·) (fun N : ℕ => totalReward R N 0 [] i / N) := by
  classical
  let B : ℝ := ∑ i, ∑ a, |M.reward i a|
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => abs_nonneg _
  have hB (i : S) (a : A) : |M.reward i a| ≤ B :=
    (Finset.single_le_sum (fun b (_ : b ∈ Finset.univ) => abs_nonneg (M.reward i b))
      (Finset.mem_univ a)).trans
      (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
        Finset.sum_nonneg fun b _ => abs_nonneg (M.reward j b)) (Finset.mem_univ i))
  have hl := reward_lower R (fun _ => -B) (fun _ => 0) 0 (fun _ => le_rfl)
    (fun _ _ i a _ _ => by simp [← Finset.sum_mul, M.trans_sum])
    (fun _ _ i a _ _ => by simpa using (neg_le_of_abs_le (hB i a)))
  apply Filter.isBoundedUnder_of
  refine ⟨-B, ?_⟩
  intro N
  by_cases hn : N = 0
  · simp [hn, hB0]
  · have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    apply (le_div_iff₀ hNp).mpr
    simpa only [zero_add, add_zero, sub_zero, mul_comm] using hl N 0 [] i

lemma affine_average_tendsto (a b : ℝ) :
    Tendsto (fun N : ℕ => ((N : ℝ) * a + b) / N) atTop (nhds a) := by
  have hh : Tendsto (fun N : ℕ => a + b / N) atTop (nhds (a + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  have hh' : Tendsto (fun N : ℕ => a + b / N) atTop (nhds a) := by
    simpa only [add_zero] using hh
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  field_simp

lemma gainInf_le_of_reward_upper (R : AvgHRPolicy M) (i : S) (a b : ℝ)
    (h : ∀ N : ℕ, totalReward R N 0 [] i ≤ (N : ℝ) * a + b) : gainInf R i ≤ a := by
  apply Filter.liminf_le_of_le (reward_averages_bounded_below R i)
  intro c hc
  apply ge_of_tendsto (affine_average_tendsto a b)
  filter_upwards [hc] with N hN
  exact hN.trans (div_le_div_of_nonneg_right (h N) (Nat.cast_nonneg N))

lemma average_tendsto_of_reward_bounds (R : AvgHRPolicy M) (i : S) (a b d : ℝ)
    (hl : ∀ N : ℕ, (N : ℝ) * a + b ≤ totalReward R N 0 [] i)
    (hu : ∀ N : ℕ, totalReward R N 0 [] i ≤ (N : ℝ) * a + d) :
    Tendsto (fun N : ℕ => totalReward R N 0 [] i / N) atTop (nhds a) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (affine_average_tendsto a b) (affine_average_tendsto a d)
    (fun N => div_le_div_of_nonneg_right (hl N) (Nat.cast_nonneg N))
    (fun N => div_le_div_of_nonneg_right (hu N) (Nat.cast_nonneg N))

end HordijkKallenbergLP.SingleLP.Proof
end ModuleScope_RewardLimit
-- End RewardLimit

-- Begin NativeOptimality
section ModuleScope_NativeOptimality

open scoped BigOperators
open MarkovDecisionProcesses Filter Topology

namespace HordijkKallenbergLP.SingleLP.Proof

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]

lemma finite_abs_bound (u : S → ℝ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ i, |u i| ≤ B := by
  classical
  exact ⟨∑ i, |u i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun i =>
    Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => abs_nonneg (u j)) (Finset.mem_univ i)⟩

lemma optimal_of_structure (M : StationaryMDP S A) (f : S → A)
    (hf : ∀ i, f i ∈ M.admissible i) (E : Set S) (φ u : S → ℝ)
    (hsh : Superharmonic M φ u)
    (harm : ∀ i, ∑ j, M.trans i (f i) j * φ j = φ i)
    (heq : ∀ i ∈ E, M.reward i (f i) = φ i + u i - ∑ j, M.trans i (f i) j * u j)
    (hE : ∀ i ∈ E, ∀ j ∉ E, M.trans i (f i) j = 0)
    (hclosed : ∀ C : Set S, C.Nonempty → C ⊆ Eᶜ →
      (∀ i ∈ C, ∀ j ∉ C, M.trans i (f i) j = 0) → False) :
    IsAvgOptimal M (stationaryPolicy M f hf) := by
  classical
  let R := stationaryPolicy M f hf
  let P : S → S → ℝ := fun i j => M.trans i (f i) j
  obtain ⟨v, _, hv⟩ := exists_lyapunov P E
    (fun i j => M.trans_nonneg i (f i) j) (fun i => M.trans_sum i (f i)) hE hclosed
  let slack : S → ℝ := fun i => φ i + u i - (∑ j, P i j * u j) - M.reward i (f i)
  obtain ⟨B, _, hB⟩ := finite_abs_bound slack
  let w : S → ℝ := fun i => u i - B * v i
  have hlow (i : S) : φ i + w i ≤ M.reward i (f i) + ∑ j, P i j * w j := by
    have hid : φ i + w i - (∑ j, P i j * w j) - M.reward i (f i) =
        slack i - B * (v i - ∑ j, P i j * v j) := by
      dsimp [w, slack]
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      have hsB : (∑ j, P i j * (B * v j)) = B * ∑ j, P i j * v j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hsB]
      ring
    rw [hv i] at hid
    by_cases hi : i ∈ E
    · have hz : slack i = 0 := by dsimp [slack, P]; rw [heq i hi]; ring
      rw [if_pos hi, hz, mul_zero, sub_zero] at hid
      linarith
    · have hh := (le_abs_self (slack i)).trans (hB i)
      rw [if_neg hi, mul_one] at hid
      linarith
  obtain ⟨U, _, hU⟩ := finite_abs_bound u
  obtain ⟨W, _, hW⟩ := finite_abs_bound w
  have hupper (R' : AvgHRPolicy M) := reward_upper R' φ u (-U)
    (fun i => neg_le_of_abs_le (hU i))
    (fun i a ha => (hsh i a ha).1) (fun i a ha => (hsh i a ha).2)
  have hsupport (t : ℕ) (h : List (S × A)) (i : S) (a : A)
      (hq : 0 < R.q t h i a) : a = f i := by
    by_contra hn
    simp [R, stationaryPolicy, hn] at hq
  have hlower := reward_lower R φ w W (fun i => le_of_abs_le (hW i))
    (fun t h i a _ hq => by rw [hsupport t h i a hq]; exact (harm i).ge)
    (fun t h i a _ hq => by rw [hsupport t h i a hq]; exact hlow i)
  have hgain (R' : AvgHRPolicy M) (i : S) : gainInf R' i ≤ φ i := by
    apply gainInf_le_of_reward_upper R' i (φ i) (u i + U)
    intro N
    have hh := hupper R' N 0 [] i
    linarith
  have hselected (i : S) : gainInf R i = φ i := by
    have ht := average_tendsto_of_reward_bounds R i (φ i) (w i - W) (u i + U)
      (fun N => by have hh := hlower N 0 [] i; linarith)
      (fun N => by have hh := hupper R N 0 [] i; linarith)
    exact ht.liminf_eq
  intro i
  change gainInf R i = ⨆ R' : AvgHRPolicy M, gainInf R' i
  let : Nonempty (AvgHRPolicy M) := ⟨R⟩
  have hb : BddAbove (Set.range (fun R' : AvgHRPolicy M => gainInf R' i)) :=
    ⟨φ i, fun _ ⟨R', hr⟩ => hr ▸ hgain R' i⟩
  apply le_antisymm (le_ciSup hb R)
  rw [hselected]
  exact ciSup_le (fun R' => hgain R' i)

end HordijkKallenbergLP.SingleLP.Proof
end ModuleScope_NativeOptimality
-- End NativeOptimality

end ThmSevenPart

section LimitPart
open Filter Topology Matrix
namespace BlackwellDiscreteDP.NearOne
section MarkovTheory
variable {n : Type*} [Fintype n] [DecidableEq n]

instance bmk_fc : FirstCountableTopology (Matrix n n ℝ) :=
  inferInstanceAs (FirstCountableTopology (n → n → ℝ))

lemma bmk_mul {A B : Matrix n n ℝ} (hA : IsMarkovMatrix A) (hB : IsMarkovMatrix B) :
    IsMarkovMatrix (A * B) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hA.1 i k) (hB.1 k j)
  · simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hB.2, mul_one]
    exact hA.2 i

lemma bmk_one : IsMarkovMatrix (1 : Matrix n n ℝ) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · rw [Matrix.one_apply]; split_ifs <;> norm_num
  · simp [Matrix.one_apply]

lemma bmk_pow {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (k : ℕ) : IsMarkovMatrix (P ^ k) := by
  induction k with
  | zero => simpa using (bmk_one (n := n))
  | succ k ih => rw [pow_succ]; exact bmk_mul ih hP

lemma bmk_le_one {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (i j : n) : P i j ≤ 1 := by
  rw [← hP.2 i]
  exact Finset.single_le_sum (f := fun j => P i j) (fun j _ => hP.1 i j) (Finset.mem_univ j)

lemma bmk_cesaro {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (N : ℕ) :
    IsMarkovMatrix (cesaroMean P N) := by
  unfold cesaroMean
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => (bmk_pow hP k).1 i j)
  · simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [(bmk_pow hP _).2 i]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    field_simp

lemma bmk_P_mul_sum (P : Matrix n n ℝ) (N : ℕ) :
    P * ∑ k ∈ Finset.range (N + 1), P ^ k = ∑ k ∈ Finset.range (N + 1), P ^ k + (P ^ (N + 1) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, ← pow_succ']
    abel

lemma bmk_sum_mul_P (P : Matrix n n ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), P ^ k) * P = ∑ k ∈ Finset.range (N + 1), P ^ k + (P ^ (N + 1) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, add_mul, ih, ← pow_succ]
    abel

lemma bmk_P_cesaro (P : Matrix n n ℝ) (N : ℕ) :
    P * cesaroMean P N - cesaroMean P N = ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1) := by
  unfold cesaroMean
  rw [Matrix.mul_smul, bmk_P_mul_sum, smul_add]
  abel

lemma bmk_cesaro_P (P : Matrix n n ℝ) (N : ℕ) :
    cesaroMean P N * P - cesaroMean P N = ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1) := by
  unfold cesaroMean
  rw [Matrix.smul_mul, bmk_sum_mul_P, smul_add]
  abel

lemma bmk_D_tendsto {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hb : ∀ N : ℕ, ‖(((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) i j‖ ≤ 1 / ((N : ℝ) + 1) := by
    intro N
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Real.norm_eq_abs]
    have h1 := (bmk_pow hP (N + 1)).1 i j
    have h2 := bmk_le_one (bmk_pow hP (N + 1)) i j
    have h3 : (0 : ℝ) ≤ (1 : Matrix n n ℝ) i j := bmk_one.1 i j
    have h4 : (1 : Matrix n n ℝ) i j ≤ 1 := bmk_le_one bmk_one i j
    rw [abs_mul, abs_of_pos (by positivity), one_div]
    have : |(P ^ (N + 1)) i j - (1 : Matrix n n ℝ) i j| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    calc ((N : ℝ) + 1)⁻¹ * |(P ^ (N + 1)) i j - (1 : Matrix n n ℝ) i j| ≤ ((N : ℝ) + 1)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_one _
  exact squeeze_zero_norm hb tendsto_one_div_add_atTop_nhds_zero_nat

lemma bmk_clus {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {L : Matrix n n ℝ}
    (hL : Tendsto (fun j => cesaroMean P (ns j)) atTop (𝓝 L)) : P * L = L ∧ L * P = L := by
  have hD := (bmk_D_tendsto hP).comp hns
  constructor
  · have h1 : Tendsto (fun j => P * cesaroMean P (ns j) - cesaroMean P (ns j)) atTop
        (𝓝 (P * L - L)) := (hL.const_mul P).sub hL
    have h2 : (fun j => P * cesaroMean P (ns j) - cesaroMean P (ns j)) =
        (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) ∘ ns := by
      funext j; exact bmk_P_cesaro P (ns j)
    rw [h2] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 hD)
  · have h1 : Tendsto (fun j => cesaroMean P (ns j) * P - cesaroMean P (ns j)) atTop
        (𝓝 (L * P - L)) := (hL.mul_const P).sub hL
    have h2 : (fun j => cesaroMean P (ns j) * P - cesaroMean P (ns j)) =
        (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) ∘ ns := by
      funext j; exact bmk_cesaro_P P (ns j)
    rw [h2] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 hD)

lemma bmk_avg_const (L : Matrix n n ℝ) (N : ℕ) :
    ((N : ℝ) + 1)⁻¹ • ∑ k ∈ Finset.range (N + 1), L = L := by
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (by positivity), one_smul]

lemma bmk_cesaro_mul_fix {P L : Matrix n n ℝ} (h : P * L = L) (N : ℕ) :
    cesaroMean P N * L = L := by
  have hk : ∀ k : ℕ, P ^ k * L = L := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Matrix.mul_assoc, ih, h]
  unfold cesaroMean
  rw [Matrix.smul_mul, Finset.sum_mul]
  simp_rw [hk]
  exact bmk_avg_const L N

lemma bmk_fix_mul_cesaro {P L : Matrix n n ℝ} (h : L * P = L) (N : ℕ) :
    L * cesaroMean P N = L := by
  have hk : ∀ k : ℕ, L * P ^ k = L := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mul_assoc, ih, h]
  unfold cesaroMean
  rw [Matrix.mul_smul, Finset.mul_sum]
  simp_rw [hk]
  exact bmk_avg_const L N

lemma bmk_compact : IsCompact {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} := by
  have e : {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} =
      Set.pi Set.univ (fun (_ : n) => Set.pi Set.univ (fun (_ : n) => Set.Icc (0 : ℝ) 1)) := by
    ext M; exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [e]
  exact isCompact_univ_pi (fun (_ : n) => isCompact_univ_pi (fun (_ : n) => isCompact_Icc))

theorem bmk_tendsto {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    Tendsto (cesaroMean P) atTop (𝓝 (limitMatrix P)) := by
  have hmem : ∀ N, cesaroMean P N ∈ {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} :=
    fun N i j => ⟨(bmk_cesaro hP N).1 i j, bmk_le_one (bmk_cesaro hP N) i j⟩
  obtain ⟨L, -, φ, hφ, hL⟩ := bmk_compact.tendsto_subseq hmem
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  obtain ⟨hPL, hLP⟩ := bmk_clus hP hφt hL
  have main : Tendsto (cesaroMean P) atTop (𝓝 L) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨L', -, ψ, hψ, hL'⟩ := bmk_compact.tendsto_subseq (fun j => hmem (ns j))
    refine ⟨ψ, ?_⟩
    have hnsψ : Tendsto (ns ∘ ψ) atTop atTop := hns.comp hψ.tendsto_atTop
    obtain ⟨hPL', hL'P⟩ := bmk_clus hP hnsψ hL'
    have e1 : L * L' = L' := by
      have t : Tendsto (fun j => cesaroMean P (φ j) * L') atTop (𝓝 (L * L')) := hL.mul_const L'
      simp_rw [bmk_cesaro_mul_fix hPL'] at t
      exact (tendsto_nhds_unique tendsto_const_nhds t).symm
    have e2 : L * L' = L := by
      have t : Tendsto (fun j => L * cesaroMean P ((ns ∘ ψ) j)) atTop (𝓝 (L * L')) :=
        hL'.const_mul L
      simp_rw [bmk_fix_mul_cesaro hLP] at t
      exact (tendsto_nhds_unique tendsto_const_nhds t).symm
    have : L' = L := e1.symm.trans e2
    rw [this] at hL'
    exact hL'
  rw [limitMatrix, main.limUnder_eq]
  exact main

variable {P : Matrix n n ℝ}

lemma bmk_PL (hP : IsMarkovMatrix P) : P * limitMatrix P = limitMatrix P :=
  (bmk_clus hP tendsto_id (bmk_tendsto hP)).1

lemma bmk_LP (hP : IsMarkovMatrix P) : limitMatrix P * P = limitMatrix P :=
  (bmk_clus hP tendsto_id (bmk_tendsto hP)).2

lemma bmk_LL (hP : IsMarkovMatrix P) : limitMatrix P * limitMatrix P = limitMatrix P := by
  have t : Tendsto (fun N => cesaroMean P N * limitMatrix P) atTop
      (𝓝 (limitMatrix P * limitMatrix P)) := (bmk_tendsto hP).mul_const _
  simp_rw [bmk_cesaro_mul_fix (bmk_PL hP)] at t
  exact (tendsto_nhds_unique tendsto_const_nhds t).symm

lemma bmk_fixvec (hP : IsMarkovMatrix P) {v : n → ℝ} (hv : P *ᵥ v = v) :
    limitMatrix P *ᵥ v = v := by
  have hk : ∀ k : ℕ, (P ^ k) *ᵥ v = v := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]
  have hA : ∀ N, cesaroMean P N *ᵥ v = v := by
    intro N
    rw [cesaroMean, Matrix.smul_mulVec, Matrix.sum_mulVec]
    simp_rw [hk]
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ (by positivity), one_smul]
  have t : Tendsto (fun N => cesaroMean P N *ᵥ v) atTop (𝓝 (limitMatrix P *ᵥ v)) :=
    ((continuous_id.matrix_mulVec continuous_const).tendsto _).comp (bmk_tendsto hP)
  simp_rw [hA] at t
  exact (tendsto_nhds_unique tendsto_const_nhds t).symm

lemma bmk_L_markov (hP : IsMarkovMatrix P) : IsMarkovMatrix (limitMatrix P) := by
  have hc : IsClosed {M : Matrix n n ℝ | IsMarkovMatrix M} := by
    have : {M : Matrix n n ℝ | IsMarkovMatrix M} =
        (⋂ i, ⋂ j, {M : Matrix n n ℝ | 0 ≤ M i j}) ∩ ⋂ i, {M : Matrix n n ℝ | ∑ j, M i j = 1} := by
      ext M; simp [IsMarkovMatrix]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
      (isClosed_iInter fun i => ?_)
    · exact isClosed_le continuous_const ((continuous_apply j).comp (continuous_apply i))
    · exact isClosed_eq (continuous_finsetSum _ fun j _ =>
        (continuous_apply j).comp (continuous_apply i)) continuous_const
  exact hc.mem_of_tendsto (bmk_tendsto hP) (Eventually.of_forall fun N => bmk_cesaro hP N)

lemma bmk_ZL_inj (hP : IsMarkovMatrix P) :
    Function.Injective (1 - P + limitMatrix P).mulVec := by
  set L := limitMatrix P
  have hLA : L * (1 - P + L) = L := by
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP]; abel
  intro v w hvw
  set d := v - w
  have hd : (1 - P + L) *ᵥ d = 0 := by
    simp only [d, Matrix.mulVec_sub, hvw, sub_self]
  have hLd : L *ᵥ d = 0 := by
    have := congrArg (fun z => L *ᵥ z) hd
    simp only [Matrix.mulVec_mulVec, hLA, Matrix.mulVec_zero] at this
    exact this
  have hPd : P *ᵥ d = d := by
    have := hd
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, hLd, Matrix.one_mulVec, add_zero, sub_eq_zero] at this
    exact this.symm
  have : d = 0 := by rw [← bmk_fixvec hP hPd, hLd]
  exact sub_eq_zero.1 this

lemma bmk_Z_unit (hP : IsMarkovMatrix P) : IsUnit (1 - P + limitMatrix P).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_injective_iff_isUnit.1 (bmk_ZL_inj hP))

lemma bmk_PH (hP : IsMarkovMatrix P) :
    P * deviationMatrix P = deviationMatrix P + limitMatrix P - 1 := by
  set L := limitMatrix P
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + L) * (1 - P + L)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hLZ : L * (1 - P + L)⁻¹ = L := by
    have hLA : L * (1 - P + L) = L := by
      rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP]; abel
    calc L * (1 - P + L)⁻¹ = (L * (1 - P + L)) * (1 - P + L)⁻¹ := by rw [hLA]
      _ = L * ((1 - P + L) * (1 - P + L)⁻¹) := Matrix.mul_assoc _ _ _
      _ = L := by rw [h1, Matrix.mul_one]
  have h2 : (1 - P + L) * (1 - P + L)⁻¹ = (1 - P + L)⁻¹ - P * (1 - P + L)⁻¹ + L * (1 - P + L)⁻¹ := by
    rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul]
  rw [h1, hLZ] at h2
  unfold deviationMatrix
  rw [Matrix.mul_sub, bmk_PL hP]
  change P * (1 - P + L)⁻¹ - L = (1 - P + L)⁻¹ - L + L - 1
  generalize (1 - P + L)⁻¹ = Z at h2 ⊢
  have : P * Z = Z + L - 1 := by rw [h2]; abel
  rw [this]; abel

lemma bmk_LH (hP : IsMarkovMatrix P) : limitMatrix P * deviationMatrix P = 0 := by
  set L := limitMatrix P
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + L) * (1 - P + L)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hLA : L * (1 - P + L) = L := by
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP]; abel
  have hLZ : L * (1 - P + L)⁻¹ = L := by
    calc L * (1 - P + L)⁻¹ = (L * (1 - P + L)) * (1 - P + L)⁻¹ := by rw [hLA]
      _ = L * ((1 - P + L) * (1 - P + L)⁻¹) := Matrix.mul_assoc _ _ _
      _ = L := by rw [h1, Matrix.mul_one]
  unfold deviationMatrix
  rw [Matrix.mul_sub, hLZ, bmk_LL hP, sub_self]

/-- maximum principle: if `w = c + β P w` and `c ≤ K` then `w ≤ K/(1-β)` -/
lemma bmk_upper (hP : IsMarkovMatrix P) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {w c : n → ℝ}
    (hw : ∀ s, w s = c s + β * (P *ᵥ w) s) {K : ℝ} (hc : ∀ s, c s ≤ K) [Nonempty n] (s : n) :
    w s ≤ K / (1 - β) := by
  obtain ⟨s0, hs0⟩ := Finite.exists_max w
  have hPw : (P *ᵥ w) s0 ≤ w s0 := by
    show ∑ j, P s0 j * w j ≤ w s0
    calc ∑ j, P s0 j * w j ≤ ∑ j, P s0 j * w s0 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hs0 j) (hP.1 s0 j)
      _ = w s0 := by rw [← Finset.sum_mul, hP.2 s0, one_mul]
  have h1 := hw s0
  have h2 : (1 - β) * w s0 ≤ K := by nlinarith [hc s0]
  rw [le_div_iff₀ (by linarith)]
  nlinarith [hs0 s]

lemma bmk_lower (hP : IsMarkovMatrix P) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {w c : n → ℝ}
    (hw : ∀ s, w s = c s + β * (P *ᵥ w) s) {K : ℝ} (hc : ∀ s, K ≤ c s) [Nonempty n] (s : n) :
    K / (1 - β) ≤ w s := by
  have := bmk_upper hP hβ0 hβ1 (w := -w) (c := -c) (K := -K)
    (fun s => by simp only [Pi.neg_apply, Matrix.mulVec_neg]; rw [hw s]; ring)
    (fun s => by simp only [Pi.neg_apply]; linarith [hc s]) s
  simp only [Pi.neg_apply, neg_div] at this
  linarith

lemma bmk_abs (hP : IsMarkovMatrix P) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {w c : n → ℝ}
    (hw : ∀ s, w s = c s + β * (P *ᵥ w) s) {K : ℝ} (hc : ∀ s, |c s| ≤ K) [Nonempty n] (s : n) :
    |w s| ≤ K / (1 - β) := by
  rw [abs_le]
  constructor
  · have := bmk_lower hP hβ0 hβ1 hw (K := -K) (fun s => (abs_le.1 (hc s)).1) s
    rw [neg_div] at this; exact this
  · exact bmk_upper hP hβ0 hβ1 hw (fun s => (abs_le.1 (hc s)).2) s

end MarkovTheory
end BlackwellDiscreteDP.NearOne
end LimitPart

-- ===== HK8B =====

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology
open HordijkKallenbergLP.SingleLP (Pair Superharmonic)

namespace HordijkKallenbergLP.Correspondence.HK8

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-! ### Sums over admissible pairs -/

def pairEquiv (M : StationaryMDP S A) : Pair M ≃ Σ i : S, {a // a ∈ M.admissible i} where
  toFun p := ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  invFun q := ⟨(q.1, q.2.1), q.2.2⟩
  left_inv p := rfl
  right_inv q := rfl

lemma pair_sum (M : StationaryMDP S A) (g : S → A → ℝ) :
    ∑ p : Pair M, g p.1.1 p.1.2 = ∑ i, ∑ a ∈ M.admissible i, g i a := by
  rw [Fintype.sum_equiv (pairEquiv M) (fun p : Pair M => g p.1.1 p.1.2) (fun q => g q.1 q.2.1) (fun p => rfl)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_coe_sort (M.admissible i) (g i)

/-- extension of a pair-indexed vector by zero -/
noncomputable def ext (M : StationaryMDP S A) (f : Pair M → ℝ) (i : S) (a : A) : ℝ :=
  if h : a ∈ M.admissible i then f ⟨(i, a), h⟩ else 0

lemma ext_pair (M : StationaryMDP S A) (f : Pair M → ℝ) (p : Pair M) :
    ext M f p.1.1 p.1.2 = f p := by
  simp [ext, p.2]

lemma pair_sum' (M : StationaryMDP S A) (f : Pair M → ℝ) :
    ∑ p : Pair M, f p = ∑ i, ∑ a ∈ M.admissible i, ext M f i a := by
  rw [← pair_sum M (ext M f)]
  exact Finset.sum_congr rfl fun p _ => (ext_pair M f p).symm

lemma stateMass_eq (M : StationaryMDP S A) (x : Pair M → ℝ) (i : S) :
    stateMass M x i = ∑ a ∈ M.admissible i, ext M x i a := by
  unfold stateMass
  rw [pair_sum' M]
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro a ha
    simp [ext, ha]
  · intro j _ hj
    apply Finset.sum_eq_zero
    intro a ha
    simp [ext, ha, hj]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma stateMass_nonneg (M : StationaryMDP S A) (x : Pair M → ℝ) (hx : ∀ p, 0 ≤ x p) (i : S) :
    0 ≤ stateMass M x i := by
  unfold stateMass
  exact Finset.sum_nonneg fun p _ => by split_ifs <;> simp [hx p]

lemma sum_mul_stateMass (M : StationaryMDP S A) (v : S → ℝ) (x : Pair M → ℝ) :
    ∑ j, v j * stateMass M x j = ∑ p, x p * v p.1.1 := by
  unfold stateMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_eq_single p.1.1]
  · simp [mul_comm]
  · intro j _ hj
    have : p.1.1 ≠ j := fun h => hj h.symm
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma sum_mul_trans (M : StationaryMDP S A) (v : S → ℝ) (z : Pair M → ℝ) :
    ∑ j, v j * ∑ p, M.trans p.1.1 p.1.2 j * z p = ∑ p, z p * ∑ j, M.trans p.1.1 p.1.2 j * v j := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => by ring

/-! ### Weak duality -/

theorem weak_duality (M : StationaryMDP S A) (β : S → ℝ) (x y : Pair M → ℝ)
    (hxy : DualFeasible M β x y) (φ u : S → ℝ) (hsh : Superharmonic M φ u) :
    dualObjective M x ≤ ∑ i, β i * φ i := by
  obtain ⟨hnn, h3, h4⟩ := hxy
  have e1 : ∑ p, x p * u p.1.1 = ∑ j, u j * stateMass M x j := (sum_mul_stateMass M u x).symm
  have e2 : ∑ p, x p * ∑ j, M.trans p.1.1 p.1.2 j * u j = ∑ j, u j * stateMass M x j := by
    rw [← sum_mul_trans]
    simp_rw [h3]
  have e3 : ∑ p, x p * φ p.1.1 = ∑ j, φ j * stateMass M x j := (sum_mul_stateMass M φ x).symm
  have e4 : ∑ j, φ j * stateMass M x j = ∑ j, β j * φ j +
      ∑ p, y p * (∑ j, M.trans p.1.1 p.1.2 j * φ j) - ∑ p, y p * φ p.1.1 := by
    rw [← sum_mul_trans, ← sum_mul_stateMass]
    have : ∀ j, stateMass M x j = β j + ∑ p, M.trans p.1.1 p.1.2 j * y p - stateMass M y j :=
      fun j => by linarith [h4 j]
    simp_rw [this, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp_rw [mul_comm (φ _) (β _)]
  have hr : ∀ p : Pair M, M.reward p.1.1 p.1.2 * x p ≤
      x p * φ p.1.1 + x p * u p.1.1 - x p * ∑ j, M.trans p.1.1 p.1.2 j * u j := by
    intro p
    have h := (hsh p.1.1 p.1.2 p.2).2
    have := mul_le_mul_of_nonneg_left h (hnn p).1
    nlinarith
  have hy : ∀ p : Pair M, y p * (∑ j, M.trans p.1.1 p.1.2 j * φ j) ≤ y p * φ p.1.1 :=
    fun p => mul_le_mul_of_nonneg_left (hsh p.1.1 p.1.2 p.2).1 (hnn p).2
  have hs1 := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => hr p)
  have hs2 := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => hy p)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hs1
  unfold dualObjective
  linarith

/-! ### Conversion to the single-LP formulation -/

lemma feasible_conv (M : StationaryMDP S A) (β : S → ℝ) (x y : Pair M → ℝ) :
    (x, y) ∈ HordijkKallenbergLP.SingleLP.dualFeasible M β ↔ DualFeasible M β x y := by
  have e1 : ∀ (z : Pair M → ℝ) (j : S), ∑ p : Pair M,
      ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * z p =
      stateMass M z j - ∑ p, M.trans p.1.1 p.1.2 j * z p := by
    intro z j
    simp [stateMass, sub_mul, Finset.sum_sub_distrib, ite_mul]
  have e2 : ∀ (z : Pair M → ℝ) (j : S),
      HordijkKallenbergLP.SingleLP.stateSum M z j = stateMass M z j := by
    intro z j
    unfold HordijkKallenbergLP.SingleLP.stateSum stateMass
    rw [Finset.sum_filter]
  constructor
  · rintro ⟨h3, h4, h5⟩
    refine ⟨h5, fun j => ?_, fun j => ?_⟩
    · have h := h3 j
      have : ∑ p : Pair M,
          ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * x p = 0 := by
        convert h using 2
      rw [e1] at this
      linarith
    · have h := h4 j
      have : stateMass M x j + ∑ p : Pair M,
          ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * y p = β j := by
        rw [← e2]; convert h using 3
      rw [e1] at this
      linarith
  · rintro ⟨h5, h3, h4⟩
    refine ⟨fun j => ?_, fun j => ?_, h5⟩
    · have : ∑ p : Pair M,
          ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * x p = 0 := by
        rw [e1]; linarith [h3 j]
      convert this using 2
    · have : stateMass M x j + ∑ p : Pair M,
          ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * y p = β j := by
        rw [e1]; linarith [h4 j]
      rw [← e2] at this
      convert this using 3

lemma objective_conv (M : StationaryMDP S A) (x : Pair M → ℝ) :
    HordijkKallenbergLP.SingleLP.dualObjective M x = dualObjective M x := by
  unfold HordijkKallenbergLP.SingleLP.dualObjective dualObjective
  congr 1

lemma optimal_conv (M : StationaryMDP S A) (β : S → ℝ) (x y : Pair M → ℝ)
    (h : DualOptimal M β x y) : HordijkKallenbergLP.SingleLP.IsDualOptimal M β (x, y) := by
  refine ⟨(feasible_conv M β x y).2 h.1, fun z hz => ?_⟩
  rw [objective_conv, objective_conv]
  exact h.2 z.1 z.2 ((feasible_conv M β z.1 z.2).1 hz)

end HordijkKallenbergLP.Correspondence.HK8

-- ===== HK8C =====

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology
open HordijkKallenbergLP.SingleLP (Pair Superharmonic)

namespace HordijkKallenbergLP.Correspondence.HK8

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-! ### Stationary randomized policies: values -/

noncomputable def Vst (M : StationaryMDP S A) (π : RandomizedPolicy M) (N : ℕ) : S → ℝ :=
  (∑ k ∈ Finset.range N, (policyMatrix M π) ^ k) *ᵥ policyReward M π

lemma Vst_succ (M : StationaryMDP S A) (π : RandomizedPolicy M) (N : ℕ) (i : S) :
    Vst M π (N + 1) i = policyReward M π i + ∑ j, policyMatrix M π i j * Vst M π N j := by
  unfold Vst
  rw [Finset.sum_range_succ']
  simp_rw [pow_succ']
  rw [← Finset.mul_sum, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, pow_zero, Matrix.one_mulVec]
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
  ring

lemma totalReward_stat (M : StationaryMDP S A) (π : RandomizedPolicy M) :
    ∀ N t h i, totalReward π.toHR N t h i = Vst M π N i := by
  intro N
  induction N with
  | zero => intro t h i; simp [totalReward, Vst]
  | succ N ih =>
    intro t h i
    rw [totalReward, Vst_succ]
    simp only [ih]
    simp only [RandomizedPolicy.toHR]
    unfold policyReward policyMatrix
    simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring

lemma policyMatrix_nonneg (M : StationaryMDP S A) (π : RandomizedPolicy M) (i j : S) :
    0 ≤ policyMatrix M π i j :=
  Finset.sum_nonneg fun a _ => mul_nonneg (π.nonneg i a) (M.trans_nonneg i a j)

lemma policyMatrix_sum (M : StationaryMDP S A) (π : RandomizedPolicy M) (i : S) :
    ∑ j, policyMatrix M π i j = 1 := by
  unfold policyMatrix
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, M.trans_sum, mul_one]
  exact π.sum_one i

lemma Vst_lower (M : StationaryMDP S A) (π : RandomizedPolicy M) (φ w : S → ℝ) (W : ℝ)
    (hW : ∀ i, w i ≤ W)
    (hharm : ∀ i, ∑ j, policyMatrix M π i j * φ j = φ i)
    (hlow : ∀ i, φ i + w i ≤ policyReward M π i + ∑ j, policyMatrix M π i j * w j) :
    ∀ (N : ℕ) i, (N : ℝ) * φ i + w i - W ≤ Vst M π N i := by
  intro N
  induction N with
  | zero => intro i; simp [Vst]; linarith [hW i]
  | succ N ih =>
    intro i
    rw [Vst_succ]
    have hc := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (ih j) (policyMatrix_nonneg M π i j)
    have hid : (∑ j, policyMatrix M π i j * ((N : ℝ) * φ j + w j - W)) =
        (N : ℝ) * (∑ j, policyMatrix M π i j * φ j) + (∑ j, policyMatrix M π i j * w j) - W := by
      simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul, policyMatrix_sum, one_mul, Finset.mul_sum]
      congr 1; congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hid, hharm i] at hc
    push_cast
    linarith [hlow i]

lemma weight_avg (M : StationaryMDP S A) (π : RandomizedPolicy M) (i : S) (f g : A → ℝ)
    (h : ∀ a ∈ M.admissible i, 0 < π.weight i a → f a = g a) :
    ∑ a ∈ M.admissible i, π.weight i a * f a = ∑ a ∈ M.admissible i, π.weight i a * g a := by
  apply Finset.sum_congr rfl
  intro a ha
  rcases (π.nonneg i a).lt_or_eq with hp | hz
  · rw [h a ha hp]
  · rw [← hz, zero_mul, zero_mul]

/-! ### The policy of a feasible dual pair -/

lemma ext_nonneg (M : StationaryMDP S A) (x : Pair M → ℝ) (hx : ∀ p, 0 ≤ x p) (i : S) (a : A) :
    0 ≤ ext M x i a := by
  unfold ext; split_ifs <;> simp [hx]

open Classical in
lemma dpw_eq (M : StationaryMDP S A) (x y : Pair M → ℝ) (i : S) (a : A) :
    dualPolicyWeight M x y i a = if a ∈ M.admissible i then
      (if i ∈ Ex M x then ext M x i a / stateMass M x i else ext M y i a / stateMass M y i)
      else 0 := by
  by_cases ha : a ∈ M.admissible i <;> by_cases hi : i ∈ Ex M x <;>
    simp [dualPolicyWeight, ext, ha, hi]

lemma mass_ge (M : StationaryMDP S A) (β : S → ℝ) (x y : Pair M → ℝ)
    (hxy : DualFeasible M β x y) (j : S) : β j ≤ stateMass M x j + stateMass M y j := by
  rw [hxy.2.2 j]
  have : 0 ≤ ∑ p : Pair M, M.trans p.1.1 p.1.2 j * y p :=
    Finset.sum_nonneg fun p _ => mul_nonneg (M.trans_nonneg _ _ _) (hxy.1 p).2
  linarith

lemma ymass_pos (M : StationaryMDP S A) (β : S → ℝ) (hβ : ∀ i, 0 < β i) (x y : Pair M → ℝ)
    (hxy : DualFeasible M β x y) (i : S) (hi : i ∉ Ex M x) : 0 < stateMass M y i := by
  have h1 := mass_ge M β x y hxy i
  have h2 : stateMass M x i ≤ 0 := not_lt.mp hi
  linarith [hβ i]

noncomputable def dualPolicy (M : StationaryMDP S A) (β : S → ℝ) (hβ : ∀ i, 0 < β i)
    (x y : Pair M → ℝ) (hxy : DualFeasible M β x y) : RandomizedPolicy M where
  weight := dualPolicyWeight M x y
  nonneg := by
    intro i a
    rw [dpw_eq]
    split_ifs with ha hi
    · exact div_nonneg (ext_nonneg M x (fun p => (hxy.1 p).1) i a) (le_of_lt hi)
    · exact div_nonneg (ext_nonneg M y (fun p => (hxy.1 p).2) i a)
        (stateMass_nonneg M y (fun p => (hxy.1 p).2) i)
    · exact le_rfl
  supported := by
    intro i a ha
    rw [dpw_eq, if_neg ha]
  sum_one := by
    classical
    intro i
    have e : ∀ a ∈ M.admissible i, dualPolicyWeight M x y i a =
        (if i ∈ Ex M x then ext M x i a / stateMass M x i else ext M y i a / stateMass M y i) := by
      intro a ha; rw [dpw_eq, if_pos ha]
    rw [Finset.sum_congr rfl e]
    split_ifs with hi
    · rw [← Finset.sum_div, ← stateMass_eq]
      exact div_self (ne_of_gt hi)
    · rw [← Finset.sum_div, ← stateMass_eq]
      exact div_self (ne_of_gt (ymass_pos M β hβ x y hxy i hi))

lemma dualPolicy_weight (M : StationaryMDP S A) (β : S → ℝ) (hβ : ∀ i, 0 < β i)
    (x y : Pair M → ℝ) (hxy : DualFeasible M β x y) (i : S) (a : A) :
    (dualPolicy M β hβ x y hxy).weight i a = dualPolicyWeight M x y i a := rfl

lemma dualPolicy_supp (M : StationaryMDP S A) (β : S → ℝ) (hβ : ∀ i, 0 < β i)
    (x y : Pair M → ℝ) (hxy : DualFeasible M β x y) (i : S) (a : A) (ha : a ∈ M.admissible i)
    (hw : 0 < (dualPolicy M β hβ x y hxy).weight i a) :
    (i ∈ Ex M x → 0 < x ⟨(i, a), ha⟩) ∧ (i ∉ Ex M x → 0 < y ⟨(i, a), ha⟩) := by
  rw [dualPolicy_weight, dpw_eq, if_pos ha] at hw
  constructor
  · intro hi
    rw [if_pos hi] at hw
    have h := (div_pos_iff_of_pos_right hi).mp hw
    simpa [ext, ha] using h
  · intro hi
    rw [if_neg hi] at hw
    have h := (div_pos_iff_of_pos_right (ymass_pos M β hβ x y hxy i hi)).mp hw
    simpa [ext, ha] using h

lemma dualPolicy_pos_of_y (M : StationaryMDP S A) (β : S → ℝ) (hβ : ∀ i, 0 < β i)
    (x y : Pair M → ℝ) (hxy : DualFeasible M β x y) (p : Pair M) (hi : p.1.1 ∉ Ex M x)
    (hy : 0 < y p) : 0 < (dualPolicy M β hβ x y hxy).weight p.1.1 p.1.2 := by
  rw [dualPolicy_weight, dpw_eq, if_pos p.2, if_neg hi, ext_pair]
  exact div_pos hy (ymass_pos M β hβ x y hxy _ hi)

/-! ### Part (b): the policy of an optimal dual solution is average optimal -/

theorem partB_core (M : StationaryMDP S A) (β : S → ℝ) (hβ : ∀ i, 0 < β i)
    (x y : Pair M → ℝ) (hopt : DualOptimal M β x y) :
    ∃ φ u : S → ℝ, Superharmonic M φ u ∧
      (∀ i, gainInf (dualPolicy M β hβ x y hopt.1).toHR i = φ i) ∧
      (∀ (R : AvgHRPolicy M) i, gainInf R i ≤ φ i) := by
  classical
  have hxy := hopt.1
  obtain ⟨hnn, h3, h4⟩ := hxy
  obtain ⟨φ, u, hsh, hxeq, hyeq⟩ :=
    HordijkKallenbergLP.SingleLP.Proof.native_certificate M β (x, y) (optimal_conv M β x y hopt)
  -- x-supported actions are harmonic for φ
  have hxharm : ∀ p : Pair M, 0 < x p → ∑ j, M.trans p.1.1 p.1.2 j * φ j = φ p.1.1 := by
    have hz : ∑ p : Pair M, x p * (φ p.1.1 - ∑ j, M.trans p.1.1 p.1.2 j * φ j) = 0 := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [← sum_mul_stateMass, ← sum_mul_trans]
      simp_rw [h3]
      ring
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun p (_ : p ∈ Finset.univ) =>
      mul_nonneg (hnn p).1 (sub_nonneg.mpr (hsh p.1.1 p.1.2 p.2).1))).mp hz
    intro p hp
    have := (mul_eq_zero.mp (hterm p (Finset.mem_univ p))).resolve_left hp.ne'
    linarith
  set π := dualPolicy M β hβ x y hopt.1 with hπ
  set P : S → S → ℝ := fun i j => policyMatrix M π i j with hP
  have hsupp := dualPolicy_supp M β hβ x y hopt.1
  -- per-action harmonicity on supported actions
  have hact : ∀ i, ∀ a ∈ M.admissible i, 0 < π.weight i a →
      ∑ j, M.trans i a j * φ j = φ i := by
    intro i a ha hw
    by_cases hi : i ∈ Ex M x
    · exact hxharm ⟨(i, a), ha⟩ ((hsupp i a ha hw).1 hi)
    · exact (hyeq ⟨(i, a), ha⟩ ((hsupp i a ha hw).2 hi)).symm
  have hharm : ∀ i, ∑ j, policyMatrix M π i j * φ j = φ i := by
    intro i
    unfold policyMatrix
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [weight_avg M π i _ (fun _ => φ i) (hact i), ← Finset.sum_mul, π.sum_one i, one_mul]
  have hreq : ∀ i ∈ Ex M x, policyReward M π i =
      φ i + u i - ∑ j, policyMatrix M π i j * u j := by
    intro i hi
    have hu : ∑ j, policyMatrix M π i j * u j =
        ∑ a ∈ M.admissible i, π.weight i a * ∑ j, M.trans i a j * u j := by
      unfold policyMatrix
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [hu]
    unfold policyReward
    rw [weight_avg M π i (fun a => M.reward i a)
      (fun a => φ i + u i - ∑ j, M.trans i a j * u j)]
    · simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul, π.sum_one i, one_mul]
    · intro a ha hw
      have := hxeq ⟨(i, a), ha⟩ ((hsupp i a ha hw).1 hi)
      simp only at this
      linarith
  -- E_x is closed
  have hEclosed : ∀ i ∈ Ex M x, ∀ j ∉ Ex M x, P i j = 0 := by
    intro i hi j hj
    have hXj : stateMass M x j = 0 :=
      le_antisymm (not_lt.mp hj) (stateMass_nonneg M x (fun p => (hnn p).1) j)
    have hin := h3 j
    rw [hXj] at hin
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun p (_ : p ∈ Finset.univ) =>
      mul_nonneg (M.trans_nonneg p.1.1 p.1.2 j) (hnn p).1)).mp hin.symm
    apply Finset.sum_eq_zero
    intro a ha
    rcases (π.nonneg i a).lt_or_eq with hw | hw
    · have hx := (hsupp i a ha hw).1 hi
      have := hterm ⟨(i, a), ha⟩ (Finset.mem_univ _)
      simp only at this
      rw [(mul_eq_zero.mp this).resolve_right hx.ne', mul_zero]
    · rw [← hw, zero_mul]
  -- no closed set outside E_x
  have hnoclosed : ∀ C : Set S, C.Nonempty → C ⊆ (Ex M x)ᶜ →
      (∀ i ∈ C, ∀ j ∉ C, P i j = 0) → False := by
    intro C hC hsub hclosed
    let ind : S → ℝ := fun j => if j ∈ C then 1 else 0
    have hind0 : ∀ j, 0 ≤ ind j := fun j => by simp only [ind]; split_ifs <;> norm_num
    have hX : ∑ j, ind j * stateMass M x j = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j ∈ C
      · have hjn : j ∉ Ex M x := hsub hj
        have : stateMass M x j = 0 :=
          le_antisymm (not_lt.mp hjn) (stateMass_nonneg M x (fun p => (hnn p).1) j)
        rw [this, mul_zero]
      · simp [ind, hj]
    have hsum : ∑ j, ind j * (stateMass M x j + stateMass M y j) =
        ∑ j, ind j * β j + ∑ j, ind j * ∑ p : Pair M, M.trans p.1.1 p.1.2 j * y p := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [h4 j]; ring
    simp_rw [mul_add, Finset.sum_add_distrib] at hsum
    rw [hX, zero_add, sum_mul_stateMass, sum_mul_trans] at hsum
    have hcomp : ∀ p : Pair M, y p * ind p.1.1 ≤ y p * ∑ j, M.trans p.1.1 p.1.2 j * ind j := by
      intro p
      by_cases hpC : p.1.1 ∈ C
      · rcases (hnn p).2.lt_or_eq with hy | hy
        · have hw := dualPolicy_pos_of_y M β hβ x y hopt.1 p (hsub hpC) hy
          have hz : ∀ j ∉ C, M.trans p.1.1 p.1.2 j = 0 := by
            intro j hj
            have h0 := hclosed p.1.1 hpC j hj
            simp only [hP, policyMatrix] at h0
            have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun a (_ : a ∈ M.admissible p.1.1) =>
              mul_nonneg (π.nonneg p.1.1 a) (M.trans_nonneg p.1.1 a j))).mp h0
            exact (mul_eq_zero.mp (hterm p.1.2 p.2)).resolve_left hw.ne'
          have hone : ∑ j, M.trans p.1.1 p.1.2 j * ind j = 1 := by
            rw [← M.trans_sum p.1.1 p.1.2]
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj : j ∈ C
            · simp [ind, hj]
            · simp [ind, hj, hz j hj]
          rw [hone]; simp [ind, hpC]
        · rw [← hy]; simp
      · have : ind p.1.1 = 0 := by simp [ind, hpC]
        rw [this, mul_zero]
        exact mul_nonneg (hnn p).2 (Finset.sum_nonneg fun j _ =>
          mul_nonneg (M.trans_nonneg _ _ _) (hind0 j))
    have hle := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => hcomp p
    obtain ⟨c, hc⟩ := hC
    have hpos : 0 < ∑ j, ind j * β j := by
      have : ind c * β c ≤ ∑ j, ind j * β j :=
        Finset.single_le_sum (fun j _ => mul_nonneg (hind0 j) (hβ j).le) (Finset.mem_univ c)
      have : ind c = 1 := by simp [ind, hc]
      nlinarith [hβ c]
    linarith
  -- Lyapunov function and the lower bound
  obtain ⟨v, _, hv⟩ := HordijkKallenbergLP.SingleLP.Proof.exists_lyapunov P (Ex M x)
    (fun i j => policyMatrix_nonneg M π i j) (fun i => policyMatrix_sum M π i) hEclosed hnoclosed
  let slack : S → ℝ := fun i => φ i + u i - (∑ j, P i j * u j) - policyReward M π i
  obtain ⟨B, _, hB⟩ := HordijkKallenbergLP.SingleLP.Proof.finite_abs_bound slack
  let w : S → ℝ := fun i => u i - B * v i
  have hlow : ∀ i, φ i + w i ≤ policyReward M π i + ∑ j, policyMatrix M π i j * w j := by
    intro i
    have hid : φ i + w i - (∑ j, P i j * w j) - policyReward M π i =
        slack i - B * (v i - ∑ j, P i j * v j) := by
      simp only [w, slack]
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      have hsB : (∑ j, P i j * (B * v j)) = B * ∑ j, P i j * v j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsB]
      ring
    rw [hv i] at hid
    by_cases hi : i ∈ Ex M x
    · have hz : slack i = 0 := by simp only [slack, hP]; rw [hreq i hi]; ring
      rw [if_pos hi, hz, mul_zero, sub_zero] at hid
      simp only [hP] at hid
      linarith
    · have hh := (le_abs_self (slack i)).trans (hB i)
      rw [if_neg hi, mul_one] at hid
      simp only [hP] at hid
      linarith
  obtain ⟨U, _, hU⟩ := HordijkKallenbergLP.SingleLP.Proof.finite_abs_bound u
  obtain ⟨W, _, hW⟩ := HordijkKallenbergLP.SingleLP.Proof.finite_abs_bound w
  have hupper (R' : AvgHRPolicy M) := HordijkKallenbergLP.SingleLP.Proof.reward_upper R' φ u (-U)
    (fun i => neg_le_of_abs_le (hU i))
    (fun i a ha => (hsh i a ha).1) (fun i a ha => (hsh i a ha).2)
  have hlower := Vst_lower M π φ w W (fun i => le_of_abs_le (hW i)) hharm hlow
  have hgain (R' : AvgHRPolicy M) (i : S) : gainInf R' i ≤ φ i := by
    apply HordijkKallenbergLP.SingleLP.Proof.gainInf_le_of_reward_upper R' i (φ i) (u i + U)
    intro N
    have hh := hupper R' N 0 [] i
    linarith
  refine ⟨φ, u, hsh, fun i => ?_, hgain⟩
  have ht := HordijkKallenbergLP.SingleLP.Proof.average_tendsto_of_reward_bounds π.toHR i
    (φ i) (w i - W) (u i + U)
    (fun N => by rw [totalReward_stat]; have hh := hlower N i; linarith)
    (fun N => by have hh := hupper π.toHR N 0 [] i; linarith)
  exact ht.liminf_eq

theorem partB (M : StationaryMDP S A) (β : S → ℝ) (hβ : ∀ i, 0 < β i)
    (x y : Pair M → ℝ) (hopt : DualOptimal M β x y) :
    (∃ π : RandomizedPolicy M, (∀ i a, π.weight i a = dualPolicyWeight M x y i a) ∧
        HordijkKallenbergLP.SingleLP.IsAvgOptimal M π.toHR) ∧
      (∃ u, Superharmonic M (optGainInf M) u) := by
  obtain ⟨φ, u, hsh, hπ, hR⟩ := partB_core M β hβ x y hopt
  have hopt' : ∀ i, optGainInf M i = φ i := by
    intro i
    change (⨆ R' : AvgHRPolicy M, gainInf R' i) = φ i
    let _ : Nonempty (AvgHRPolicy M) := ⟨(dualPolicy M β hβ x y hopt.1).toHR⟩
    have hb : BddAbove (Set.range (fun R' : AvgHRPolicy M => gainInf R' i)) :=
      ⟨φ i, fun _ ⟨R', hr⟩ => hr ▸ hR R' i⟩
    apply le_antisymm (ciSup_le (fun R' => hR R' i))
    rw [← hπ i]
    exact le_ciSup hb _
  refine ⟨⟨dualPolicy M β hβ x y hopt.1, fun i a => rfl, fun i => ?_⟩, u, ?_⟩
  · rw [hπ i, hopt' i]
  · have : optGainInf M = φ := funext hopt'
    rw [this]; exact hsh

end HordijkKallenbergLP.Correspondence.HK8

-- ===== HK8D =====

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology
open HordijkKallenbergLP.SingleLP (Pair Superharmonic)

namespace HordijkKallenbergLP.Correspondence.HK8

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-! ### Attainment of the dual maximum -/

/-- the column of the dual LP attached to a variable -/
noncomputable def gen (M : StationaryMDP S A) : Pair M ⊕ Pair M → Option (S ⊕ S) → ℝ
  | .inl p, none => M.reward p.1.1 p.1.2
  | .inl p, some (.inl j) => (if p.1.1 = j then 1 else 0) - M.trans p.1.1 p.1.2 j
  | .inl p, some (.inr j) => if p.1.1 = j then 1 else 0
  | .inr _, none => 0
  | .inr _, some (.inl _) => 0
  | .inr p, some (.inr j) => (if p.1.1 = j then 1 else 0) - M.trans p.1.1 p.1.2 j

noncomputable def target (β : S → ℝ) (t : ℝ) : Option (S ⊕ S) → ℝ
  | none => t
  | some (.inl _) => 0
  | some (.inr j) => β j

lemma gen_sum (M : StationaryMDP S A) (c : Pair M ⊕ Pair M → ℝ) (o : Option (S ⊕ S)) :
    (∑ v, c v • gen M v) o = match o with
      | none => dualObjective M (fun p => c (.inl p))
      | some (.inl j) => stateMass M (fun p => c (.inl p)) j -
          ∑ p : Pair M, M.trans p.1.1 p.1.2 j * c (.inl p)
      | some (.inr j) => stateMass M (fun p => c (.inl p)) j + stateMass M (fun p => c (.inr p)) j -
          ∑ p : Pair M, M.trans p.1.1 p.1.2 j * c (.inr p) := by
  rw [Finset.sum_apply, Fintype.sum_sum_type]
  rcases o with _ | (j | j)
  · simp [gen, dualObjective, mul_comm]
  · simp only [Pi.smul_apply, gen, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero]
    simp only [stateMass, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  · simp only [Pi.smul_apply, gen, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero]
    simp only [stateMass, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
    have : ∑ p : Pair M, c (Sum.inr p) * M.trans p.1.1 p.1.2 j =
        ∑ p : Pair M, M.trans p.1.1 p.1.2 j * c (Sum.inr p) :=
      Finset.sum_congr rfl fun p _ => mul_comm _ _
    rw [this]; ring

lemma feasible_iff_cone (M : StationaryMDP S A) (β : S → ℝ) (c : Pair M ⊕ Pair M → ℝ)
    (hc : ∀ v, 0 ≤ c v) (t : ℝ) :
    (∑ v, c v • gen M v) = target β t ↔
      DualFeasible M β (fun p => c (.inl p)) (fun p => c (.inr p)) ∧
        dualObjective M (fun p => c (.inl p)) = t := by
  constructor
  · intro h
    have hn := congrFun h none
    rw [gen_sum] at hn
    refine ⟨⟨fun p => ⟨hc _, hc _⟩, fun j => ?_, fun j => ?_⟩, hn⟩
    · have := congrFun h (some (.inl j))
      rw [gen_sum] at this
      simp only [target] at this
      linarith
    · have := congrFun h (some (.inr j))
      rw [gen_sum] at this
      simp only [target] at this
      linarith
  · rintro ⟨⟨_, h3, h4⟩, ho⟩
    funext o
    rw [gen_sum]
    rcases o with _ | (j | j)
    · exact ho
    · simp only [target]; linarith [h3 j]
    · simp only [target]; linarith [h4 j]

lemma trivial_superharmonic (M : StationaryMDP S A) :
    ∃ K : ℝ, Superharmonic M (fun _ => K) (fun _ => 0) := by
  classical
  refine ⟨∑ i, ∑ a, |M.reward i a|, fun i a ha => ⟨?_, ?_⟩⟩
  · simp [← Finset.sum_mul, M.trans_sum]
  · simp only [mul_zero, Finset.sum_const_zero, add_zero]
    exact (le_abs_self _).trans ((Finset.single_le_sum
      (fun b (_ : b ∈ Finset.univ) => abs_nonneg (M.reward i b)) (Finset.mem_univ a)).trans
      (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
        Finset.sum_nonneg fun b _ => abs_nonneg (M.reward j b)) (Finset.mem_univ i)))

theorem dual_attains (M : StationaryMDP S A) (β : S → ℝ) (x₀ y₀ : Pair M → ℝ)
    (h₀ : DualFeasible M β x₀ y₀) : ∃ x y, DualOptimal M β x y := by
  classical
  let T : Set ℝ := {t | ∃ x y, DualFeasible M β x y ∧ dualObjective M x = t}
  have hne : T.Nonempty := ⟨_, x₀, y₀, h₀, rfl⟩
  obtain ⟨K, hK⟩ := trivial_superharmonic M
  have hbdd : BddAbove T := by
    refine ⟨∑ i, β i * K, ?_⟩
    rintro t ⟨x, y, hxy, rfl⟩
    exact weak_duality M β x y hxy _ _ hK
  obtain ⟨tseq, -, htend, hmem⟩ := exists_seq_tendsto_sSup hne hbdd
  have hcone : ∀ n, target β (tseq n) ∈
      HordijkKallenbergLP.SingleLP.Proof.finiteCone (gen M) := by
    intro n
    obtain ⟨x, y, hxy, hobj⟩ := hmem n
    refine ⟨Sum.elim x y, ?_, ?_⟩
    · intro v; cases v with
      | inl p => exact (hxy.1 p).1
      | inr p => exact (hxy.1 p).2
    · rw [feasible_iff_cone M β (Sum.elim x y) (by
        intro v; cases v with
        | inl p => exact (hxy.1 p).1
        | inr p => exact (hxy.1 p).2)]
      exact ⟨hxy, hobj⟩
  have htcont : Continuous (target β) := by
    apply continuous_pi
    intro o
    rcases o with _ | (j | j)
    · exact continuous_id
    · exact continuous_const
    · exact continuous_const
  have hlim : target β (sSup T) ∈ HordijkKallenbergLP.SingleLP.Proof.finiteCone (gen M) :=
    (HordijkKallenbergLP.SingleLP.Proof.finiteCone_closed (gen M)).mem_of_tendsto
      ((htcont.tendsto _).comp htend) (Eventually.of_forall hcone)
  obtain ⟨c, hc, hcs⟩ := hlim
  obtain ⟨hfeas, hobj⟩ := (feasible_iff_cone M β c hc _).1 hcs
  refine ⟨_, _, hfeas, fun x' y' h' => ?_⟩
  rw [hobj]
  exact le_csSup hbdd ⟨x', y', h', rfl⟩

/-- Existence of a superharmonic pair whose first component is the optimal gain, once the dual
program is feasible. -/
theorem superharmonic_optGain (M : StationaryMDP S A) (β : S → ℝ) (hβ : ∀ i, 0 < β i)
    (x₀ y₀ : Pair M → ℝ) (h₀ : DualFeasible M β x₀ y₀) :
    ∃ u, Superharmonic M (optGainInf M) u := by
  obtain ⟨x, y, hopt⟩ := dual_attains M β x₀ y₀ h₀
  exact (partB M β hβ x y hopt).2

end HordijkKallenbergLP.Correspondence.HK8

-- ===== HK8E =====

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology
open HordijkKallenbergLP.SingleLP (Pair Superharmonic)

namespace HordijkKallenbergLP.Correspondence.HK8

/-! ### Finite Markov chain facts about the limit and deviation matrices -/

section Chain

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma acc_of_pow_pos {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    ∀ (k : ℕ) (l i : n), 0 < (P ^ k) l i → Accessible P l i := by
  intro k
  induction k with
  | zero =>
    intro l i h
    by_cases hli : l = i
    · subst hli; exact Relation.ReflTransGen.refl
    · simp [Matrix.one_apply, hli] at h
  | succ k ih =>
    intro l i h
    rw [pow_succ, Matrix.mul_apply] at h
    have : ∃ j, 0 < (P ^ k) l j * P j i := by
      by_contra hc
      push_neg at hc
      have := Finset.sum_nonpos (fun j (_ : j ∈ Finset.univ) => hc j)
      linarith
    obtain ⟨j, hj⟩ := this
    have h1 : 0 < (P ^ k) l j := by
      by_contra h0
      have : (P ^ k) l j = 0 := le_antisymm (not_lt.mp h0) ((bmk_pow hP k).1 l j)
      rw [this, zero_mul] at hj
      exact lt_irrefl _ hj
    have h2 : 0 < P j i := by
      by_contra h0
      have : P j i = 0 := le_antisymm (not_lt.mp h0) (hP.1 j i)
      rw [this, mul_zero] at hj
      exact lt_irrefl _ hj
    exact (ih l j h1).tail h2

lemma L_entry_tendsto {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (l i : n) :
    Tendsto (fun N => cesaroMean P N l i) atTop (𝓝 (limitMatrix P l i)) := by
  have hc : Continuous (fun Mx : Matrix n n ℝ => Mx l i) :=
    (continuous_apply i).comp (continuous_apply l)
  exact (hc.tendsto _).comp (bmk_tendsto hP)

lemma acc_of_L_pos {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) {l i : n}
    (h : 0 < limitMatrix P l i) : Accessible P l i := by
  by_contra hacc
  have hz : ∀ k, (P ^ k) l i = 0 := fun k =>
    le_antisymm (not_lt.mp (fun h' => hacc (acc_of_pow_pos hP k l i h'))) ((bmk_pow hP k).1 l i)
  have hc : ∀ N, cesaroMean P N l i = 0 := by
    intro N
    simp [cesaroMean, Matrix.smul_apply, Matrix.sum_apply, hz]
  have ht := L_entry_tendsto hP l i
  simp_rw [hc] at ht
  have := tendsto_nhds_unique tendsto_const_nhds ht
  linarith

lemma L_nonneg {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (l i : n) : 0 ≤ limitMatrix P l i :=
  (bmk_L_markov hP).1 l i

/-- Columns of the limit matrix vanish at non-recurrent states. -/
lemma L_col_zero {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) {i : n}
    (hi : ¬ IsRecurrent P i) (l : n) : limitMatrix P l i = 0 := by
  classical
  set μ : n → ℝ := fun s => limitMatrix P l s with hμdef
  have hμ0 : ∀ s, 0 ≤ μ s := fun s => L_nonneg hP l s
  have hμP : ∀ t, μ t = ∑ s, μ s * P s t := by
    intro t
    have := congrFun (congrFun (bmk_LP hP) l) t
    rw [Matrix.mul_apply] at this
    exact this.symm
  let U : Set n := {s | Accessible P s i}
  have hUi : i ∈ U := Relation.ReflTransGen.refl
  have hout : ∀ s t, s ∉ U → t ∈ U → P s t = 0 := by
    intro s t hs ht
    by_contra hne
    have hpos : 0 < P s t := lt_of_le_of_ne (hP.1 s t) (Ne.symm hne)
    exact hs (Relation.ReflTransGen.head hpos ht)
  let ind : n → ℝ := fun t => if t ∈ U then 1 else 0
  have hind0 : ∀ t, 0 ≤ ind t := fun t => by simp only [ind]; split_ifs <;> norm_num
  have hind1 : ∀ t, ind t ≤ 1 := fun t => by simp only [ind]; split_ifs <;> norm_num
  let q : n → ℝ := fun s => ∑ t, P s t * ind t
  have hq1 : ∀ s, q s ≤ 1 := by
    intro s
    calc q s ≤ ∑ t, P s t * 1 :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hind1 t) (hP.1 s t)
      _ = 1 := by simp [hP.2 s]
  have hq0 : ∀ s, s ∉ U → q s = 0 := by
    intro s hs
    apply Finset.sum_eq_zero
    intro t _
    by_cases ht : t ∈ U
    · rw [hout s t hs ht, zero_mul]
    · simp [ind, ht]
  have hsum : ∑ s, μ s * (ind s - q s) = 0 := by
    have e1 : ∑ s, μ s * ind s = ∑ s, μ s * q s := by
      calc ∑ s, μ s * ind s = ∑ t, ind t * ∑ s, μ s * P s t :=
            Finset.sum_congr rfl fun t _ => by rw [← hμP t, mul_comm]
        _ = ∑ s, μ s * q s := by
            simp only [q, Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    simp_rw [mul_sub, Finset.sum_sub_distrib, e1, sub_self]
  have hterm0 : ∀ s, 0 ≤ μ s * (ind s - q s) := by
    intro s
    by_cases hs : s ∈ U
    · have : ind s = 1 := by simp [ind, hs]
      rw [this]; exact mul_nonneg (hμ0 s) (by linarith [hq1 s])
    · have : ind s = 0 := by simp [ind, hs]
      rw [this, hq0 s hs]; simp
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun s (_ : s ∈ Finset.univ) => hterm0 s)).mp hsum
  obtain ⟨j, hij, hji⟩ : ∃ j, Accessible P i j ∧ ¬ Accessible P j i := by
    simpa [IsRecurrent] using hi
  have hexit : ∃ a b, Accessible P i a ∧ a ∈ U ∧ b ∉ U ∧ 0 < P a b := by
    have hjU : j ∉ U := hji
    clear hji
    revert hjU
    induction hij with
    | refl => intro h; exact absurd hUi h
    | @tail k j' hik hkj ih =>
      intro hj'
      by_cases hk : k ∈ U
      · exact ⟨k, j', hik, hk, hj', hkj⟩
      · exact ih hk
  obtain ⟨a, b, hia, haU, hbU, hab⟩ := hexit
  have hμa : μ a = 0 := by
    by_contra hne
    have hpos : 0 < μ a := lt_of_le_of_ne (hμ0 a) (Ne.symm hne)
    have h1 := hzero a (Finset.mem_univ a)
    have hind : ind a = 1 := by simp [ind, haU]
    rw [hind] at h1
    have hqa : q a = 1 := by
      have := (mul_eq_zero.mp h1).resolve_left hpos.ne'
      linarith
    have hcomp : ∑ t, P a t * (1 - ind t) = 0 := by
      simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib, hP.2 a]
      change 1 - q a = 0
      rw [hqa, sub_self]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun t (_ : t ∈ Finset.univ) =>
      mul_nonneg (hP.1 a t) (by linarith [hind1 t]))).mp hcomp
    have := hterm b (Finset.mem_univ b)
    have hindb : ind b = 0 := by simp [ind, hbU]
    rw [hindb, sub_zero, mul_one] at this
    linarith
  have hback : ∀ s, Accessible P s a → μ s = 0 := by
    intro s hs
    induction hs using Relation.ReflTransGen.head_induction_on with
    | refl => exact hμa
    | @head s' c hsc hca ih =>
      have hc := hμP c
      have hle : μ s' * P s' c ≤ ∑ t, μ t * P t c :=
        Finset.single_le_sum (f := fun t => μ t * P t c)
          (fun t _ => mul_nonneg (hμ0 t) (hP.1 t c)) (Finset.mem_univ s')
      rw [← hc, ih] at hle
      by_contra hne
      have := mul_pos (lt_of_le_of_ne (hμ0 s') (Ne.symm hne)) hsc
      linarith
  exact hback i hia

lemma pow_mul_L {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (k : ℕ) :
    P ^ k * limitMatrix P = limitMatrix P := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Matrix.mul_assoc, ih, bmk_PL hP]

lemma S_mul_Z {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (m : ℕ) :
    (∑ k ∈ Finset.range m, (P ^ k - limitMatrix P)) * (1 - P + limitMatrix P) = 1 - P ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Matrix.add_mul, ih]
    have : (P ^ m - limitMatrix P) * (1 - P + limitMatrix P) = P ^ m - P ^ (m + 1) := by
      rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, pow_mul_L hP,
        Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP, pow_succ]
      abel
    rw [this]; abel

lemma L_mul_Zi {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    limitMatrix P * (1 - P + limitMatrix P)⁻¹ = limitMatrix P := by
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + limitMatrix P) * (1 - P + limitMatrix P)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hu
  have hLA : limitMatrix P * (1 - P + limitMatrix P) = limitMatrix P := by
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP]; abel
  calc limitMatrix P * (1 - P + limitMatrix P)⁻¹
      = (limitMatrix P * (1 - P + limitMatrix P)) * (1 - P + limitMatrix P)⁻¹ := by rw [hLA]
    _ = limitMatrix P * ((1 - P + limitMatrix P) * (1 - P + limitMatrix P)⁻¹) :=
        Matrix.mul_assoc _ _ _
    _ = limitMatrix P := by rw [h1, Matrix.mul_one]

lemma Zi_mul_L {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    (1 - P + limitMatrix P)⁻¹ * limitMatrix P = limitMatrix P := by
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + limitMatrix P)⁻¹ * (1 - P + limitMatrix P) = 1 :=
    Matrix.nonsing_inv_mul _ hu
  have hAL : (1 - P + limitMatrix P) * limitMatrix P = limitMatrix P := by
    rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, bmk_PL hP, bmk_LL hP]; abel
  calc (1 - P + limitMatrix P)⁻¹ * limitMatrix P
      = (1 - P + limitMatrix P)⁻¹ * ((1 - P + limitMatrix P) * limitMatrix P) := by rw [hAL]
    _ = ((1 - P + limitMatrix P)⁻¹ * (1 - P + limitMatrix P)) * limitMatrix P :=
        (Matrix.mul_assoc _ _ _).symm
    _ = limitMatrix P := by rw [h1, Matrix.one_mul]

lemma DP_eq {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    deviationMatrix P * P = deviationMatrix P + limitMatrix P - 1 := by
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + limitMatrix P)⁻¹ * (1 - P + limitMatrix P) = 1 :=
    Matrix.nonsing_inv_mul _ hu
  rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Zi_mul_L hP] at h1
  unfold deviationMatrix
  rw [Matrix.sub_mul, bmk_LP hP]
  generalize (1 - P + limitMatrix P)⁻¹ = Z at h1 ⊢
  have : Z * P = Z + limitMatrix P - 1 := by rw [← h1]; abel
  rw [this]; abel

lemma S_eq {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (m : ℕ) :
    ∑ k ∈ Finset.range m, (P ^ k - limitMatrix P) = (1 - P ^ m) * (1 - P + limitMatrix P)⁻¹ := by
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + limitMatrix P) * (1 - P + limitMatrix P)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hu
  rw [← S_mul_Z hP m, Matrix.mul_assoc, h1, Matrix.mul_one]

lemma avg_eq {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (N : ℕ) :
    ((N : ℝ) + 1)⁻¹ • ∑ m ∈ Finset.range (N + 1), ∑ k ∈ Finset.range m, (P ^ k - limitMatrix P) =
      (1 - cesaroMean P N) * (1 - P + limitMatrix P)⁻¹ := by
  simp_rw [S_eq hP]
  rw [← Finset.sum_mul, ← Matrix.smul_mul, Finset.sum_sub_distrib, smul_sub, bmk_avg_const]
  rfl

lemma D_col_nonneg {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (i : n)
    (hcol : ∀ k, limitMatrix P k i = 0) (k : n) : 0 ≤ deviationMatrix P k i := by
  have hD : deviationMatrix P = (1 - limitMatrix P) * (1 - P + limitMatrix P)⁻¹ := by
    unfold deviationMatrix
    rw [Matrix.sub_mul, Matrix.one_mul, L_mul_Zi hP]
  have ht0 : Tendsto (fun N => (1 - cesaroMean P N) * (1 - P + limitMatrix P)⁻¹) atTop
      (𝓝 ((1 - limitMatrix P) * (1 - P + limitMatrix P)⁻¹)) :=
    (tendsto_const_nhds.sub (bmk_tendsto hP)).mul_const _
  have ht : Tendsto (fun N => ((1 - cesaroMean P N) * (1 - P + limitMatrix P)⁻¹) k i) atTop
      (𝓝 (deviationMatrix P k i)) := by
    rw [hD]
    exact (((continuous_apply i).comp (continuous_apply k)).tendsto _).comp ht0
  apply ge_of_tendsto ht
  apply Eventually.of_forall
  intro N
  rw [← avg_eq hP N]
  simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.sub_apply, hcol, sub_zero, smul_eq_mul]
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun j _ => (bmk_pow hP j).1 k i)

end Chain

/-! ### The representative of a stationary policy -/

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

lemma policyMatrix_markov (M : StationaryMDP S A) (π : RandomizedPolicy M) :
    IsMarkovMatrix (policyMatrix M π) :=
  ⟨policyMatrix_nonneg M π, policyMatrix_sum M π⟩

lemma mem_ergodicClass (M : StationaryMDP S A) (π : RandomizedPolicy M) (l i : S) :
    i ∈ ergodicClass M π l ↔ Accessible (policyMatrix M π) l i := by
  classical
  simp [ergodicClass]

lemma le_gamma (M : StationaryMDP S A) (β : S → ℝ) (π : RandomizedPolicy M) (l i : S)
    (hl : IsRecurrent (policyMatrix M π) l) (hi : i ∈ ergodicClass M π l) :
    -(∑ k, β k * D M π k i) / ((ergodicClass M π l).sum fun k => Pstar M π k i) ≤
      gamma M β π l := by
  classical
  unfold gamma
  rw [if_pos hl]
  exact Finset.le_sup' (fun i => -(∑ k, β k * D M π k i) /
    ((ergodicClass M π l).sum fun k => Pstar M π k i)) hi

lemma gamma_not_rec (M : StationaryMDP S A) (β : S → ℝ) (π : RandomizedPolicy M) (l : S)
    (hl : ¬ IsRecurrent (policyMatrix M π) l) : gamma M β π l = 0 := by
  classical
  unfold gamma
  rw [if_neg hl]

lemma rep_coef_nonneg (M : StationaryMDP S A) (β : S → ℝ) (hβ : ∀ i, 0 < β i)
    (π : RandomizedPolicy M) (i : S) :
    0 ≤ (∑ k, β k * D M π k i) + ∑ l, gamma M β π l * Pstar M π l i := by
  classical
  have hP := policyMatrix_markov M π
  set P := policyMatrix M π with hPdef
  have hL : ∀ a b, Pstar M π a b = limitMatrix P a b := fun a b => rfl
  have hDd : ∀ a b, D M π a b = deviationMatrix P a b := fun a b => rfl
  by_cases hcol : ∀ l, Pstar M π l i = 0
  · simp only [hcol, mul_zero, Finset.sum_const_zero, add_zero]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hβ k).le
      (by rw [hDd]; exact D_col_nonneg hP i (fun k => by rw [← hL]; exact hcol k) k)
  push_neg at hcol
  obtain ⟨l0, hl0⟩ := hcol
  have hl0pos : 0 < limitMatrix P l0 i := lt_of_le_of_ne (L_nonneg hP l0 i) (Ne.symm hl0)
  have hrec : IsRecurrent P i := by
    by_contra h
    exact hl0 (L_col_zero hP h l0)
  set C := ergodicClass M π i with hCdef
  set den := C.sum fun k => Pstar M π k i with hden
  have hden_pos : 0 < den := by
    have hLL := congrFun (congrFun (bmk_LL hP) l0) i
    rw [Matrix.mul_apply] at hLL
    have : ∃ j, 0 < limitMatrix P l0 j * limitMatrix P j i := by
      by_contra hc
      push_neg at hc
      have := Finset.sum_nonpos (fun j (_ : j ∈ Finset.univ) => hc j)
      linarith
    obtain ⟨j, hj⟩ := this
    have h1 : 0 < limitMatrix P l0 j := by
      by_contra h0
      have : limitMatrix P l0 j = 0 := le_antisymm (not_lt.mp h0) (L_nonneg hP l0 j)
      rw [this, zero_mul] at hj; exact lt_irrefl _ hj
    have h2 : 0 < limitMatrix P j i := by
      by_contra h0
      have : limitMatrix P j i = 0 := le_antisymm (not_lt.mp h0) (L_nonneg hP j i)
      rw [this, mul_zero] at hj; exact lt_irrefl _ hj
    have hjrec : IsRecurrent P j := by
      by_contra h
      exact (ne_of_gt h1) (L_col_zero hP h l0)
    have hji : Accessible P j i := acc_of_L_pos hP h2
    have hij : Accessible P i j := hjrec i hji
    have hjC : j ∈ C := (mem_ergodicClass M π i j).2 hij
    calc 0 < Pstar M π j i := h2
      _ ≤ den := Finset.single_le_sum (f := fun k => Pstar M π k i)
          (fun k _ => L_nonneg hP k i) hjC
  set bd := ∑ k, β k * D M π k i with hbd
  set ρ := -bd / den with hρ
  have hterm : ∀ l, (if l ∈ C then ρ * Pstar M π l i else 0) ≤ gamma M β π l * Pstar M π l i := by
    intro l
    by_cases hli : Pstar M π l i = 0
    · rw [hli]; simp
    have hlipos : 0 < limitMatrix P l i := lt_of_le_of_ne (L_nonneg hP l i) (Ne.symm hli)
    have hacc : Accessible P l i := acc_of_L_pos hP hlipos
    by_cases hlrec : IsRecurrent P l
    · have hil : Accessible P i l := hlrec i hacc
      have hlC : l ∈ C := (mem_ergodicClass M π i l).2 hil
      have heq : ergodicClass M π l = C := by
        ext k
        rw [mem_ergodicClass, mem_ergodicClass]
        exact ⟨fun h => hil.trans h, fun h => hacc.trans h⟩
      have hg := le_gamma M β π l i hlrec ((mem_ergodicClass M π l i).2 hacc)
      rw [heq] at hg
      rw [if_pos hlC]
      exact mul_le_mul_of_nonneg_right hg hlipos.le
    · have hlC : l ∉ C := by
        intro hlC
        have hil : Accessible P i l := (mem_ergodicClass M π i l).1 hlC
        apply hlrec
        intro m hlm
        have him : Accessible P i m := hil.trans hlm
        exact (hrec m him).trans hil
      rw [if_neg hlC, gamma_not_rec M β π l hlrec, zero_mul]
  have hsum := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hterm l
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum] at hsum
  have : ρ * den = -bd := by rw [hρ]; field_simp
  rw [← hden, this] at hsum
  linarith

/-! ### Feasibility and objective of the representative -/

lemma stateMass_form (M : StationaryMDP S A) (π : RandomizedPolicy M) (F : S → ℝ) (j : S) :
    stateMass M (fun p => F p.1.1 * π.weight p.1.1 p.1.2) j = F j := by
  rw [stateMass_eq]
  have : ∀ a ∈ M.admissible j, ext M (fun p : Pair M => F p.1.1 * π.weight p.1.1 p.1.2) j a =
      F j * π.weight j a := by
    intro a ha; simp [ext, ha]
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, π.sum_one j, mul_one]

lemma trans_form (M : StationaryMDP S A) (π : RandomizedPolicy M) (F : S → ℝ) (j : S) :
    ∑ p : Pair M, M.trans p.1.1 p.1.2 j * (F p.1.1 * π.weight p.1.1 p.1.2) =
      ∑ i, F i * policyMatrix M π i j := by
  rw [pair_sum M (fun i a => M.trans i a j * (F i * π.weight i a))]
  apply Finset.sum_congr rfl
  intro i _
  unfold policyMatrix
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma vec_mul_eq (v : S → ℝ) (B C : Matrix S S ℝ) (j : S) :
    ∑ i, (∑ k, v k * B k i) * C i j = ∑ k, v k * (B * C) k j := by
  simp_rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

theorem rep_feasible (M : StationaryMDP S A) (β : S → ℝ) (hβ : ∀ i, 0 < β i)
    (π : RandomizedPolicy M) :
    DualFeasible M β (representativeX M β π) (representativeY M β π) := by
  have hP := policyMatrix_markov M π
  refine ⟨fun p => ⟨?_, ?_⟩, fun j => ?_, fun j => ?_⟩
  · exact mul_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (hβ k).le (L_nonneg hP k _))
      (π.nonneg _ _)
  · exact mul_nonneg (rep_coef_nonneg M β hβ π _) (π.nonneg _ _)
  · unfold representativeX
    rw [stateMass_form M π (fun i => ∑ k, β k * Pstar M π k i),
      trans_form M π (fun i => ∑ k, β k * Pstar M π k i), vec_mul_eq]
    simp only [Pstar]
    rw [bmk_LP hP]
  · unfold representativeX representativeY
    rw [stateMass_form M π (fun i => ∑ k, β k * Pstar M π k i),
      stateMass_form M π (fun i => ∑ k, β k * D M π k i + ∑ l, gamma M β π l * Pstar M π l i),
      trans_form M π (fun i => ∑ k, β k * D M π k i + ∑ l, gamma M β π l * Pstar M π l i)]
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [vec_mul_eq, vec_mul_eq]
    simp only [Pstar, D]
    rw [bmk_LP hP, DP_eq hP]
    simp only [Matrix.sub_apply, Matrix.add_apply, mul_sub, mul_add, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Matrix.one_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

theorem stat_gain (M : StationaryMDP S A) (π : RandomizedPolicy M) (i : S) :
    gainInf π.toHR i = (Pstar M π *ᵥ policyReward M π) i := by
  have hP := policyMatrix_markov M π
  unfold gainInf
  simp_rw [totalReward_stat]
  have ht : Tendsto (fun N : ℕ => Vst M π N i / N) atTop
      (𝓝 ((Pstar M π *ᵥ policyReward M π) i)) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    have e : ∀ N : ℕ, Vst M π (N + 1) i / ((N + 1 : ℕ) : ℝ) =
        (cesaroMean (policyMatrix M π) N *ᵥ policyReward M π) i := by
      intro N
      unfold Vst cesaroMean
      rw [Matrix.smul_mulVec]
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    simp_rw [e]
    exact (((continuous_apply i).comp (continuous_id.matrix_mulVec continuous_const)).tendsto _).comp
      (bmk_tendsto hP)
  exact ht.liminf_eq

theorem rep_objective (M : StationaryMDP S A) (β : S → ℝ) (π : RandomizedPolicy M) :
    dualObjective M (representativeX M β π) = ∑ i, β i * gainInf π.toHR i := by
  simp_rw [stat_gain]
  unfold dualObjective representativeX
  rw [pair_sum M (fun i a => M.reward i a * ((∑ k, β k * Pstar M π k i) * π.weight i a))]
  have : ∀ i, ∑ a ∈ M.admissible i, M.reward i a * ((∑ k, β k * Pstar M π k i) * π.weight i a) =
      (∑ k, β k * Pstar M π k i) * policyReward M π i := by
    intro i
    unfold policyReward
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  simp_rw [this, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

end HordijkKallenbergLP.Correspondence.HK8

-- ===== HK8F =====

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology

namespace HordijkKallenbergLP.Correspondence.HK8

theorem theorem_8_core {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [DecidableEq A] [Nonempty S]
    (M : StationaryMDP S A) (β : S → ℝ)
    (hβpos : ∀ i, 0 < β i) (hβsum : ∑ i, β i = 1) :
    (∀ π : RandomizedPolicy M, HordijkKallenbergLP.SingleLP.IsAvgOptimal M π.toHR →
      DualOptimal M β (representativeX M β π) (representativeY M β π)) ∧
    (∀ x y : HordijkKallenbergLP.SingleLP.Pair M → ℝ, DualOptimal M β x y →
      ∃ π : RandomizedPolicy M,
        (∀ i a, π.weight i a = dualPolicyWeight M x y i a) ∧
        HordijkKallenbergLP.SingleLP.IsAvgOptimal M π.toHR) := by
  refine ⟨fun π hπ => ?_, fun x y h => (partB M β hβpos x y h).1⟩
  have hfeas := rep_feasible M β hβpos π
  obtain ⟨u, hsh⟩ := superharmonic_optGain M β hβpos _ _ hfeas
  refine ⟨hfeas, fun x' y' h' => ?_⟩
  rw [rep_objective]
  have hw := weak_duality M β x' y' h' _ _ hsh
  have : ∑ i, β i * gainInf π.toHR i = ∑ i, β i * optGainInf M i :=
    Finset.sum_congr rfl fun i _ => by rw [hπ i]
  rw [this]
  exact hw

end HordijkKallenbergLP.Correspondence.HK8


-- ===== HK8G =====

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology
open HordijkKallenbergLP.SingleLP (Pair Superharmonic)

namespace HordijkKallenbergLP.Correspondence.HK8

section Chain2
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A nonnegative invariant row vector vanishes at non-recurrent states. -/
lemma stat_zero_of_not_rec {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (μ : n → ℝ)
    (hμ0 : ∀ s, 0 ≤ μ s) (hμP : ∀ t, μ t = ∑ s, μ s * P s t) {i : n}
    (hi : ¬ IsRecurrent P i) : μ i = 0 := by
  classical
  let U : Set n := {s | Accessible P s i}
  have hUi : i ∈ U := Relation.ReflTransGen.refl
  have hout : ∀ s t, s ∉ U → t ∈ U → P s t = 0 := by
    intro s t hs ht
    by_contra hne
    have hpos : 0 < P s t := lt_of_le_of_ne (hP.1 s t) (Ne.symm hne)
    exact hs (Relation.ReflTransGen.head hpos ht)
  let ind : n → ℝ := fun t => if t ∈ U then 1 else 0
  have hind0 : ∀ t, 0 ≤ ind t := fun t => by simp only [ind]; split_ifs <;> norm_num
  have hind1 : ∀ t, ind t ≤ 1 := fun t => by simp only [ind]; split_ifs <;> norm_num
  let q : n → ℝ := fun s => ∑ t, P s t * ind t
  have hq1 : ∀ s, q s ≤ 1 := by
    intro s
    calc q s ≤ ∑ t, P s t * 1 :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hind1 t) (hP.1 s t)
      _ = 1 := by simp [hP.2 s]
  have hq0 : ∀ s, s ∉ U → q s = 0 := by
    intro s hs
    apply Finset.sum_eq_zero
    intro t _
    by_cases ht : t ∈ U
    · rw [hout s t hs ht, zero_mul]
    · simp [ind, ht]
  have hsum : ∑ s, μ s * (ind s - q s) = 0 := by
    have e1 : ∑ s, μ s * ind s = ∑ s, μ s * q s := by
      calc ∑ s, μ s * ind s = ∑ t, ind t * ∑ s, μ s * P s t :=
            Finset.sum_congr rfl fun t _ => by rw [← hμP t, mul_comm]
        _ = ∑ s, μ s * q s := by
            simp only [q, Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    simp_rw [mul_sub, Finset.sum_sub_distrib, e1, sub_self]
  have hterm0 : ∀ s, 0 ≤ μ s * (ind s - q s) := by
    intro s
    by_cases hs : s ∈ U
    · have : ind s = 1 := by simp [ind, hs]
      rw [this]; exact mul_nonneg (hμ0 s) (by linarith [hq1 s])
    · have : ind s = 0 := by simp [ind, hs]
      rw [this, hq0 s hs]; simp
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun s (_ : s ∈ Finset.univ) => hterm0 s)).mp hsum
  obtain ⟨j, hij, hji⟩ : ∃ j, Accessible P i j ∧ ¬ Accessible P j i := by
    simpa [IsRecurrent] using hi
  have hexit : ∃ a b, Accessible P i a ∧ a ∈ U ∧ b ∉ U ∧ 0 < P a b := by
    have hjU : j ∉ U := hji
    clear hji
    revert hjU
    induction hij with
    | refl => intro h; exact absurd hUi h
    | @tail k j' hik hkj ih =>
      intro hj'
      by_cases hk : k ∈ U
      · exact ⟨k, j', hik, hk, hj', hkj⟩
      · exact ih hk
  obtain ⟨a, b, hia, haU, hbU, hab⟩ := hexit
  have hμa : μ a = 0 := by
    by_contra hne
    have hpos : 0 < μ a := lt_of_le_of_ne (hμ0 a) (Ne.symm hne)
    have h1 := hzero a (Finset.mem_univ a)
    have hind : ind a = 1 := by simp [ind, haU]
    rw [hind] at h1
    have hqa : q a = 1 := by
      have := (mul_eq_zero.mp h1).resolve_left hpos.ne'
      linarith
    have hcomp : ∑ t, P a t * (1 - ind t) = 0 := by
      simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib, hP.2 a]
      change 1 - q a = 0
      rw [hqa, sub_self]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun t (_ : t ∈ Finset.univ) =>
      mul_nonneg (hP.1 a t) (by linarith [hind1 t]))).mp hcomp
    have := hterm b (Finset.mem_univ b)
    have hindb : ind b = 0 := by simp [ind, hbU]
    rw [hindb, sub_zero, mul_one] at this
    linarith
  have hback : ∀ s, Accessible P s a → μ s = 0 := by
    intro s hs
    induction hs using Relation.ReflTransGen.head_induction_on with
    | refl => exact hμa
    | @head s' c hsc hca ih =>
      have hc := hμP c
      have hle : μ s' * P s' c ≤ ∑ t, μ t * P t c :=
        Finset.single_le_sum (f := fun t => μ t * P t c)
          (fun t _ => mul_nonneg (hμ0 t) (hP.1 t c)) (Finset.mem_univ s')
      rw [← hc, ih] at hle
      by_contra hne
      have := mul_pos (lt_of_le_of_ne (hμ0 s') (Ne.symm hne)) hsc
      linarith
  exact hback i hia

end Chain2

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

lemma dp_structure (M : StationaryMDP S A) (β : S → ℝ) (hβ : ∀ i, 0 < β i)
    (x y : Pair M → ℝ) (hxy0 : DualFeasible M β x y) :
    (∀ i ∈ Ex M x, ∀ j ∉ Ex M x, policyMatrix M (dualPolicy M β hβ x y hxy0) i j = 0) ∧
    (∀ C : Set S, C.Nonempty → C ⊆ (Ex M x)ᶜ →
      (∀ i ∈ C, ∀ j ∉ C, policyMatrix M (dualPolicy M β hβ x y hxy0) i j = 0) → False) := by
  classical
  have hxy := hxy0
  obtain ⟨hnn, h3, h4⟩ := hxy
  set π := dualPolicy M β hβ x y hxy0 with hπ
  set P : S → S → ℝ := fun i j => policyMatrix M π i j with hP
  have hsupp := dualPolicy_supp M β hβ x y hxy0
  -- E_x is closed
  have hEclosed : ∀ i ∈ Ex M x, ∀ j ∉ Ex M x, P i j = 0 := by
    intro i hi j hj
    have hXj : stateMass M x j = 0 :=
      le_antisymm (not_lt.mp hj) (stateMass_nonneg M x (fun p => (hnn p).1) j)
    have hin := h3 j
    rw [hXj] at hin
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun p (_ : p ∈ Finset.univ) =>
      mul_nonneg (M.trans_nonneg p.1.1 p.1.2 j) (hnn p).1)).mp hin.symm
    apply Finset.sum_eq_zero
    intro a ha
    rcases (π.nonneg i a).lt_or_eq with hw | hw
    · have hx := (hsupp i a ha hw).1 hi
      have := hterm ⟨(i, a), ha⟩ (Finset.mem_univ _)
      simp only at this
      rw [(mul_eq_zero.mp this).resolve_right hx.ne', mul_zero]
    · rw [← hw, zero_mul]
  -- no closed set outside E_x
  have hnoclosed : ∀ C : Set S, C.Nonempty → C ⊆ (Ex M x)ᶜ →
      (∀ i ∈ C, ∀ j ∉ C, P i j = 0) → False := by
    intro C hC hsub hclosed
    let ind : S → ℝ := fun j => if j ∈ C then 1 else 0
    have hind0 : ∀ j, 0 ≤ ind j := fun j => by simp only [ind]; split_ifs <;> norm_num
    have hX : ∑ j, ind j * stateMass M x j = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j ∈ C
      · have hjn : j ∉ Ex M x := hsub hj
        have : stateMass M x j = 0 :=
          le_antisymm (not_lt.mp hjn) (stateMass_nonneg M x (fun p => (hnn p).1) j)
        rw [this, mul_zero]
      · simp [ind, hj]
    have hsum : ∑ j, ind j * (stateMass M x j + stateMass M y j) =
        ∑ j, ind j * β j + ∑ j, ind j * ∑ p : Pair M, M.trans p.1.1 p.1.2 j * y p := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [h4 j]; ring
    simp_rw [mul_add, Finset.sum_add_distrib] at hsum
    rw [hX, zero_add, sum_mul_stateMass, sum_mul_trans] at hsum
    have hcomp : ∀ p : Pair M, y p * ind p.1.1 ≤ y p * ∑ j, M.trans p.1.1 p.1.2 j * ind j := by
      intro p
      by_cases hpC : p.1.1 ∈ C
      · rcases (hnn p).2.lt_or_eq with hy | hy
        · have hw := dualPolicy_pos_of_y M β hβ x y hxy0 p (hsub hpC) hy
          have hz : ∀ j ∉ C, M.trans p.1.1 p.1.2 j = 0 := by
            intro j hj
            have h0 := hclosed p.1.1 hpC j hj
            simp only [hP, policyMatrix] at h0
            have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun a (_ : a ∈ M.admissible p.1.1) =>
              mul_nonneg (π.nonneg p.1.1 a) (M.trans_nonneg p.1.1 a j))).mp h0
            exact (mul_eq_zero.mp (hterm p.1.2 p.2)).resolve_left hw.ne'
          have hone : ∑ j, M.trans p.1.1 p.1.2 j * ind j = 1 := by
            rw [← M.trans_sum p.1.1 p.1.2]
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj : j ∈ C
            · simp [ind, hj]
            · simp [ind, hj, hz j hj]
          rw [hone]; simp [ind, hpC]
        · rw [← hy]; simp
      · have : ind p.1.1 = 0 := by simp [ind, hpC]
        rw [this, mul_zero]
        exact mul_nonneg (hnn p).2 (Finset.sum_nonneg fun j _ =>
          mul_nonneg (M.trans_nonneg _ _ _) (hind0 j))
    have hle := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => hcomp p
    obtain ⟨c, hc⟩ := hC
    have hpos : 0 < ∑ j, ind j * β j := by
      have : ind c * β c ≤ ∑ j, ind j * β j :=
        Finset.single_le_sum (fun j _ => mul_nonneg (hind0 j) (hβ j).le) (Finset.mem_univ c)
      have : ind c = 1 := by simp [ind, hc]
      nlinarith [hβ c]
    linarith
  exact ⟨hEclosed, hnoclosed⟩

end HordijkKallenbergLP.Correspondence.HK8

-- ===== HK8H =====

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology
open HordijkKallenbergLP.SingleLP (Pair Superharmonic)

namespace HordijkKallenbergLP.Correspondence.HK8

variable {S A : Type*} [Fintype S] [Fintype A]

lemma gain_le_of_superharmonic (M : StationaryMDP S A) (φ u : S → ℝ) (hsh : Superharmonic M φ u)
    (R : AvgHRPolicy M) (i : S) : gainInf R i ≤ φ i := by
  obtain ⟨U, _, hU⟩ := HordijkKallenbergLP.SingleLP.Proof.finite_abs_bound u
  have hupper := HordijkKallenbergLP.SingleLP.Proof.reward_upper R φ u (-U)
    (fun i => neg_le_of_abs_le (hU i))
    (fun i a ha => (hsh i a ha).1) (fun i a ha => (hsh i a ha).2)
  apply HordijkKallenbergLP.SingleLP.Proof.gainInf_le_of_reward_upper R i (φ i) (u i + U)
  intro N
  have hh := hupper N 0 [] i
  linarith

lemma optGain_le_of_superharmonic (M : StationaryMDP S A) (φ u : S → ℝ)
    (hsh : Superharmonic M φ u) (i : S) : optGainInf M i ≤ φ i := by
  classical
  change (⨆ R' : AvgHRPolicy M, gainInf R' i) ≤ φ i
  let d : S → A := fun i => (M.admissible_nonempty i).choose
  have hd : ∀ i, d i ∈ M.admissible i := fun i => (M.admissible_nonempty i).choose_spec
  let _ : Nonempty (AvgHRPolicy M) := ⟨stationaryPolicy M d hd⟩
  exact ciSup_le (fun R => gain_le_of_superharmonic M φ u hsh R i)

/-- a deterministic randomized policy -/
noncomputable def detPolicy [DecidableEq A] (M : StationaryMDP S A) : RandomizedPolicy M where
  weight i a := if a = (M.admissible_nonempty i).choose then 1 else 0
  nonneg i a := by split_ifs <;> norm_num
  supported i a ha := by
    split_ifs with h
    · exact absurd (h ▸ (M.admissible_nonempty i).choose_spec) ha
    · rfl
  sum_one i := by
    rw [Finset.sum_ite_eq' (M.admissible i) _ (fun _ => (1 : ℝ))]
    simp [(M.admissible_nonempty i).choose_spec]

theorem theorem_6_core [Nonempty S] (M : StationaryMDP S A) :
    (∃ u : S → ℝ, Superharmonic M (optGainInf M) u) ∧
    (∀ φ u : S → ℝ, Superharmonic M φ u → ∀ i, optGainInf M i ≤ φ i) := by
  classical
  refine ⟨?_, fun φ u hsh i => optGain_le_of_superharmonic M φ u hsh i⟩
  let β : S → ℝ := fun _ => 1
  have hβ : ∀ i, 0 < β i := fun _ => one_pos
  exact superharmonic_optGain M β hβ _ _ (rep_feasible M β hβ (detPolicy M))

variable [DecidableEq S] [DecidableEq A]

/-- The duality gap identity. -/
lemma duality_gap (M : StationaryMDP S A) (β : S → ℝ) (x y : Pair M → ℝ)
    (hxy : DualFeasible M β x y) (φ u : S → ℝ) :
    ∑ i, β i * φ i - dualObjective M x =
      ∑ p, x p * (φ p.1.1 + u p.1.1 - (∑ j, M.trans p.1.1 p.1.2 j * u j) - M.reward p.1.1 p.1.2) +
      ∑ p, y p * (φ p.1.1 - ∑ j, M.trans p.1.1 p.1.2 j * φ j) := by
  obtain ⟨hnn, h3, h4⟩ := hxy
  have e1 : ∑ p, x p * u p.1.1 = ∑ j, u j * stateMass M x j := (sum_mul_stateMass M u x).symm
  have e2 : ∑ p, x p * ∑ j, M.trans p.1.1 p.1.2 j * u j = ∑ j, u j * stateMass M x j := by
    rw [← sum_mul_trans]
    simp_rw [h3]
  have e3 : ∑ p, x p * φ p.1.1 = ∑ j, φ j * stateMass M x j := (sum_mul_stateMass M φ x).symm
  have e4 : ∑ j, φ j * stateMass M x j = ∑ j, β j * φ j +
      ∑ p, y p * (∑ j, M.trans p.1.1 p.1.2 j * φ j) - ∑ p, y p * φ p.1.1 := by
    rw [← sum_mul_trans, ← sum_mul_stateMass]
    have : ∀ j, stateMass M x j = β j + ∑ p, M.trans p.1.1 p.1.2 j * y p - stateMass M y j :=
      fun j => by linarith [h4 j]
    simp_rw [this, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp_rw [mul_comm (φ _) (β _)]
  simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  unfold dualObjective
  have e5 : ∑ p, x p * M.reward p.1.1 p.1.2 = ∑ p, M.reward p.1.1 p.1.2 * x p :=
    Finset.sum_congr rfl fun p _ => mul_comm _ _
  linarith

theorem proposition_4_core [Nonempty S] (M : StationaryMDP S A) (β : S → ℝ)
    (hβpos : ∀ i, 0 < β i)
    (x y : Pair M → ℝ) (hxy : DualOptimal M β x y)
    (φ u : S → ℝ) (hφu : PrimalOptimal M β φ u) :
    ∀ i a, 0 < dualPolicyWeight M x y i a →
      (∑ j, M.trans i a j * φ j = φ i) ∧
      (i ∈ Ex M x → φ i + u i = M.reward i a + ∑ j, M.trans i a j * u j) := by
  obtain ⟨⟨π', hw', hopt'⟩, u', hsh'⟩ := partB M β hβpos x y hxy
  obtain ⟨hshφ, hmin⟩ := hφu
  -- value comparison
  have hrepf := rep_feasible M β hβpos π'
  have hobj : ∑ i, β i * φ i ≤ dualObjective M x := by
    have h1 := hmin _ _ hsh'
    have h2 := hxy.2 _ _ hrepf
    rw [rep_objective] at h2
    have h3 : ∑ i, β i * gainInf π'.toHR i = ∑ i, β i * optGainInf M i :=
      Finset.sum_congr rfl fun i _ => by rw [hopt' i]
    unfold primalObjective at h1
    linarith
  have hgap := duality_gap M β x y hxy.1 φ u
  obtain ⟨hnn, h3, h4⟩ := hxy.1
  have ht1 : ∀ p : Pair M, 0 ≤ x p * (φ p.1.1 + u p.1.1 - (∑ j, M.trans p.1.1 p.1.2 j * u j) -
      M.reward p.1.1 p.1.2) := fun p => mul_nonneg (hnn p).1 (by
        have := (hshφ p.1.1 p.1.2 p.2).2; linarith)
  have ht2 : ∀ p : Pair M, 0 ≤ y p * (φ p.1.1 - ∑ j, M.trans p.1.1 p.1.2 j * φ j) :=
    fun p => mul_nonneg (hnn p).2 (sub_nonneg.mpr (hshφ p.1.1 p.1.2 p.2).1)
  have hs1 := Finset.sum_nonneg fun p (_ : p ∈ Finset.univ) => ht1 p
  have hs2 := Finset.sum_nonneg fun p (_ : p ∈ Finset.univ) => ht2 p
  have hz1 := (Finset.sum_eq_zero_iff_of_nonneg (fun p (_ : p ∈ Finset.univ) => ht1 p)).mp
    (by linarith)
  have hz2 := (Finset.sum_eq_zero_iff_of_nonneg (fun p (_ : p ∈ Finset.univ) => ht2 p)).mp
    (by linarith)
  have hxharm : ∀ p : Pair M, 0 < x p → ∑ j, M.trans p.1.1 p.1.2 j * φ j = φ p.1.1 := by
    have hz : ∑ p : Pair M, x p * (φ p.1.1 - ∑ j, M.trans p.1.1 p.1.2 j * φ j) = 0 := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [← sum_mul_stateMass, ← sum_mul_trans]
      simp_rw [h3]
      ring
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun p (_ : p ∈ Finset.univ) =>
      mul_nonneg (hnn p).1 (sub_nonneg.mpr (hshφ p.1.1 p.1.2 p.2).1))).mp hz
    intro p hp
    have := (mul_eq_zero.mp (hterm p (Finset.mem_univ p))).resolve_left hp.ne'
    linarith
  intro i a hw
  have ha : a ∈ M.admissible i := by
    by_contra ha
    rw [dpw_eq, if_neg ha] at hw
    exact lt_irrefl _ hw
  have hsupp := dualPolicy_supp M β hβpos x y hxy.1 i a ha hw
  constructor
  · by_cases hi : i ∈ Ex M x
    · exact hxharm ⟨(i, a), ha⟩ (hsupp.1 hi)
    · have := (mul_eq_zero.mp (hz2 ⟨(i, a), ha⟩ (Finset.mem_univ _))).resolve_left
        (hsupp.2 hi).ne'
      simp only at this
      linarith
  · intro hi
    have := (mul_eq_zero.mp (hz1 ⟨(i, a), ha⟩ (Finset.mem_univ _))).resolve_left
      (hsupp.1 hi).ne'
    simp only at this
    linarith

theorem proposition_5_core [Nonempty S] (M : StationaryMDP S A) (β : S → ℝ)
    (hβpos : ∀ i, 0 < β i)
    (x y : Pair M → ℝ) (hxy : DualFeasible M β x y)
    (π : RandomizedPolicy M)
    (hπ : ∀ i a, π.weight i a = dualPolicyWeight M x y i a) :
    ∀ i, i ∈ Ex M x ↔ IsRecurrent (policyMatrix M π) i := by
  classical
  have hPeq : policyMatrix M π = policyMatrix M (dualPolicy M β hβpos x y hxy) := by
    funext i j
    simp only [policyMatrix, hπ, dualPolicy_weight]
  rw [hPeq]
  set P := policyMatrix M (dualPolicy M β hβpos x y hxy) with hPdef
  have hP : IsMarkovMatrix P := policyMatrix_markov M _
  obtain ⟨hEclosed, hnoclosed⟩ := dp_structure M β hβpos x y hxy
  have hxy' := hxy
  obtain ⟨hnn, h3, h4⟩ := hxy'
  -- E_x is closed along paths
  have hpath : ∀ j k, Accessible P j k → j ∈ Ex M x → k ∈ Ex M x := by
    intro j k hjk hj
    induction hjk with
    | refl => exact hj
    | @tail b c _ hbc ih =>
      by_contra hc
      have : P b c = 0 := hEclosed b ih c hc
      rw [this] at hbc
      exact lt_irrefl _ hbc
  intro i
  constructor
  · intro hi
    by_contra hrec
    -- the state masses form an invariant vector
    set X : S → ℝ := fun j => stateMass M x j with hX
    have hX0 : ∀ j, 0 ≤ X j := fun j => stateMass_nonneg M x (fun p => (hnn p).1) j
    have hxform : ∀ p : Pair M, x p = X p.1.1 *
        (dualPolicy M β hβpos x y hxy).weight p.1.1 p.1.2 := by
      intro p
      rw [dualPolicy_weight, dpw_eq, if_pos p.2, ext_pair]
      by_cases hp : p.1.1 ∈ Ex M x
      · rw [if_pos hp]
        have hpos : 0 < X p.1.1 := hp
        rw [mul_div_assoc', mul_comm, mul_div_assoc,
          show X p.1.1 / stateMass M x p.1.1 = 1 from div_self hpos.ne', mul_one]
      · rw [if_neg hp]
        have hXz : X p.1.1 = 0 := le_antisymm (not_lt.mp hp) (hX0 _)
        rw [hXz, zero_mul]
        have hs : stateMass M x p.1.1 = 0 := hXz
        unfold stateMass at hs
        have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun q (_ : q ∈ Finset.univ) => by
          split_ifs <;> simp [(hnn q).1])).mp hs
        have := hterm p (Finset.mem_univ p)
        simpa using this
    have hinv : ∀ t, X t = ∑ s, X s * P s t := by
      intro t
      have := h3 t
      rw [show (fun p : Pair M => M.trans p.1.1 p.1.2 t * x p) = fun p : Pair M =>
        M.trans p.1.1 p.1.2 t * (X p.1.1 *
          (dualPolicy M β hβpos x y hxy).weight p.1.1 p.1.2) from
        funext fun p => by rw [← hxform p]] at this
      rw [trans_form] at this
      exact this
    have hz := stat_zero_of_not_rec hP X hX0 hinv hrec
    exact (ne_of_gt hi) hz
  · intro hrec
    by_contra hi
    let C : Set S := {j | Accessible P i j}
    apply hnoclosed C ⟨i, Relation.ReflTransGen.refl⟩
    · intro j hj hjE
      exact hi (hpath j i (hrec j hj) hjE)
    · intro j hj k hk
      by_contra hne
      have hpos : 0 < P j k := lt_of_le_of_ne (hP.1 j k) (Ne.symm hne)
      exact hk (Relation.ReflTransGen.tail hj hpos)

end HordijkKallenbergLP.Correspondence.HK8


open HordijkKallenbergLP.Correspondence MarkovDecisionProcesses Matrix in
theorem solution {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [DecidableEq A] [Nonempty S]
    (M : StationaryMDP S A) (β : S → ℝ)
    (hβpos : ∀ i, 0 < β i) (hβsum : ∑ i, β i = 1)
    (x y : HordijkKallenbergLP.SingleLP.Pair M → ℝ) (hxy : DualOptimal M β x y)
    (φ u : S → ℝ) (hφu : PrimalOptimal M β φ u) :
    ∀ i a, 0 < dualPolicyWeight M x y i a →
      (∑ j, M.trans i a j * φ j = φ i) ∧
      (i ∈ Ex M x → φ i + u i = M.reward i a + ∑ j, M.trans i a j * u j) :=
  HordijkKallenbergLP.Correspondence.HK8.proposition_4_core M β hβpos x y hxy φ u hφu
