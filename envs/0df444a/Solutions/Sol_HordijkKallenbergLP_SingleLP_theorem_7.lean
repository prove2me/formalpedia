-- Prove2me | solution 1 for HordijkKallenbergLP.SingleLP.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-13T03:22:02.114871+00:00
-- url     : https://prove2.me/submissions/b771ea39-d458-4c30-a864-6984e4a725f2

-- Complete checked reconstruction of the native extreme-LP average-optimal policy theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Mathlib


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

-- Begin RootAssembly
section ModuleScope_RootAssembly
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology
namespace HordijkKallenbergLP.SingleLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 7.** If the simplex method is used to solve the dual problem (3)–(5) and an optimal
solution `(x, y)` is obtained, then the policy `f^∞`, where `f(i) = a_i` such that `x_{i a_i} > 0`
for `i ∈ E_x = {i | Σ_a x_{ia} > 0}` and `y_{i a_i} > 0` for `i ∉ E_x`, is average optimal.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 357, Theorem 7.

**Formalization Note.** "The simplex method is used and an optimal solution is obtained" is
encoded as: `(x, y)` is an optimal solution of the dual program that is an extreme point of its
feasible set (a basic feasible solution, which is what the simplex method returns; the paper's
proof of Proposition 3 uses exactly this). Without extremality the statement is a different,
unproved claim. The conclusion holds for *every* `f` obeying the rule (Remark after Theorem 7:
"an arbitrary action"). Average optimality is Hordijk and Kallenberg's: `φ_i(f^∞) = φ_i` for all
`i`, against all history-dependent randomized policies. -/
theorem theorem_7 (M : StationaryMDP S A) [Nonempty S]
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hext : z ∈ Set.extremePoints ℝ (dualFeasible M β))
    (hopt : IsDualOptimal M β z)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (hsel : IsSelection M z.1 z.2 f hf) :
    IsAvgOptimal M (stationaryPolicy M f hf)  := by
  have _positive_beta := hβpos
  have _normalized_beta := hβsum
  obtain ⟨φ, u, hsh, harm, heq, hE, hclosed⟩ :=
    Proof.selected_structure M β z hext hopt f hf hsel
  exact Proof.optimal_of_structure M f hf (Ex M z.1) φ u hsh harm heq hE hclosed

end HordijkKallenbergLP.SingleLP
end ModuleScope_RootAssembly
-- End RootAssembly

-- Begin Solution
section ModuleScope_Solution
open MarkovDecisionProcesses HordijkKallenbergLP.SingleLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

theorem solution (M : StationaryMDP S A) [Nonempty S]
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hext : z ∈ Set.extremePoints ℝ (dualFeasible M β))
    (hopt : IsDualOptimal M β z)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (hsel : IsSelection M z.1 z.2 f hf) :
    IsAvgOptimal M (stationaryPolicy M f hf)  := by
  exact HordijkKallenbergLP.SingleLP.theorem_7 M β hβpos hβsum z hext hopt f hf hsel
end ModuleScope_Solution
-- End Solution
