-- Prove2me | solution 1 for KallenbergLP.Constrained.limitPoints_eq_polytope
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-13T00:42:49.381287+00:00
-- url     : https://prove2.me/submissions/dfae0512-9732-4152-ba41-cb0b6411def4

-- Complete checked reconstruction of the native Kallenberg occupation-polytope equality.
-- Licensed under Apache 2.0.
import Definitions.Def_KallenbergLP_Constrained_Frequencies


-- Begin Canonical

-- End Canonical

-- Begin PairAlgebra

open scoped BigOperators
open MarkovDecisionProcesses KallenbergLP.AverageLP

namespace KallenbergLP.Constrained.Proof

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

def stateMass (M : StationaryMDP S A) (v : Pair M → ℝ) (j : S) : ℝ :=
  ∑ p, if p.1.1 = j then v p else 0

def incomingMass (M : StationaryMDP S A) (v : Pair M → ℝ) (j : S) : ℝ :=
  ∑ p, v p * M.trans p.1.1 p.1.2 j

def balanceMass (M : StationaryMDP S A) (v : Pair M → ℝ) : S → ℝ :=
  stateMass M v - incomingMass M v

lemma stateMass_nonneg (M : StationaryMDP S A) {v : Pair M → ℝ}
    (hv : ∀ p, 0 ≤ v p) (j : S) : 0 ≤ stateMass M v j := by
  exact Finset.sum_nonneg fun p _ => by split_ifs; exact hv p; exact le_rfl

omit [DecidableEq S] in
lemma incomingMass_nonneg (M : StationaryMDP S A) {v : Pair M → ℝ}
    (hv : ∀ p, 0 ≤ v p) (j : S) : 0 ≤ incomingMass M v j := by
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hv p) (M.trans_nonneg _ _ _)

lemma sum_stateMass (M : StationaryMDP S A) (v : Pair M → ℝ) :
    ∑ j, stateMass M v j = ∑ p, v p := by
  simp only [stateMass]
  rw [Finset.sum_comm]
  simp

omit [DecidableEq S] in
lemma sum_incomingMass (M : StationaryMDP S A) (v : Pair M → ℝ) :
    ∑ j, incomingMass M v j = ∑ p, v p := by
  simp only [incomingMass]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, M.trans_sum, mul_one]

lemma balanceMass_native (M : StationaryMDP S A) (v : Pair M → ℝ) (j : S) :
    balanceMass M v j =
      ∑ p, ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * v p := by
  simp only [balanceMass, Pi.sub_apply, stateMass, incomingMass, sub_mul,
    Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp
  · apply Finset.sum_congr rfl
    intro p _
    ring

end KallenbergLP.Constrained.Proof
-- End PairAlgebra

-- Begin PairSums

open scoped BigOperators
open MarkovDecisionProcesses KallenbergLP.AverageLP

namespace KallenbergLP.Constrained.Proof

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

def pairEquiv (M : StationaryMDP S A) : Pair M ≃ Σ s, {a // a ∈ M.admissible s} where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun p := ⟨(p.1, p.2.1), p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq S] in
lemma sum_pair (M : StationaryMDP S A) (f : Pair M → ℝ) :
    ∑ p, f p = ∑ s, ∑ a : {a // a ∈ M.admissible s}, f ⟨(s, a), a.2⟩ := by
  have hh := Fintype.sum_equiv (pairEquiv M) f
    (fun p : Σ s, {a // a ∈ M.admissible s} => f ⟨(p.1, p.2), p.2.2⟩) (fun _ => rfl)
  simpa only [Fintype.sum_sigma] using hh

lemma stateMass_eq_sum (M : StationaryMDP S A) (v : Pair M → ℝ) (s : S) :
    stateMass M v s = ∑ a : {a // a ∈ M.admissible s}, v ⟨(s, a), a.2⟩ := by
  rw [stateMass, sum_pair]
  rw [Finset.sum_eq_single s]
  · simp
  · intro b _ hbs
    simp [hbs]
  · simp

omit [DecidableEq S] [DecidableEq A] in
lemma sum_admissible_subtype (M : StationaryMDP S A) (s : S) (f : A → ℝ) :
    ∑ a : {a // a ∈ M.admissible s}, f a = ∑ a ∈ M.admissible s, f a := by
  exact Finset.sum_coe_sort (M.admissible s) f

lemma stateMass_le_total (M : StationaryMDP S A) {v : Pair M → ℝ}
    (hv : ∀ p, 0 ≤ v p) (s : S) : stateMass M v s ≤ ∑ p, v p := by
  apply Finset.sum_le_sum
  intro p _
  split_ifs
  · exact le_rfl
  · exact hv p

lemma le_stateMass (M : StationaryMDP S A) {v : Pair M → ℝ}
    (hv : ∀ p, 0 ≤ v p) (p : Pair M) : v p ≤ stateMass M v p.1.1 := by
  have := Finset.single_le_sum (fun q (_ : q ∈ Finset.univ) =>
    show 0 ≤ if q.1.1 = p.1.1 then v q else 0 from by split_ifs; exact hv q; exact le_rfl)
    (Finset.mem_univ p)
  simpa [stateMass] using this

end KallenbergLP.Constrained.Proof
-- End PairSums

-- Begin OccupationBasic

open scoped BigOperators
open MarkovDecisionProcesses KallenbergLP.AverageLP

namespace KallenbergLP.Constrained.Proof

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : StationaryMDP S A}

omit [DecidableEq A] in
lemma occ_nonneg (R : AvgHRPolicy M) (k t : ℕ) (h : List (S × A)) (s : S) (p : Pair M) :
    0 ≤ occ R k t h s p := by
  induction k generalizing t h s with
  | zero =>
    simp only [occ]
    split_ifs
    · exact R.nonneg _ _ _ _
    · exact le_rfl
  | succ k ih =>
    exact Finset.sum_nonneg fun a _ =>
      mul_nonneg (R.nonneg _ _ _ _) (Finset.sum_nonneg fun j _ =>
        mul_nonneg (M.trans_nonneg _ _ _) (ih _ _ _))

lemma occ_sum (R : AvgHRPolicy M) (k t : ℕ) (h : List (S × A)) (s : S) :
    ∑ p, occ R k t h s p = 1 := by
  induction k generalizing t h s with
  | zero =>
    change stateMass M (fun p => R.q t h s p.1.2) s = 1
    rw [stateMass_eq_sum, sum_admissible_subtype]
    exact R.sum_one _ _ _
  | succ k ih =>
    simp only [occ]
    rw [Finset.sum_comm, ← R.sum_one t h s]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.mul_sum]
    have hh : (∑ p, ∑ j, M.trans s a j * occ R k (t + 1) (h ++ [(s, a)]) j p) = 1 := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, ih, mul_one]
      exact M.trans_sum _ _
    rw [hh, mul_one]

noncomputable def occupation (β : S → ℝ) (R : AvgHRPolicy M) (t : ℕ) (p : Pair M) : ℝ :=
  ∑ i, β i * prob R t i p

omit [DecidableEq A] in
lemma occupation_nonneg {β : S → ℝ} (hβ : ∀ i, 0 ≤ β i) (R : AvgHRPolicy M)
    (t : ℕ) (p : Pair M) : 0 ≤ occupation β R t p := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hβ i) (occ_nonneg R t 0 [] i p)

lemma occupation_sum {β : S → ℝ} (hβ : ∑ i, β i = 1) (R : AvgHRPolicy M) (t : ℕ) :
    ∑ p, occupation β R t p = 1 := by
  simp only [occupation, prob]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, occ_sum, mul_one]
  exact hβ

end KallenbergLP.Constrained.Proof
-- End OccupationBasic

-- Begin PairLinear

open scoped BigOperators
open MarkovDecisionProcesses KallenbergLP.AverageLP

namespace KallenbergLP.Constrained.Proof

variable {S A I : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

lemma stateMass_sum (M : StationaryMDP S A) (s : Finset I) (v : I → Pair M → ℝ) :
    stateMass M (fun p => ∑ i ∈ s, v i p) = fun j => ∑ i ∈ s, stateMass M (v i) j := by
  funext j
  simp only [stateMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp_all

lemma stateMass_smul (M : StationaryMDP S A) (c : ℝ) (v : Pair M → ℝ) :
    stateMass M (fun p => c * v p) = fun j => c * stateMass M v j := by
  funext j
  simp only [stateMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp

omit [DecidableEq S] in
lemma incomingMass_sum (M : StationaryMDP S A) (s : Finset I) (v : I → Pair M → ℝ) :
    incomingMass M (fun p => ∑ i ∈ s, v i p) =
      fun j => ∑ i ∈ s, incomingMass M (v i) j := by
  funext j
  simp only [incomingMass, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [DecidableEq S] in
lemma incomingMass_smul (M : StationaryMDP S A) (c : ℝ) (v : Pair M → ℝ) :
    incomingMass M (fun p => c * v p) = fun j => c * incomingMass M v j := by
  funext j
  simp only [incomingMass, Finset.mul_sum, mul_assoc]

def stateLinear (M : StationaryMDP S A) : (Pair M → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun := stateMass M
  map_add' v w := by
    ext j
    simp only [stateMass, Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp
  map_smul' c v := stateMass_smul M c v

def incomingLinear (M : StationaryMDP S A) : (Pair M → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun := incomingMass M
  map_add' v w := by
    ext j
    simp only [incomingMass, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c v := incomingMass_smul M c v

def balanceLinear (M : StationaryMDP S A) : (Pair M → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun := balanceMass M
  map_add' v w := by
    ext j
    simp only [balanceMass_native, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    ext j
    simp only [balanceMass_native, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring

end KallenbergLP.Constrained.Proof
-- End PairLinear

-- Begin OccupationBalance

open scoped BigOperators
open MarkovDecisionProcesses KallenbergLP.AverageLP

namespace KallenbergLP.Constrained.Proof

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : StationaryMDP S A}

omit [DecidableEq A] in
lemma occ_linear_succ {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : (Pair M → ℝ) →ₗ[ℝ] E) (R : AvgHRPolicy M)
    (k t : ℕ) (h : List (S × A)) (s : S) :
    L (fun p => occ R (k + 1) t h s p) =
      ∑ a ∈ M.admissible s, R.q t h s a •
        ∑ j, M.trans s a j • L (fun p => occ R k (t + 1) (h ++ [(s, a)]) j p) := by
  have heq : (fun p => occ R (k + 1) t h s p) =
      ∑ a ∈ M.admissible s, R.q t h s a •
        ∑ j, M.trans s a j • (fun p => occ R k (t + 1) (h ++ [(s, a)]) j p) := by
    ext p
    simp [occ, Finset.sum_apply]
  rw [heq]
  simp only [map_sum, map_smul]

lemma state_occ_zero (R : AvgHRPolicy M) (t : ℕ) (h : List (S × A)) (s j : S) :
    stateMass M (fun p => occ R 0 t h s p) j = if j = s then 1 else 0 := by
  rw [stateMass_eq_sum]
  by_cases hjs : j = s
  · subst j
    simp only [occ, if_true]
    rw [sum_admissible_subtype]
    exact R.sum_one _ _ _
  · simp [occ, hjs]

lemma incoming_occ_zero (R : AvgHRPolicy M) (t : ℕ) (h : List (S × A)) (s j : S) :
    incomingMass M (fun p => occ R 0 t h s p) j =
      ∑ a ∈ M.admissible s, R.q t h s a * M.trans s a j := by
  rw [incomingMass, sum_pair]
  rw [Finset.sum_eq_single s]
  · simpa only [occ, if_true] using sum_admissible_subtype M s
      (fun a => R.q t h s a * M.trans s a j)
  · intro b _ hbs
    simp [occ, hbs]
  · simp

lemma occ_state_next (R : AvgHRPolicy M) (k t : ℕ) (h : List (S × A)) (s : S) :
    stateMass M (fun p => occ R (k + 1) t h s p) =
      incomingMass M (fun p => occ R k t h s p) := by
  induction k generalizing t h s with
  | zero =>
    have hh := occ_linear_succ (stateLinear M) R 0 t h s
    change stateMass M (fun p => occ R (0 + 1) t h s p) = _ at hh
    rw [hh]
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, stateLinear,
      LinearMap.coe_mk, AddHom.coe_mk, state_occ_zero]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact (incoming_occ_zero R t h s j).symm
  | succ k ih =>
    change (stateLinear M) (fun p => occ R (k + 1 + 1) t h s p) =
      (incomingLinear M) (fun p => occ R (k + 1) t h s p)
    rw [occ_linear_succ, occ_linear_succ]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact ih _ _ _

lemma occupation_initial (β : S → ℝ) (R : AvgHRPolicy M) :
    stateMass M (occupation β R 0) = β := by
  change stateMass M (fun p => ∑ i, β i * occ R 0 0 [] i p) = β
  rw [stateMass_sum]
  simp_rw [stateMass_smul]
  ext j
  simp [state_occ_zero]

lemma occupation_next (β : S → ℝ) (R : AvgHRPolicy M) (t : ℕ) :
    stateMass M (occupation β R (t + 1)) = incomingMass M (occupation β R t) := by
  change stateMass M (fun p => ∑ i, β i * occ R (t + 1) 0 [] i p) =
    incomingMass M (fun p => ∑ i, β i * occ R t 0 [] i p)
  rw [stateMass_sum, incomingMass_sum]
  simp_rw [stateMass_smul, incomingMass_smul, occ_state_next]

end KallenbergLP.Constrained.Proof
-- End OccupationBalance

-- Begin FrequencyBalance

open scoped BigOperators
open MarkovDecisionProcesses KallenbergLP.AverageLP

namespace KallenbergLP.Constrained.Proof

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : StationaryMDP S A}

lemma cumulative_balance (β : S → ℝ) (R : AvgHRPolicy M) (n : ℕ) :
    balanceLinear M (∑ t ∈ Finset.range n, occupation β R t) =
      β - stateMass M (occupation β R n) := by
  induction n with
  | zero => simp [occupation_initial]
  | succ n ih =>
    rw [Finset.sum_range_succ, map_add, ih]
    ext j
    change (β j - stateMass M (occupation β R n) j) +
      (stateMass M (occupation β R n) j - incomingMass M (occupation β R n) j) = _
    rw [← occupation_next]
    simp only [Pi.sub_apply]
    ring

omit [DecidableEq A] in
lemma freq_vector (β : S → ℝ) (R : AvgHRPolicy M) (n : ℕ) :
    freq β R n = (n : ℝ)⁻¹ • ∑ t ∈ Finset.range n, occupation β R t := by
  ext p
  simp [freq, occupation, Finset.sum_apply]

omit [DecidableEq A] in
lemma freq_nonneg {β : S → ℝ} (hβ : ∀ i, 0 ≤ β i) (R : AvgHRPolicy M) (n : ℕ)
    (p : Pair M) : 0 ≤ freq β R n p := by
  rw [freq_vector]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
    (Finset.sum_nonneg fun t _ => occupation_nonneg hβ R t p)

lemma freq_balance (β : S → ℝ) (R : AvgHRPolicy M) (n : ℕ) :
    balanceMass M (freq β R n) =
      (n : ℝ)⁻¹ • (β - stateMass M (occupation β R n)) := by
  change balanceLinear M (freq β R n) = _
  rw [freq_vector, map_smul, cumulative_balance]

noncomputable def triangularOccupation (β : S → ℝ) (R : AvgHRPolicy M) (n : ℕ) : Pair M → ℝ :=
  (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, ∑ t ∈ Finset.range k, occupation β R t

omit [DecidableEq A] in
lemma triangular_nonneg {β : S → ℝ} (hβ : ∀ i, 0 ≤ β i) (R : AvgHRPolicy M) (n : ℕ)
    (p : Pair M) : 0 ≤ triangularOccupation β R n p := by
  simp only [triangularOccupation, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
    (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun t _ => occupation_nonneg hβ R t p)

lemma triangular_balance (β : S → ℝ) (R : AvgHRPolicy M) (n : ℕ) (hn : 0 < n) :
    balanceMass M (triangularOccupation β R n) = β - stateMass M (freq β R n) := by
  change balanceLinear M _ = _
  rw [triangularOccupation, map_smul, map_sum]
  simp_rw [cumulative_balance]
  rw [freq_vector]
  change (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, (β - stateMass M (occupation β R k))) =
    β - stateLinear M ((n : ℝ)⁻¹ • _)
  rw [map_smul, map_sum]
  ext j
  simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    stateLinear, LinearMap.coe_mk, AddHom.coe_mk]
  field_simp
  simp

end KallenbergLP.Constrained.Proof
-- End FrequencyBalance

-- Begin ConeReduction

open scoped BigOperators

namespace KallenbergLP.Constrained.Proof

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

end KallenbergLP.Constrained.Proof
-- End ConeReduction

-- Begin ConeClosed

open scoped BigOperators

namespace KallenbergLP.Constrained.Proof

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

end KallenbergLP.Constrained.Proof
-- End ConeClosed

-- Begin BalanceCone

open scoped BigOperators
open MarkovDecisionProcesses KallenbergLP.AverageLP

namespace KallenbergLP.Constrained.Proof

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

def balanceCone (M : StationaryMDP S A) : Set (S → ℝ) :=
  finiteCone (fun p : Pair M => fun j =>
    (if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j)

lemma balanceCone_closed (M : StationaryMDP S A) : IsClosed (balanceCone M) :=
  finiteCone_closed _

lemma mem_balanceCone (M : StationaryMDP S A) (z : S → ℝ) :
    z ∈ balanceCone M ↔ ∃ y : Pair M → ℝ, (∀ p, 0 ≤ y p) ∧ balanceMass M y = z := by
  have hh (y : Pair M → ℝ) : (∑ p : Pair M, y p •
      (fun j => (if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j)) =
      balanceMass M y := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, balanceMass_native]
    apply Finset.sum_congr rfl
    intro p _
    ring
  change (∃ y : Pair M → ℝ, (∀ p, 0 ≤ y p) ∧ _ = z) ↔ _
  simp_rw [hh]

end KallenbergLP.Constrained.Proof
-- End BalanceCone

-- Begin NativeNecessity

open scoped BigOperators
open MarkovDecisionProcesses KallenbergLP.AverageLP Filter

namespace KallenbergLP.Constrained.Proof

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : StationaryMDP S A}

lemma freq_balance_tendsto_zero {β : S → ℝ} (hβ0 : ∀ i, 0 ≤ β i)
    (hβ1 : ∑ i, β i = 1) (R : AvgHRPolicy M) (φ : ℕ → ℕ) (hφ : StrictMono φ) (j : S) :
    Tendsto (fun n => balanceMass M (freq β R (φ n)) j) atTop (nhds 0) := by
  have hinv : Tendsto (fun n => ((φ n : ℕ) : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  have hbound (n : ℕ) : |balanceMass M (freq β R (φ n)) j| ≤
      (φ n : ℝ)⁻¹ * (|β j| + 1) := by
    rw [freq_balance]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ (φ n : ℝ)⁻¹ by positivity)]
    apply mul_le_mul_of_nonneg_left _ (show (0 : ℝ) ≤ (φ n : ℝ)⁻¹ by positivity)
    have hm0 := stateMass_nonneg M (occupation_nonneg hβ0 R (φ n)) j
    have hm1 := stateMass_le_total M (occupation_nonneg hβ0 R (φ n)) j
    rw [occupation_sum hβ1] at hm1
    calc |β j - stateMass M (occupation β R (φ n)) j| ≤
        |β j| + |stateMass M (occupation β R (φ n)) j| := abs_sub _ _
      _ ≤ |β j| + 1 := by rw [abs_of_nonneg hm0]; linarith
  have hh := squeeze_zero (fun n => abs_nonneg _) hbound
    (by simpa only [zero_mul] using hinv.mul_const (|β j| + 1))
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hh

lemma limitPoint_feasible {β : S → ℝ} (hβ0 : ∀ i, 0 ≤ β i)
    (hβ1 : ∑ i, β i = 1) (R : AvgHRPolicy M) {x : Pair M → ℝ}
    (hx : x ∈ limitPoints β R) : ∃ y, IsFeasible477 M β x y := by
  obtain ⟨φ, hφ, hx⟩ := hx
  have hxn (p : Pair M) : 0 ≤ x p :=
    ge_of_tendsto ((continuous_apply p).tendsto x |>.comp hx)
      (Filter.Eventually.of_forall fun n => freq_nonneg hβ0 R (φ n) p)
  have hb : balanceMass M x = 0 := by
    have hh := (balanceLinear M).continuous_of_finiteDimensional.tendsto x |>.comp hx
    ext j
    exact tendsto_nhds_unique ((continuous_apply j).tendsto _ |>.comp hh)
      (freq_balance_tendsto_zero hβ0 hβ1 R φ hφ j)
  have htarget : Tendsto (fun n => β - stateMass M (freq β R (φ n))) atTop
      (nhds (β - stateMass M x)) :=
    tendsto_const_nhds.sub ((stateLinear M).continuous_of_finiteDimensional.tendsto x |>.comp hx)
  have hpos : ∀ᶠ n in atTop, 0 < φ n := hφ.tendsto_atTop.eventually (eventually_gt_atTop 0)
  have hc : β - stateMass M x ∈ balanceCone M :=
    (balanceCone_closed M).mem_of_tendsto htarget (hpos.mono fun n hn =>
      (mem_balanceCone M _).mpr ⟨triangularOccupation β R (φ n),
        triangular_nonneg hβ0 R (φ n), triangular_balance β R (φ n) hn⟩)
  obtain ⟨y, hy, heq⟩ := (mem_balanceCone M _).mp hc
  refine ⟨y, hxn, hy, ?_, ?_⟩
  · intro j
    simpa only [balanceMass_native, Pi.zero_apply] using congrFun hb j
  · intro j
    have hj := congrFun heq j
    rw [balanceMass_native] at hj
    change stateMass M x j + _ = β j
    simp only [Pi.sub_apply] at hj
    linarith

lemma native_necessity (M : StationaryMDP S A) (β : S → ℝ) (hβ0 : ∀ i, 0 ≤ β i)
    (hβ1 : ∑ i, β i = 1) : Lset M β (fun _ => True) ⊆ polytopeX M β := by
  rintro x ⟨R, _, hx⟩
  exact limitPoint_feasible hβ0 hβ1 R hx

end KallenbergLP.Constrained.Proof
-- End NativeNecessity

-- Begin FinitePush
open scoped BigOperators
namespace KallenbergLP.Constrained.Proof
variable {S : Type*} [Fintype S]
def pushMass (Q : S → S → ℝ) (v : S → ℝ) (j : S) : ℝ := ∑ i, v i * Q i j
lemma pushMass_zero (Q : S → S → ℝ) : pushMass Q 0 = 0 := by ext j; simp [pushMass]
lemma pushMass_add (Q : S → S → ℝ) (v w : S → ℝ) :
    pushMass Q (v+w) = pushMass Q v + pushMass Q w := by
  ext j; simp [pushMass, add_mul, Finset.sum_add_distrib]
lemma pushMass_smul (Q : S → S → ℝ) (c : ℝ) (v : S → ℝ) :
    pushMass Q (c • v) = c • pushMass Q v := by
  ext j; simp [pushMass, Finset.mul_sum, mul_assoc]
lemma pushMass_nonneg {Q : S → S → ℝ} (hQ : ∀ i j, 0 ≤ Q i j)
    {v : S → ℝ} (hv : ∀ i, 0 ≤ v i) : ∀ j, 0 ≤ pushMass Q v j :=
  fun j => Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (hQ i j))
lemma pushMass_mono {Q : S → S → ℝ} (hQ : ∀ i j, 0 ≤ Q i j)
    {v w : S → ℝ} (h : ∀ i, v i ≤ w i) : ∀ j, pushMass Q v j ≤ pushMass Q w j :=
  fun j => Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (h i) (hQ i j))
lemma pushMass_sum {J : Type*} (Q : S → S → ℝ) (F : Finset J) (v : J → S → ℝ) :
    pushMass Q (∑ t ∈ F, v t) = ∑ t ∈ F, pushMass Q (v t) := by
  ext j
  simp only [pushMass, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
lemma sum_pushMass (Q : S → S → ℝ) (v : S → ℝ) :
    ∑ j, pushMass Q v j = ∑ i, v i * ∑ j, Q i j := by
  simp only [pushMass, Finset.mul_sum]
  exact Finset.sum_comm
noncomputable def evolveMass (Q : S → S → ℝ) (β : S → ℝ) : ℕ → S → ℝ
  | 0 => β
  | n+1 => pushMass Q (evolveMass Q β n)
lemma evolveMass_nonneg {Q : S → S → ℝ} (hQ : ∀ i j, 0 ≤ Q i j)
    {β : S → ℝ} (hβ : ∀ i, 0 ≤ β i) (n : ℕ) : ∀ i, 0 ≤ evolveMass Q β n i := by
  induction n with
  | zero => exact hβ
  | succ n ih => exact pushMass_nonneg hQ ih
lemma evolveMass_prefix (Q : S → S → ℝ) (β : S → ℝ) (n : ℕ) :
    (∑ t ∈ Finset.range (n+1), evolveMass Q β t) =
      β + pushMass Q (∑ t ∈ Finset.range n, evolveMass Q β t) := by
  rw [Finset.sum_range_succ', pushMass_sum]
  simp only [evolveMass]
  exact add_comm _ _
lemma evolveMass_prefix_le {Q : S → S → ℝ} (hQ : ∀ i j, 0 ≤ Q i j)
    (β z : S → ℝ) (hz : ∀ i, 0 ≤ z i) (heq : β + pushMass Q z = z) (n : ℕ) :
    ∀ i, (∑ t ∈ Finset.range n, evolveMass Q β t) i ≤ z i := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    rw [evolveMass_prefix]
    intro i
    have hh := pushMass_mono hQ ih i
    have hi := congrFun heq i
    change β i + pushMass Q z i = z i at hi
    change β i + pushMass Q (∑ t ∈ Finset.range n, evolveMass Q β t) i ≤ z i
    linarith
end KallenbergLP.Constrained.Proof
-- End FinitePush

-- Begin StateAlgebra
open scoped BigOperators
open MarkovDecisionProcesses KallenbergLP.AverageLP
namespace KallenbergLP.Constrained.Proof
variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
def weightState (M : StationaryMDP S A) (h : S → ℝ) (v : Pair M → ℝ) (p : Pair M) : ℝ := h p.1.1 * v p
lemma stateMass_add (M : StationaryMDP S A) (v w : Pair M → ℝ) :
    stateMass M (v+w) = stateMass M v + stateMass M w := by
  ext j; simp only [stateMass, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _; split_ifs <;> simp
omit [DecidableEq S] in
lemma incomingMass_add (M : StationaryMDP S A) (v w : Pair M → ℝ) :
    incomingMass M (v+w) = incomingMass M v + incomingMass M w := by
  ext j; simp [incomingMass, add_mul, Finset.sum_add_distrib]
lemma stateMass_weightState (M : StationaryMDP S A) (h : S → ℝ) (v : Pair M → ℝ) (j : S) :
    stateMass M (weightState M h v) j = h j * stateMass M v j := by
  simp only [stateMass, weightState, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.1.1 = j
  · simp [hp]
  · simp [hp]
lemma stateMass_congr_on (M : StationaryMDP S A) {v w : Pair M → ℝ} (j : S)
    (h : ∀ p, p.1.1 = j → v p = w p) : stateMass M v j = stateMass M w j := by
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.1.1 = j
  · simp [hp, h p hp]
  · simp [hp]
def pairMatrix (M : StationaryMDP S A) (v : Pair M → ℝ) (i j : S) : ℝ :=
  ∑ p, if p.1.1 = i then v p * M.trans p.1.1 p.1.2 j else 0
lemma pairMatrix_nonneg (M : StationaryMDP S A) {v : Pair M → ℝ}
    (hv : ∀ p, 0 ≤ v p) (i j : S) : 0 ≤ pairMatrix M v i j := by
  apply Finset.sum_nonneg; intro p _; split_ifs
  · exact mul_nonneg (hv p) (M.trans_nonneg _ _ _)
  · exact le_rfl
lemma pairMatrix_row (M : StationaryMDP S A) (v : Pair M → ℝ) (i : S) :
    ∑ j, pairMatrix M v i j = stateMass M v i := by
  simp only [pairMatrix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.1.1 = i
  · simp [hp, ← Finset.mul_sum, M.trans_sum]
  · simp [hp]
lemma pushMass_pairMatrix (M : StationaryMDP S A) (v : Pair M → ℝ) (h : S → ℝ) :
    pushMass (pairMatrix M v) h = incomingMass M (weightState M h v) := by
  ext j
  simp only [pushMass, pairMatrix, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [incomingMass, weightState]
  apply Finset.sum_congr rfl
  intro p _
  simp only [mul_ite, mul_zero]
  simp [eq_comm, mul_assoc]
end KallenbergLP.Constrained.Proof
-- End StateAlgebra

-- Begin StationaryRule
open scoped BigOperators
open MarkovDecisionProcesses KallenbergLP.AverageLP
namespace KallenbergLP.Constrained.Proof
variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
noncomputable def postFallbackAction (M : StationaryMDP S A) (s : S) : A :=
  (M.admissible_nonempty s).choose
omit [DecidableEq S] [DecidableEq A] in
lemma postFallbackAction_mem (M : StationaryMDP S A) (s : S) : postFallbackAction M s ∈ M.admissible s :=
  (M.admissible_nonempty s).choose_spec
noncomputable def fallbackWeight (M : StationaryMDP S A) (p : Pair M) : ℝ :=
  if p.1.2 = postFallbackAction M p.1.1 then 1 else 0
omit [DecidableEq S] in
lemma fallbackWeight_nonneg (M : StationaryMDP S A) (p : Pair M) : 0 ≤ fallbackWeight M p := by
  unfold fallbackWeight; split_ifs <;> norm_num
lemma stateMass_fallbackWeight (M : StationaryMDP S A) (s : S) :
    stateMass M (fallbackWeight M) s = 1 := by
  let p : Pair M := ⟨(s, postFallbackAction M s), postFallbackAction_mem M s⟩
  rw [stateMass, Finset.sum_eq_single p]
  · simp [p, fallbackWeight]
  · intro q _ hqp
    by_cases hqs : q.1.1 = s
    · have hqa : q.1.2 ≠ postFallbackAction M s := by
        intro hh; apply hqp; apply Subtype.ext; exact Prod.ext hqs hh
      simp [hqs, fallbackWeight, hqa]
    · simp [hqs]
  · simp
noncomputable def stationaryWeight (M : StationaryMDP S A) (x : Pair M → ℝ) (p : Pair M) : ℝ :=
  if 0 < stateMass M x p.1.1 then x p / stateMass M x p.1.1 else fallbackWeight M p
lemma stationaryWeight_nonneg (M : StationaryMDP S A) {x : Pair M → ℝ}
    (hx : ∀ p, 0 ≤ x p) (p : Pair M) : 0 ≤ stationaryWeight M x p := by
  unfold stationaryWeight; split_ifs with h
  · exact div_nonneg (hx p) h.le
  · exact fallbackWeight_nonneg M p
lemma stateMass_stationaryWeight (M : StationaryMDP S A) (x : Pair M → ℝ) (s : S) :
    stateMass M (stationaryWeight M x) s = 1 := by
  by_cases h : 0 < stateMass M x s
  · calc
      _ = stateMass M (weightState M (fun s => (stateMass M x s)⁻¹) x) s := by
        apply stateMass_congr_on M s
        intro p hp
        simp [stationaryWeight, hp, h, weightState, div_eq_mul_inv, mul_comm]
      _ = 1 := by rw [stateMass_weightState]; exact inv_mul_cancel₀ h.ne'
  · calc
      _ = stateMass M (fallbackWeight M) s := by
        apply stateMass_congr_on M s
        intro p hp
        simp [stationaryWeight, hp, h]
      _ = 1 := stateMass_fallbackWeight M s
lemma weightState_stationaryWeight (M : StationaryMDP S A) {x : Pair M → ℝ}
    (hx : ∀ p, 0 ≤ x p) : weightState M (stateMass M x) (stationaryWeight M x) = x := by
  funext p
  have ha := stateMass_nonneg M hx p.1.1
  by_cases h : 0 < stateMass M x p.1.1
  · simp only [weightState, stationaryWeight, if_pos h]
    exact mul_div_cancel₀ (x p) h.ne'
  · have hz : stateMass M x p.1.1 = 0 := le_antisymm (le_of_not_gt h) ha
    have hxp : x p = 0 := le_antisymm ((le_stateMass M hx p).trans_eq hz) (hx p)
    simp [weightState, hz, hxp]
end KallenbergLP.Constrained.Proof
-- End StationaryRule

-- Begin SplitWeight
open scoped BigOperators
open MarkovDecisionProcesses KallenbergLP.AverageLP
namespace KallenbergLP.Constrained.Proof
variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
def totalState (M : StationaryMDP S A) (x y : Pair M → ℝ) : S → ℝ := stateMass M x + stateMass M y
noncomputable def transientWeight (M : StationaryMDP S A) (x y : Pair M → ℝ) (p : Pair M) : ℝ :=
  y p / totalState M x y p.1.1
noncomputable def killWeight (M : StationaryMDP S A) (x y : Pair M → ℝ) (s : S) : ℝ :=
  stateMass M x s / totalState M x y s
lemma totalState_nonneg (M : StationaryMDP S A) {x y : Pair M → ℝ}
    (hx : ∀ p, 0 ≤ x p) (hy : ∀ p, 0 ≤ y p) (s : S) : 0 ≤ totalState M x y s :=
  add_nonneg (stateMass_nonneg M hx s) (stateMass_nonneg M hy s)
lemma transientWeight_nonneg (M : StationaryMDP S A) {x y : Pair M → ℝ}
    (hx : ∀ p, 0 ≤ x p) (hy : ∀ p, 0 ≤ y p) (p : Pair M) : 0 ≤ transientWeight M x y p :=
  div_nonneg (hy p) (totalState_nonneg M hx hy p.1.1)
lemma killWeight_nonneg (M : StationaryMDP S A) {x y : Pair M → ℝ}
    (hx : ∀ p, 0 ≤ x p) (hy : ∀ p, 0 ≤ y p) (s : S) : 0 ≤ killWeight M x y s :=
  div_nonneg (stateMass_nonneg M hx s) (totalState_nonneg M hx hy s)
lemma totalState_zero (M : StationaryMDP S A) {x y : Pair M → ℝ}
    (hx : ∀ p, 0 ≤ x p) (hy : ∀ p, 0 ≤ y p) {s : S} (hz : totalState M x y s = 0) :
    stateMass M x s = 0 ∧ stateMass M y s = 0 := by
  have ha := stateMass_nonneg M hx s
  have hb := stateMass_nonneg M hy s
  change stateMass M x s + stateMass M y s = 0 at hz
  constructor <;> linarith
lemma totalState_mul_kill (M : StationaryMDP S A) {x y : Pair M → ℝ}
    (hx : ∀ p, 0 ≤ x p) (hy : ∀ p, 0 ≤ y p) (s : S) :
    totalState M x y s * killWeight M x y s = stateMass M x s := by
  by_cases hz : totalState M x y s = 0
  · simp [killWeight, hz, (totalState_zero M hx hy hz).1]
  · unfold killWeight
    field_simp
lemma weightState_transientWeight (M : StationaryMDP S A) {x y : Pair M → ℝ}
    (hx : ∀ p, 0 ≤ x p) (hy : ∀ p, 0 ≤ y p) :
    weightState M (totalState M x y) (transientWeight M x y) = y := by
  funext p
  by_cases hz : totalState M x y p.1.1 = 0
  · have hys := (totalState_zero M hx hy hz).2
    have hyp : y p = 0 := le_antisymm ((le_stateMass M hy p).trans_eq hys) (hy p)
    simp [weightState, transientWeight, hz, hyp]
  · unfold weightState transientWeight
    field_simp
lemma stateMass_transientWeight (M : StationaryMDP S A) (x y : Pair M → ℝ) (s : S) :
    stateMass M (transientWeight M x y) s = stateMass M y s / totalState M x y s := by
  have he : transientWeight M x y = weightState M (fun s => (totalState M x y s)⁻¹) y := by
    funext p; simp [transientWeight, weightState, div_eq_mul_inv, mul_comm]
  rw [he, stateMass_weightState]
  simp [div_eq_mul_inv, mul_comm]
lemma transient_kill_sum (M : StationaryMDP S A) (x y : Pair M → ℝ) {s : S}
    (hz : totalState M x y s ≠ 0) :
    stateMass M (transientWeight M x y) s + killWeight M x y s = 1 := by
  rw [stateMass_transientWeight]
  unfold killWeight
  rw [← add_div]
  have he : stateMass M y s + stateMass M x s = totalState M x y s := add_comm _ _
  rw [he, div_self hz]
end KallenbergLP.Constrained.Proof
-- End SplitWeight

-- Begin FeasibleSplit
open scoped BigOperators
open MarkovDecisionProcesses KallenbergLP.AverageLP
namespace KallenbergLP.Constrained.Proof
variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
lemma feasible_incoming_x (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hf : IsFeasible477 M β x y) : incomingMass M x = stateMass M x := by
  funext j
  have hh := hf.2.2.1 j
  rw [← balanceMass_native] at hh
  change stateMass M x j - incomingMass M x j = 0 at hh
  linarith
lemma feasible_balance_y (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hf : IsFeasible477 M β x y) : β + incomingMass M y = totalState M x y := by
  funext j
  have hh := hf.2.2.2 j
  rw [← balanceMass_native] at hh
  change stateMass M x j + (stateMass M y j - incomingMass M y j) = β j at hh
  change β j + incomingMass M y j = stateMass M x j + stateMass M y j
  linarith
lemma feasible_sum_x (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hf : IsFeasible477 M β x y) (hβ : ∑ j, β j = 1) : ∑ p, x p = 1 := by
  have hh := congrArg (fun v : S → ℝ => ∑ j, v j) (feasible_balance_y M hf)
  simp only [Pi.add_apply, totalState, Finset.sum_add_distrib, sum_stateMass, sum_incomingMass, hβ] at hh
  linarith
lemma feasible_push_transient (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hf : IsFeasible477 M β x y) :
    β + pushMass (pairMatrix M (transientWeight M x y)) (totalState M x y) = totalState M x y := by
  rw [pushMass_pairMatrix, weightState_transientWeight M hf.1 hf.2.1]
  exact feasible_balance_y M hf
lemma feasible_push_stationary (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hf : IsFeasible477 M β x y) :
    pushMass (pairMatrix M (stationaryWeight M x)) (stateMass M x) = stateMass M x := by
  rw [pushMass_pairMatrix, weightState_stationaryWeight M hf.1]
  exact feasible_incoming_x M hf
end KallenbergLP.Constrained.Proof
-- End FeasibleSplit

-- Begin FinitePost
open scoped BigOperators
namespace KallenbergLP.Constrained.Proof
variable {S : Type*} [Fintype S]
noncomputable def postMass (K : S → S → ℝ) (c : ℕ → S → ℝ) : ℕ → S → ℝ
  | 0 => 0
  | n+1 => pushMass K (postMass K c n + c n)
lemma postMass_nonneg {K : S → S → ℝ} (hK : ∀ i j, 0 ≤ K i j)
    {c : ℕ → S → ℝ} (hc : ∀ n i, 0 ≤ c n i) (n : ℕ) : ∀ i, 0 ≤ postMass K c n i := by
  induction n with
  | zero => intro i; exact le_rfl
  | succ n ih => exact pushMass_nonneg hK (fun i => add_nonneg (ih i) (hc n i))
lemma postMass_prefix (K : S → S → ℝ) (c : ℕ → S → ℝ) (n : ℕ) :
    (∑ t ∈ Finset.range (n+1), (postMass K c t + c t)) =
      pushMass K (∑ t ∈ Finset.range n, (postMass K c t + c t)) +
        ∑ t ∈ Finset.range (n+1), c t := by
  rw [Finset.sum_add_distrib, Finset.sum_range_succ' (fun t => postMass K c t)]
  simp only [postMass, add_zero]
  rw [pushMass_sum]
lemma postMass_prefix_le {K : S → S → ℝ} (hK : ∀ i j, 0 ≤ K i j)
    (c : ℕ → S → ℝ) (a : S → ℝ) (hKa : pushMass K a = a)
    (hc : ∀ n i, (∑ t ∈ Finset.range n, c t) i ≤ a i) (n : ℕ) :
    ∀ i, (∑ t ∈ Finset.range n, (postMass K c t + c t)) i ≤ (n:ℝ)*a i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [postMass_prefix]
    intro i
    have hh := pushMass_mono hK ih i
    have heq : pushMass K (fun i => (n:ℝ)*a i) i = (n:ℝ)*a i := by
      change pushMass K ((n:ℝ) • a) i = _
      rw [pushMass_smul, hKa]
      rfl
    rw [heq] at hh
    have ht := hc (n+1) i
    change pushMass K (∑ t ∈ Finset.range n, (postMass K c t + c t)) i +
      (∑ t ∈ Finset.range (n+1), c t) i ≤ (↑(n+1):ℝ)*a i
    push_cast
    linarith
end KallenbergLP.Constrained.Proof
-- End FinitePost

-- Begin SplitFlow
open scoped BigOperators
open MarkovDecisionProcesses KallenbergLP.AverageLP
namespace KallenbergLP.Constrained.Proof
variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
noncomputable def transientMass (M : StationaryMDP S A) (β : S → ℝ) (x y : Pair M → ℝ) : ℕ → S → ℝ :=
  evolveMass (pairMatrix M (transientWeight M x y)) β
noncomputable def absorbedMass (M : StationaryMDP S A) (β : S → ℝ) (x y : Pair M → ℝ) (n : ℕ) (s : S) : ℝ :=
  transientMass M β x y n s * killWeight M x y s
noncomputable def activeMass (M : StationaryMDP S A) (β : S → ℝ) (x y : Pair M → ℝ) : ℕ → S → ℝ :=
  postMass (pairMatrix M (stationaryWeight M x)) (absorbedMass M β x y)
noncomputable def constructedFlow (M : StationaryMDP S A) (β : S → ℝ) (x y : Pair M → ℝ) (n : ℕ) : Pair M → ℝ :=
  weightState M (transientMass M β x y n) (transientWeight M x y) +
    weightState M (activeMass M β x y n + absorbedMass M β x y n) (stationaryWeight M x)
lemma transientMass_nonneg (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hβ : ∀ s, 0 ≤ β s) (hf : IsFeasible477 M β x y) (n : ℕ) : ∀ s, 0 ≤ transientMass M β x y n s :=
  evolveMass_nonneg (pairMatrix_nonneg M (transientWeight_nonneg M hf.1 hf.2.1)) hβ n
lemma transientMass_prefix_le (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hf : IsFeasible477 M β x y) (n : ℕ) :
    ∀ s, (∑ t ∈ Finset.range n, transientMass M β x y t) s ≤ totalState M x y s :=
  evolveMass_prefix_le (pairMatrix_nonneg M (transientWeight_nonneg M hf.1 hf.2.1))
    β (totalState M x y) (totalState_nonneg M hf.1 hf.2.1) (feasible_push_transient M hf) n
lemma transientMass_le (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hβ : ∀ s, 0 ≤ β s) (hf : IsFeasible477 M β x y) (n : ℕ) (s : S) :
    transientMass M β x y n s ≤ totalState M x y s := by
  have hh := Finset.single_le_sum (s := Finset.range (n+1))
    (fun t _ => transientMass_nonneg M hβ hf t s) (Finset.mem_range.mpr (Nat.lt_succ_self n))
  exact hh.trans (by simpa only [Finset.sum_apply] using transientMass_prefix_le M hf (n+1) s)
lemma absorbedMass_nonneg (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hβ : ∀ s, 0 ≤ β s) (hf : IsFeasible477 M β x y) (n : ℕ) (s : S) :
    0 ≤ absorbedMass M β x y n s :=
  mul_nonneg (transientMass_nonneg M hβ hf n s) (killWeight_nonneg M hf.1 hf.2.1 s)
lemma absorbedMass_prefix_le (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hf : IsFeasible477 M β x y) (n : ℕ) (s : S) :
    (∑ t ∈ Finset.range n, absorbedMass M β x y t) s ≤ stateMass M x s := by
  simp only [Finset.sum_apply, absorbedMass, ← Finset.sum_mul]
  calc
    _ ≤ totalState M x y s * killWeight M x y s :=
      mul_le_mul_of_nonneg_right (by simpa only [Finset.sum_apply] using transientMass_prefix_le M hf n s)
        (killWeight_nonneg M hf.1 hf.2.1 s)
    _ = _ := totalState_mul_kill M hf.1 hf.2.1 s
lemma activeMass_nonneg (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hβ : ∀ s, 0 ≤ β s) (hf : IsFeasible477 M β x y) (n : ℕ) : ∀ s, 0 ≤ activeMass M β x y n s :=
  postMass_nonneg (pairMatrix_nonneg M (stationaryWeight_nonneg M hf.1)) (absorbedMass_nonneg M hβ hf) n
lemma constructedFlow_nonneg (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hβ : ∀ s, 0 ≤ β s) (hf : IsFeasible477 M β x y) (n : ℕ) (p : Pair M) :
    0 ≤ constructedFlow M β x y n p :=
  add_nonneg (mul_nonneg (transientMass_nonneg M hβ hf n p.1.1) (transientWeight_nonneg M hf.1 hf.2.1 p))
    (mul_nonneg (add_nonneg (activeMass_nonneg M hβ hf n p.1.1) (absorbedMass_nonneg M hβ hf n p.1.1))
      (stationaryWeight_nonneg M hf.1 p))
lemma stateMass_constructedFlow (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hβ : ∀ s, 0 ≤ β s) (hf : IsFeasible477 M β x y) (n : ℕ) :
    stateMass M (constructedFlow M β x y n) = transientMass M β x y n + activeMass M β x y n := by
  funext s
  simp only [constructedFlow, stateMass_add, Pi.add_apply, stateMass_weightState, stateMass_stationaryWeight, mul_one]
  by_cases hz : totalState M x y s = 0
  · have ht : transientMass M β x y n s = 0 :=
      le_antisymm ((transientMass_le M hβ hf n s).trans_eq hz) (transientMass_nonneg M hβ hf n s)
    simp [absorbedMass, ht]
  · have hh := transient_kill_sum M x y hz
    dsimp only [absorbedMass]
    calc
      _ = transientMass M β x y n s * (stateMass M (transientWeight M x y) s + killWeight M x y s) + activeMass M β x y n s := by ring
      _ = _ := by rw [hh, mul_one]
lemma incomingMass_constructedFlow (M : StationaryMDP S A) (β : S → ℝ) (x y : Pair M → ℝ) (n : ℕ) :
    incomingMass M (constructedFlow M β x y n) = transientMass M β x y (n+1) + activeMass M β x y (n+1) := by
  rw [constructedFlow, incomingMass_add, ← pushMass_pairMatrix, ← pushMass_pairMatrix]
  rfl
lemma constructedFlow_initial (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hβ : ∀ s, 0 ≤ β s) (hf : IsFeasible477 M β x y) :
    stateMass M (constructedFlow M β x y 0) = β := by
  rw [stateMass_constructedFlow M hβ hf]
  simp [transientMass, activeMass, evolveMass, postMass]
lemma constructedFlow_balance (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hβ : ∀ s, 0 ≤ β s) (hf : IsFeasible477 M β x y) (n : ℕ) :
    stateMass M (constructedFlow M β x y (n+1)) = incomingMass M (constructedFlow M β x y n) := by
  rw [stateMass_constructedFlow M hβ hf, incomingMass_constructedFlow]
end KallenbergLP.Constrained.Proof
-- End SplitFlow

-- Begin FiniteDeficit
open scoped BigOperators
open Filter Topology
namespace KallenbergLP.Constrained.Proof
variable {J : Type*} [Fintype J]
lemma finite_deficit_bound (x y a b : J → ℝ) (T : ℝ)
    (hy : ∀ j, 0 ≤ y j) (ha : ∀ j, 0 ≤ a j) (hay : ∀ j, a j ≤ y j)
    (hb : ∀ j, b j ≤ T*x j) (hm : ∑ j, (a j+b j) = T) (hx : ∑ j, x j = 1) (j : J) :
    |a j+b j-T*x j| ≤ ∑ i, y i := by
  classical
  let d := fun i => T*x i-b i
  have hd : ∀ i, 0 ≤ d i := fun i => sub_nonneg.mpr (hb i)
  have heq : ∑ i, d i = ∑ i, a i := by
    simp only [d, Finset.sum_sub_distrib, ← Finset.mul_sum, hx, mul_one]
    rw [Finset.sum_add_distrib] at hm
    linarith
  have hsum : ∑ i, a i ≤ ∑ i, y i := Finset.sum_le_sum (fun i _ => hay i)
  have haj : a j ≤ ∑ i, y i := (Finset.single_le_sum (fun i _ => ha i) (Finset.mem_univ j)).trans hsum
  have hdj : d j ≤ ∑ i, y i := (Finset.single_le_sum (fun i _ => hd i) (Finset.mem_univ j)).trans (heq.le.trans hsum)
  have hy0 : 0 ≤ ∑ i, y i := Finset.sum_nonneg (fun i _ => hy i)
  rw [abs_le]
  dsimp only [d] at hdj
  constructor <;> linarith [ha j, hd j]
omit [Fintype J] in
lemma frequency_limit_of_bound (v : ℕ → J → ℝ) (x : J → ℝ) (B : ℝ)
    (_hB : 0 ≤ B) (h : ∀ n j, |(∑ t ∈ Finset.range n, v t j)-(n:ℝ)*x j| ≤ B) :
    Tendsto (fun n : ℕ => fun j => (n:ℝ)⁻¹ * ∑ t ∈ Finset.range n, v t j) atTop (𝓝 x) := by
  apply tendsto_pi_nhds.mpr
  intro j
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun n : ℕ => B/(n:ℝ)) atTop (𝓝 0) := by
    have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa only [div_eq_mul_inv, mul_zero] using (tendsto_const_nhds.mul hi : Tendsto (fun n : ℕ => B*(n:ℝ)⁻¹) atTop (𝓝 (B*0)))
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _)) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  rw [Real.norm_eq_abs]
  have he : (n:ℝ)⁻¹*(∑ t ∈ Finset.range n, v t j)-x j =
      ((∑ t ∈ Finset.range n, v t j)-(n:ℝ)*x j)/(n:ℝ) := by field_simp
  rw [he, abs_div, abs_of_pos hn0]
  exact div_le_div_of_nonneg_right (h n j) hn0.le
end KallenbergLP.Constrained.Proof
-- End FiniteDeficit

-- Begin SplitBounds
open scoped BigOperators
open MarkovDecisionProcesses KallenbergLP.AverageLP Filter Topology
namespace KallenbergLP.Constrained.Proof
variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
lemma constructedFlow_mass (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hβ : ∀ s, 0 ≤ β s) (hβ1 : ∑ s, β s = 1) (hf : IsFeasible477 M β x y) (n : ℕ) :
    ∑ p, constructedFlow M β x y n p = 1 := by
  induction n with
  | zero =>
    rw [← sum_stateMass, constructedFlow_initial M hβ hf]
    exact hβ1
  | succ n ih =>
    rw [← sum_stateMass, constructedFlow_balance M hβ hf, sum_incomingMass]
    exact ih
lemma transientAction_prefix_le (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hf : IsFeasible477 M β x y) (n : ℕ) (p : Pair M) :
    (∑ t ∈ Finset.range n, weightState M (transientMass M β x y t) (transientWeight M x y) p) ≤ y p := by
  simp only [weightState, ← Finset.sum_mul]
  calc
    _ ≤ totalState M x y p.1.1 * transientWeight M x y p :=
      mul_le_mul_of_nonneg_right (by simpa only [Finset.sum_apply] using transientMass_prefix_le M hf n p.1.1)
        (transientWeight_nonneg M hf.1 hf.2.1 p)
    _ = _ := congrFun (weightState_transientWeight M hf.1 hf.2.1) p
lemma postAction_prefix_le (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hf : IsFeasible477 M β x y) (n : ℕ) (p : Pair M) :
    (∑ t ∈ Finset.range n, weightState M (activeMass M β x y t + absorbedMass M β x y t) (stationaryWeight M x) p) ≤ (n:ℝ)*x p := by
  have hh := postMass_prefix_le (pairMatrix_nonneg M (stationaryWeight_nonneg M hf.1))
    (absorbedMass M β x y) (stateMass M x) (feasible_push_stationary M hf)
    (absorbedMass_prefix_le M hf) n p.1.1
  simp only [weightState, Pi.add_apply, ← Finset.sum_mul]
  calc
    _ ≤ ((n:ℝ)*stateMass M x p.1.1)*stationaryWeight M x p :=
      mul_le_mul_of_nonneg_right (by simpa only [Finset.sum_apply, activeMass, Pi.add_apply] using hh)
        (stationaryWeight_nonneg M hf.1 p)
    _ = _ := by
      rw [mul_assoc]
      exact congrArg (fun z : ℝ => (n:ℝ)*z) (congrFun (weightState_stationaryWeight M hf.1) p)
lemma constructedFlow_error (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hβ : ∀ s, 0 ≤ β s) (hβ1 : ∑ s, β s = 1) (hf : IsFeasible477 M β x y) (n : ℕ) (p : Pair M) :
    |(∑ t ∈ Finset.range n, constructedFlow M β x y t p)-(n:ℝ)*x p| ≤ ∑ q, y q := by
  let a : Pair M → ℝ := fun q => ∑ t ∈ Finset.range n, weightState M (transientMass M β x y t) (transientWeight M x y) q
  let b : Pair M → ℝ := fun q => ∑ t ∈ Finset.range n, weightState M (activeMass M β x y t + absorbedMass M β x y t) (stationaryWeight M x) q
  have hab : ∀ q, a q+b q = ∑ t ∈ Finset.range n, constructedFlow M β x y t q := by
    intro q; simp only [a,b,constructedFlow,Pi.add_apply,Finset.sum_add_distrib]
  have hm : ∑ q, (a q+b q) = (n:ℝ) := by
    simp_rw [hab]
    rw [Finset.sum_comm]
    simp [constructedFlow_mass M hβ hβ1 hf]
  have hh := finite_deficit_bound x y a b (n:ℝ) hf.2.1
    (fun q => Finset.sum_nonneg (fun t _ => mul_nonneg (transientMass_nonneg M hβ hf t q.1.1) (transientWeight_nonneg M hf.1 hf.2.1 q)))
    (transientAction_prefix_le M hf n) (postAction_prefix_le M hf n) hm (feasible_sum_x M hf hβ1) p
  rw [hab] at hh
  exact hh
lemma constructedFlow_converges (M : StationaryMDP S A) {β : S → ℝ} {x y : Pair M → ℝ}
    (hβ : ∀ s, 0 ≤ β s) (hβ1 : ∑ s, β s = 1) (hf : IsFeasible477 M β x y) :
    Tendsto (fun n : ℕ => fun p => (n:ℝ)⁻¹ * ∑ t ∈ Finset.range n, constructedFlow M β x y t p) atTop (𝓝 x) :=
  frequency_limit_of_bound (constructedFlow M β x y) x (∑ p, y p)
    (Finset.sum_nonneg (fun p _ => hf.2.1 p)) (constructedFlow_error M hβ hβ1 hf)
end KallenbergLP.Constrained.Proof
-- End SplitBounds

-- Begin FlowPolicy

open scoped BigOperators
open MarkovDecisionProcesses KallenbergLP.AverageLP

namespace KallenbergLP.Constrained.Proof

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  (M : StationaryMDP S A)

noncomputable def fallbackAction (s : S) : A := Classical.choose (M.admissible_nonempty s)

omit [DecidableEq S] [DecidableEq A] in
lemma fallbackAction_mem (s : S) : fallbackAction M s ∈ M.admissible s :=
  Classical.choose_spec (M.admissible_nonempty s)

noncomputable def flowPolicy (v : ℕ → Pair M → ℝ) (hv : ∀ t p, 0 ≤ v t p) : AvgHRPolicy M where
  q t _ s a := if ha : a ∈ M.admissible s then
    if 0 < stateMass M (v t) s then v t ⟨(s, a), ha⟩ / stateMass M (v t) s
    else if a = fallbackAction M s then 1 else 0
    else 0
  nonneg t h s a := by
    split_ifs <;> first
    | exact div_nonneg (hv _ _) (stateMass_nonneg M (hv t) s)
    | positivity
  sum_one t h s := by
    by_cases hs : 0 < stateMass M (v t) s
    · simp only [hs, if_true]
      have hh : (∑ a ∈ M.admissible s,
          if ha : a ∈ M.admissible s then v t ⟨(s, a), ha⟩ / stateMass M (v t) s else 0) =
          (∑ a : {a // a ∈ M.admissible s}, v t ⟨(s, a), a.2⟩) / stateMass M (v t) s := by
        rw [Finset.sum_div]
        rw [← Finset.sum_attach]
        simp
      rw [hh, ← stateMass_eq_sum, div_self hs.ne']
    · simp only [hs, if_false]
      have hm := fallbackAction_mem M s
      simp [hm]

lemma flowPolicy_markov (v : ℕ → Pair M → ℝ) (hv : ∀ t p, 0 ≤ v t p) :
    IsMarkov (flowPolicy M v hv) := by
  intro t h h' s a ha
  rfl

lemma flowPolicy_action (v : ℕ → Pair M → ℝ) (hv : ∀ t p, 0 ≤ v t p)
    (t : ℕ) (h : List (S × A)) (p : Pair M) :
    stateMass M (v t) p.1.1 * (flowPolicy M v hv).q t h p.1.1 p.1.2 = v t p := by
  simp only [flowPolicy, p.2, dite_true]
  by_cases hp : 0 < stateMass M (v t) p.1.1
  · rw [if_pos hp]
    exact mul_div_cancel₀ _ hp.ne'
  · rw [if_neg hp]
    have hz : stateMass M (v t) p.1.1 = 0 :=
      le_antisymm (le_of_not_gt hp) (stateMass_nonneg M (hv t) _)
    have hvp : v t p = 0 := le_antisymm ((le_stateMass M (hv t) p).trans_eq hz) (hv t p)
    simp [hz, hvp]

end KallenbergLP.Constrained.Proof
-- End FlowPolicy

-- Begin MarkovTransport

open scoped BigOperators
open MarkovDecisionProcesses KallenbergLP.AverageLP

namespace KallenbergLP.Constrained.Proof

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : StationaryMDP S A}

omit [DecidableEq A] in
lemma occ_history (R : AvgHRPolicy M) (hR : IsMarkov R) (k t : ℕ)
    (h h' : List (S × A)) (s : S) (p : Pair M) :
    occ R k t h s p = occ R k t h' s p := by
  induction k generalizing t h h' s with
  | zero =>
    simp only [occ]
    split_ifs with hs
    · exact hR t h h' s p.1.2 (hs ▸ p.2)
    · rfl
  | succ k ih =>
    simp only [occ]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hR t h h' s a ha]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact ih _ _ _ _

omit [DecidableEq S] in
lemma pair_expectation (μ : S → ℝ) (q g : S → A → ℝ) :
    (∑ s, μ s * ∑ a ∈ M.admissible s, q s a * g s a) =
      ∑ p : Pair M, μ p.1.1 * q p.1.1 p.1.2 * g p.1.1 p.1.2 := by
  rw [sum_pair]
  apply Finset.sum_congr rfl
  intro s _
  change μ s * (∑ a ∈ M.admissible s, q s a * g s a) =
    ∑ a : {a // a ∈ M.admissible s}, μ s * q s a * g s a
  rw [sum_admissible_subtype M s (fun a => μ s * q s a * g s a), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

omit [DecidableEq S] in
lemma transport_expectation (μ : S → ℝ) (q : S → A → ℝ) (v : Pair M → ℝ)
    (hv : ∀ p, μ p.1.1 * q p.1.1 p.1.2 = v p) (f : S → ℝ) :
    (∑ s, μ s * ∑ a ∈ M.admissible s, q s a * ∑ j, M.trans s a j * f j) =
      ∑ j, incomingMass M v j * f j := by
  rw [pair_expectation]
  simp_rw [hv, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  rfl

lemma markov_flow_law (R : AvgHRPolicy M) (hR : IsMarkov R)
    (μ : ℕ → S → ℝ) (v : ℕ → Pair M → ℝ)
    (hact : ∀ t p, μ t p.1.1 * R.q t [] p.1.1 p.1.2 = v t p)
    (hnext : ∀ t, μ (t + 1) = incomingMass M (v t))
    (k t : ℕ) (h : List (S × A)) (p : Pair M) :
    ∑ s, μ t s * occ R k t h s p = v (t + k) p := by
  induction k generalizing t h with
  | zero =>
    simp only [occ, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    rw [hR t h [] _ _ p.2]
    simpa only [Nat.add_zero] using hact t p
  | succ k ih =>
    have heq : ∀ s, occ R (k + 1) t h s p =
        ∑ a ∈ M.admissible s, R.q t [] s a *
          ∑ j, M.trans s a j * occ R k (t + 1) [] j p := by
      intro s
      simp only [occ]
      apply Finset.sum_congr rfl
      intro a ha
      rw [hR t h [] s a ha]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [occ_history R hR k (t + 1) (h ++ [(s, a)]) [] j p]
    simp_rw [heq]
    rw [transport_expectation _ _ _ (hact t), ← hnext, ih]
    congr 1
    omega

end KallenbergLP.Constrained.Proof
-- End MarkovTransport

-- Begin FlowRealization

open scoped BigOperators
open MarkovDecisionProcesses KallenbergLP.AverageLP

namespace KallenbergLP.Constrained.Proof

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : StationaryMDP S A}

lemma realize_flow (β : S → ℝ) (v : ℕ → Pair M → ℝ)
    (hv : ∀ t p, 0 ≤ v t p) (hinit : stateMass M (v 0) = β)
    (hnext : ∀ t, stateMass M (v (t + 1)) = incomingMass M (v t)) :
    ∃ R : AvgHRPolicy M, ∀ t p, (∑ i, β i * prob R t i p) = v t p := by
  refine ⟨flowPolicy M v hv, ?_⟩
  intro t p
  have hh := markov_flow_law (flowPolicy M v hv) (flowPolicy_markov M v hv)
    (fun t => stateMass M (v t)) v (fun t p => flowPolicy_action M v hv t [] p)
    hnext t 0 [] p
  simpa only [hinit, Nat.zero_add, prob] using hh

end KallenbergLP.Constrained.Proof
-- End FlowRealization

-- Begin NativeSufficiency

open scoped BigOperators
open MarkovDecisionProcesses KallenbergLP.AverageLP Filter

namespace KallenbergLP.Constrained.Proof

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

lemma native_sufficiency (M : StationaryMDP S A) (β : S → ℝ)
    (hβ0 : ∀ i, 0 ≤ β i) (hβ1 : ∑ i, β i = 1) :
    polytopeX M β ⊆ Lset M β (fun _ => True) := by
  rintro x ⟨y, hf⟩
  obtain ⟨R, hR⟩ := realize_flow β (constructedFlow M β x y)
    (constructedFlow_nonneg M hβ0 hf) (constructedFlow_initial M hβ0 hf)
    (constructedFlow_balance M hβ0 hf)
  refine ⟨R, trivial, id, strictMono_id, ?_⟩
  have heq : (fun n => freq β R n) =
      (fun n : ℕ => fun p => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, constructedFlow M β x y t p) := by
    funext n p
    simp only [freq, hR]
  change Tendsto (fun n => freq β R n) atTop (nhds x)
  rw [heq]
  exact constructedFlow_converges M hβ0 hβ1 hf

end KallenbergLP.Constrained.Proof
-- End NativeSufficiency

-- Begin RootAssembly

namespace KallenbergLP.Constrained

open MarkovDecisionProcesses

/-- Kallenberg (1983), Theorem 4.7.2, p. 138: `L = X`. The set of all limit points of the expected
state-action frequencies, over all (history-dependent, randomized) policies, equals the polytope
`X` of (4.7.8). -/
theorem limitPoints_eq_polytope {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (β : S → ℝ) (hβ0 : ∀ j, 0 ≤ β j)
    (hβ1 : ∑ j, β j = 1) :
    Lset M β (fun _ => True) = polytopeX M β := by
  exact Set.Subset.antisymm (Proof.native_necessity M β hβ0 hβ1)
    (Proof.native_sufficiency M β hβ0 hβ1)

end KallenbergLP.Constrained
-- End RootAssembly

-- Begin Solution

open MarkovDecisionProcesses KallenbergLP.Constrained

theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (β : S → ℝ) (hβ0 : ∀ j, 0 ≤ β j)
    (hβ1 : ∑ j, β j = 1) :
    Lset M β (fun _ => True) = polytopeX M β :=
  limitPoints_eq_polytope M β hβ0 hβ1
-- End Solution
