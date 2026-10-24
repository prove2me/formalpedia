-- Prove2me | solution 1 for KVVMatching.UpperBound.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T19:56:09.19918+00:00
-- url     : https://prove2.me/submissions/52c0d555-bc08-46ca-ab0e-21f222fe8a7d

import Init
import Mathlib
import Definitions.Def_KVVMatching_UpperBound_RandomValue
import Definitions.Def_KVVMatching_UpperBound_Triangular

open Finset
noncomputable section
namespace UniformDeletion
variable {X : Type*} [DecidableEq X]
lemma erase_counting (s : Finset X) (k : ℕ) (f : Finset X → ℝ) :
    (∑ E ∈ s.powersetCard (k+1), ∑ r ∈ E, f (E.erase r)) =
      (s.card-k : ℕ) * ∑ T ∈ s.powersetCard k, f T := by
  classical
  rw [Finset.sum_sigma']
  have hbij : (∑ p ∈ (s.powersetCard (k+1)).sigma (fun E => E), f (p.1.erase p.2)) =
      ∑ q ∈ (s.powersetCard k).sigma (fun T => s \ T), f q.1 := by
    apply Finset.sum_bij (fun p _ => ⟨p.1.erase p.2,p.2⟩)
    · intro p hp
      obtain ⟨hE,hr⟩ := mem_sigma.mp hp
      obtain ⟨hEs,hEc⟩ := mem_powersetCard.mp hE
      apply mem_sigma.mpr
      refine ⟨mem_powersetCard.mpr ⟨(erase_subset _ _).trans hEs,?_⟩,?_⟩
      · rw [card_erase_of_mem hr,hEc]; omega
      · exact mem_sdiff.mpr ⟨hEs hr,notMem_erase _ _⟩
    · intro p hp q hq heq
      have h1 : p.1.erase p.2 = q.1.erase q.2 := congrArg Sigma.fst heq
      have h2 : p.2 = q.2 := eq_of_heq (Sigma.mk.inj heq).2
      have hp2 := (mem_sigma.mp hp).2
      have hq2 := (mem_sigma.mp hq).2
      have hE : p.1 = q.1 := by
        rw [← insert_erase hp2,← insert_erase hq2,h1,h2]
      cases p; cases q; simp_all
    · intro q hq
      obtain ⟨hT,hr⟩ := mem_sigma.mp hq
      obtain ⟨hTs,hTc⟩ := mem_powersetCard.mp hT
      obtain ⟨hrs,hrT⟩ := mem_sdiff.mp hr
      refine ⟨⟨insert q.2 q.1,q.2⟩,mem_sigma.mpr ⟨?_,mem_insert_self _ _⟩,?_⟩
      · exact mem_powersetCard.mpr ⟨insert_subset hrs hTs,by rw [card_insert_of_notMem hrT,hTc]⟩
      · simp [erase_insert hrT]
    · intro p hp
      rfl
  rw [hbij, Finset.sum_sigma]
  simp only [sum_const, nsmul_eq_mul]
  rw [mul_sum]
  apply sum_congr rfl
  intro T hT
  rw [card_sdiff_of_subset (mem_powersetCard.mp hT).1,(mem_powersetCard.mp hT).2]
end UniformDeletion

open Finset
noncomputable section
namespace UniformDeletion
variable {X : Type*} [DecidableEq X]
lemma boundary_counting (s : Finset X) (z : X) (hz : z ∈ s) (k : ℕ)
    (f : Finset X → ℝ) :
    (∑ T ∈ s.powersetCard (k+1), f (T.erase z)) =
      (∑ T ∈ (s.erase z).powersetCard (k+1), f T) +
      ∑ T ∈ (s.erase z).powersetCard k, f T := by
  classical
  conv_lhs => rw [← insert_erase hz, powersetCard_succ_insert (notMem_erase z s)]
  rw [sum_union]
  · congr 1
    · apply sum_congr rfl
      intro T hT
      rw [erase_eq_of_notMem]
      exact fun h => (notMem_erase z s) ((mem_powersetCard.mp hT).1 h)
    · rw [sum_image]
      · apply sum_congr rfl
        intro T hT
        rw [erase_insert]
        exact fun h => (notMem_erase z s) ((mem_powersetCard.mp hT).1 h)
      · intro T hT U hU heq
        have hTz : z ∉ T := fun h => (notMem_erase z s) ((mem_powersetCard.mp hT).1 h)
        have hUz : z ∉ U := fun h => (notMem_erase z s) ((mem_powersetCard.mp hU).1 h)
        simpa [erase_insert hTz, erase_insert hUz] using congrArg (fun E => E.erase z) heq
  · apply disjoint_left.mpr
    intro T hT hT'
    obtain ⟨U,hU,rfl⟩ := mem_image.mp hT'
    exact (notMem_erase z s) ((mem_powersetCard.mp hT).1 (mem_insert_self _ _))
end UniformDeletion

open Finset
noncomputable section
namespace KVVMatching.UpperBound.CountProcess
lemma locality {n : ℕ} (t : ℕ) (S T : Finset (Fin n))
    (h : ∀ r : Fin n, r.val < t → (r ∈ S ↔ r ∈ T)) :
    randomValueAux (upperTriangular n) t S = randomValueAux (upperTriangular n) t T := by
  classical
  induction t generalizing S T with
  | zero => rfl
  | succ t ih =>
    by_cases ht : t < n
    · have he : eligibleRows (upperTriangular n) S ⟨t,ht⟩ =
          eligibleRows (upperTriangular n) T ⟨t,ht⟩ := by
        ext r
        simp only [eligibleRows,mem_filter,mem_univ,true_and,upperTriangular,Set.mem_setOf_eq]
        constructor <;> rintro ⟨hr,hs⟩
        · exact ⟨hr,fun hh => hs ((h r (by change r.val ≤ t at hr; omega)).mpr hh)⟩
        · exact ⟨hr,fun hh => hs ((h r (by change r.val ≤ t at hr; omega)).mp hh)⟩
      simp only [randomValueAux,dif_pos ht,he]
      split_ifs
      · congr 1
        congr 1
        apply sum_congr rfl
        intro r hr
        apply ih
        intro q hq
        simp only [mem_insert]
        rw [h q (by omega)]
      · apply ih
        intro r hr
        exact h r (by omega)
    · simp only [randomValueAux,dif_neg ht]

def activeRows (n t : ℕ) : Finset (Fin n) := univ.filter (fun r => r.val < t)
def remainingValue {n : ℕ} (t : ℕ) (E : Finset (Fin n)) : ℝ :=
  randomValueAux (upperTriangular n) t (univ \ E)

lemma eligible_complement {n t : ℕ} (ht : t < n) (E : Finset (Fin n))
    (hE : E ⊆ activeRows n (t+1)) :
    eligibleRows (upperTriangular n) (univ \ E) ⟨t,ht⟩ = E := by
  classical
  ext r
  simp only [eligibleRows,mem_filter,mem_univ,true_and,upperTriangular,Set.mem_setOf_eq,
    mem_sdiff,not_and,true_implies,not_not]
  constructor
  · exact And.right
  · intro hr
    exact ⟨by have := (mem_filter.mp (hE hr)).2; change r.val ≤ t; omega,hr⟩

lemma remaining_next {n t : ℕ} (ht : t < n) (E : Finset (Fin n))
    (hE : E ⊆ activeRows n (t+1)) (hne : E.Nonempty) :
    remainingValue (t+1) E = 1 + (∑ r ∈ E,
      remainingValue t ((E.erase r).erase ⟨t,ht⟩)) / (E.card : ℝ) := by
  classical
  unfold remainingValue
  rw [randomValueAux,dif_pos ht,eligible_complement ht E hE,if_pos hne]
  congr 1
  congr 1
  apply sum_congr rfl
  intro r hr
  apply locality
  intro q hq
  have hqt : q ≠ ⟨t,ht⟩ := by intro he; subst q; simp at hq
  simp only [mem_sdiff,mem_erase,mem_insert,mem_univ,true_and,hqt,true_and]
  tauto

lemma remaining_empty {n : ℕ} (t : ℕ) : remainingValue (n:=n) t ∅ = 0 := by
  classical
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases ht : t < n
    · have he : eligibleRows (upperTriangular n) (univ : Finset (Fin n)) ⟨t,ht⟩ = ∅ := by
        ext r; simp [eligibleRows]
      simpa [remainingValue,randomValueAux,ht,he] using ih
    · simp [remainingValue,randomValueAux,ht]
end KVVMatching.UpperBound.CountProcess

open Finset
noncomputable section
namespace KVVMatching.UpperBound.CountProcess
lemma active_erase {n t : ℕ} (ht : t < n) :
    (activeRows n (t+1)).erase ⟨t,ht⟩ = activeRows n t := by
  classical
  ext r
  simp only [activeRows,mem_erase,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨hne,hr⟩
    have : r.val ≠ t := by intro he; apply hne; exact Fin.ext he
    omega
  · intro hr
    exact ⟨by intro he; subst r; simp at hr,by omega⟩
lemma active_card {n t : ℕ} (ht : t ≤ n) : (activeRows n t).card = t := by
  classical
  have he : activeRows n t = (Finset.univ : Finset (Fin t)).image
      (fun r => (⟨r.val,lt_of_lt_of_le r.isLt ht⟩ : Fin n)) := by
    ext r
    simp only [activeRows,mem_filter,mem_univ,true_and,mem_image]
    constructor
    · intro hr
      exact ⟨⟨r.val,hr⟩,rfl⟩
    · rintro ⟨s,hs⟩
      have := congrArg Fin.val hs
      simpa [← this] using s.isLt
  rw [he,card_image_of_injective]
  · simp
  · intro a b heq
    exact Fin.ext (congrArg (Fin.val (n:=n)) heq)

def aggregate (n t k : ℕ) : ℝ :=
  ∑ E ∈ (activeRows n t).powersetCard k, remainingValue t E

lemma aggregate_zero (n t : ℕ) : aggregate n t 0 = 0 := by
  simp [aggregate,remaining_empty]
lemma aggregate_time_zero (n k : ℕ) : aggregate n 0 k = 0 := by
  simp [aggregate,remainingValue,randomValueAux]

lemma aggregate_step {n t k : ℕ} (ht : t < n) :
    aggregate n (t+1) (k+1) = ((t+1).choose (k+1) : ℝ) +
      ((t+1-k : ℕ) : ℝ) / (k+1) *
        (∑ T ∈ (activeRows n (t+1)).powersetCard k,
          remainingValue t (T.erase ⟨t,ht⟩)) := by
  classical
  unfold aggregate
  have hs : (∑ E ∈ (activeRows n (t+1)).powersetCard (k+1), remainingValue (t+1) E) =
      ∑ E ∈ (activeRows n (t+1)).powersetCard (k+1),
        (1 + (∑ r ∈ E, remainingValue t ((E.erase r).erase ⟨t,ht⟩)) / (k+1)) := by
    apply sum_congr rfl
    intro E hE
    obtain ⟨hEs,hEc⟩ := mem_powersetCard.mp hE
    have hne : E.Nonempty := card_pos.mp (by omega)
    rw [remaining_next ht E hEs hne,hEc]
    simp
  rw [hs,sum_add_distrib,← sum_div,UniformDeletion.erase_counting
    (activeRows n (t+1)) k (fun T => remainingValue t (T.erase ⟨t,ht⟩))]
  simp only [sum_const,card_powersetCard,nsmul_eq_mul,mul_one,active_card (by omega : t+1 ≤ n)]
  ring

lemma aggregate_one {n t : ℕ} (ht : t < n) : aggregate n (t+1) 1 = t+1 := by
  rw [show 1=0+1 from rfl,aggregate_step ht]
  simp [remaining_empty]

lemma aggregate_two_step {n t k : ℕ} (ht : t < n) :
    aggregate n (t+1) (k+2) = ((t+1).choose (k+2) : ℝ) +
      ((t-k : ℕ) : ℝ) / (k+2) * (aggregate n t (k+1) + aggregate n t k) := by
  have hz : (⟨t,ht⟩ : Fin n) ∈ activeRows n (t+1) := by simp [activeRows]
  rw [show k+2=(k+1)+1 by omega,aggregate_step ht,
    UniformDeletion.boundary_counting _ _ hz k (remainingValue t),active_erase ht]
  simp only [aggregate,Nat.add_sub_add_right,Nat.cast_add,Nat.cast_one]
  congr 2 <;> ring

end KVVMatching.UpperBound.CountProcess

open Finset
noncomputable section
namespace KVVMatching.UpperBound.CountProcess
/-- The sum of expected matching sizes over all k-subsets of the active t rows.
    Dividing by t.choose k gives the uniform-subset expectation when k≤t. -/
def countTotal : ℕ → ℕ → ℝ
  | 0, _ => 0
  | t+1, 0 => 0
  | t+1, 1 => t+1
  | t+1, k+2 => ((t+1).choose (k+2) : ℝ) +
      ((t-k : ℕ) : ℝ) / (k+2) * (countTotal t (k+1) + countTotal t k)

lemma aggregate_eq_total (n t k : ℕ) (ht : t ≤ n) : aggregate n t k = countTotal t k := by
  induction t generalizing k with
  | zero => exact aggregate_time_zero n k
  | succ t ih =>
    cases k with
    | zero => exact aggregate_zero n (t+1)
    | succ k =>
      cases k with
      | zero => exact aggregate_one (by omega)
      | succ k =>
        rw [show k+1+1=k+2 by omega,aggregate_two_step (by omega),countTotal,
          ih (k+1) (by omega),ih k (by omega)]

/-- Exact finite recurrence for the platform's RANDOM value on the complete
    upper-triangular graph. The asymptotic limit is a separate obligation. -/
theorem randomValue_eq_countTotal (n : ℕ) :
    randomValue (upperTriangular n) = countTotal n n := by
  have h := aggregate_eq_total n n n le_rfl
  have he : activeRows n n = univ := by ext r; simp [activeRows]
  have hc : (univ : Finset (Fin n)).card = n := by simp
  have hp : (univ : Finset (Fin n)).powersetCard n = {univ} := by
    simpa only [hc] using powersetCard_self (univ : Finset (Fin n))
  simpa only [aggregate,he,hp,sum_singleton,remainingValue,sdiff_self,Finset.bot_eq_empty,randomValue] using h
end KVVMatching.UpperBound.CountProcess

namespace KVVMatching.UpperBound.CountProcess
/-- Expected number of future matches when the k eligible rows are uniform
    among t currently active rows. -/
noncomputable def countValue : ℕ → ℕ → ℝ
  | 0, _ => 0
  | t+1, 0 => 0
  | t+1, 1 => 1
  | t+1, k+2 => 1 + ((k+1 : ℕ) : ℝ) / (t+1) * countValue t k +
      ((t-k : ℕ) : ℝ) / (t+1) * countValue t (k+1)

lemma total_eq_countValue (t k : ℕ) (hk : k ≤ t) :
    countTotal t k = (t.choose k : ℝ) * countValue t k := by
  induction t generalizing k with
  | zero => simp [countTotal,countValue]
  | succ t ih =>
    cases k with
    | zero => simp [countTotal,countValue]
    | succ k =>
      cases k with
      | zero => simp [countTotal,countValue]
      | succ k =>
        have hk1 : k+1 ≤ t := by omega
        have hk0 : k ≤ t := by omega
        have hchoose1 : ((t+1 : ℕ) : ℝ) * (t.choose (k+1) : ℝ) =
            ((t+1).choose (k+2) : ℝ) * (k+2) := by
          exact_mod_cast Nat.add_one_mul_choose_eq t (k+1)
        have hchoose2 : (t.choose (k+1) : ℝ) * (k+1) =
            (t.choose k : ℝ) * ((t-k : ℕ) : ℝ) := by
          exact_mod_cast Nat.choose_succ_right_eq t k
        push_cast at hchoose1
        have htpos : (t+1 : ℝ) ≠ 0 := by positivity
        have hkpos : (k+2 : ℝ) ≠ 0 := by positivity
        have hcoef1 : ((t-k : ℕ) : ℝ) / (k+2) * (t.choose (k+1) : ℝ) =
            ((t+1).choose (k+2) : ℝ) * (((t-k : ℕ) : ℝ) / (t+1)) := by
          field_simp [htpos,hkpos]
          nlinarith [congrArg (fun z : ℝ => z * ((t-k : ℕ) : ℝ)) hchoose1]
        have hcoef2 : ((t-k : ℕ) : ℝ) / (k+2) * (t.choose k : ℝ) =
            ((t+1).choose (k+2) : ℝ) * ((k+1 : ℝ) / (t+1)) := by
          field_simp [htpos,hkpos]
          nlinarith [congrArg (fun z : ℝ => z * (k+1)) hchoose1,
            congrArg (fun z : ℝ => z * (t+1)) hchoose2]
        simp only [countTotal,countValue,ih (k+1) hk1,ih k hk0]
        rw [mul_add,← mul_assoc,← mul_assoc,hcoef1,hcoef2]
        push_cast
        ring

 theorem randomValue_eq_countValue (n : ℕ) :
    randomValue (upperTriangular n) = countValue n n := by
  rw [randomValue_eq_countTotal,total_eq_countValue n n le_rfl]
  simp
end KVVMatching.UpperBound.CountProcess

open Finset
namespace KVVMatching.UpperBound.CountProcess
noncomputable def countStep (v : ℕ → ℝ) (t : ℕ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | k+2 => 1 + ((k+1 : ℕ) : ℝ) / (t+1) * v k +
      ((t-k : ℕ) : ℝ) / (t+1) * v (k+1)
lemma countValue_step (t k : ℕ) : countValue (t+1) k = countStep (countValue t) t k := by
  cases k with
  | zero => rfl
  | succ k => cases k <;> rfl

lemma countStep_nonexpansive (v w : ℕ → ℝ) (t k : ℕ) (hk : k ≤ t+1)
    (B : ℝ) (hB : 0 ≤ B) (h : ∀ j ≤ t, |v j-w j| ≤ B) :
    |countStep v t k-countStep w t k| ≤ B := by
  cases k with
  | zero => simpa [countStep] using hB
  | succ k =>
    cases k with
    | zero => simpa [countStep] using hB
    | succ k =>
      have hk1 : k+1 ≤ t := by omega
      have hcast : ((t-k : ℕ) : ℝ) = (t:ℝ)-k := by rw [Nat.cast_sub (by omega)]
      have hp : 0 ≤ ((k+1 : ℕ) : ℝ) / (t+1) := by positivity
      have hq : 0 ≤ ((t-k : ℕ) : ℝ) / (t+1) := by positivity
      have hpq : ((k+1 : ℕ) : ℝ) / (t+1) + ((t-k : ℕ) : ℝ) / (t+1) = 1 := by
        rw [hcast]
        push_cast
        field_simp
        ring
      change |(1 + ((k+1 : ℕ) : ℝ) / (t+1) * v k + ((t-k : ℕ) : ℝ) / (t+1) * v (k+1)) -
        (1 + ((k+1 : ℕ) : ℝ) / (t+1) * w k + ((t-k : ℕ) : ℝ) / (t+1) * w (k+1))| ≤ B
      have heq : (1 + ((k+1 : ℕ) : ℝ) / (t+1) * v k + ((t-k : ℕ) : ℝ) / (t+1) * v (k+1)) -
        (1 + ((k+1 : ℕ) : ℝ) / (t+1) * w k + ((t-k : ℕ) : ℝ) / (t+1) * w (k+1)) =
        ((k+1 : ℕ) : ℝ) / (t+1) * (v k-w k) + ((t-k : ℕ) : ℝ) / (t+1) * (v (k+1)-w (k+1)) := by ring
      rw [heq]
      calc
        _ ≤ |((k+1 : ℕ) : ℝ) / (t+1) * (v k-w k)| +
          |((t-k : ℕ) : ℝ) / (t+1) * (v (k+1)-w (k+1))| := abs_add_le _ _
        _ = ((k+1 : ℕ) : ℝ) / (t+1) * |v k-w k| +
          ((t-k : ℕ) : ℝ) / (t+1) * |v (k+1)-w (k+1)| := by rw [abs_mul,abs_mul,abs_of_nonneg hp,abs_of_nonneg hq]
        _ ≤ ((k+1 : ℕ) : ℝ) / (t+1) * B + ((t-k : ℕ) : ℝ) / (t+1) * B :=
          add_le_add (mul_le_mul_of_nonneg_left (h k (by omega)) hp)
            (mul_le_mul_of_nonneg_left (h (k+1) hk1) hq)
        _ = B := by rw [← add_mul,hpq,one_mul]

/-- Accumulated one-step residuals control the exact finite RANDOM value. -/
theorem approximation_bound (v : ℕ → ℕ → ℝ) (ε : ℕ → ℝ)
    (hε : ∀ t, 0 ≤ ε t) (hv : v 0 0 = 0)
    (hr : ∀ t k, k ≤ t+1 → |countStep (v t) t k-v (t+1) k| ≤ ε t)
    (t k : ℕ) (hk : k ≤ t) :
    |countValue t k-v t k| ≤ ∑ j ∈ range t, ε j := by
  induction t generalizing k with
  | zero =>
    have : k=0 := by omega
    subst k
    simp [countValue,hv]
  | succ t ih =>
    rw [countValue_step,sum_range_succ]
    calc
      _ ≤ |countStep (countValue t) t k-countStep (v t) t k| +
        |countStep (v t) t k-v (t+1) k| := abs_sub_le _ _ _
      _ ≤ (∑ j ∈ range t, ε j) + ε t := add_le_add
        (countStep_nonexpansive _ _ t k hk _ (sum_nonneg (fun j _ => hε j))
          (fun j hj => ih j hj)) (hr t k hk)
end KVVMatching.UpperBound.CountProcess

open Finset
namespace KVVMatching.UpperBound.CountProcess
lemma exp_mix (p y : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    |(1-p)*Real.exp (-p*y)+p*Real.exp ((1-p)*y)-1| ≤ y^2 := by
  have hu : |-p*y| ≤ y := by rw [abs_mul,abs_neg,abs_of_nonneg hp,abs_of_nonneg hy]; nlinarith
  have hv : |(1-p)*y| ≤ y := by rw [abs_mul,abs_of_nonneg (by linarith : 0 ≤ 1-p),abs_of_nonneg hy]; nlinarith
  have h1 := Real.abs_exp_sub_one_sub_id_le (hu.trans hy1)
  have h2 := Real.abs_exp_sub_one_sub_id_le (hv.trans hy1)
  have hs1 : (-p*y)^2 ≤ y^2 := by nlinarith [sq_abs (-p*y)]
  have hs2 : ((1-p)*y)^2 ≤ y^2 := by nlinarith [sq_abs ((1-p)*y)]
  have heq : (1-p)*Real.exp (-p*y)+p*Real.exp ((1-p)*y)-1 =
      (1-p)*(Real.exp (-p*y)-1-(-p*y))+p*(Real.exp ((1-p)*y)-1-(1-p)*y) := by ring
  rw [heq]
  calc
    _ ≤ |(1-p)*(Real.exp (-p*y)-1-(-p*y))|+|p*(Real.exp ((1-p)*y)-1-(1-p)*y)| := abs_add_le _ _
    _ = (1-p)*|Real.exp (-p*y)-1-(-p*y)|+p*|Real.exp ((1-p)*y)-1-(1-p)*y| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hp,abs_of_nonneg (by linarith : 0 ≤ 1-p)]
    _ ≤ (1-p)*y^2+p*y^2 := add_le_add
      (mul_le_mul_of_nonneg_left (h1.trans hs1) (by linarith)) (mul_le_mul_of_nonneg_left (h2.trans hs2) hp)
    _ = y^2 := by ring

lemma exp_scalar_error (t p : ℝ) (ht : 1 ≤ t) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    |Real.exp (-p) * ((t+1)*Real.exp (-(1/(t+1))) -
      t*((1-p)*Real.exp (-p*(1/t))+p*Real.exp ((1-p)*(1/t))))| ≤ 1/(t+1)+1/t := by
  have ht0 : 0 < t := by linarith
  have hx0 : 0 < t+1 := by linarith
  have hy : 0 ≤ 1/t := by positivity
  have hy1 : 1/t ≤ 1 := (div_le_one ht0).mpr ht
  have hx : |-(1/(t+1))| ≤ 1 := by
    rw [abs_neg,abs_of_nonneg (by positivity : 0 ≤ 1/(t+1))]
    exact (div_le_one hx0).mpr (by linarith)
  have hmix := exp_mix p (1/t) hp hp1 hy hy1
  have he := Real.abs_exp_sub_one_sub_id_le hx
  have hT : |(t+1)*Real.exp (-(1/(t+1)))-t| ≤ 1/(t+1) := by
    have heq : (t+1)*Real.exp (-(1/(t+1)))-t =
      (t+1)*(Real.exp (-(1/(t+1)))-1-(-(1/(t+1)))) := by field_simp <;> ring
    rw [heq,abs_mul,abs_of_pos hx0]
    calc
      _ ≤ (t+1)*(-(1/(t+1)))^2 := mul_le_mul_of_nonneg_left he hx0.le
      _ = 1/(t+1) := by field_simp <;> ring
  have hM : |t*((1-p)*Real.exp (-p*(1/t))+p*Real.exp ((1-p)*(1/t)))-t| ≤ 1/t := by
    rw [← mul_sub_one,abs_mul,abs_of_pos ht0]
    calc
      _ ≤ t*(1/t)^2 := mul_le_mul_of_nonneg_left hmix ht0.le
      _ = 1/t := by field_simp <;> ring
  have hexp : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ |(t+1)*Real.exp (-(1/(t+1))) -
      t*((1-p)*Real.exp (-p*(1/t))+p*Real.exp ((1-p)*(1/t)))| := mul_le_of_le_one_left (abs_nonneg _) hexp
    _ ≤ |(t+1)*Real.exp (-(1/(t+1)))-t| +
      |t-t*((1-p)*Real.exp (-p*(1/t))+p*Real.exp ((1-p)*(1/t)))| := abs_sub_le _ _ _
    _ ≤ 1/(t+1)+1/t := by rw [abs_sub_comm t]; exact add_le_add hT hM
end KVVMatching.UpperBound.CountProcess

namespace KVVMatching.UpperBound.CountProcess
noncomputable def fluidValue (t k : ℕ) : ℝ :=
  (t:ℝ)*(1-Real.exp (-(k:ℝ)/(t:ℝ)))
lemma fluid_zero (t : ℕ) : fluidValue t 0 = 0 := by simp [fluidValue]

lemma fluid_step_error (t k : ℕ) (ht : 1 ≤ t) (hk : k ≤ t+1) :
    |countStep (fluidValue t) t k-fluidValue (t+1) k| ≤
      1/((t:ℝ)+1)+1/(t:ℝ) := by
  have htR : (1:ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0:ℝ) < t := by linarith
  have hxpos : (0:ℝ) < (t:ℝ)+1 := by linarith
  cases k with
  | zero => simp [countStep,fluid_zero]; positivity
  | succ k =>
    cases k with
    | zero =>
      have h := exp_scalar_error (t:ℝ) 0 htR le_rfl (by norm_num)
      simp only [neg_zero,zero_mul,Real.exp_zero,one_mul,sub_zero,mul_zero,add_zero] at h
      convert h using 1 <;> simp only [countStep,fluidValue,Nat.cast_add,Nat.cast_one]
      congr 1
      ring
    | succ k =>
      have hkt : k ≤ t := by omega
      let p : ℝ := ((k:ℝ)+1)/((t:ℝ)+1)
      have hp : 0 ≤ p := by dsimp [p]; positivity
      have hp1 : p ≤ 1 := by
        apply (div_le_one hxpos).mpr
        have : (k:ℝ) ≤ t := by exact_mod_cast hkt
        linarith
      have e0 : -(k:ℝ)/(t:ℝ) = -p+(1-p)*(1/(t:ℝ)) := by
        dsimp [p]; field_simp [htpos.ne',hxpos.ne'] <;> ring
      have e1 : -((k:ℝ)+1)/(t:ℝ) = -p+ -p*(1/(t:ℝ)) := by
        dsimp [p]; field_simp [htpos.ne',hxpos.ne'] <;> ring
      have e2 : -((k:ℝ)+1+1)/((t:ℝ)+1) = -p+ -(1/((t:ℝ)+1)) := by
        dsimp [p]; field_simp [hxpos.ne'] <;> ring
      have hc : ((t-k:ℕ):ℝ)/((t:ℝ)+1) = 1-p := by
        rw [Nat.cast_sub hkt]
        dsimp [p]; field_simp [hxpos.ne'] <;> ring
      have heq : countStep (fluidValue t) t (k+1+1)-fluidValue (t+1) (k+1+1) =
          Real.exp (-p) * (((t:ℝ)+1)*Real.exp (-(1/((t:ℝ)+1))) -
          (t:ℝ)*((1-p)*Real.exp (-p*(1/(t:ℝ)))+p*Real.exp ((1-p)*(1/(t:ℝ))))) := by
        simp only [countStep,fluidValue,Nat.cast_add,Nat.cast_one]
        rw [e0,e1,e2,hc]
        simp only [Real.exp_add]
        change 1+p*((t:ℝ)*(1-Real.exp (-p)*Real.exp ((1-p)*(1/(t:ℝ)))))+
          (1-p)*((t:ℝ)*(1-Real.exp (-p)*Real.exp (-p*(1/(t:ℝ)))))-
          ((t:ℝ)+1)*(1-Real.exp (-p)*Real.exp (-(1/((t:ℝ)+1)))) = _
        ring
      rw [heq]
      exact exp_scalar_error (t:ℝ) p htR hp hp1
end KVVMatching.UpperBound.CountProcess

open Filter Topology Finset
noncomputable section
namespace KVVMatching.UpperBound.CountProcess
def errorBudget (t : ℕ) : ℝ := if t=0 then 1 else 1/((t:ℝ)+1)+1/(t:ℝ)
lemma errorBudget_nonneg (t : ℕ) : 0 ≤ errorBudget t := by
  unfold errorBudget
  split_ifs <;> positivity
lemma fluid_residual (t k : ℕ) (hk : k ≤ t+1) :
    |countStep (fluidValue t) t k-fluidValue (t+1) k| ≤ errorBudget t := by
  by_cases ht : t=0
  · subst t
    have hk01 : k=0 ∨ k=1 := by omega
    rcases hk01 with rfl | rfl
    · simp [errorBudget,countStep,fluid_zero]
    · simpa [countStep,fluidValue,errorBudget,abs_of_pos (Real.exp_pos (-1))] using
        (Real.exp_le_one_iff.mpr (show (-1:ℝ) ≤ 0 by norm_num))
  · simpa [errorBudget,ht] using fluid_step_error t k (by omega) hk

lemma value_error (n : ℕ) :
    |randomValue (upperTriangular n)-fluidValue n n| ≤ ∑ j ∈ range n, errorBudget j := by
  rw [randomValue_eq_countValue]
  exact approximation_bound fluidValue errorBudget errorBudget_nonneg (by simp [fluidValue])
    fluid_residual n n le_rfl

lemma errorBudget_tendsto : Tendsto errorBudget atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hs := hi.comp (tendsto_add_atTop_nat 1)
  have hh := hi.add hs
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp [errorBudget,show n ≠ 0 by omega,Nat.cast_add,Nat.cast_one,one_div,add_comm]
end KVVMatching.UpperBound.CountProcess

open KVVMatching.UpperBound KVVMatching.UpperBound.CountProcess
 theorem solution :
    Tendsto (fun n : ℕ => randomValue (upperTriangular n)/(n:ℝ)) atTop (𝓝 (1-Real.exp (-1))) := by
  have hb : Tendsto (fun n : ℕ => (∑ j ∈ range n, errorBudget j)/(n:ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv,mul_comm] using errorBudget_tendsto.cesaro
  have he : Tendsto (fun n : ℕ => |randomValue (upperTriangular n)/(n:ℝ)-(1-Real.exp (-1))|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun n => abs_nonneg _)) ?_ hb
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
    have hfluid : fluidValue n n = (n:ℝ)*(1-Real.exp (-1)) := by
      unfold fluidValue
      rw [neg_div,div_self hn0.ne']
    have hh := div_le_div_of_nonneg_right (value_error n) hn0.le
    rw [hfluid] at hh
    have heq : randomValue (upperTriangular n)/(n:ℝ)-(1-Real.exp (-1)) =
        (randomValue (upperTriangular n)-(n:ℝ)*(1-Real.exp (-1)))/(n:ℝ) := by
      field_simp
    rw [heq,abs_div,abs_of_pos hn0]
    exact hh
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using he)
