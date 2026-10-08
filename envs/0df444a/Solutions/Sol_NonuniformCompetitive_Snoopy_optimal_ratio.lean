-- Prove2me | solution 1 for NonuniformCompetitive.Snoopy.optimal_ratio
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-07T00:46:33.754395+00:00
-- url     : https://prove2.me/submissions/afbf28fc-f397-4fef-8519-8b06bd92b3c1

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_ep
import Definitions.Def_NonuniformCompetitive_Snoopy_model
import Definitions.Def_NonuniformCompetitive_Snoopy_randomized

set_option autoImplicit false

/- Complete checked body: AttributedSnoopy -/
section

set_option autoImplicit false

section
-- Prove2me | solution 1 for NonuniformCompetitive.Snoopy.lp_attained
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:04:21.485324+00:00
-- url     : https://prove2.me/submissions/58f64418-74af-473d-9d49-7cdbf7abef09

open NonuniformCompetitive.Snoopy
open scoped BigOperators

theorem checked_lp_attained (p : ℕ) (hp : 1 ≤ p) (α : ℝ) (π : ℕ → ℝ)
    (hα : α = ep p / (ep p - 1))
    (hπ : ∀ k, π k = (α - 1) * ((((p : ℝ) + 1) / p) ^ (k - 1) - 1)) :
    π (p + 1) = 1 ∧ 0 ≤ π 1 ∧ (∀ k ∈ Finset.Icc 1 p, π k ≤ π (k + 1)) ∧
      ∀ k ≤ p, π (k + 1) * p + ∑ i ∈ Finset.Icc 1 k, (1 - π i) = α * k := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  let r : ℝ := ((p:ℝ)+1)/p
  have hr : 1 < r := by dsimp [r]; apply (lt_div_iff₀ hpR).mpr; linarith
  have hep : ep p=r^p := by unfold ep; congr 1; dsimp [r]; field_simp [ne_of_gt hpR]
  have he : 1 < ep p := by rw [hep]; exact one_lt_pow₀ hr (by omega)
  have hc : 0 < α-1 := by rw [hα]; apply sub_pos.mpr; apply (lt_div_iff₀ (by linarith : 0 < ep p-1)).mpr; linarith
  have heq : (α-1)*(ep p-1)=1 := by rw [hα]; field_simp [ne_of_gt (sub_pos.mpr he)]; ring
  have hpi (k : ℕ) : π (k+1)=(α-1)*(r^k-1) := by rw [hπ]; simp [r]
  refine ⟨?_,?_,?_,?_⟩
  · rw [hpi,← hep,heq]
  · rw [hπ]; simp
  · intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [hπ,hpi]
    apply mul_le_mul_of_nonneg_left _ hc.le
    apply sub_le_sub_right
    change r^(k-1) ≤ r^k
    exact pow_le_pow_right₀ hr.le (by omega)
  · intro k hk
    have hall : ∀ k : ℕ, π (k+1)*(p:ℝ)+∑ i∈Finset.Icc 1 k, (1-π i)=α*k := by
      intro k
      induction k with
      | zero => rw [hpi]; simp
      | succ k ih =>
        have hrec : π (k+2)*(p:ℝ)-(p+1)*π (k+1)=α-1 := by
          rw [hpi (k+1),hpi k,pow_succ]
          dsimp [r]
          field_simp [ne_of_gt hpR]
          ring
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1)]
        push_cast
        nlinarith
    exact hall k

end

section
-- Prove2me | solution 1 for NonuniformCompetitive.Snoopy.lp_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:04:22.210482+00:00
-- url     : https://prove2.me/submissions/4744e7b2-0a92-4c8e-83f2-56dedebb6451

open NonuniformCompetitive.Snoopy
open scoped BigOperators

theorem checked_lp_lower_bound (p : ℕ) (hp : 1 ≤ p) (π : ℕ → ℝ) (α : ℝ)
    (hπ : π (p + 1) = 1)
    (hcon : ∀ k ≤ p, π (k + 1) * p + ∑ i ∈ Finset.Icc 1 k, (1 - π i) ≤ α * k) :
    ep p / (ep p - 1) ≤ α := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  let r : ℝ := ((p:ℝ)+1)/p
  let S (k : ℕ) : ℝ := ∑ i∈Finset.Icc 1 k, π i
  have hr : 1 < r := by dsimp [r]; apply (lt_div_iff₀ hpR).mpr; linarith
  have hep : ep p=r^p := by unfold ep; congr 1; dsimp [r]; field_simp [ne_of_gt hpR]
  have he : 1 < ep p := by rw [hep]; exact one_lt_pow₀ hr (by omega)
  have hcon' (k : ℕ) (hk : k ≤ p) : π (k+1)*(p:ℝ) + k - S k ≤ α*k := by
    have h := hcon k hk
    simp [Finset.sum_sub_distrib] at h
    dsimp [S]
    linarith
  have hb : ∀ k ≤ p, S k ≤ (α-1)*((p:ℝ)*(r^k-1)-k) := by
    intro k
    induction k with
    | zero => intro hk; simp [S]
    | succ k ih =>
      intro hk
      have hki : k ≤ p := by omega
      have ih' := ih hki
      have hstep : π (k+1) ≤ (α-1)*(r^k-1) := by
        apply (mul_le_mul_iff_right₀ hpR).mp
        nlinarith [hcon' k hki]
      have halg : (α-1)*((p:ℝ)*(r^(k+1)-1)-(k+1)) =
          (α-1)*((p:ℝ)*(r^k-1)-k)+(α-1)*(r^k-1) := by
        rw [pow_succ]
        dsimp [r]
        field_simp [ne_of_gt hpR]
        ring
      have hS : S (k+1)=S k+π (k+1) := by
        exact Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1) π
      rw [hS]
      push_cast
      rw [halg]
      exact add_le_add ih' hstep
  have hlast := hcon' p le_rfl
  rw [hπ] at hlast
  have hb' := hb p le_rfl
  rw [← hep] at hb'
  have hfinal : 1 ≤ (α-1)*(ep p-1) := by
    apply (mul_le_mul_iff_right₀ hpR).mp
    nlinarith
  apply (div_le_iff₀ (by linarith : 0 < ep p-1)).mpr
  nlinarith

end

end

/- Complete checked body: ThresholdLaw -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.SnoopyProof

open NonuniformCompetitive.Snoopy

noncomputable def snoopyRatio (p : ℕ) : ℝ := ep p / (ep p-1)

noncomputable def thresholdCDF (p k : ℕ) : ℝ :=
  (snoopyRatio p-1)*((((p:ℝ)+1)/p)^k-1)

@[simp] theorem thresholdCDF_zero (p : ℕ) : thresholdCDF p 0=0 := by
  simp [thresholdCDF]

theorem snoopyRatio_gt_one (p : ℕ) (hp : 1 ≤ p) : 1 < snoopyRatio p := by
  have hpR : (0:ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hbase : (1:ℝ) < 1+1/(p:ℝ) := by linarith [one_div_pos.mpr hpR]
  have he : 1 < ep p := one_lt_pow₀ hbase (by omega)
  unfold snoopyRatio
  exact (lt_div_iff₀ (sub_pos.mpr he)).2 (by linarith)

theorem thresholdCDF_top (p : ℕ) (hp : 1 ≤ p) : thresholdCDF p p=1 := by
  have h := checked_lp_attained p hp (snoopyRatio p)
    (fun k => thresholdCDF p (k-1)) rfl (fun k => rfl)
  simpa only [Nat.add_sub_cancel] using h.1

theorem thresholdCDF_step_mono (p : ℕ) (hp : 1 ≤ p) {k : ℕ} (hk : k < p) :
    thresholdCDF p k ≤ thresholdCDF p (k+1) := by
  have h := checked_lp_attained p hp (snoopyRatio p)
    (fun k => thresholdCDF p (k-1)) rfl (fun k => rfl)
  have hm := h.2.2.1 (k+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  simpa only [Nat.add_sub_cancel] using hm

theorem thresholdCDF_mono (p : ℕ) (hp : 1 ≤ p) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ p) :
    thresholdCDF p a ≤ thresholdCDF p b := by
  induction b,hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact (ih (by omega)).trans (thresholdCDF_step_mono p hp (by omega))

theorem thresholdCDF_bounds (p : ℕ) (hp : 1 ≤ p) {k : ℕ} (hk : k ≤ p) :
    0 ≤ thresholdCDF p k ∧ thresholdCDF p k ≤ 1 := by
  constructor
  · simpa only [thresholdCDF_zero] using thresholdCDF_mono p hp (Nat.zero_le k) hk
  · simpa only [thresholdCDF_top p hp] using thresholdCDF_mono p hp hk (le_refl p)

theorem thresholdCDF_recurrence (p : ℕ) (hp : 1 ≤ p) (k : ℕ) :
    1-thresholdCDF p k+(p:ℝ)*(thresholdCDF p (k+1)-thresholdCDF p k)=snoopyRatio p := by
  have hn : (p:ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  unfold thresholdCDF
  rw [pow_succ]
  field_simp [hn]
  ring

noncomputable def thresholdWeight (p : ℕ) (j : Fin p) : ℝ :=
  thresholdCDF p (j.val+1)-thresholdCDF p j.val

theorem thresholdWeight_nonneg (p : ℕ) (hp : 1 ≤ p) (j : Fin p) :
    0 ≤ thresholdWeight p j :=
  sub_nonneg.mpr (thresholdCDF_step_mono p hp j.isLt)

theorem thresholdCDF_telescope (p k : ℕ) :
    ∑ j ∈ Finset.range k, (thresholdCDF p (j+1)-thresholdCDF p j)=thresholdCDF p k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ,ih]; ring

theorem thresholdWeight_sum (p : ℕ) (hp : 1 ≤ p) : ∑ j : Fin p, thresholdWeight p j=1 := by
  unfold thresholdWeight
  rw [Fin.sum_univ_eq_sum_range (fun j => thresholdCDF p (j+1)-thresholdCDF p j),
    thresholdCDF_telescope,thresholdCDF_top p hp]

theorem thresholdWeight_cdf (p : ℕ) (_hp : 1 ≤ p) {k : ℕ} (hk : k ≤ p) :
    ∑ j : Fin p, (if j.val+1 ≤ k then thresholdWeight p j else 0)=thresholdCDF p k := by
  classical
  unfold thresholdWeight
  rw [Fin.sum_univ_eq_sum_range (fun j => if j+1 ≤ k then
    thresholdCDF p (j+1)-thresholdCDF p j else 0)]
  have hset : (Finset.range p).filter (fun j => j+1 ≤ k) = Finset.range k := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [← Finset.sum_filter,hset,thresholdCDF_telescope]

theorem thresholdWeight_shared (p : ℕ) (hp : 1 ≤ p) {k : ℕ} (hk : k ≤ p) :
    ∑ j : Fin p, (if j.val+1 ≤ k then 0 else thresholdWeight p j)=1-thresholdCDF p k := by
  have he (j : Fin p) : (if j.val+1 ≤ k then 0 else thresholdWeight p j) =
      thresholdWeight p j-(if j.val+1 ≤ k then thresholdWeight p j else 0) := by
    split <;> simp
  simp_rw [he]
  rw [Finset.sum_sub_distrib,thresholdWeight_sum p hp,thresholdWeight_cdf p hp hk]

end NonuniformCompetitive.SnoopyProof

end

/- Complete checked body: UpperCounter -/
section

set_option autoImplicit false

open scoped ENNReal

namespace NonuniformCompetitive.SnoopyProof

open NonuniformCompetitive.Snoopy

def reqProcessor {n : ℕ} : Req n → Fin n
  | .read i => i
  | .write i => i

structure UpperState (n : ℕ) where
  owner : State n
  count : ℕ
  benchmark : ℕ

def upperStart (n : ℕ) : UpperState n := ⟨none,0,0⟩

def upperStep {n : ℕ} (p : ℕ) (u : UpperState n) : Req n → UpperState n
  | .read i =>
      if u.owner = some i then u else ⟨some i,0,u.benchmark⟩
  | .write i =>
      let k := if u.owner = some i then u.count else 0
      ⟨some i,min (k+1) p,u.benchmark + if k < p then 1 else 0⟩

def upperCounter {n : ℕ} (p : ℕ) (h : List (Req n)) : UpperState n :=
  h.foldl (upperStep p) (upperStart n)

@[simp] theorem upperCounter_nil (n p : ℕ) :
    upperCounter p ([] : List (Req n)) = upperStart n := rfl

theorem upperCounter_append_one {n : ℕ} (p : ℕ) (h : List (Req n)) (r : Req n) :
    upperCounter p (h++[r]) = upperStep p (upperCounter p h) r := by
  simp only [upperCounter,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem upperStep_owner {n : ℕ} (p : ℕ) (u : UpperState n) (r : Req n) :
    (upperStep p u r).owner = some (reqProcessor r) := by
  cases r with
  | read i =>
    simp only [upperStep,reqProcessor]
    split <;> simp_all
  | write i => rfl

theorem upperCounter_owner_append {n : ℕ} (p : ℕ) (h : List (Req n)) (r : Req n) :
    (upperCounter p (h++[r])).owner = some (reqProcessor r) := by
  rw [upperCounter_append_one,upperStep_owner]

theorem upperStep_count_le {n : ℕ} (p : ℕ) (u : UpperState n)
    (hu : u.count ≤ p) (r : Req n) : (upperStep p u r).count ≤ p := by
  cases r with
  | read i => simp only [upperStep]; split <;> simp_all
  | write i => exact min_le_right _ _

theorem upperCounter_count_le {n : ℕ} (p : ℕ) (h : List (Req n)) :
    (upperCounter p h).count ≤ p := by
  induction h using List.reverseRecOn with
  | nil => simp [upperCounter,upperStart]
  | append_singleton h r ih =>
    rw [upperCounter_append_one]
    exact upperStep_count_le p _ ih r

theorem upperCounter_benchmark_mono {n : ℕ} (p : ℕ) (h : List (Req n)) (r : Req n) :
    (upperCounter p h).benchmark ≤ (upperCounter p (h++[r])).benchmark := by
  rw [upperCounter_append_one]
  cases r with
  | read i => simp only [upperStep]; split <;> simp
  | write i => exact Nat.le_add_right _ _

theorem admissible_prefix {n : ℕ} {h k : List (Req n)} (hh : Admissible (h++k)) :
    Admissible h := by
  intro j i hj
  have hjlen : j < h.length := List.getElem?_eq_some_iff.mp hj |>.1
  have hj' : (h++k)[j]? = some (Req.write i) := by
    rwa [List.getElem?_append_left hjlen]
  obtain ⟨hpos,hprev⟩ := hh j i hj'
  refine ⟨hpos,?_⟩
  have hlt : j-1 < h.length := by omega
  simpa only [List.getElem?_append_left hlt] using hprev

theorem write_owner_of_admissible_append {n : ℕ} (p : ℕ) (h : List (Req n))
    (i : Fin n) (hh : Admissible (h++[Req.write i])) :
    (upperCounter p h).owner = some i := by
  have hlast : (h++[Req.write i])[h.length]? = some (Req.write i) := by simp
  obtain ⟨hpos,hprev⟩ := hh h.length i hlast
  rcases List.eq_nil_or_concat h with he | ⟨l,r,he⟩
  · simp [he] at hpos
  rw [List.concat_eq_append] at he
  subst h
  rw [upperCounter_owner_append]
  simp only [List.length_append,List.length_cons,List.length_nil,
    Nat.add_sub_cancel] at hprev
  have hp : ((l++[r])++[Req.write i])[l.length]? = some r := by simp
  rw [hp] at hprev
  rcases hprev with hr | hr <;> cases Option.some.inj hr <;> rfl

def offlinePotential {n : ℕ} (u : UpperState n) (s : State n) : ℕ :=
  match u.owner with
  | none => 0
  | some i => if s = some i then u.count else 0

theorem offlinePotential_le {n : ℕ} (p : ℕ) (h : List (Req n)) (s : State n) :
    offlinePotential (upperCounter p h) s ≤ p := by
  unfold offlinePotential
  split
  · exact Nat.zero_le _
  · split
    · exact upperCounter_count_le p h
    · exact Nat.zero_le _

@[simp] theorem offlinePotential_start {n : ℕ} (s : State n) :
    offlinePotential (upperStart n) s = 0 := by simp [offlinePotential,upperStart]

end NonuniformCompetitive.SnoopyProof

end

/- Complete checked body: ThresholdPolicy -/
section

set_option autoImplicit false

open scoped ENNReal

namespace NonuniformCompetitive.SnoopyProof

open NonuniformCompetitive.Snoopy

def thresholdAfter {n : ℕ} (p J : ℕ) (s₀ : State n) (h : List (Req n)) : State n :=
  if h=[] then s₀ else
    if J ≤ (upperCounter p h).count then (upperCounter p h).owner else none

def thresholdAlgorithm {n : ℕ} (p J : ℕ) (s₀ : State n) : OnlineAlgorithm n where
  after := thresholdAfter p J s₀
  moment h :=
    match h.getLast? with
    | some (.write _) => thresholdAfter p J s₀ h.dropLast
    | _ => thresholdAfter p J s₀ h
  lookaheadZero h i := by simp

@[simp] theorem thresholdAfter_nil {n : ℕ} (p J : ℕ) (s₀ : State n) :
    thresholdAfter p J s₀ [] = s₀ := by simp [thresholdAfter]

theorem thresholdAfter_nonempty {n : ℕ} (p J : ℕ) (s₀ : State n) {h : List (Req n)}
    (hh : h ≠ []) : thresholdAfter p J s₀ h =
      if J ≤ (upperCounter p h).count then (upperCounter p h).owner else none := by
  simp only [thresholdAfter,if_neg hh]

theorem thresholdAfter_append {n : ℕ} (p J : ℕ) (s₀ : State n) (h : List (Req n)) (r : Req n) :
    thresholdAfter p J s₀ (h++[r]) =
      if J ≤ (upperStep p (upperCounter p h) r).count then some (reqProcessor r) else none := by
  rw [thresholdAfter_nonempty p J s₀ (by simp),upperCounter_append_one,upperStep_owner]

@[simp] theorem threshold_moment_read {n : ℕ} (p J : ℕ) (s₀ : State n)
    (h : List (Req n)) (i : Fin n) :
    (thresholdAlgorithm p J s₀).moment (h++[.read i]) =
      thresholdAfter p J s₀ (h++[.read i]) := by simp [thresholdAlgorithm]

@[simp] theorem threshold_moment_write {n : ℕ} (p J : ℕ) (s₀ : State n)
    (h : List (Req n)) (i : Fin n) :
    (thresholdAlgorithm p J s₀).moment (h++[.write i]) =
      thresholdAfter p J s₀ h := by simp [thresholdAlgorithm]

theorem upperCounter_owner_nonempty {n : ℕ} (p : ℕ) {h : List (Req n)} (hh : h ≠ []) :
    (upperCounter p h).owner ≠ none := by
  rcases List.eq_nil_or_concat h with he | ⟨l,r,he⟩
  · exact (hh he).elim
  · rw [List.concat_eq_append] at he
    subst h
    rw [upperCounter_owner_append]
    simp

theorem threshold_read_reset {n : ℕ} (p J : ℕ) (hJ : 0 < J) (s₀ : State n)
    (h : List (Req n)) (i : Fin n) (hi : (upperCounter p h).owner ≠ some i) :
    thresholdAfter p J s₀ (h++[.read i]) = none := by
  rw [thresholdAfter_append]
  simp [upperStep,hi,Nat.not_le.mpr hJ]

theorem threshold_read_preserves {n : ℕ} (p J : ℕ) (s₀ : State n)
    (h : List (Req n)) (i : Fin n) (hi : (upperCounter p h).owner = some i) :
    thresholdAfter p J s₀ (h++[.read i]) = thresholdAfter p J s₀ h := by
  have hn : h ≠ [] := by intro he; simp [he,upperStart] at hi
  rw [thresholdAfter_append,thresholdAfter_nonempty p J s₀ hn]
  simp only [upperStep,hi,ite_true,reqProcessor]

theorem threshold_write_after {n : ℕ} (p J : ℕ) (s₀ : State n)
    (h : List (Req n)) (i : Fin n) (hi : (upperCounter p h).owner = some i) :
    thresholdAfter p J s₀ (h++[.write i]) =
      if J ≤ min ((upperCounter p h).count+1) p then some i else none := by
  rw [thresholdAfter_append]
  simp only [upperStep,if_pos hi,reqProcessor]

def initialSharedCharge {n : ℕ} (p : ℕ) : State n → ℕ
  | none => 0
  | some _ => p

def thresholdCharge {n : ℕ} (p J : ℕ) (s₀ : State n) (h : List (Req n)) : Req n → ℕ
  | .read i =>
      if h=[] then initialSharedCharge p s₀ else
      if (upperCounter p h).owner=some i then 0 else
      if J ≤ (upperCounter p h).count then p else 0
  | .write _ => if J ≤ (upperCounter p h).count then 0 else 1

end NonuniformCompetitive.SnoopyProof

end

/- Complete checked body: CostBasics -/
section

set_option autoImplicit false

open scoped ENNReal

namespace NonuniformCompetitive.SnoopyProof

open NonuniformCompetitive.Snoopy

def shiftAlgorithm {n : ℕ} (A : OnlineAlgorithm n) (h : List (Req n)) : OnlineAlgorithm n where
  moment l := A.moment (h ++ l)
  after l := A.after (h ++ l)
  lookaheadZero l i := by
    simpa only [List.append_assoc] using A.lookaheadZero (h ++ l) i

@[simp] theorem shift_nil {n : ℕ} (A : OnlineAlgorithm n) : shiftAlgorithm A [] = A := by
  cases A
  simp [shiftAlgorithm]

@[simp] theorem shift_shift {n : ℕ} (A : OnlineAlgorithm n) (h l : List (Req n)) :
    shiftAlgorithm (shiftAlgorithm A h) l = shiftAlgorithm A (h ++ l) := by
  cases A
  simp [shiftAlgorithm, List.append_assoc]

@[simp] theorem cost_nil {n p : ℕ} (A : OnlineAlgorithm n) : A.cost p [] = 0 := by
  simp [OnlineAlgorithm.cost]

theorem cost_cons {n p : ℕ} (A : OnlineAlgorithm n) (r : Req n) (l : List (Req n)) :
    A.cost p (r :: l) = stepCost p r (A.after []) (A.moment [r]) (A.after [r]) +
      (shiftAlgorithm A [r]).cost p l := by
  simp [OnlineAlgorithm.cost, Fin.sum_univ_succ, shiftAlgorithm]

theorem cost_append {n p : ℕ} (A : OnlineAlgorithm n) (h l : List (Req n)) :
    A.cost p (h ++ l) = A.cost p h + (shiftAlgorithm A h).cost p l := by
  induction h generalizing A with
  | nil => simp
  | cons r h ih =>
    rw [List.cons_append, cost_cons, ih, cost_cons, shift_shift]
    simp only [List.singleton_append, add_assoc]

theorem cost_append_singleton {n p : ℕ} (A : OnlineAlgorithm n) (h : List (Req n)) (r : Req n) :
    A.cost p (h ++ [r]) = A.cost p h +
      stepCost p r (A.after h) (A.moment (h ++ [r])) (A.after (h ++ [r])) := by
  rw [cost_append, cost_cons, cost_nil, add_zero]
  simp only [shiftAlgorithm, List.append_nil]

theorem cost_prefix_le {n p : ℕ} (A : OnlineAlgorithm n) (h l : List (Req n)) :
    A.cost p h ≤ A.cost p (h ++ l) := by
  rw [cost_append]
  exact le_add_of_nonneg_right bot_le

theorem task_le_step {n : ℕ} (p : ℕ) (r : Req n) (a b c : State n) :
    taskCost r b ≤ stepCost p r a b c := by
  unfold stepCost
  exact (le_add_of_nonneg_left bot_le).trans (le_add_of_nonneg_right bot_le)

theorem write_cost_ge_one {n p : ℕ} (A : OnlineAlgorithm n) (i : Fin n)
    (h : A.after [] ≠ some i) : (1 : ℝ≥0∞) ≤ A.cost p [Req.write i] := by
  rw [cost_cons, cost_nil, add_zero]
  have hm := A.lookaheadZero [] i
  simp only [List.nil_append] at hm
  apply le_trans _ (task_le_step p (Req.write i) _ _ _)
  rw [hm]
  by_cases hs : A.after [] = none
  · simp [taskCost, hs]
  · simp [taskCost, h, hs]

end NonuniformCompetitive.SnoopyProof

end

/- Complete checked body: ThresholdSteps -/
section

set_option autoImplicit false

open scoped ENNReal

namespace NonuniformCompetitive.SnoopyProof

open NonuniformCompetitive.Snoopy

theorem threshold_step_nat {n : ℕ} (p J : ℕ) (hJ : 0 < J) (s₀ : State n)
    (h : List (Req n)) (r : Req n) (hσ : Admissible (h++[r])) :
    stepCost p r ((thresholdAlgorithm p J s₀).after h)
      ((thresholdAlgorithm p J s₀).moment (h++[r]))
      ((thresholdAlgorithm p J s₀).after (h++[r])) =
      (thresholdCharge p J s₀ h r : ℝ≥0∞) := by
  classical
  change stepCost p r (thresholdAfter p J s₀ h)
    ((thresholdAlgorithm p J s₀).moment (h++[r]))
    (thresholdAfter p J s₀ (h++[r])) = _
  cases r with
  | read i =>
    rw [threshold_moment_read]
    by_cases hh : h=[]
    · subst h
      have hi : (upperCounter p ([] : List (Req n))).owner ≠ some i := by simp [upperStart]
      rw [threshold_read_reset p J hJ s₀ [] i hi,thresholdAfter_nil]
      cases s₀ <;> simp [thresholdCharge,initialSharedCharge,stepCost,transCost,taskCost]
    · by_cases ho : (upperCounter p h).owner=some i
      · rw [threshold_read_preserves p J s₀ h i ho]
        rw [thresholdAfter_nonempty p J s₀ hh,ho]
        by_cases hk : J ≤ (upperCounter p h).count <;>
          simp [thresholdCharge,hh,ho,hk,stepCost,transCost,taskCost]
      · rw [threshold_read_reset p J hJ s₀ h i ho,thresholdAfter_nonempty p J s₀ hh]
        cases hu : (upperCounter p h).owner with
        | none => exact (upperCounter_owner_nonempty p hh hu).elim
        | some j =>
          have hji : j ≠ i := by intro hj; subst j; exact ho hu
          by_cases hk : J ≤ (upperCounter p h).count <;>
            simp [thresholdCharge,hh,hu,hji,hk,stepCost,transCost,taskCost]
  | write i =>
    have ho := write_owner_of_admissible_append p h i hσ
    have hh : h ≠ [] := by intro he; simp [he,upperStart] at ho
    have hk := upperCounter_count_le p h
    rw [threshold_moment_write,threshold_write_after p J s₀ h i ho,
      thresholdAfter_nonempty p J s₀ hh,ho]
    by_cases hj : J ≤ (upperCounter p h).count
    · have hj' : J ≤ min ((upperCounter p h).count+1) p := le_min (by omega) (hj.trans hk)
      simp [thresholdCharge,hj,hj',stepCost,transCost,taskCost]
    · by_cases hj' : J ≤ min ((upperCounter p h).count+1) p <;>
        simp [thresholdCharge,hj,hj',stepCost,transCost,taskCost]

theorem threshold_cost_finite {n : ℕ} (p J : ℕ) (hJ : 0 < J) (s₀ : State n)
    (h : List (Req n)) (hσ : Admissible h) :
    (thresholdAlgorithm p J s₀).cost p h ≠ ⊤ := by
  revert hσ
  induction h using List.reverseRecOn with
  | nil => intro _; simp
  | append_singleton h r ih =>
    intro hσ
    rw [cost_append_singleton,threshold_step_nat p J hJ s₀ h r hσ]
    exact ENNReal.add_ne_top.mpr ⟨ih (admissible_prefix hσ),by simp⟩

theorem threshold_cost_toReal_append {n : ℕ} (p J : ℕ) (hJ : 0 < J) (s₀ : State n)
    (h : List (Req n)) (r : Req n) (hσ : Admissible (h++[r])) :
    ((thresholdAlgorithm p J s₀).cost p (h++[r])).toReal =
      ((thresholdAlgorithm p J s₀).cost p h).toReal + thresholdCharge p J s₀ h r := by
  rw [cost_append_singleton,threshold_step_nat p J hJ s₀ h r hσ,
    ENNReal.toReal_add (threshold_cost_finite p J hJ s₀ h (admissible_prefix hσ)) (by simp),
    ENNReal.toReal_natCast]

end NonuniformCompetitive.SnoopyProof

end

/- Complete checked body: UpperPotential -/
section

set_option autoImplicit false

open scoped ENNReal

namespace NonuniformCompetitive.SnoopyProof

open NonuniformCompetitive.Snoopy

def upperCharge {n : ℕ} (p : ℕ) (u : UpperState n) : Req n → ℕ
  | .read _ => 0
  | .write i => if (if u.owner = some i then u.count else 0) < p then 1 else 0

theorem upperStep_benchmark {n : ℕ} (p : ℕ) (u : UpperState n) (r : Req n) :
    (upperStep p u r).benchmark = u.benchmark + upperCharge p u r := by
  cases r with
  | read i => simp only [upperStep,upperCharge,Nat.add_zero]; split <;> rfl
  | write i => rfl

theorem transCost_triangle {n : ℕ} (p : ℕ) (a b c : State n) :
    transCost p a c ≤ transCost p a b + transCost p b c := by
  classical
  cases a with
  | none => simp [transCost]
  | some i =>
    by_cases hc : c = some i
    · simp [transCost,hc]
    by_cases hb : b = some i
    · subst b; simp [transCost,hc]
    · rw [transCost,if_neg hc,transCost,if_neg hb]
      exact le_add_of_nonneg_right zero_le

theorem transCost_le_stepCost {n : ℕ} (p : ℕ) (r : Req n) (a b c : State n) :
    transCost p a c ≤ stepCost p r a b c := by
  apply (transCost_triangle p a b c).trans
  exact add_le_add (le_add_of_nonneg_right zero_le) le_rfl

theorem read_release_lower {n : ℕ} (p : ℕ) (i j : Fin n) (hij : j ≠ i)
    (mom aft : State n) :
    (p : ℝ≥0∞) ≤ stepCost p (.read i) (some j) mom aft := by
  classical
  by_cases hm : mom = some j
  · subst mom
    simp [stepCost,taskCost,hij]
  · have he : transCost p (some j) mom = p := by simp [transCost,hm]
    rw [← he]
    exact le_trans (le_add_of_nonneg_right zero_le) (le_add_of_nonneg_right zero_le)

theorem potential_change_le {n : ℕ} (p : ℕ) (u : UpperState n) (hu : u.count ≤ p)
    (a b : State n) :
    (offlinePotential u a : ℝ≥0∞) ≤ transCost p a b + offlinePotential u b := by
  classical
  cases ho : u.owner with
  | none => simp [offlinePotential,ho]
  | some i =>
    by_cases ha : a = some i
    · subst a
      by_cases hb : b = some i
      · subst b; simp [offlinePotential,ho,transCost]
      · simpa [offlinePotential,ho,transCost,hb] using
          (show (u.count : ℝ≥0∞) ≤ p by exact_mod_cast hu)
    · simp [offlinePotential,ho,ha]

theorem upper_potential_step {n : ℕ} (p : ℕ) (u : UpperState n)
    (hu : u.count ≤ p) (r : Req n)
    (hvalid : ∀ i, r = .write i → u.owner = some i)
    (prev mom aft : State n) (hw : r.isWrite = true → mom = prev) :
    (upperCharge p u r : ℝ≥0∞) + offlinePotential u prev ≤
      stepCost p r prev mom aft + offlinePotential (upperStep p u r) aft := by
  classical
  cases r with
  | read i =>
    by_cases ho : u.owner = some i
    · simp only [upperCharge,Nat.cast_zero,zero_add,upperStep,if_pos ho]
      exact (potential_change_le p u hu prev aft).trans
        (add_le_add (transCost_le_stepCost p (.read i) prev mom aft) le_rfl)
    · have hnew : offlinePotential (upperStep p u (.read i)) aft = 0 := by
        simp [upperStep,ho,offlinePotential]
      rw [hnew,Nat.cast_zero,add_zero]
      simp only [upperCharge,Nat.cast_zero,zero_add]
      cases hou : u.owner with
      | none => simp [offlinePotential,hou]
      | some j =>
        have hji : j ≠ i := by intro h; subst j; exact ho hou
        by_cases hpv : prev = some j
        · subst prev
          simp only [offlinePotential,hou,ite_true]
          exact (show (u.count : ℝ≥0∞) ≤ p by exact_mod_cast hu).trans
            (read_release_lower p i j hji mom aft)
        · simp [offlinePotential,hou,hpv]
  | write i =>
    have ho := hvalid i rfl
    have hm : mom = prev := hw rfl
    subst mom
    have hcount : (if u.count < p then 1 else 0) + u.count = min (u.count+1) p := by
      by_cases hk : u.count < p
      · simp only [if_pos hk,min_eq_left (show u.count+1 ≤ p by omega)]; omega
      · simp only [if_neg hk,min_eq_right (show p ≤ u.count+1 by omega)]; omega
    cases prev with
    | none =>
      by_cases hk : u.count < p <;>
        simp [upperCharge,ho,upperStep,offlinePotential,stepCost,transCost,taskCost,hk]
    | some j =>
      by_cases hji : j = i
      · subst j
        by_cases ha : aft = some i
        · subst aft
          simpa [upperCharge,upperStep,ho,offlinePotential,stepCost,transCost,taskCost] using
            (show ((if u.count < p then 1 else 0) : ℝ≥0∞) + (u.count : ℝ≥0∞) ≤
              (min (u.count+1) p : ℕ) by exact_mod_cast hcount.le)
        · have hc : (if u.count < p then 1 else 0) + u.count ≤ p := hcount.le.trans (min_le_right _ _)
          simpa [upperCharge,upperStep,ho,offlinePotential,stepCost,transCost,taskCost,ha] using
            (show ((if u.count < p then 1 else 0) : ℝ≥0∞) + (u.count : ℝ≥0∞) ≤ p by
              exact_mod_cast hc)
      · simp [stepCost,taskCost,hji]

end NonuniformCompetitive.SnoopyProof

end

/- Complete checked body: ThresholdMean -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.SnoopyProof

open NonuniformCompetitive.Snoopy

noncomputable def thresholdMeanCost {n : ℕ} (p : ℕ) (s₀ : State n) (h : List (Req n)) : ℝ :=
  ∑ j : Fin p, thresholdWeight p j*((thresholdAlgorithm p (j.val+1) s₀).cost p h).toReal

noncomputable def thresholdMeanCharge {n : ℕ} (p : ℕ) (s₀ : State n)
    (h : List (Req n)) (r : Req n) : ℝ :=
  ∑ j : Fin p, thresholdWeight p j*(thresholdCharge p (j.val+1) s₀ h r : ℝ)

noncomputable def thresholdReserve {n : ℕ} (p : ℕ) (h : List (Req n)) : ℝ :=
  (p:ℝ)*thresholdCDF p (upperCounter p h).count

def initialAllowance {n : ℕ} (p : ℕ) (s₀ : State n) (h : List (Req n)) : ℝ :=
  if h=[] then 0 else (initialSharedCharge p s₀ : ℝ)

@[simp] theorem thresholdMeanCost_nil {n : ℕ} (p : ℕ) (s₀ : State n) :
    thresholdMeanCost p s₀ [] = 0 := by simp [thresholdMeanCost]

theorem threshold_mean_append {n : ℕ} (p : ℕ) (s₀ : State n)
    (h : List (Req n)) (r : Req n) (hσ : Admissible (h++[r])) :
    thresholdMeanCost p s₀ (h++[r]) = thresholdMeanCost p s₀ h+thresholdMeanCharge p s₀ h r := by
  unfold thresholdMeanCost thresholdMeanCharge
  simp_rw [threshold_cost_toReal_append p _ (Nat.succ_pos _) s₀ h r hσ,mul_add]
  exact Finset.sum_add_distrib

theorem threshold_mean_write {n : ℕ} (p : ℕ) (hp : 1 ≤ p) (s₀ : State n)
    (h : List (Req n)) (i : Fin n) :
    thresholdMeanCharge p s₀ h (.write i)=1-thresholdCDF p (upperCounter p h).count := by
  unfold thresholdMeanCharge
  simp only [thresholdCharge,Nat.cast_ite,Nat.cast_zero,Nat.cast_one,mul_ite,mul_zero,mul_one]
  exact thresholdWeight_shared p hp (upperCounter_count_le p h)

theorem threshold_mean_read_initial {n : ℕ} (p : ℕ) (hp : 1 ≤ p) (s₀ : State n) (i : Fin n) :
    thresholdMeanCharge p s₀ [] (.read i) = initialSharedCharge p s₀ := by
  simp only [thresholdMeanCharge,thresholdCharge,ite_true]
  rw [← Finset.sum_mul,thresholdWeight_sum p hp,one_mul]

theorem threshold_mean_read_same {n : ℕ} (p : ℕ) (s₀ : State n)
    (h : List (Req n)) (i : Fin n) (hh : h ≠ []) (ho : (upperCounter p h).owner=some i) :
    thresholdMeanCharge p s₀ h (.read i)=0 := by
  simp [thresholdMeanCharge,thresholdCharge,hh,ho]

theorem threshold_mean_read_reset {n : ℕ} (p : ℕ) (hp : 1 ≤ p) (s₀ : State n)
    (h : List (Req n)) (i : Fin n) (hh : h ≠ []) (ho : (upperCounter p h).owner≠some i) :
    thresholdMeanCharge p s₀ h (.read i)=thresholdReserve p h := by
  unfold thresholdMeanCharge
  simp only [thresholdCharge,if_neg hh,if_neg ho,Nat.cast_ite,Nat.cast_zero,mul_ite,mul_zero]
  have he : (∑ j : Fin p, if j.val+1 ≤ (upperCounter p h).count then
      thresholdWeight p j*(p:ℝ) else 0) =
      (∑ j : Fin p, if j.val+1 ≤ (upperCounter p h).count then thresholdWeight p j else 0)*(p:ℝ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _hj
    split <;> simp
  rw [he,thresholdWeight_cdf p hp (upperCounter_count_le p h)]
  exact mul_comm _ _

theorem threshold_amortized_step {n : ℕ} (p : ℕ) (hp : 1 ≤ p) (s₀ : State n)
    (h : List (Req n)) (r : Req n) (hh : h ≠ []) (hσ : Admissible (h++[r])) :
    thresholdMeanCharge p s₀ h r+thresholdReserve p (h++[r]) =
      snoopyRatio p*(upperCharge p (upperCounter p h) r : ℝ)+thresholdReserve p h := by
  cases r with
  | read i =>
    by_cases ho : (upperCounter p h).owner=some i
    · rw [threshold_mean_read_same p s₀ h i hh ho]
      simp [thresholdReserve,upperCounter_append_one,upperStep,ho,upperCharge]
    · rw [threshold_mean_read_reset p hp s₀ h i hh ho]
      simp [thresholdReserve,upperCounter_append_one,upperStep,ho,upperCharge]
  | write i =>
    have ho := write_owner_of_admissible_append p h i hσ
    have hk := upperCounter_count_le p h
    rw [threshold_mean_write p hp s₀ h i]
    simp only [thresholdReserve,upperCounter_append_one,upperStep,if_pos ho,upperCharge]
    by_cases hlt : (upperCounter p h).count < p
    · rw [if_pos hlt,min_eq_left (show (upperCounter p h).count+1 ≤ p by omega)]
      push_cast
      have hr := thresholdCDF_recurrence p hp (upperCounter p h).count
      linarith
    · have he : (upperCounter p h).count=p := by omega
      simp [he,thresholdCDF_top p hp]

theorem threshold_mean_identity {n : ℕ} (p : ℕ) (hp : 1 ≤ p) (s₀ : State n)
    (h : List (Req n)) (hσ : Admissible h) :
    thresholdMeanCost p s₀ h+thresholdReserve p h =
      snoopyRatio p*((upperCounter p h).benchmark : ℝ)+initialAllowance p s₀ h := by
  revert hσ
  induction h using List.reverseRecOn with
  | nil => intro _; simp [thresholdReserve,upperStart,initialAllowance]
  | append_singleton h r ih =>
    intro hσ
    by_cases hh : h=[]
    · subst h
      cases r with
      | read i =>
        rw [threshold_mean_append p s₀ [] (.read i) hσ,threshold_mean_read_initial p hp s₀ i]
        simp [thresholdReserve,upperCounter,upperStep,upperStart,initialAllowance]
      | write i =>
        have hz := (hσ 0 i (by simp)).1
        omega
    · have hi := ih (admissible_prefix hσ)
      have ha := threshold_amortized_step p hp s₀ h r hh hσ
      have hB : (upperCounter p (h++[r])).benchmark =
          (upperCounter p h).benchmark+upperCharge p (upperCounter p h) r := by
        rw [upperCounter_append_one,upperStep_benchmark]
      have hinit : initialAllowance p s₀ (h++[r])=initialAllowance p s₀ h := by
        simp [initialAllowance,hh]
      rw [threshold_mean_append p s₀ h r hσ,hB,Nat.cast_add,hinit]
      nlinarith

theorem threshold_mean_bound {n : ℕ} (p : ℕ) (hp : 1 ≤ p) (s₀ : State n)
    (h : List (Req n)) (hσ : Admissible h) :
    thresholdMeanCost p s₀ h ≤ snoopyRatio p*((upperCounter p h).benchmark : ℝ)+p := by
  have hi := threshold_mean_identity p hp s₀ h hσ
  have hr : 0 ≤ thresholdReserve p h :=
    mul_nonneg (Nat.cast_nonneg _) (thresholdCDF_bounds p hp (upperCounter_count_le p h)).1
  have hinit : initialAllowance p s₀ h ≤ p := by
    unfold initialAllowance
    split
    · positivity
    · cases s₀ <;> simp [initialSharedCharge]
  linarith

end NonuniformCompetitive.SnoopyProof

end

/- Complete checked body: RandomizedThreshold -/
section

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace NonuniformCompetitive.SnoopyProof

open NonuniformCompetitive.Snoopy

noncomputable def thresholdPMF (p : ℕ) (hp : 1 ≤ p) : PMF (Fin p) :=
  PMF.ofFintype (fun j => ENNReal.ofReal (thresholdWeight p j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _hj => thresholdWeight_nonneg p hp j),
      thresholdWeight_sum p hp,ENNReal.ofReal_one])

@[simp] theorem thresholdPMF_apply (p : ℕ) (hp : 1 ≤ p) (j : Fin p) :
    thresholdPMF p hp j = ENNReal.ofReal (thresholdWeight p j) := rfl

noncomputable def mixedThreshold (n p : ℕ) (hp : 1 ≤ p) (s₀ : State n) :
    RandomizedAlgorithm n p := by
  classical
  letI : MeasurableSpace (Fin p) := ⊤
  exact
    { ι := Fin p
      μ := (thresholdPMF p hp).toMeasure
      prob := inferInstance
      alg := fun j => thresholdAlgorithm p (j.val+1) s₀
      meas := fun _ => measurable_of_countable _ }

theorem mixedThreshold_starts (n p : ℕ) (hp : 1 ≤ p) (s₀ : State n)
    (j : (mixedThreshold n p hp s₀).ι) :
    ((mixedThreshold n p hp s₀).alg j).after [] = s₀ := by
  exact thresholdAfter_nil p (j.val+1) s₀

theorem mixedThreshold_expCost {n : ℕ} (p : ℕ) (hp : 1 ≤ p) (s₀ : State n)
    (h : List (Req n)) (hσ : Admissible h) :
    (mixedThreshold n p hp s₀).expCost h = ENNReal.ofReal (thresholdMeanCost p s₀ h) := by
  classical
  let : MeasurableSpace (Fin p) := ⊤
  change (∫⁻ j : Fin p, (thresholdAlgorithm p (j.val+1) s₀).cost p h
    ∂(thresholdPMF p hp).toMeasure) = _
  rw [lintegral_fintype]
  unfold thresholdMeanCost
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _hj =>
    mul_nonneg (thresholdWeight_nonneg p hp j) ENNReal.toReal_nonneg)]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [(thresholdPMF p hp).toMeasure_apply_singleton j (measurableSet_singleton j),
    thresholdPMF_apply,ENNReal.ofReal_mul (thresholdWeight_nonneg p hp j),
    ENNReal.ofReal_toReal (threshold_cost_finite p (j.val+1) (Nat.succ_pos _) s₀ h hσ)]
  exact mul_comm _ _

end NonuniformCompetitive.SnoopyProof

end

/- Complete checked body: ClockSchedule -/
section

set_option autoImplicit false

open scoped ENNReal

namespace NonuniformCompetitive.SnoopyProof

open NonuniformCompetitive.Snoopy

def clockAlgorithm {n : ℕ} (m s : ℕ → State n) : OnlineAlgorithm n where
  after h := s h.length
  moment h :=
    match h.getLast? with
    | some (.write _) => s (h.length-1)
    | _ => m h.length
  lookaheadZero h i := by simp

theorem clockAlgorithm_cost {n p : ℕ} (σ : List (Req n)) (m s : ℕ → State n)
    (hw : RespectsWrites σ m s) :
    (clockAlgorithm m s).cost p σ = scheduleCost p σ m s := by
  unfold OnlineAlgorithm.cost scheduleCost
  apply Finset.sum_congr rfl
  intro j _hj
  have hlen : j.val ≤ σ.length := Nat.le_of_lt j.isLt
  have hnext : j.val+1 ≤ σ.length := Nat.succ_le_of_lt j.isLt
  have hlast : (σ.take (j.val+1)).getLast? = some σ[j] := by
    rw [List.take_succ_eq_append_getElem j.isLt]
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or,Fin.getElem_fin]
  have hm : (clockAlgorithm m s).moment (σ.take (j.val+1)) = m (j.val+1) := by
    simp only [clockAlgorithm,hlast,List.length_take,min_eq_left hnext]
    cases hr : σ[j] with
    | read i => simp
    | write i =>
      simp only [Nat.add_sub_cancel]
      exact (hw j (by simp [hr,Req.isWrite])).symm
  rw [hm]
  simp only [clockAlgorithm,List.length_take,min_eq_left hlen,min_eq_left hnext]

theorem shared_schedule_admissible {n : ℕ} (s₀ : State n) (σ : List (Req n))
    (hσ : Admissible σ) :
    RespectsWrites σ (fun _ => none) (fun j => if j=0 then s₀ else none) := by
  intro j hj
  cases hr : σ[j] with
  | read i => simp [hr,Req.isWrite] at hj
  | write i =>
    have hget : σ[j.val]? = some (.write i) := by
      rw [List.getElem?_eq_getElem j.isLt]
      exact congrArg some (by simpa only [Fin.getElem_fin] using hr)
    have hpos := (hσ j i hget).1
    simp only [if_neg (Nat.ne_of_gt hpos)]

theorem shared_schedule_finite {n : ℕ} (p : ℕ) (s₀ : State n) (σ : List (Req n)) :
    scheduleCost p σ (fun _ => none) (fun j => if j=0 then s₀ else none) ≠ ⊤ := by
  unfold scheduleCost
  apply ENNReal.sum_ne_top.mpr
  intro j _hj
  cases hr : σ[j] with
  | read i =>
    cases s₀ <;> by_cases hj : j.val=0 <;>
      simp [stepCost,transCost,taskCost,hj]
  | write i =>
    cases s₀ <;> by_cases hj : j.val=0 <;>
      simp [stepCost,transCost,taskCost,hj]

theorem offlineCost_ne_top {n : ℕ} (p : ℕ) (s₀ : State n) (σ : List (Req n))
    (hσ : Admissible σ) : offlineCost p s₀ σ ≠ ⊤ := by
  apply ne_top_of_le_ne_top (shared_schedule_finite p s₀ σ)
  apply iInf_le_of_le (fun _ => none)
  apply iInf_le_of_le (fun j => if j=0 then s₀ else none)
  apply iInf_le_of_le (by simp)
  exact iInf_le _ (shared_schedule_admissible s₀ σ hσ)

end NonuniformCompetitive.SnoopyProof

end

/- Complete checked body: UpperBenchmark -/
section

set_option autoImplicit false

open scoped ENNReal

namespace NonuniformCompetitive.SnoopyProof

open NonuniformCompetitive.Snoopy

theorem benchmark_le_cost_potential {n : ℕ} (p : ℕ) (A : OnlineAlgorithm n)
    (h : List (Req n)) (hσ : Admissible h) :
    ((upperCounter p h).benchmark : ℝ≥0∞) ≤
      A.cost p h + offlinePotential (upperCounter p h) (A.after h) := by
  revert hσ
  induction h using List.reverseRecOn with
  | nil => intro _; simp [upperStart]
  | append_singleton h r ih =>
    intro hσ
    have hpre : Admissible h := admissible_prefix hσ
    have hval : ∀ i, r = .write i → (upperCounter p h).owner = some i := by
      intro i hi
      subst r
      exact write_owner_of_admissible_append p h i hσ
    have hl : r.isWrite = true → A.moment (h++[r]) = A.after h := by
      intro hr
      cases r with
      | read i => simp [Req.isWrite] at hr
      | write i => exact A.lookaheadZero h i
    have hp := upper_potential_step p (upperCounter p h) (upperCounter_count_le p h)
      r hval (A.after h) (A.moment (h++[r])) (A.after (h++[r])) hl
    have hbench : (upperCounter p (h++[r])).benchmark =
        (upperCounter p h).benchmark+upperCharge p (upperCounter p h) r := by
      rw [upperCounter_append_one,upperStep_benchmark]
    calc
      ((upperCounter p (h++[r])).benchmark : ℝ≥0∞) =
          ((upperCounter p h).benchmark : ℝ≥0∞)+upperCharge p (upperCounter p h) r := by
            rw [hbench,Nat.cast_add]
      _ ≤ (A.cost p h+offlinePotential (upperCounter p h) (A.after h))+
          upperCharge p (upperCounter p h) r := add_le_add (ih hpre) le_rfl
      _ = A.cost p h + (upperCharge p (upperCounter p h) r +
          offlinePotential (upperCounter p h) (A.after h)) := by ac_rfl
      _ ≤ A.cost p h + (stepCost p r (A.after h) (A.moment (h++[r]))
          (A.after (h++[r])) + offlinePotential (upperStep p (upperCounter p h) r)
          (A.after (h++[r]))) := add_le_add le_rfl hp
      _ = A.cost p (h++[r])+offlinePotential (upperCounter p (h++[r]))
          (A.after (h++[r])) := by rw [cost_append_singleton,upperCounter_append_one]; ac_rfl

theorem benchmark_le_cost_add {n : ℕ} (p : ℕ) (A : OnlineAlgorithm n)
    (h : List (Req n)) (hσ : Admissible h) :
    ((upperCounter p h).benchmark : ℝ≥0∞) ≤ A.cost p h+p := by
  exact (benchmark_le_cost_potential p A h hσ).trans
    (add_le_add le_rfl (by exact_mod_cast offlinePotential_le p h (A.after h)))

theorem benchmark_le_offline_add_ennreal {n : ℕ} (p : ℕ) (s₀ : State n)
    (h : List (Req n)) (hσ : Admissible h) :
    ((upperCounter p h).benchmark : ℝ≥0∞) ≤ offlineCost p s₀ h+p := by
  unfold offlineCost
  simp_rw [ENNReal.iInf_add]
  refine le_iInf (fun m => le_iInf (fun s => le_iInf (fun _hs => le_iInf (fun hw => ?_))))
  have hb := benchmark_le_cost_add p (clockAlgorithm m s) h hσ
  rwa [clockAlgorithm_cost h m s hw] at hb

theorem benchmark_le_offline_add {n : ℕ} (p : ℕ) (s₀ : State n)
    (h : List (Req n)) (hσ : Admissible h) :
    ((upperCounter p h).benchmark : ℝ) ≤ (offlineCost p s₀ h).toReal+p := by
  have hf := offlineCost_ne_top p s₀ h hσ
  have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf,by simp⟩)
    (benchmark_le_offline_add_ennreal p s₀ h hσ)
  simpa only [ENNReal.toReal_add hf (by simp : (p : ℝ≥0∞) ≠ ⊤),ENNReal.toReal_natCast] using hh

end NonuniformCompetitive.SnoopyProof

end

/- Complete checked body: UpperBound -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.SnoopyProof

open NonuniformCompetitive.Snoopy

theorem ratio_attained_direct (n p : ℕ) (hp : 1 ≤ p) (s₀ : State n) :
    ∃ A : RandomizedAlgorithm n p, A.IsCompetitiveFrom s₀ (ep p/(ep p-1)) := by
  refine ⟨mixedThreshold n p hp s₀,?_,(p:ℝ)+snoopyRatio p*(p:ℝ),?_⟩
  · exact mixedThreshold_starts n p hp s₀
  · intro h hσ
    rw [mixedThreshold_expCost p hp s₀ h hσ]
    apply ENNReal.ofReal_mono
    have hm := threshold_mean_bound p hp s₀ h hσ
    have hb := benchmark_le_offline_add p s₀ h hσ
    have hα : 0 ≤ snoopyRatio p := (by norm_num : (0:ℝ) ≤ 1).trans (snoopyRatio_gt_one p hp).le
    have hmul := mul_le_mul_of_nonneg_left hb hα
    change thresholdMeanCost p s₀ h ≤ snoopyRatio p*(offlineCost p s₀ h).toReal+
      ((p:ℝ)+snoopyRatio p*(p:ℝ))
    nlinarith

end NonuniformCompetitive.SnoopyProof

end

/- Complete checked body: OfflinePlans -/
section

set_option autoImplicit false

open scoped ENNReal

namespace NonuniformCompetitive.SnoopyProof

open NonuniformCompetitive.Snoopy

inductive Plan (n : ℕ) where
  | nil
  | cons (r : Req n) (moment after : State n) (tail : Plan n)

namespace Plan

variable {n : ℕ}

def requests : Plan n → List (Req n)
  | .nil => []
  | .cons r _ _ t => r :: t.requests

def moment : Plan n → ℕ → State n
  | .nil, _ => none
  | .cons _ m _ _, 1 => m
  | .cons _ _ _ t, k+2 => t.moment (k+1)
  | .cons _ _ _ _, 0 => none

def after (s : State n) : Plan n → ℕ → State n
  | _, 0 => s
  | .nil, _+1 => none
  | .cons _ _ a t, k+1 => t.after a k

def Valid (s : State n) : Plan n → Prop
  | .nil => True
  | .cons r m a t => (r.isWrite = true → m = s) ∧ t.Valid a

noncomputable def cost (p : ℕ) (s : State n) : Plan n → ℝ≥0∞
  | .nil => 0
  | .cons r m a t => stepCost p r s m a + t.cost p a

lemma after_zero (P : Plan n) (s : State n) : P.after s 0 = s := by cases P <;> rfl

lemma respects (P : Plan n) (s : State n) (h : P.Valid s) :
    RespectsWrites P.requests P.moment (P.after s) := by
  induction P generalizing s with
  | nil => intro j; exact Fin.elim0 j
  | cons r m a t ih =>
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact h.1
    · exact ih a h.2 k

lemma schedule_cost (P : Plan n) (p : ℕ) (s : State n) :
    scheduleCost p P.requests P.moment (P.after s) = P.cost p s := by
  induction P generalizing s with
  | nil => simp [scheduleCost,requests,cost]
  | cons r m a t ih =>
    change (∑ j : Fin (t.requests.length+1),
      stepCost p (r::t.requests)[j] ((Plan.cons r m a t).after s j)
        ((Plan.cons r m a t).moment (j+1)) ((Plan.cons r m a t).after s (j+1))) = _
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,Fin.val_succ,
      after,moment,after_zero]
    change stepCost p r s m a +
      (∑ j : Fin t.requests.length,
        stepCost p t.requests[j] (t.after a j) (t.moment (j+1)) (t.after a (j+1))) = _
    rw [show (∑ j : Fin t.requests.length,
        stepCost p t.requests[j] (t.after a j) (t.moment (j+1)) (t.after a (j+1))) = t.cost p a
      from ih a]
    rfl

lemma offline_le (P : Plan n) (p : ℕ) (s : State n) (h : P.Valid s) :
    offlineCost p s P.requests ≤ P.cost p s := by
  unfold offlineCost
  apply iInf_le_of_le P.moment
  apply iInf_le_of_le (P.after s)
  apply iInf_le_of_le (P.after_zero s)
  apply iInf_le_of_le (P.respects s h)
  exact (P.schedule_cost p s).le

end Plan

end NonuniformCompetitive.SnoopyProof

end

/- Complete checked body: FiniteLaw -/
section

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace NonuniformCompetitive.SnoopyProof

/-- A finite probability tree. Its branches are fixed before any algorithm coins are sampled. -/
inductive FiniteLaw (α : Type*) where
  | pure (a : α)
  | mix (q r : ℝ≥0) (sum_one : q + r = 1) (left right : FiniteLaw α)

namespace FiniteLaw

variable {α β : Type*}

def All (Q : FiniteLaw α) (P : α → Prop) : Prop :=
  match Q with
  | .pure a => P a
  | .mix _ _ _ L R => L.All P ∧ R.All P

noncomputable def mean (Q : FiniteLaw α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  match Q with
  | .pure a => f a
  | .mix q r _ L R => q * L.mean f + r * R.mean f

noncomputable def realMean (Q : FiniteLaw α) (f : α → ℝ) : ℝ :=
  match Q with
  | .pure a => f a
  | .mix q r _ L R => q * L.realMean f + r * R.realMean f

def map (f : α → β) (Q : FiniteLaw α) : FiniteLaw β :=
  match Q with
  | .pure a => .pure (f a)
  | .mix q r h L R => .mix q r h (L.map f) (R.map f)

def bind (Q : FiniteLaw α) (F : α → FiniteLaw β) : FiniteLaw β :=
  match Q with
  | .pure a => F a
  | .mix q r h L R => .mix q r h (L.bind F) (R.bind F)

lemma all_of_forall (Q : FiniteLaw α) {P : α → Prop} (h : ∀ a, P a) : Q.All P := by
  induction Q with
  | pure a => exact h a
  | mix q r hs L R hL hR => exact ⟨hL,hR⟩

lemma all_mono (Q : FiniteLaw α) {P T : α → Prop} (h : Q.All P) (hm : ∀ a, P a → T a) :
    Q.All T := by
  induction Q with
  | pure a => exact hm a h
  | mix q r hs L R hL hR => exact ⟨hL h.1,hR h.2⟩

@[simp] lemma all_map (Q : FiniteLaw α) (f : α → β) (P : β → Prop) :
    (Q.map f).All P ↔ Q.All (fun a => P (f a)) := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [map,All,hL,hR]

@[simp] lemma all_bind (Q : FiniteLaw α) (F : α → FiniteLaw β) (P : β → Prop) :
    (Q.bind F).All P ↔ Q.All (fun a => (F a).All P) := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [bind,All,hL,hR]

@[simp] lemma mean_const (Q : FiniteLaw α) (c : ℝ≥0∞) : Q.mean (fun _ => c) = c := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR =>
    simp only [mean,hL,hR,← add_mul,← ENNReal.coe_add,hs,ENNReal.coe_one,one_mul]

@[simp] lemma realMean_const (Q : FiniteLaw α) (c : ℝ) : Q.realMean (fun _ => c) = c := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR =>
    simp only [realMean,hL,hR,← add_mul,← NNReal.coe_add,hs,NNReal.coe_one,one_mul]

lemma mean_add (Q : FiniteLaw α) (f g : α → ℝ≥0∞) :
    Q.mean (fun a => f a + g a) = Q.mean f + Q.mean g := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [mean,hL,hR]; ring

lemma realMean_add (Q : FiniteLaw α) (f g : α → ℝ) :
    Q.realMean (fun a => f a + g a) = Q.realMean f + Q.realMean g := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [realMean,hL,hR]; ring

lemma realMean_sub (Q : FiniteLaw α) (f g : α → ℝ) :
    Q.realMean (fun a => f a - g a) = Q.realMean f - Q.realMean g := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [realMean,hL,hR]; ring

lemma mean_mul_const (Q : FiniteLaw α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    Q.mean (fun a => f a * c) = Q.mean f * c := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [mean,hL,hR]; ring

lemma realMean_mul_const (Q : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    Q.realMean (fun a => f a * c) = Q.realMean f * c := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [realMean,hL,hR]; ring

lemma mean_mono (Q : FiniteLaw α) {f g : α → ℝ≥0∞} (h : Q.All (fun a => f a ≤ g a)) :
    Q.mean f ≤ Q.mean g := by
  induction Q with
  | pure a => exact h
  | mix q r hs L R hL hR =>
    dsimp only [mean]
    gcongr
    · exact hL h.1
    · exact hR h.2

lemma realMean_nonneg (Q : FiniteLaw α) {f : α → ℝ} (h : Q.All (fun a => 0 ≤ f a)) :
    0 ≤ Q.realMean f := by
  induction Q with
  | pure a => exact h
  | mix q r hs L R hL hR =>
    exact add_nonneg (mul_nonneg q.coe_nonneg (hL h.1)) (mul_nonneg r.coe_nonneg (hR h.2))

lemma mean_congr (Q : FiniteLaw α) {f g : α → ℝ≥0∞} (h : Q.All (fun a => f a = g a)) :
    Q.mean f = Q.mean g := by
  apply le_antisymm
  · exact Q.mean_mono (Q.all_mono h (fun _ h => h.le))
  · exact Q.mean_mono (Q.all_mono h (fun _ h => h.ge))

lemma realMean_congr (Q : FiniteLaw α) {f g : α → ℝ} (h : Q.All (fun a => f a = g a)) :
    Q.realMean f = Q.realMean g := by
  induction Q with
  | pure a => exact h
  | mix q r hs L R hL hR => simp only [realMean,hL h.1,hR h.2]

@[simp] lemma mean_map (Q : FiniteLaw α) (f : α → β) (g : β → ℝ≥0∞) :
    (Q.map f).mean g = Q.mean (fun a => g (f a)) := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [map,mean,hL,hR]

@[simp] lemma realMean_map (Q : FiniteLaw α) (f : α → β) (g : β → ℝ) :
    (Q.map f).realMean g = Q.realMean (fun a => g (f a)) := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [map,realMean,hL,hR]

@[simp] lemma mean_bind (Q : FiniteLaw α) (F : α → FiniteLaw β) (g : β → ℝ≥0∞) :
    (Q.bind F).mean g = Q.mean (fun a => (F a).mean g) := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [bind,mean,hL,hR]

@[simp] lemma realMean_bind (Q : FiniteLaw α) (F : α → FiniteLaw β) (g : β → ℝ) :
    (Q.bind F).realMean g = Q.realMean (fun a => (F a).realMean g) := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [bind,realMean,hL,hR]

lemma mean_ofReal (Q : FiniteLaw α) {f : α → ℝ} (h : Q.All (fun a => 0 ≤ f a)) :
    Q.mean (fun a => ENNReal.ofReal (f a)) = ENNReal.ofReal (Q.realMean f) := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR =>
    simp only [mean,realMean,hL h.1,hR h.2]
    rw [ENNReal.ofReal_add (mul_nonneg q.coe_nonneg (L.realMean_nonneg h.1))
      (mul_nonneg r.coe_nonneg (R.realMean_nonneg h.2)),
      ENNReal.ofReal_mul q.coe_nonneg,ENNReal.ofReal_mul r.coe_nonneg,
      ENNReal.ofReal_coe_nnreal,ENNReal.ofReal_coe_nnreal]

lemma measurable_mean {Ω : Type*} [MeasurableSpace Ω] (Q : FiniteLaw α)
    (f : α → Ω → ℝ≥0∞) (hf : ∀ a, Measurable (f a)) :
    Measurable (fun ω => Q.mean (fun a => f a ω)) := by
  induction Q with
  | pure a => exact hf a
  | mix q r hs L R hL hR => exact (measurable_const.mul hL).add (measurable_const.mul hR)

lemma mean_lintegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Q : FiniteLaw α) (f : α → Ω → ℝ≥0∞) (hf : ∀ a, Measurable (f a)) :
    Q.mean (fun a => ∫⁻ ω, f a ω ∂μ) = ∫⁻ ω, Q.mean (fun a => f a ω) ∂μ := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR =>
    simp only [mean,hL,hR]
    have hLm : Measurable (fun ω => (q : ℝ≥0∞) * L.mean (fun a => f a ω)) :=
      measurable_const.mul (L.measurable_mean f hf)
    symm
    calc
      _ = (∫⁻ ω, (q : ℝ≥0∞) * L.mean (fun a => f a ω) ∂μ) +
          ∫⁻ ω, (r : ℝ≥0∞) * R.mean (fun a => f a ω) ∂μ :=
        lintegral_add_left hLm _
      _ = _ := by rw [lintegral_const_mul _ (L.measurable_mean f hf),
        lintegral_const_mul _ (R.measurable_mean f hf)]

end FiniteLaw
end NonuniformCompetitive.SnoopyProof

end

/- Complete checked body: ReleasePotential -/
section

set_option autoImplicit false

open scoped ENNReal

namespace NonuniformCompetitive.SnoopyProof

open NonuniformCompetitive.Snoopy

noncomputable def releasePotential {n : ℕ} (p : ℕ) (i : Fin n) (s : State n) : ℝ≥0∞ :=
  if s = some i then p else 0

lemma potential_transfer {n : ℕ} (p : ℕ) (i : Fin n) (s t : State n) :
    releasePotential p i s ≤ transCost p s t + releasePotential p i t := by
  by_cases hs : s = some i
  · subst s
    by_cases ht : t = some i
    · subst t
      simp [releasePotential, transCost]
    · simp [releasePotential, transCost, ht]
  · simp [releasePotential, hs]

lemma potential_step {n : ℕ} (p : ℕ) (i : Fin n) (r : Req n) (a b c : State n) :
    releasePotential p i a ≤ stepCost p r a b c + releasePotential p i c := by
  calc
    _ ≤ transCost p a b + releasePotential p i b := potential_transfer p i a b
    _ ≤ transCost p a b + (transCost p b c + releasePotential p i c) :=
      add_le_add le_rfl (potential_transfer p i b c)
    _ ≤ (transCost p a b + (transCost p b c + releasePotential p i c)) + taskCost r b :=
      le_add_of_nonneg_right bot_le
    _ = _ := by unfold stepCost; ac_rfl

lemma potential_read {n : ℕ} (p : ℕ) (i j : Fin n) (hij : i ≠ j) (a b c : State n) :
    releasePotential p i a ≤ stepCost p (Req.read j) a b c := by
  have hb : releasePotential p i b ≤ taskCost (Req.read j) b := by
    by_cases h : b = some i
    · subst b
      simp [releasePotential, taskCost, hij]
    · simp [releasePotential, h]
  calc
    _ ≤ transCost p a b + releasePotential p i b := potential_transfer p i a b
    _ ≤ transCost p a b + taskCost (Req.read j) b := add_le_add le_rfl hb
    _ ≤ stepCost p (Req.read j) a b c := le_add_of_nonneg_right bot_le

lemma potential_le_cost {n p : ℕ} (A : OnlineAlgorithm n) (i : Fin n) (l : List (Req n)) :
    releasePotential p i (A.after []) ≤ A.cost p l + releasePotential p i (A.after l) := by
  induction l generalizing A with
  | nil => simp
  | cons r l ih =>
    have h := potential_step p i r (A.after []) (A.moment [r]) (A.after [r])
    have ht := ih (shiftAlgorithm A [r])
    simp only [shiftAlgorithm, List.singleton_append] at ht
    calc
      _ ≤ stepCost p r (A.after []) (A.moment [r]) (A.after [r]) + releasePotential p i (A.after [r]) := h
      _ ≤ stepCost p r (A.after []) (A.moment [r]) (A.after [r]) +
          ((shiftAlgorithm A [r]).cost p l + releasePotential p i (A.after (r :: l))) :=
        add_le_add le_rfl ht
      _ = _ := by rw [cost_cons, add_assoc]

lemma private_release {n p : ℕ} (A : OnlineAlgorithm n) (i j : Fin n) (hij : i ≠ j)
    (hA : A.after [] = some i) (l : List (Req n)) :
    (p : ℝ≥0∞) ≤ A.cost p (l ++ [Req.read j]) := by
  have h := potential_le_cost (p := p) A i l
  rw [hA] at h
  simp only [releasePotential] at h
  have hr := potential_read p i j hij (A.after l) (A.moment (l ++ [Req.read j]))
    (A.after (l ++ [Req.read j]))
  calc
    _ ≤ A.cost p l + releasePotential p i (A.after l) := h
    _ ≤ A.cost p l + stepCost p (Req.read j) (A.after l) (A.moment (l ++ [Req.read j]))
        (A.after (l ++ [Req.read j])) := add_le_add le_rfl hr
    _ = _ := (cost_append_singleton A l (Req.read j)).symm

lemma writes_then_read_lower {n p : ℕ} (A : OnlineAlgorithm n) (i j : Fin n) (hij : i ≠ j)
    (k : ℕ) (hk : k ≤ p) : (k : ℝ≥0∞) ≤ A.cost p (List.replicate k (Req.write i) ++ [Req.read j]) := by
  induction k generalizing A with
  | zero => simp
  | succ k ih =>
    by_cases hA : A.after [] = some i
    · have hk' : ((k + 1 : ℕ) : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast hk
      exact hk'.trans (private_release A i j hij hA (List.replicate (k+1) (Req.write i)))
    · rw [List.replicate_succ, List.cons_append, cost_cons]
      have hw := write_cost_ge_one (p := p) A i hA
      rw [cost_cons, cost_nil, add_zero] at hw
      have ht := ih (shiftAlgorithm A [Req.write i]) (by omega)
      have hb := add_le_add hw ht
      simpa only [Nat.cast_add, Nat.cast_one, add_comm] using hb

end NonuniformCompetitive.SnoopyProof

end

/- Complete checked body: HardLaw -/
section

set_option autoImplicit false

open scoped ENNReal NNReal

namespace NonuniformCompetitive.SnoopyProof

open NonuniformCompetitive.Snoopy

noncomputable def hardStop (p : ℕ) : ℝ≥0 := ((p : ℝ≥0) + 1)⁻¹
noncomputable def hardGo (p : ℕ) : ℝ≥0 := (p : ℝ≥0) / ((p : ℝ≥0) + 1)

lemma hard_sum (p : ℕ) : hardStop p + hardGo p = 1 := by
  unfold hardStop hardGo
  have h : (p : ℝ≥0) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma hard_go_real (p : ℕ) : (hardGo p : ℝ) * ((p : ℝ) + 1) = p := by
  simp only [hardGo,NNReal.coe_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
  exact div_mul_cancel₀ _ (by positivity)

lemma hard_go_ennreal (p : ℕ) : (hardGo p : ℝ≥0∞) * ((p : ℝ≥0∞) + 1) = p := by
  have h : hardGo p * ((p : ℝ≥0) + 1) = p := by
    unfold hardGo
    exact div_mul_cancel₀ _ (by positivity)
  exact_mod_cast h

noncomputable def hardLaw (p : ℕ) : ℕ → FiniteLaw ℕ
  | 0 => .pure p
  | k + 1 => .mix (hardStop p) (hardGo p) (hard_sum p) (.pure 0) ((hardLaw p k).map Nat.succ)

lemma hard_writes_mean (p k : ℕ) : (hardLaw p k).realMean (fun w => (w : ℝ)) = p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [hardLaw,FiniteLaw.realMean,FiniteLaw.realMean_map,Nat.cast_zero,mul_zero,zero_add,
      Nat.cast_succ]
    rw [FiniteLaw.realMean_add,FiniteLaw.realMean_const,ih]
    exact hard_go_real p

lemma hard_support (p k : ℕ) : (hardLaw p k).All (fun w => w < k ∨ w = p + k) := by
  induction k with
  | zero => exact Or.inr (by omega)
  | succ k ih =>
    refine ⟨Or.inl (by omega),?_⟩
    rw [FiniteLaw.all_map]
    exact FiniteLaw.all_mono _ ih (by intro w hw; omega)

lemma hard_tail_mean (p k : ℕ) :
    (hardLaw p k).realMean (fun w => if w = p + k then 1 else 0) = (hardGo p : ℝ) ^ k := by
  induction k with
  | zero => simp [hardLaw,FiniteLaw.realMean]
  | succ k ih =>
    simp only [hardLaw,FiniteLaw.realMean,FiniteLaw.realMean_map]
    have hzero : ¬ 0 = p + (k + 1) := by omega
    have heq : (fun w : ℕ => if w.succ = p + (k + 1) then (1 : ℝ) else 0) =
        fun w => if w = p + k then 1 else 0 := by
      funext w
      have hiff : w.succ = p + (k + 1) ↔ w = p + k := by omega
      simp only [hiff]
    rw [if_neg hzero, mul_zero, zero_add,heq,ih,pow_succ]
    ring

lemma hard_min_mean (p : ℕ) :
    (hardLaw p p).realMean (fun w => ((min w p : ℕ) : ℝ)) =
      (p : ℝ) * (1 - (hardGo p : ℝ) ^ p) := by
  have heq : (hardLaw p p).All (fun w => ((min w p : ℕ) : ℝ) =
      (w : ℝ) - (if w = p + p then 1 else 0) * (p : ℝ)) := by
    apply FiniteLaw.all_mono _ (hard_support p p)
    intro w hw
    rcases hw with hw | rfl
    · have hn : w ≠ p + p := by omega
      simp [min_eq_left hw.le,hn]
    · simp only [min_eq_right (by omega : p ≤ p + p),ite_true,one_mul,Nat.cast_add]
      ring
  rw [FiniteLaw.realMean_congr _ heq,FiniteLaw.realMean_sub,hard_writes_mean,
    FiniteLaw.realMean_mul_const,hard_tail_mean]
  ring

lemma hard_go_lt_one (p : ℕ) : (hardGo p : ℝ) < 1 := by
  simp only [hardGo,NNReal.coe_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
  exact (div_lt_one (by positivity)).mpr (by linarith)

lemma hard_ep_identity (p : ℕ) (hp : 1 ≤ p) :
    (1 - (hardGo p : ℝ) ^ p) * (ep p / (ep p - 1)) = 1 ∧
      0 < 1 - (hardGo p : ℝ) ^ p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hbase : (hardGo p : ℝ) = (1 + 1 / (p : ℝ))⁻¹ := by
    simp only [hardGo,NNReal.coe_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
    field_simp
  have he : 1 < ep p := by
    unfold ep
    have hpos : (0 : ℝ) < 1 / (p : ℝ) := by positivity
    exact one_lt_pow₀ (by linarith : (1 : ℝ) < 1 + 1 / (p : ℝ)) (by omega)
  have hpow : (hardGo p : ℝ) ^ p = (ep p)⁻¹ := by rw [hbase,inv_pow]; rfl
  rw [hpow]
  constructor
  · field_simp [ne_of_gt (lt_trans zero_lt_one he), ne_of_gt (sub_pos.mpr he)]
  · exact sub_pos.mpr (inv_lt_one_of_one_lt₀ he)

lemma hard_suffix_lower {n p : ℕ} (A : OnlineAlgorithm n) (i j : Fin n) (hij : i ≠ j) (k : ℕ) :
    (p : ℝ≥0∞) ≤ (hardLaw p k).mean
      (fun w => A.cost p (List.replicate w (Req.write i) ++ [Req.read j])) := by
  induction k generalizing A with
  | zero => exact writes_then_read_lower A i j hij p le_rfl
  | succ k ih =>
    by_cases hA : A.after [] = some i
    · have h := (hardLaw p (k+1)).mean_mono
        ((hardLaw p (k+1)).all_of_forall (fun w => private_release (p := p) A i j hij hA
          (List.replicate w (Req.write i))))
      simpa only [FiniteLaw.mean_const] using h
    · simp only [hardLaw,FiniteLaw.mean,FiniteLaw.mean_map,List.replicate_zero,List.nil_append,
        List.replicate_succ,List.cons_append,cost_cons]
      rw [FiniteLaw.mean_add,FiniteLaw.mean_const]
      have hw := write_cost_ge_one (p := p) A i hA
      rw [cost_cons,cost_nil,add_zero] at hw
      have ht := ih (shiftAlgorithm A [Req.write i])
      calc
        (p : ℝ≥0∞) = (hardGo p : ℝ≥0∞) * (1 + (p : ℝ≥0∞)) := by
          rw [add_comm 1,hard_go_ennreal]
        _ ≤ (hardGo p : ℝ≥0∞) *
            (stepCost p (Req.write i) (A.after []) (A.moment [Req.write i]) (A.after [Req.write i]) +
            (hardLaw p k).mean (fun w => (shiftAlgorithm A [Req.write i]).cost p
              (List.replicate w (Req.write i) ++ [Req.read j]))) := by gcongr
        _ ≤ _ := le_add_of_nonneg_left bot_le

def hardPhase {n : ℕ} (i j : Fin n) (w : ℕ) : List (Req n) :=
  Req.read i :: (List.replicate w (Req.write i) ++ [Req.read j])

lemma hard_phase_lower {n p : ℕ} (A : OnlineAlgorithm n) (i j : Fin n) (hij : i ≠ j) :
    (p : ℝ≥0∞) ≤ (hardLaw p p).mean (fun w => A.cost p (hardPhase i j w)) := by
  simp only [hardPhase,cost_cons]
  rw [FiniteLaw.mean_add,FiniteLaw.mean_const]
  exact (hard_suffix_lower (shiftAlgorithm A [Req.read i]) i j hij p).trans
    (le_add_of_nonneg_left bot_le)

end NonuniformCompetitive.SnoopyProof

end

/- Complete checked body: RepeatedLaw -/
section

set_option autoImplicit false

open scoped ENNReal

namespace NonuniformCompetitive.SnoopyProof

open NonuniformCompetitive.Snoopy

namespace FiniteLaw

variable {α : Type*}

def iid (Q : FiniteLaw α) : ℕ → FiniteLaw (List α)
  | 0 => .pure []
  | k+1 => Q.bind (fun a => (iid Q k).map (List.cons a))

lemma iid_all (Q : FiniteLaw α) {P : α → Prop} (h : Q.All P) (k : ℕ) :
    (Q.iid k).All (fun l => ∀ a ∈ l, P a) := by
  induction k with
  | zero => simp [iid,All]
  | succ k ih =>
    rw [iid,all_bind]
    apply Q.all_mono h
    intro a ha
    rw [all_map]
    apply (Q.iid k).all_mono ih
    intro l hl b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact hl b hb

lemma iid_real_sum (Q : FiniteLaw α) (g : α → ℝ) (k : ℕ) :
    (Q.iid k).realMean (fun l => (l.map g).sum) = (k : ℝ) * Q.realMean g := by
  induction k with
  | zero => simp [iid,realMean]
  | succ k ih =>
    simp only [iid,realMean_bind,realMean_map,List.map_cons,List.sum_cons]
    have h : (fun a => (Q.iid k).realMean (fun l => g a + (l.map g).sum)) =
        fun a => g a + (k : ℝ) * Q.realMean g := by
      funext a
      rw [realMean_add,realMean_const,ih]
    rw [h,realMean_add,realMean_const]
    simp only [Nat.cast_succ]
    ring

end FiniteLaw

def phaseWord {n : ℕ} (i j : Fin n) (ws : List ℕ) : List (Req n) :=
  ws.flatMap (hardPhase i j)

lemma repeated_lower {n p : ℕ} (A : OnlineAlgorithm n) (i j : Fin n) (hij : i ≠ j) (k : ℕ) :
    (k : ℝ≥0∞) * p ≤ ((hardLaw p p).iid k).mean (fun ws => A.cost p (phaseWord i j ws)) := by
  induction k generalizing A with
  | zero => simp [FiniteLaw.iid,FiniteLaw.mean,phaseWord]
  | succ k ih =>
    simp only [FiniteLaw.iid,FiniteLaw.mean_bind,FiniteLaw.mean_map,phaseWord,List.flatMap_cons,
      cost_append]
    have h : (fun w => ((hardLaw p p).iid k).mean
        (fun ws => A.cost p (hardPhase i j w) +
          (shiftAlgorithm A (hardPhase i j w)).cost p (ws.flatMap (hardPhase i j)))) =
        fun w => A.cost p (hardPhase i j w) + ((hardLaw p p).iid k).mean
          (fun ws => (shiftAlgorithm A (hardPhase i j w)).cost p (phaseWord i j ws)) := by
      funext w
      rw [FiniteLaw.mean_add,FiniteLaw.mean_const]
      rfl
    rw [h,FiniteLaw.mean_add]
    have ht : (k : ℝ≥0∞) * p ≤ (hardLaw p p).mean (fun w => ((hardLaw p p).iid k).mean
        (fun ws => (shiftAlgorithm A (hardPhase i j w)).cost p (phaseWord i j ws))) := by
      have hm := (hardLaw p p).mean_mono ((hardLaw p p).all_of_forall
        (fun w => ih (shiftAlgorithm A (hardPhase i j w))))
      simpa only [FiniteLaw.mean_const] using hm
    have hh := add_le_add (hard_phase_lower (p := p) A i j hij) ht
    simpa only [Nat.cast_succ,add_mul,one_mul,add_comm] using hh

end NonuniformCompetitive.SnoopyProof

end

/- Complete checked body: AdmissibleWords -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.SnoopyProof

open NonuniformCompetitive.Snoopy

lemma admissible_append {n : ℕ} {l r : List (Req n)} (hl : Admissible l) (hr : Admissible r) :
    Admissible (l ++ r) := by
  intro k i hk
  by_cases h : k < l.length
  · rw [List.getElem?_append_left h] at hk
    obtain ⟨hp,hprev⟩ := hl k i hk
    refine ⟨hp,?_⟩
    rw [List.getElem?_append_left (by omega : k-1<l.length)]
    exact hprev
  · rw [List.getElem?_append_right (by omega)] at hk
    obtain ⟨hp,hprev⟩ := hr (k-l.length) i hk
    refine ⟨by omega,?_⟩
    rw [List.getElem?_append_right (by omega : l.length≤k-1)]
    have he : k-1-l.length = (k-l.length)-1 := by omega
    simpa only [he] using hprev

lemma read_writes_admissible {n : ℕ} (i : Fin n) (w : ℕ) :
    Admissible (Req.read i :: List.replicate w (Req.write i)) := by
  intro k j hk
  cases k with
  | zero => simp at hk
  | succ k =>
    have hkw : k < w := by
      by_contra hn
      simp [List.getElem?_eq_none (by simp; omega : (List.replicate w (Req.write i)).length ≤ k)] at hk
    have hj : i=j := by simpa [List.getElem?_replicate,hkw] using hk
    subst j
    refine ⟨by omega,?_⟩
    cases k with
    | zero => simp
    | succ k =>
      right
      simp [show k<w by omega]

lemma hardPhase_admissible {n : ℕ} (i j : Fin n) (w : ℕ) : Admissible (hardPhase i j w) := by
  have hr : Admissible [Req.read j] := by
    intro k a hk
    cases k <;> simp at hk
  exact admissible_append (read_writes_admissible i w) hr

end NonuniformCompetitive.SnoopyProof
end

/- Complete checked body: OfflinePhasePlans -/
section

set_option autoImplicit false

open scoped ENNReal

namespace NonuniformCompetitive.SnoopyProof

open NonuniformCompetitive.Snoopy

noncomputable def rentState {n : ℕ} (p w : ℕ) (i : Fin n) : State n :=
  if w < p then none else some i

def writePlan {n : ℕ} (i : Fin n) (s : State n) (tail : Plan n) : ℕ → Plan n
  | 0 => tail
  | w+1 => .cons (.write i) s s (writePlan i s tail w)

lemma writePlan_requests {n : ℕ} (i : Fin n) (s : State n) (tail : Plan n) (w : ℕ) :
    (writePlan i s tail w).requests = List.replicate w (.write i) ++ tail.requests := by
  induction w with
  | zero => rfl
  | succ w ih => simp only [writePlan,Plan.requests,List.replicate_succ,List.cons_append,ih]

lemma writePlan_valid {n : ℕ} (i : Fin n) (s : State n) (tail : Plan n)
    (h : tail.Valid s) (w : ℕ) : (writePlan i s tail w).Valid s := by
  induction w with
  | zero => exact h
  | succ w ih => exact ⟨fun _ => rfl,ih⟩

lemma writePlan_cost {n : ℕ} (p : ℕ) (i : Fin n) (s : State n) (tail : Plan n) (w : ℕ) :
    (writePlan i s tail w).cost p s = (w : ℝ≥0∞) * taskCost (.write i) s + tail.cost p s := by
  induction w with
  | zero => simp [writePlan]
  | succ w ih =>
    simp only [writePlan,Plan.cost,ih,stepCost,transCost,ite_true,zero_add,add_zero,Nat.cast_succ]
    ring

noncomputable def phasePlanInto {n : ℕ} (p : ℕ) (i j : Fin n) (w : ℕ) (tail : Plan n) : Plan n :=
  .cons (.read i) (rentState p w i) (rentState p w i)
    (writePlan i (rentState p w i) (.cons (.read j) none none tail) w)

lemma phasePlanInto_requests {n : ℕ} (p : ℕ) (i j : Fin n) (w : ℕ) (tail : Plan n) :
    (phasePlanInto p i j w tail).requests = hardPhase i j w ++ tail.requests := by
  simp [phasePlanInto,Plan.requests,writePlan_requests,hardPhase]

lemma phasePlanInto_valid {n : ℕ} (p : ℕ) (i j : Fin n) (w : ℕ) (tail : Plan n)
    (h : tail.Valid none) (s : State n) : (phasePlanInto p i j w tail).Valid s := by
  refine ⟨by simp [Req.isWrite],?_⟩
  apply writePlan_valid i (rentState p w i) (.cons (.read j) none none tail) ?_ w
  exact ⟨by simp [Req.isWrite],h⟩

lemma phasePlanInto_cost {n : ℕ} (p : ℕ) (i j : Fin n) (w : ℕ) (tail : Plan n) (s : State n) :
    (phasePlanInto p i j w tail).cost p s = transCost p s (rentState p w i) +
      (min w p : ℕ) + tail.cost p none := by
  unfold phasePlanInto
  simp only [Plan.cost,writePlan_cost]
  by_cases hw : w < p
  · simp [rentState,hw,stepCost,taskCost,transCost,min_eq_left hw.le,add_assoc]
  · simp [rentState,hw,stepCost,taskCost,transCost,min_eq_right (by omega : p≤w),add_assoc]

noncomputable def allPhasePlan {n : ℕ} (p : ℕ) (i j : Fin n) : List ℕ → Plan n
  | [] => .nil
  | w::ws => phasePlanInto p i j w (allPhasePlan p i j ws)

lemma allPhasePlan_requests {n : ℕ} (p : ℕ) (i j : Fin n) (ws : List ℕ) :
    (allPhasePlan p i j ws).requests = phaseWord i j ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [allPhasePlan,phasePlanInto_requests,ih,phaseWord,List.flatMap_cons]

lemma allPhasePlan_valid {n : ℕ} (p : ℕ) (i j : Fin n) (ws : List ℕ) (s : State n) :
    (allPhasePlan p i j ws).Valid s := by
  induction ws generalizing s with
  | nil => trivial
  | cons w ws ih => exact phasePlanInto_valid p i j w _ (ih none) s

lemma allPhasePlan_shared_cost {n : ℕ} (p : ℕ) (i j : Fin n) (ws : List ℕ) :
    (allPhasePlan p i j ws).cost p none = ((ws.map (fun w => min w p)).sum : ℕ) := by
  induction ws with
  | nil => simp [allPhasePlan,Plan.cost]
  | cons w ws ih =>
    rw [allPhasePlan,phasePlanInto_cost,ih]
    have ht : transCost p (none : State n) (rentState p w i) = 0 := by
      simp [transCost]
    simp [ht]

lemma allPhasePlan_cost_le {n : ℕ} (p : ℕ) (i j : Fin n) (ws : List ℕ) (s : State n) :
    (allPhasePlan p i j ws).cost p s ≤ (p : ℝ≥0∞) + ((ws.map (fun w => min w p)).sum : ℕ) := by
  cases ws with
  | nil => simp [allPhasePlan,Plan.cost]
  | cons w ws =>
    rw [allPhasePlan,phasePlanInto_cost,allPhasePlan_shared_cost]
    have ht : transCost p s (rentState p w i) ≤ p := by
      unfold transCost
      split
      · exact bot_le
      · cases s <;> simp
    simpa only [List.map_cons,List.sum_cons,Nat.cast_add,add_assoc] using
      add_le_add (add_le_add ht le_rfl) le_rfl

lemma phaseWord_admissible {n : ℕ} (i j : Fin n) (ws : List ℕ) : Admissible (phaseWord i j ws) := by
  induction ws with
  | nil => intro k a hk; simp [phaseWord] at hk
  | cons w ws ih => exact admissible_append (hardPhase_admissible i j w) ih

lemma offline_phaseWord_le {n : ℕ} (p : ℕ) (i j : Fin n) (ws : List ℕ) (s : State n) :
    offlineCost p s (phaseWord i j ws) ≤ (p : ℝ≥0∞) + ((ws.map (fun w => min w p)).sum : ℕ) := by
  rw [← allPhasePlan_requests p i j ws]
  exact (Plan.offline_le _ p s (allPhasePlan_valid p i j ws s)).trans
    (allPhasePlan_cost_le p i j ws s)

end NonuniformCompetitive.SnoopyProof

end

/- Complete checked body: LowerBound -/
section

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace NonuniformCompetitive.SnoopyProof

open NonuniformCompetitive.Snoopy

lemma randomized_repeated_lower {n p : ℕ} (A : RandomizedAlgorithm n p)
    (i j : Fin n) (hij : i ≠ j) (k : ℕ) :
    (k : ℝ≥0∞) * p ≤ ((hardLaw p p).iid k).mean (fun ws => A.expCost (phaseWord i j ws)) := by
  let := A.ms
  let := A.prob
  unfold RandomizedAlgorithm.expCost
  rw [FiniteLaw.mean_lintegral A.μ _ _ (fun ws => A.meas (phaseWord i j ws))]
  calc
    _ = ∫⁻ _ω, (k : ℝ≥0∞) * p ∂A.μ := by simp
    _ ≤ _ := lintegral_mono (fun ω => repeated_lower (A.alg ω) i j hij k)

lemma offline_phaseWord_real_le {n : ℕ} (p : ℕ) (i j : Fin n) (ws : List ℕ) (s : State n) :
    (offlineCost p s (phaseWord i j ws)).toReal ≤
      (p : ℝ) + ((ws.map (fun w => min w p)).sum : ℕ) := by
  have h := ENNReal.toReal_mono (by finiteness)
    (offline_phaseWord_le p i j ws s)
  simpa only [ENNReal.toReal_add (by finiteness : (p : ℝ≥0∞) ≠ ⊤)
    (by finiteness : (((ws.map (fun w => min w p)).sum : ℕ) : ℝ≥0∞) ≠ ⊤),
    ENNReal.toReal_natCast] using h

lemma hard_offline_mean (p k : ℕ) :
    ((hardLaw p p).iid k).realMean
      (fun ws => (((ws.map (fun w => min w p)).sum : ℕ) : ℝ)) =
      (k : ℝ) * ((p : ℝ) * (1 - (hardGo p : ℝ)^p)) := by
  have he : (fun ws : List ℕ => (((ws.map (fun w => min w p)).sum : ℕ) : ℝ)) =
      fun ws => (ws.map (fun w => ((min w p : ℕ) : ℝ))).sum := by
    funext ws
    induction ws with
    | nil => simp
    | cons w ws ih => simp only [List.map_cons,List.sum_cons,Nat.cast_add,ih]
  rw [he,FiniteLaw.iid_real_sum,hard_min_mean]

lemma lower_numeric_bound {n p : ℕ} (A : RandomizedAlgorithm n p) (s₀ : State n)
    (c a : ℝ) (hA : ∀ σ, Admissible σ →
      A.expCost σ ≤ ENNReal.ofReal (c*(offlineCost p s₀ σ).toReal+a))
    (i j : Fin n) (hij : i ≠ j) (k : ℕ) :
    (k : ℝ)*p ≤ max c 0 * ((p : ℝ)+(k : ℝ)*((p : ℝ)*(1-(hardGo p : ℝ)^p))) + max a 0 := by
  let C := max c 0
  let D := max a 0
  have hC : 0 ≤ C := le_max_right _ _
  have hD : 0 ≤ D := le_max_right _ _
  let g : List ℕ → ℝ := fun ws =>
    C*((p : ℝ)+(((ws.map (fun w => min w p)).sum : ℕ) : ℝ))+D
  have hg : ∀ ws, 0 ≤ g ws := by intro ws; dsimp [g]; positivity
  have hmean := ((hardLaw p p).iid k).mean_mono
    (((hardLaw p p).iid k).all_of_forall (fun ws =>
      (hA _ (phaseWord_admissible i j ws)).trans
        (ENNReal.ofReal_le_ofReal (show c*(offlineCost p s₀ (phaseWord i j ws)).toReal+a ≤ g ws from by
          have ho := offline_phaseWord_real_le p i j ws s₀
          have hn := ENNReal.toReal_nonneg (a := offlineCost p s₀ (phaseWord i j ws))
          have hc : c ≤ C := le_max_left _ _
          have ha : a ≤ D := le_max_left _ _
          dsimp [g]
          calc
            _ ≤ C*(offlineCost p s₀ (phaseWord i j ws)).toReal+D := by nlinarith
            _ ≤ _ := by gcongr))))
  have hm : ((hardLaw p p).iid k).realMean g =
      C*((p : ℝ)+(k : ℝ)*((p : ℝ)*(1-(hardGo p : ℝ)^p)))+D := by
    dsimp only [g]
    simp_rw [mul_comm C]
    rw [FiniteLaw.realMean_add,FiniteLaw.realMean_const,FiniteLaw.realMean_mul_const,
      FiniteLaw.realMean_add,FiniteLaw.realMean_const,hard_offline_mean]
  rw [FiniteLaw.mean_ofReal _ (((hardLaw p p).iid k).all_of_forall hg),hm] at hmean
  have hn : 0 ≤ C*((p : ℝ)+(k : ℝ)*((p : ℝ)*(1-(hardGo p : ℝ)^p)))+D := by
    rw [← hm]
    exact FiniteLaw.realMean_nonneg _ (((hardLaw p p).iid k).all_of_forall hg)
  have hlow := (randomized_repeated_lower A i j hij k).trans hmean
  have hcst : (k : ℝ≥0∞)*(p : ℝ≥0∞) = ENNReal.ofReal ((k : ℝ)*p) := by simp
  rw [hcst] at hlow
  exact (ENNReal.ofReal_le_ofReal_iff hn).mp hlow

lemma linear_coefficient_le {a b d : ℝ} (h : ∀ k : ℕ, (k : ℝ)*a ≤ (k : ℝ)*b+d) : a ≤ b := by
  by_contra hn
  have hab : 0 < a-b := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨k,hk⟩ := exists_nat_gt (d/(a-b))
  have hm : d < (k : ℝ)*(a-b) := (div_lt_iff₀ hab).mp hk
  have hh := h k
  nlinarith

theorem no_better_ratio_direct (n p : ℕ) (hn : 2 ≤ n) (hp : 1 ≤ p) (s₀ : State n)
    (A : RandomizedAlgorithm n p) (c : ℝ) (hA : A.IsCompetitiveFrom s₀ c) :
    ep p / (ep p - 1) ≤ c := by
  obtain ⟨a,ha⟩ := hA.2
  let i : Fin n := ⟨1,by omega⟩
  let j : Fin n := ⟨0,by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i,j] at this
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  obtain ⟨hid,hpos⟩ := hard_ep_identity p hp
  have hcoef : (p : ℝ) ≤ max c 0 * ((p : ℝ)*(1-(hardGo p : ℝ)^p)) := by
    apply linear_coefficient_le (d := max c 0 * p + max a 0)
    intro k
    have hh := lower_numeric_bound A s₀ c a ha i j hij k
    nlinarith
  have hscaled : (p : ℝ)*1 ≤ (p : ℝ)*(max c 0 * (1-(hardGo p : ℝ)^p)) := by
    nlinarith [hcoef]
  have hunit : 1 ≤ max c 0 * (1-(hardGo p : ℝ)^p) :=
    (mul_le_mul_iff_right₀ hp0).mp hscaled
  have hr : ep p/(ep p-1) ≤ max c 0 := by
    have hh : (1-(hardGo p : ℝ)^p)*(ep p/(ep p-1)) ≤ (1-(hardGo p : ℝ)^p)*max c 0 := by
      rw [hid,mul_comm]
      exact hunit
    exact (mul_le_mul_iff_right₀ hpos).mp hh
  have halpha : 0 < ep p/(ep p-1) :=
    (mul_pos_iff_of_pos_left hpos).mp (by rw [hid]; norm_num)
  by_cases hc : 0 ≤ c
  · simpa only [max_eq_left hc] using hr
  · rw [max_eq_right (le_of_not_ge hc)] at hr
    linarith

end NonuniformCompetitive.SnoopyProof

end

/- Complete checked body: SnoopyRoot -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.Snoopy

/-- Theorem 4 (Karlin, Manasse, McGeoch, Owicki, Algorithmica 11 (1994), p. 551), for the
single-block snoopy-caching task system of §3.1 (p. 550) with `n ≥ 2` processors and block size
`p − 1` (block-transfer cost `p ≥ 1`), from every initial state `s₀`:
1. no randomized on-line algorithm is `c`-competitive against an oblivious adversary for any
   `c < e_p / (e_p − 1)`;
2. some randomized on-line algorithm is `e_p / (e_p − 1)`-competitive.
Competitiveness is over admissible request sequences (every write of processor `i` directly
follows a read or write of `i`). -/
theorem optimal_ratio (n p : ℕ) (hn : 2 ≤ n) (hp : 1 ≤ p) (s₀ : State n) :
    (∀ (A : RandomizedAlgorithm n p) (c : ℝ), A.IsCompetitiveFrom s₀ c → ep p / (ep p - 1) ≤ c) ∧
      ∃ A : RandomizedAlgorithm n p, A.IsCompetitiveFrom s₀ (ep p / (ep p - 1)) := by
  constructor
  · intro A c hA
    exact NonuniformCompetitive.SnoopyProof.no_better_ratio_direct n p hn hp s₀ A c hA
  · exact NonuniformCompetitive.SnoopyProof.ratio_attained_direct n p hp s₀

end NonuniformCompetitive.Snoopy

end

open NonuniformCompetitive.Snoopy


theorem solution (n p : ℕ) (hn : 2 ≤ n) (hp : 1 ≤ p) (s₀ : State n) :
    (∀ (A : RandomizedAlgorithm n p) (c : ℝ), A.IsCompetitiveFrom s₀ c → ep p / (ep p - 1) ≤ c) ∧
      ∃ A : RandomizedAlgorithm n p, A.IsCompetitiveFrom s₀ (ep p / (ep p - 1)) := by
  exact NonuniformCompetitive.Snoopy.optimal_ratio n p hn hp s₀

#print axioms NonuniformCompetitive.Snoopy.optimal_ratio
#print axioms solution
