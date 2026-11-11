-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.HistoryCompatibleCertificate.compatible_certificate_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:25:49.094031+00:00
-- url     : https://prove2.me/submissions/45aab364-0a4e-4d19-833b-0e06cca2db2c

import Mathlib
import Definitions.Def_Q238K014
import Definitions.Def_Q238K023
import Theorems.Thm_OAI_MetricKMedianRecovery_valid_execution_bounded_price_strictness_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ExecutionState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

namespace AtomicStep

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {loc : D → X} {F : Finset X} {v lam eta : ℝ}
  {s s' : ExecutionState D X} (H : AtomicStep loc F v lam eta s s')

include H

lemma active_before (hz : 0 ≤ s.phase) (j : D)
    (hj : activeAt loc (1 - 3 * v) s'.phase s'.opened j) :
    activeAt loc (1 - 3 * v) s.phase s.opened j := by
  intro f hf
  exact lt_of_le_of_lt (H.phase_le hz) (hj f (H.opened_subset hf))

lemma active_budget_lower (hv1 : v < 1 / 6) (hz : 0 ≤ s.phase)
    (j : D) (hj : activeAt loc (1 - 3 * v) s.phase s.opened j) :
    s.phase ≤ s'.budget j := by
  have ht : 0 ≤ 1 - 3 * v := by linarith only [hv1]
  cases H with
  | regular i W tau hi hW hbid hpayment hdual =>
    simp only [regularUpdate, hj, ↓reduceIte]
    split_ifs with hw
    · exact (hbid j hw).1
    · exact le_rfl
  | free => simp only [freeUpdate, hj, ↓reduceIte, le_refl]
  | update =>
    simp only [phaseUpdate, hj, ↓reduceIte]
    calc
      s.phase = clippedAt loc (1 - 3 * v) s.phase s.opened j :=
        (clippedAt_of_active loc (1 - 3 * v) s.phase s.opened j ht hj).symm
      _ ≤ clippedAt loc (1 - 3 * v) ((1 + v ^ 2) * s.phase) s.opened j := by
        apply clippedAt_mono_phase
        nlinarith only [mul_nonneg (sq_nonneg v) hz]

lemma surviving_budget (hv1 : v < 1 / 6) (hz : 0 < s.phase)
    (j : D) (hj : activeAt loc (1 - 3 * v) s'.phase s'.opened j) :
    s'.budget j = s'.phase := by
  have hjold := H.active_before hz.le j hj
  have ht : 0 ≤ 1 - 3 * v := by linarith only [hv1]
  have htv : (1 - 3 * v) * v < 1 := by
    have hv1' : v < 1 := by linarith only [hv1]
    nlinarith only [hv1', sq_nonneg v]
  cases H with
  | regular i W tau hi hW hbid hpayment hdual =>
    simp only [regularUpdate, hjold, ↓reduceIte]
    split_ifs with hw
    · have hfar : v * s.phase < dist i (loc j) := by
        by_contra hh
        have hd := le_of_not_gt hh
        have hc := hj i (by simp [regularUpdate])
        change s.phase < (1 - 3 * v) * dist (loc j) i at hc
        rw [dist_comm (loc j) i] at hc
        have hmul := mul_le_mul_of_nonneg_left hd ht
        have htvs := mul_lt_mul_of_pos_right htv hz
        nlinarith only [hc, hmul, htvs]
      exact (hbid j hw).2.2.2 hfar
    · rfl
  | free => simp only [freeUpdate, hjold, ↓reduceIte]
  | update =>
    simp only [phaseUpdate, hjold, ↓reduceIte]
    exact clippedAt_of_active loc (1 - 3 * v) ((1 + v ^ 2) * s.phase) s.opened j ht hj

end AtomicStep
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Removal
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

lemma activeAt_of_superset {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q W : Finset X) (hQW : Q ⊆ W) (j : D)
    (hj : activeAt loc t z W j) : activeAt loc t z Q j :=
  fun f hf => hj f (hQW hf)

lemma inactive_connection_le_phase {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (j : D)
    (ht : 0 ≤ t) (hj : ¬activeAt loc t z Q j) :
    t * nearestDistance (loc j) Q ≤ z :=
  not_lt.mp (fun h => hj ((activeAt_iff loc t z Q j ht
    (inactive_nonempty loc t z Q j hj)).mpr h))

open Classical in
lemma regular_slack_gain {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    (loc : D → X) (v : ℝ) (s : ExecutionState D X) (i : X) (W : Finset X) (tau : D → ℝ)
    (ht : 0 ≤ 1 - 3 * v) (hW : s.opened ⊆ W)
    (hbid : admissibleBids loc (1 - 3 * v) (1 + v ^ 2) v s.phase W i tau)
    (hcommon : ∀ j, activeAt loc (1 - 3 * v) s.phase s.opened j → s.budget j = s.phase)
    (j : D) :
    max ((if activeAt loc (1 - 3 * v) s.phase W j then tau j
      else (1 - 3 * v) * nearestDistance (loc j) W) - (1 - 3 * v) * dist i (loc j)) 0 ≤
      clientSlack loc (1 - 3 * v) (regularUpdate loc (1 - 3 * v) s i W tau) j -
        clientSlack loc (1 - 3 * v) s j := by
  classical
  let t := 1 - 3 * v
  let c := clippedAt loc t s.phase (insert i s.opened) j
  have hcz : c ≤ s.phase := clippedAt_le_phase loc t s.phase (insert i s.opened) j
  have hci : c ≤ t * dist i (loc j) := by
    simpa only [dist_comm (loc j) i] using
      clippedAt_le_connection loc t s.phase (insert i s.opened) j i (Finset.mem_insert_self _ _) ht
  have hcc : c ≤ clippedAt loc t s.phase s.opened j :=
    clippedAt_antitone_open loc t s.phase s.opened (insert i s.opened) j ht (Finset.subset_insert _ _)
  by_cases hj : activeAt loc t s.phase s.opened j
  · have hbudget := hcommon j hj
    have hclip := clippedAt_of_active loc t s.phase s.opened j ht hj
    by_cases hw : activeAt loc t s.phase W j
    · change max ((if activeAt loc t s.phase W j then tau j else _) - t * dist i (loc j)) 0 ≤ _
      rw [ite_eq_left hw]
      change _ ≤ (if activeAt loc t s.phase s.opened j then
        if activeAt loc t s.phase W j then tau j else s.phase else s.budget j) - c -
        (s.budget j - clippedAt loc t s.phase s.opened j)
      rw [ite_eq_left hj, ite_eq_left hw, hbudget, hclip]
      apply max_le
      · linarith only [hci]
      · linarith only [hcz, (hbid j hw).1]
    · have hcw := inactive_connection_le_phase loc t s.phase W j ht hw
      change max ((if activeAt loc t s.phase W j then tau j else _) - t * dist i (loc j)) 0 ≤ _
      rw [ite_eq_right hw]
      change _ ≤ (if activeAt loc t s.phase s.opened j then
        if activeAt loc t s.phase W j then tau j else s.phase else s.budget j) - c -
        (s.budget j - clippedAt loc t s.phase s.opened j)
      rw [ite_eq_left hj, ite_eq_right hw, hbudget, hclip]
      apply max_le
      · linarith only [hci, hcw]
      · linarith only [hcz]
  · have hw : ¬activeAt loc t s.phase W j := fun h =>
      hj (activeAt_of_superset loc t s.phase s.opened W hW j h)
    have hQ := inactive_nonempty loc t s.phase s.opened j hj
    have hclip := clippedAt_of_inactive loc t s.phase s.opened j ht hj
    have hcw := mul_le_mul_of_nonneg_left (nearestDistance_antitone (loc j) s.opened W hQ hW) ht
    change max ((if activeAt loc t s.phase W j then tau j else _) - t * dist i (loc j)) 0 ≤ _
    rw [ite_eq_right hw]
    change _ ≤ (if activeAt loc t s.phase s.opened j then
      if activeAt loc t s.phase W j then tau j else s.phase else s.budget j) - c -
      (s.budget j - clippedAt loc t s.phase s.opened j)
    rw [ite_eq_right hj, hclip]
    rw [hclip] at hcc
    apply max_le
    · linarith only [hcw, hci]
    · linarith only [hcc]

lemma regular_payment_gain {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    (loc : D → X) (v : ℝ) (s : ExecutionState D X) (i : X) (W : Finset X) (tau : D → ℝ)
    (ht : 0 ≤ 1 - 3 * v) (hW : s.opened ⊆ W)
    (hbid : admissibleBids loc (1 - 3 * v) (1 + v ^ 2) v s.phase W i tau)
    (hcommon : ∀ j, activeAt loc (1 - 3 * v) s.phase s.opened j → s.budget j = s.phase) :
    openingPayment loc (1 - 3 * v) s.phase W i tau ≤
      totalSlack loc (1 - 3 * v) (regularUpdate loc (1 - 3 * v) s i W tau) -
        totalSlack loc (1 - 3 * v) s := by
  unfold openingPayment totalSlack
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum (fun j _ => regular_slack_gain loc v s i W tau ht hW hbid hcommon j)

namespace AtomicStep

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {loc : D → X} {F : Finset X} {v lam eta : ℝ}
  {s s' : ExecutionState D X} (H : AtomicStep loc F v lam eta s s')

include H

lemma budget_mono (hv1 : v < 1 / 6) (hz : 0 ≤ s.phase)
    (hcommon : ∀ j, activeAt loc (1 - 3 * v) s.phase s.opened j → s.budget j = s.phase)
    (j : D) : s.budget j ≤ s'.budget j := by
  by_cases hj : activeAt loc (1 - 3 * v) s.phase s.opened j
  · rw [hcommon j hj]
    exact H.active_budget_lower hv1 hz j hj
  · exact (H.inactive_frozen j hj).ge

lemma slack_mono (hv1 : v < 1 / 6) (hz : 0 ≤ s.phase)
    (hcommon : ∀ j, activeAt loc (1 - 3 * v) s.phase s.opened j → s.budget j = s.phase)
    (j : D) : clientSlack loc (1 - 3 * v) s j ≤ clientSlack loc (1 - 3 * v) s' j := by
  have ht : 0 ≤ 1 - 3 * v := by linarith only [hv1]
  have hbudget := H.budget_mono hv1 hz hcommon j
  cases H with
  | regular =>
    exact sub_le_sub hbudget (clippedAt_antitone_open loc (1 - 3 * v) s.phase s.opened _ j ht
      (Finset.subset_insert _ _))
  | free =>
    exact sub_le_sub hbudget (clippedAt_antitone_open loc (1 - 3 * v) s.phase s.opened _ j ht
      (Finset.subset_insert _ _))
  | update =>
    by_cases hj : activeAt loc (1 - 3 * v) s.phase s.opened j
    · simp only [clientSlack, phaseUpdate, hj, ↓reduceIte, hcommon j hj,
        clippedAt_of_active loc (1 - 3 * v) s.phase s.opened j ht hj, sub_self, le_refl]
    · have hzy : s.phase ≤ (1 + v ^ 2) * s.phase := by
        nlinarith only [mul_nonneg (sq_nonneg v) hz]
      have hj' := inactive_at_later_phase loc (1 - 3 * v) s.phase ((1 + v ^ 2) * s.phase)
        s.opened j hzy hj
      simp only [clientSlack, phaseUpdate, hj, ↓reduceIte,
        clippedAt_of_inactive loc (1 - 3 * v) s.phase s.opened j ht hj,
        clippedAt_of_inactive loc (1 - 3 * v) ((1 + v ^ 2) * s.phase) s.opened j ht hj', le_refl]

lemma total_slack_mono (hv1 : v < 1 / 6) (hz : 0 ≤ s.phase)
    (hcommon : ∀ j, activeAt loc (1 - 3 * v) s.phase s.opened j → s.budget j = s.phase) :
    totalSlack loc (1 - 3 * v) s ≤ totalSlack loc (1 - 3 * v) s' :=
  Finset.sum_le_sum (fun j _ => H.slack_mono hv1 hz hcommon j)

end AtomicStep

namespace ValidExecution

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {steps : ℕ} {v lam eta : ℝ} (E : ValidExecution D X steps v lam eta)

lemma active_budget (hv1 : v < 1 / 6) (n : ℕ) (hn : n ≤ steps) (j : D)
    (hj : activeAt E.location (1 - 3 * v) (E.state n).phase (E.state n).opened j) :
    (E.state n).budget j = (E.state n).phase := by
  cases n with
  | zero => rw [E.initial]; rfl
  | succ n =>
    exact (E.transition n (by omega)).surviving_budget hv1 (E.phase_pos n (by omega)) j hj

lemma total_slack_mono (hv1 : v < 1 / 6) (n : ℕ) (hn : n < steps) :
    totalSlack E.location (1 - 3 * v) (E.state n) ≤
      totalSlack E.location (1 - 3 * v) (E.state (n + 1)) :=
  (E.transition n hn).total_slack_mono hv1 (E.phase_pos n hn.le).le (E.active_budget hv1 n hn.le)

lemma regular_payment_gain (hv1 : v < 1 / 6) (n : ℕ) (hn : n < steps)
    (H : CertifiedRegularStep E.location E.regular v lam eta (E.state n) (E.state (n + 1))) :
    lam - (Fintype.card D : ℝ) * eta ≤
      totalSlack E.location (1 - 3 * v) (E.state (n + 1)) -
        totalSlack E.location (1 - 3 * v) (E.state n) := by
  obtain ⟨i, W, tau, _, hW, hbid, hpay, _, heq⟩ := H
  rw [heq]
  exact hpay.trans (MetricKMedianRecovery.regular_payment_gain E.location v (E.state n) i W tau
    (by linarith only [hv1]) hW hbid (E.active_budget hv1 n hn.le))

end ValidExecution

theorem valid_execution_payment
    {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    {steps : ℕ} (v lam eta : ℝ) (E : ValidExecution D X steps v lam eta)
    (paid : Finset ℕ) (hpaid : paid ⊆ Finset.range steps)
    (hregular : ∀ n ∈ paid, CertifiedRegularStep E.location E.regular v lam eta
      (E.state n) (E.state (n + 1)))
    (hv1 : v < 1 / 6) :
    (1 - 3 * v) * (∑ j, nearestDistance (E.location j) (E.state steps).opened) +
      (paid.card : ℝ) * (lam - (Fintype.card D : ℝ) * eta) ≤
      ∑ j, (E.state steps).budget j := by
  classical
  let L := lam - (Fintype.card D : ℝ) * eta
  have hsum : ∀ m ≤ steps, (∑ n ∈ Finset.range m, if n ∈ paid then L else 0) ≤
      totalSlack E.location (1 - 3 * v) (E.state m) := by
    intro m hm
    induction m with
    | zero =>
      rw [E.initial]
      simp [totalSlack, clientSlack, initialState, clippedAt]
    | succ m ih =>
      have hm' : m < steps := by omega
      have hprev := ih hm'.le
      rw [Finset.sum_range_succ]
      by_cases hp : m ∈ paid
      · rw [ite_eq_left hp]
        have hg := E.regular_payment_gain hv1 m hm' (hregular m hp)
        linarith only [hprev, hg]
      · rw [ite_eq_right hp, add_zero]
        exact hprev.trans (E.total_slack_mono hv1 m hm')
  have hfilter : (Finset.range steps).filter (fun n => n ∈ paid) = paid := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hpaid h, h⟩⟩
  have hpaid_sum : (∑ n ∈ Finset.range steps, if n ∈ paid then L else 0) =
      (paid.card : ℝ) * L := by
    rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul]
  have hbound := hsum steps le_rfl
  rw [hpaid_sum] at hbound
  have hfinal : totalSlack E.location (1 - 3 * v) (E.state steps) =
      (∑ j, (E.state steps).budget j) -
        (1 - 3 * v) * (∑ j, nearestDistance (E.location j) (E.state steps).opened) := by
    unfold totalSlack clientSlack
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact clippedAt_of_inactive E.location (1 - 3 * v) (E.state steps).phase
      (E.state steps).opened j (by linarith only [hv1]) (E.terminated j)
  rw [hfinal] at hbound
  linarith only [hbound]

lemma dualRowTerm_pair {D : Type*} [DecidableEq D]
    (P : Finset D) (r : D → D → Prop) (alpha d : D → ℝ)
    (hr : ∀ j k, r j k → ¬r k j) (hd : ∀ j, 0 ≤ d j) (k j : D) :
    (alpha k - 2 * d k) + (alpha j - 2 * d j) ≤
      dualRowTerm P r alpha d k j + dualRowTerm P r alpha d j k := by
  classical
  unfold dualRowTerm
  have hsym : (j ∈ P ∧ k ∈ P) ↔ (k ∈ P ∧ j ∈ P) := and_comm
  simp only [hsym]
  by_cases hp : k ∈ P ∧ j ∈ P <;> simp only [hp, true_and, ↓reduceIte]
  all_goals
    by_cases hjk : r j k
    · have hkj := hr j k hjk
      simp only [hjk, hkj, ↓reduceIte]
      linarith only
    · by_cases hkj : r k j
      · simp only [hjk, hkj, ↓reduceIte]
        linarith only
      · simp only [hjk, hkj, ↓reduceIte]
        linarith only [hd j, hd k]

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_EntryReplay
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.HistoryExecution
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma path_states {Y : Type*} {R : Y → Y → Prop} {a b : Y} (h : Relation.ReflTransGen R a b) :
    ∃ n : ℕ, ∃ state : ℕ → Y, state 0 = a ∧ state n = b ∧
      ∀ k, k < n → R (state k) (state (k+1)) := by
  induction h with
  | refl => exact ⟨0,fun _ => a,rfl,rfl,by omega⟩
  | @tail b c hab hbc ih =>
    obtain ⟨n,state,hzero,hend,hstep⟩ := ih
    let state' : ℕ → Y := fun k => if k ≤ n then state k else c
    refine ⟨n+1,state',by simpa only [state',Nat.zero_le,↓reduceIte] using hzero,?_,?_⟩
    · simp only [state',Nat.not_succ_le_self,↓reduceIte]
    · intro k hk
      by_cases hkn : k < n
      · simpa only [state',ite_eq_left hkn.le,ite_eq_left (Nat.succ_le_of_lt hkn)] using hstep k hkn
      · have he : k = n := by omega
        subst k
        simpa only [state',le_refl,↓reduceIte,Nat.not_succ_le_self,hend] using hbc

end MetricKMedianRecovery.HistoryExecution

namespace MetricKMedianRecovery.CountedHistoryExecution
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

theorem entry_replay (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (i : X)
    (hFB : Disjoint F B) (s : ExecutionState D X) (hopen : s.opened = Q) (hphase : s.phase = z)
    (h : PhaseSequence.Entry loc F B Q v z lam eta i) :
    ∃ s' : ExecutionState D X, Step loc F v lam eta s s' ∧
      s'.opened = insert i Q ∧ s'.phase = z := by
  rcases h.2 with hfree | ⟨hi,W,hQ,_,tau,hbid,hpay,hdual⟩
  · have hiF : i ∉ F := fun hi => Finset.disjoint_left.mp hFB hi hfree
    have he : (insert i Q ∩ F) = Q ∩ F := by
      ext x
      by_cases hx : x = i
      · subst x; simp [hiF]
      · simp [hx]
    refine ⟨freeUpdate loc (1-3*v) s i,⟨AtomicStep.free s i,?_⟩,?_,?_⟩
    · intro hlt
      have hc : ¬(Q ∩ F).card < (Q ∩ F).card := by omega
      exact (hc (by simpa only [freeUpdate,hopen,he] using hlt)).elim
    · simpa only [freeUpdate] using congrArg (insert i) hopen
    · exact hphase
  · have hw : s.opened ⊆ W := by simpa only [hopen] using hQ
    have hb : admissibleBids loc (1-3*v) (1+v^2) v s.phase W i tau := by
      simpa only [hphase] using hbid
    have hp : lam-(Fintype.card D:ℝ)*eta ≤ openingPayment loc (1-3*v) s.phase W i tau := by
      simpa only [hphase] using hpay
    have hd : ∀ i₀ ∈ F, ∀ a, activeAt loc (1-3*v) s.phase W a →
        openingDual loc (1-3*v) s.phase W i₀ tau a ≤ lam := by
      simpa only [hphase] using hdual
    refine ⟨regularUpdate loc (1-3*v) s i W tau,
      ⟨AtomicStep.regular s i W tau hi hw hb hp hd,?_⟩,?_,?_⟩
    · intro _
      exact ⟨i,W,tau,hi,hw,hb,hp,hd,rfl⟩
    · simpa only [regularUpdate] using congrArg (insert i) hopen
    · exact hphase

theorem prefix_replay (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (H : List X)
    (hFB : Disjoint F B) (h : PhaseSequence.Prefix loc F B v z lam eta Q H)
    (s : ExecutionState D X) (hopen : s.opened = Q) (hphase : s.phase = z) :
    ∃ s' : ExecutionState D X, Relation.ReflTransGen (Step loc F v lam eta) s s' ∧
      s'.opened = Q ∪ H.toFinset ∧ s'.phase = z := by
  induction h generalizing s with
  | nil Q => exact ⟨s,Relation.ReflTransGen.refl,by simpa using hopen,hphase⟩
  | @cons Q i H hi htail ih =>
    obtain ⟨s1,hstep,hs1,hz1⟩ := entry_replay loc F B Q v z lam eta i hFB s hopen hphase hi
    obtain ⟨s2,hrest,hs2,hz2⟩ := ih s1 hs1 hz1
    refine ⟨s2,hrest.head hstep,?_,hz2⟩
    simpa only [List.toFinset_cons,Finset.insert_union,Finset.union_insert] using hs2

theorem history_replay (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ) (q : ℕ)
    (T : List (List X)) (hFB : Disjoint F B) (h : PhaseHistoryTransfer.History loc F B v lam eta q Q T)
    (s : ExecutionState D X) (hopen : s.opened = Q) (hphase : s.phase = (1+v^2)^q) :
    ∃ s' : ExecutionState D X, Relation.ReflTransGen (Step loc F v lam eta) s s' ∧
      s'.opened = PhaseHistoryTransfer.after Q T ∧ s'.phase = (1+v^2)^(q+T.length) := by
  induction h generalizing s with
  | nil q Q => exact ⟨s,Relation.ReflTransGen.refl,hopen,by simpa using hphase⟩
  | @cons q Q H T hhead htail ih =>
    obtain ⟨s1,hsteps,hs1,hz1⟩ := prefix_replay loc F B Q v ((1+v^2)^q) lam eta H
      hFB hhead.1 s hopen hphase
    let s2 := phaseUpdate loc (1-3*v) (1+v^2) s1
    have hupdate : Step loc F v lam eta s1 s2 := by
      constructor
      · apply AtomicStep.update
        simpa only [PhaseSequence.Maximal,hs1,hz1] using hhead.2
      · intro hlt
        have he : s2.opened = s1.opened := rfl
        rw [he] at hlt
        exact (Nat.lt_irrefl _ hlt).elim
    have hopen2 : s2.opened = Q ∪ H.toFinset := hs1
    have hphase2 : s2.phase = (1+v^2)^(q+1) := by
      change (1+v^2)*s1.phase = _
      rw [hz1,pow_succ (1+v^2) q,mul_comm]
    obtain ⟨s3,hrest,hs3,hz3⟩ := ih s2 hopen2 hphase2
    refine ⟨s3,(hsteps.tail hupdate).trans hrest,hs3,?_⟩
    simpa only [List.length_cons,Nat.add_right_comm,Nat.add_assoc] using hz3

end MetricKMedianRecovery.CountedHistoryExecution

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_RegularDualWitness
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

lemma final_dual_of_rows {D : Type*} [DecidableEq D]
    (C P : Finset D) (r : D → D → Prop) (alpha d : D → ℝ) (lam : ℝ)
    (hC : C.Nonempty) (hr : ∀ j k, r j k → ¬r k j) (hd : ∀ j, 0 ≤ d j)
    (hrows : ∀ k ∈ C, (∑ j ∈ C, dualRowTerm P r alpha d k j) ≤ lam) :
    (∑ j ∈ C, (alpha j - 2 * d j)) ≤ lam := by
  classical
  have hp := Finset.sum_le_sum (s := C) (fun k _ =>
    Finset.sum_le_sum (s := C) (fun j _ => dualRowTerm_pair P r alpha d hr hd k j))
  have hswap : (∑ x ∈ C, ∑ y ∈ C, dualRowTerm P r alpha d y x) =
      ∑ x ∈ C, ∑ y ∈ C, dualRowTerm P r alpha d x y := Finset.sum_comm
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum] at hp
  rw [hswap] at hp
  have hb := Finset.sum_le_sum (s := C) hrows
  rw [Finset.sum_const, nsmul_eq_mul] at hb
  have hc : 0 < (C.card : ℝ) := by exact_mod_cast hC.card_pos
  nlinarith only [hp, hb, hc]

namespace AtomicStep

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {loc : D → X} {F : Finset X} {v lam eta : ℝ}
  {s s' : ExecutionState D X} (H : AtomicStep loc F v lam eta s s')

include H

lemma preserves_connection_bound (hv1 : v < 1 / 6) (j : D) (f : X)
    (hf : f ∈ s.opened) (hb : s.budget j ≤ (1 - 3 * v) * dist (loc j) f) :
    s'.budget j ≤ (1 - 3 * v) * dist (loc j) f := by
  classical
  have ht : 0 ≤ 1 - 3 * v := by linarith only [hv1]
  by_cases hj : activeAt loc (1 - 3 * v) s.phase s.opened j
  · have hz := (hj f hf).le
    cases H with
    | regular i W tau hi hW hbid hpay hdual =>
      simp only [regularUpdate, hj, ↓reduceIte]
      split_ifs with hw
      · exact (hbid j hw).2.2.1 f (hW hf)
      · exact hz
    | free => simpa only [freeUpdate, hj, ↓reduceIte] using hz
    | update =>
      simpa only [phaseUpdate, hj, ↓reduceIte] using
        clippedAt_le_connection loc (1 - 3 * v) ((1 + v ^ 2) * s.phase) s.opened j f hf ht
  · rw [H.inactive_frozen j hj]
    exact hb

end AtomicStep

lemma AtomicStep.witness_cases {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    {loc : D → X} {F : Finset X} {v lam eta : ℝ} {s s' : ExecutionState D X}
    (H : AtomicStep loc F v lam eta s s') :
    Nonempty (RegularDualWitness loc F v lam s s') ∨
      (∃ i, s' = freeUpdate loc (1 - 3 * v) s i) ∨
      s' = phaseUpdate loc (1 - 3 * v) (1 + v ^ 2) s := by
  cases H with
  | regular i W tau hi hW hbid hpay hdual =>
    exact Or.inl ⟨⟨i, W, tau, hW, hbid, hdual, rfl⟩⟩
  | free i => exact Or.inr (Or.inl ⟨i, rfl⟩)
  | update => exact Or.inr (Or.inr rfl)

namespace ValidExecution

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {steps : ℕ} {v lam eta : ℝ} (E : ValidExecution D X steps v lam eta)

lemma precedes_asymm (j k : D) (h : E.precedes j k) : ¬E.precedes k j := by
  intro h'
  rcases h with h | ⟨he, h⟩ <;> rcases h' with h' | ⟨he', h'⟩
  · omega
  · omega
  · omega
  · exact (lt_asymm h h')

lemma finalBudget_at_removal (j : D) :
    E.finalBudget j = (E.state ((E.removal j).val + 1)).budget j :=
  E.budget_frozen (Nat.succ_le_of_lt (E.removal j).isLt) le_rfl j (E.removal_inactive j)

lemma finalBudget_le_connection (hv1 : v < 1 / 6) (n : ℕ) (hn : n ≤ steps)
    (j : D) (hj : activeAt E.location (1 - 3 * v) (E.state n).phase (E.state n).opened j)
    (f : X) (hf : f ∈ (E.state n).opened) :
    E.finalBudget j ≤ (1 - 3 * v) * dist (E.location j) f := by
  have hinv : ∀ m, n ≤ m → m ≤ steps →
      (E.state m).budget j ≤ (1 - 3 * v) * dist (E.location j) f := by
    intro m hnm hm
    induction m, hnm using Nat.le_induction with
    | base => rw [E.active_budget hv1 n hn j hj]; exact (hj f hf).le
    | succ m hnm ih =>
      exact (E.transition m (by omega)).preserves_connection_bound hv1 j f
        ((E.opened_mono hnm (by omega)) hf) (ih (by omega))
  exact hinv steps hn le_rfl

lemma freezing_removes_contributor (hv : 0 < v) (hv1 : v < 1 / 6)
    (i : X) (n : ℕ) (hn : n < steps)
    (W : RegularDualWitness E.location E.regular v lam (E.state n) (E.state (n + 1)))
    (hfreeze : dist i W.facility ≤ (1 + 3 * v) * (E.state n).phase / 2)
    (j : D) (hc : E.Contributor i j) : (E.removal j).val ≤ n := by
  by_contra h
  have hbefore : n + 1 ≤ (E.removal j).val := by omega
  have ha := (E.active_iff_before_removal (n + 1) (by omega) j).mpr hbefore
  have hf : W.facility ∈ (E.state (n + 1)).opened := by
    have heq := congrArg ExecutionState.opened W.updated
    rw [heq]; exact Finset.mem_insert_self _ _
  have hbudget := E.finalBudget_le_connection hv1 (n + 1) (by omega) j ha W.facility hf
  have hz : (E.state n).phase < (1 - 3 * v) * dist (E.location j) W.facility := by
    simpa only [W.updated, regularUpdate] using ha W.facility hf
  have hm := mul_lt_mul_of_pos_left hz (show 0 < 1 + 3 * v by linarith only [hv])
  have hd := dist_nonneg (x := E.location j) (y := W.facility)
  have hc1 : (1 - 3 * v) * dist (E.location j) W.facility ≤ dist (E.location j) W.facility := by
    nlinarith only [mul_nonneg hv.le hd]
  have hc2 : (1 + 3 * v) * ((1 - 3 * v) * dist (E.location j) W.facility) ≤
      dist (E.location j) W.facility := by
    nlinarith only [mul_nonneg (sq_nonneg v) hd]
  have htri : dist (E.location j) W.facility ≤ dist i (E.location j) + dist i W.facility := by
    simpa only [dist_comm (E.location j) i] using dist_triangle (E.location j) i W.facility
  unfold Contributor at hc
  linarith only [hbudget, hfreeze, hm, hc1, hc2, htri, hc]

end ValidExecution

lemma dualRowTerm_le_bid {D X : Type*} [DecidableEq D] [PseudoMetricSpace X]
    (loc : D → X) (P : Finset D) (r : D → D → Prop) (alpha : D → ℝ)
    (t z : ℝ) (Q : Finset X) (i : X) (k j : D)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hkP : k ∉ P) (hz : alpha k ≤ z)
    (hcap : ∀ f ∈ Q, alpha k ≤ t * dist (loc k) f)
    (hfuture : ¬r j k → alpha k ≤ clippedAt loc t z Q j) :
    dualRowTerm P r alpha (fun a => dist i (loc a)) k j ≤
      max (clippedAt loc t z Q j - dist i (loc j)) 0 := by
  classical
  unfold dualRowTerm
  simp only [hkP, false_and, ↓reduceIte]
  by_cases hr : r j k
  · rw [ite_eq_left hr]
    apply le_trans _ (le_max_left _ _)
    by_cases hj : activeAt loc t z Q j
    · rw [clippedAt_of_active loc t z Q j ht hj]
      linarith only [hz, dist_nonneg (x := i) (y := loc j),
        dist_nonneg (x := i) (y := loc k)]
    · rw [clippedAt_of_inactive loc t z Q j ht hj]
      have htri := capped_triangle_row loc t (alpha k) Q i k j ht ht1
        (inactive_nonempty loc t z Q j hj) hcap
      linarith only [htri]
  · rw [ite_eq_right hr, sub_zero]
    exact (sub_le_sub_right (hfuture hr) _).trans (le_max_left _ _)

lemma sum_dualRow_le_bidRow {D X : Type*} [Fintype D] [DecidableEq D] [PseudoMetricSpace X]
    (loc : D → X) (C P : Finset D) (r : D → D → Prop) (alpha : D → ℝ)
    (t z : ℝ) (Q : Finset X) (i : X) (k : D)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hkP : k ∉ P) (hz : alpha k ≤ z)
    (hcap : ∀ f ∈ Q, alpha k ≤ t * dist (loc k) f)
    (hfuture : ∀ j ∈ C, ¬r j k → alpha k ≤ clippedAt loc t z Q j) :
    (∑ j ∈ C, dualRowTerm P r alpha (fun a => dist i (loc a)) k j) ≤
      bidRow loc t z Q i := by
  classical
  calc
    _ ≤ ∑ j ∈ C, max (clippedAt loc t z Q j - dist i (loc j)) 0 :=
      Finset.sum_le_sum (fun j hj => dualRowTerm_le_bid loc P r alpha t z Q i k j
        ht ht1 hkP hz hcap (hfuture j hj))
    _ ≤ bidRow loc t z Q i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
        (fun j _ _ => le_max_right _ _)

namespace ValidExecution

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {steps : ℕ} {v lam eta : ℝ} (E : ValidExecution D X steps v lam eta)

lemma unfrozen_regular_budget (hv : 0 < v) (hv1 : v < 1 / 6)
    (i : X) (k : D) (hc : E.Contributor i k)
    (W : RegularDualWitness E.location E.regular v lam
      (E.state (E.removal k)) (E.state ((E.removal k).val + 1)))
    (hnf : ¬E.RegularFreezesAt i (E.removal k)) :
    E.finalBudget k = (E.state (E.removal k)).phase := by
  have hz := (E.phase_pos (E.removal k) (E.removal k).isLt.le).le
  have hnotfreeze : (1 + 3 * v) * (E.state (E.removal k)).phase / 2 <
      dist i W.facility := lt_of_not_ge (fun h => hnf ⟨W, h⟩)
  have hfar : v * (E.state (E.removal k)).phase < dist W.facility (E.location k) := by
    by_contra h
    have hnear := le_of_not_gt h
    have htri : dist i W.facility ≤ dist i (E.location k) + dist W.facility (E.location k) := by
      simpa only [dist_comm (E.location k) W.facility] using dist_triangle i (E.location k) W.facility
    have hvv : v ^ 2 ≤ v := by nlinarith only [hv, hv1]
    have hmul := mul_le_mul_of_nonneg_right hvv hz
    have hcap := E.final_cap k
    change E.finalBudget k ≤ _ at hcap
    unfold Contributor at hc
    nlinarith only [hnear, htri, hmul, hcap, hc, hnotfreeze]
  rw [E.finalBudget_at_removal k, W.updated]
  simp only [regularUpdate, E.removal_active k, ↓reduceIte]
  split_ifs with hw
  · exact (W.admissible k hw).2.2.2 hfar
  · rfl

lemma phase_removal_budget (k : D) (n : ℕ)
    (hn : (E.removal k).val = n)
    (hupdate : E.state (n + 1) = phaseUpdate E.location (1 - 3 * v) (1 + v ^ 2) (E.state n)) :
    E.finalBudget k = clippedAt E.location (1 - 3 * v) ((1 + v ^ 2) * (E.state n).phase)
      (E.state n).opened k := by
  have ha := E.removal_active k
  rw [hn] at ha
  rw [E.finalBudget_at_removal k, hn, hupdate]
  simp only [phaseUpdate, ha, ↓reduceIte]

lemma removal_row [DecidableEq D] (hv : 0 < v) (hv1 : v < 1 / 6) (hlam : 0 < lam)
    (i : X) (hi : i ∈ E.regular) (C : Finset D) (k : D) (hc : E.Contributor i k)
    (hnf : ¬E.RegularFreezesAt i (E.removal k)) :
    (∑ j ∈ C, dualRowTerm ∅ E.precedes E.finalBudget (fun a => dist i (E.location a)) k j) ≤ lam := by
  classical
  have ht : 0 ≤ 1 - 3 * v := by linarith only [hv1]
  have ht1 : 1 - 3 * v ≤ 1 := by linarith only [hv]
  let n := (E.removal k).val
  have hn : n < steps := (E.removal k).isLt
  have hopenrow : E.finalBudget k = (E.state n).phase →
      (∑ j ∈ C, dualRowTerm ∅ E.precedes E.finalBudget (fun a => dist i (E.location a)) k j) ≤ lam := by
    intro hb
    apply le_trans (sum_dualRow_le_bidRow E.location C ∅ E.precedes E.finalBudget
      (1 - 3 * v) (E.state n).phase (E.state n).opened i k ht ht1 (by simp) hb.le
      (fun f hf => hb ▸ (E.removal_active k f hf).le) ?_)
      (E.no_overbid hv hv1 hlam n hn.le i hi)
    intro j _ hnot
    have hnj : n ≤ (E.removal j).val := by
      by_contra hh
      exact hnot (Or.inl (by omega))
    have ha := (E.active_iff_before_removal n hn.le j).mpr hnj
    rw [clippedAt_of_active E.location (1 - 3 * v) (E.state n).phase (E.state n).opened j ht ha, hb]
  rcases (E.transition n hn).witness_cases with hW | hW | heq
  · obtain ⟨W⟩ := hW
    exact hopenrow (E.unfrozen_regular_budget hv hv1 i k hc W hnf)
  · obtain ⟨h, heq⟩ := hW
    apply hopenrow
    have ha : activeAt E.location (1 - 3 * v) (E.state n).phase (E.state n).opened k :=
      E.removal_active k
    rw [E.finalBudget_at_removal k, heq]
    simp only [freeUpdate, ha, ↓reduceIte]
  · have hb := E.phase_removal_budget k n rfl heq
    apply le_trans (sum_dualRow_le_bidRow E.location C ∅ E.precedes E.finalBudget
      (1 - 3 * v) ((1 + v ^ 2) * (E.state n).phase) (E.state n).opened i k ht ht1 (by simp)
      (hb ▸ clippedAt_le_phase E.location (1 - 3 * v) _ (E.state n).opened k)
      (fun f hf => hb ▸ clippedAt_le_connection E.location (1 - 3 * v) _ (E.state n).opened k f hf ht) ?_)
      (by simpa only [heq, phaseUpdate] using E.no_overbid hv hv1 hlam (n + 1) (by omega) i hi)
    intro j _ hnot
    by_cases ha : activeAt E.location (1 - 3 * v) ((1 + v ^ 2) * (E.state n).phase) (E.state n).opened j
    · rw [clippedAt_of_active E.location (1 - 3 * v) _ (E.state n).opened j ht ha]
      rw [hb]
      exact clippedAt_le_phase E.location (1 - 3 * v) _ (E.state n).opened k
    · have hnj : (E.removal j).val = n := by
        have hbefore : ¬(n + 1 ≤ (E.removal j).val) := by
          intro hh
          apply ha
          simpa only [heq, phaseUpdate] using (E.active_iff_before_removal (n + 1) (by omega) j).mpr hh
        have hnge : n ≤ (E.removal j).val := by
          by_contra hh
          exact hnot (Or.inl (by omega))
        omega
      have hjalpha : E.finalBudget k ≤ E.finalBudget j := by
        by_contra hh
        exact hnot (Or.inr ⟨hnj, lt_of_not_ge hh⟩)
      rw [E.phase_removal_budget j n hnj heq] at hjalpha
      exact hjalpha

end ValidExecution

lemma lastRelation_asymm {D : Type*} [DecidableEq D] (P : Finset D) (r : D → D → Prop)
    (hr : ∀ j k, r j k → ¬r k j) (j k : D) (h : lastRelation P r j k) :
    ¬lastRelation P r k j := by
  rintro ⟨hk, hj | hkj⟩
  · exact h.1 hj
  · rcases h.2 with hp | hjk
    · exact hk hp
    · exact hr j k hjk hkj

namespace ValidExecution

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {steps : ℕ} {v lam eta : ℝ} (E : ValidExecution D X steps v lam eta)

lemma witness_active_removal (hv : 0 < v) (hv1 : v < 1 / 6)
    (i : X) (n : ℕ) (hn : n < steps)
    (W : RegularDualWitness E.location E.regular v lam (E.state n) (E.state (n + 1)))
    (hfreeze : dist i W.facility ≤ (1 + 3 * v) * (E.state n).phase / 2)
    (j : D) (hc : E.Contributor i j)
    (ha : activeAt E.location (1 - 3 * v) (E.state n).phase W.witness j) :
    (E.removal j).val = n := by
  have hu := E.freezing_removes_contributor hv hv1 i n hn W hfreeze j hc
  have hl := (E.active_iff_before_removal n hn.le j).mp
    (activeAt_of_superset E.location (1 - 3 * v) (E.state n).phase (E.state n).opened W.witness
      W.contains j ha)
  omega

lemma witness_active_budget (n : ℕ)
    (W : RegularDualWitness E.location E.regular v lam (E.state n) (E.state (n + 1)))
    (j : D) (hr : (E.removal j).val = n)
    (ha : activeAt E.location (1 - 3 * v) (E.state n).phase W.witness j) :
    E.finalBudget j = W.bid j := by
  have haq := activeAt_of_superset E.location (1 - 3 * v) (E.state n).phase
    (E.state n).opened W.witness W.contains j ha
  rw [E.finalBudget_at_removal j, hr]
  have heq := congrArg (fun s => s.budget j) W.updated
  simpa only [regularUpdate, haq, ha, ↓reduceIte] using heq

lemma witness_inactive_budget (n : ℕ)
    (W : RegularDualWitness E.location E.regular v lam (E.state n) (E.state (n + 1)))
    (j : D) (hr : (E.removal j).val = n)
    (ha : ¬activeAt E.location (1 - 3 * v) (E.state n).phase W.witness j) :
    E.finalBudget j = (E.state n).phase := by
  have haq := E.removal_active j
  rw [hr] at haq
  rw [E.finalBudget_at_removal j, hr]
  have heq := congrArg (fun s => s.budget j) W.updated
  simpa only [regularUpdate, haq, ha, ↓reduceIte] using heq

lemma contributor_dual_bound [DecidableEq D] (hv : 0 < v) (hv1 : v < 1 / 6) (hlam : 0 < lam)
    (i : X) (hi : i ∈ E.regular) (C : Finset D) (hC : C.Nonempty)
    (hcontributors : ∀ j ∈ C, E.Contributor i j) :
    (∑ j ∈ C, (E.finalBudget j - 2 * dist i (E.location j))) ≤ lam := by
  classical
  have ht : 0 ≤ 1 - 3 * v := by linarith only [hv1]
  have ht1 : 1 - 3 * v ≤ 1 := by linarith only [hv]
  by_cases hex : ∃ n, n < steps ∧ E.RegularFreezesAt i n
  · let n := Nat.find hex
    have hn : n < steps := (Nat.find_spec hex).1
    obtain ⟨W, hfreeze⟩ := (Nat.find_spec hex).2
    let P := C.filter (fun j => activeAt E.location (1 - 3 * v) (E.state n).phase W.witness j)
    have hP : ∀ j, j ∈ P ↔ j ∈ C ∧
        activeAt E.location (1 - 3 * v) (E.state n).phase W.witness j := fun _ => Finset.mem_filter
    have hPrank : ∀ j ∈ P, (E.removal j).val = n := by
      intro j hj
      exact E.witness_active_removal hv hv1 i n hn W hfreeze j
        (hcontributors j ((hP j).mp hj).1) ((hP j).mp hj).2
    have hPbudget : ∀ j ∈ P, E.finalBudget j = W.bid j := by
      intro j hj
      exact E.witness_active_budget n W j (hPrank j hj) ((hP j).mp hj).2
    have hranks : ∀ j ∈ C, (E.removal j).val ≤ n := fun j hj =>
      E.freezing_removes_contributor hv hv1 i n hn W hfreeze j (hcontributors j hj)
    apply final_dual_of_rows C P (lastRelation P E.precedes) E.finalBudget
      (fun j => dist i (E.location j)) lam hC
      (lastRelation_asymm P E.precedes E.precedes_asymm) (fun _ => dist_nonneg)
    intro k hk
    by_cases hkP : k ∈ P
    · have hak := ((hP k).mp hkP).2
      have hdual := W.dual i hi k hak
      apply le_trans _ hdual
      calc
        _ ≤ ∑ j ∈ C, if activeAt E.location (1 - 3 * v) (E.state n).phase W.witness j then
            max (W.bid j - dist i (E.location j)) 0
          else max (W.bid k - 2 * dist i (E.location j) - dist i (E.location k)) 0 := by
          apply Finset.sum_le_sum
          intro j hj
          by_cases hjP : j ∈ P
          · have haj := ((hP j).mp hjP).2
            simp only [dualRowTerm, hkP, hjP, true_and, ↓reduceIte, lastRelation,
              not_true_eq_false, false_and, sub_zero, hPbudget j hjP, haj]
            exact le_max_left _ _
          · have haj : ¬activeAt E.location (1 - 3 * v) (E.state n).phase W.witness j := by
              intro ha; exact hjP ((hP j).mpr ⟨hj, ha⟩)
            simp only [dualRowTerm, hkP, hjP, and_false, ↓reduceIte, lastRelation,
              not_false_eq_true, true_or, and_self, hPbudget k hkP, haj]
            linarith only [le_max_left (W.bid k - 2 * dist i (E.location j) - dist i (E.location k)) 0]
        _ ≤ openingDual E.location (1 - 3 * v) (E.state n).phase W.witness i W.bid k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
          intro j _ _
          split_ifs <;> exact le_max_right _ _
    · have hkn : (E.removal k).val ≤ n := hranks k hk
      rcases lt_or_eq_of_le hkn with hkn | hkn
      · have hnotfreeze : ¬E.RegularFreezesAt i (E.removal k) := by
          intro hh
          exact Nat.find_min hex hkn ⟨(E.removal k).isLt, hh⟩
        have hrow := E.removal_row hv hv1 hlam i hi C k (hcontributors k hk) hnotfreeze
        convert hrow using 1
        all_goals try with_reducible_and_instances rfl
        apply Finset.sum_congr rfl
        intro j hj
        have hrel : lastRelation P E.precedes j k ↔ E.precedes j k := by
          simp only [lastRelation, hkP, false_or]
          constructor
          · exact fun h => h.2
          · intro hjk
            refine ⟨?_, hjk⟩
            intro hjP
            have hjn := hPrank j hjP
            rcases hjk with h | ⟨h, _⟩ <;> omega
        simp only [dualRowTerm, hkP, false_and, Finset.notMem_empty, hrel, ↓reduceIte]
      · have haw : ¬activeAt E.location (1 - 3 * v) (E.state n).phase W.witness k := by
          intro hh; exact hkP ((hP k).mpr ⟨hk, hh⟩)
        have hb := E.witness_inactive_budget n W k hkn haw
        have haq := E.removal_active k
        rw [hkn] at haq
        apply le_trans (sum_dualRow_le_bidRow E.location C P (lastRelation P E.precedes) E.finalBudget
          (1 - 3 * v) (E.state n).phase (E.state n).opened i k ht ht1 hkP hb.le
          (fun f hf => hb ▸ (haq f hf).le) ?_)
          (E.no_overbid hv hv1 hlam n hn.le i hi)
        intro j hj hnot
        have hnj : n ≤ (E.removal j).val := by
          by_contra hh
          have hjn : (E.removal j).val < n := by omega
          have hjP : j ∉ P := by intro h; have he := hPrank j h; omega
          exact hnot ⟨hjP, Or.inr (Or.inl (by omega))⟩
        have haj := (E.active_iff_before_removal n hn.le j).mpr hnj
        rw [clippedAt_of_active E.location (1 - 3 * v) (E.state n).phase (E.state n).opened j ht haj, hb]
  · apply final_dual_of_rows C ∅ E.precedes E.finalBudget (fun j => dist i (E.location j)) lam
      hC E.precedes_asymm (fun _ => dist_nonneg)
    intro k hk
    exact E.removal_row hv hv1 hlam i hi C k (hcontributors k hk)
      (fun h => hex ⟨E.removal k, (E.removal k).isLt, h⟩)

end ValidExecution

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_ValidExecutionFinalDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

theorem valid_execution_final_dual
    {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    {steps : ℕ} (v lam eta : ℝ) (E : ValidExecution D X steps v lam eta)
    (hv : 0 < v) (hv1 : v < 1 / 6) (hlam : 0 < lam)
    (i : X) (hi : i ∈ E.regular) :
    (∑ j, max ((E.state steps).budget j - 2 * dist i (E.location j)) 0) ≤ lam := by
  classical
  let C := Finset.univ.filter (E.Contributor i)
  have heq : (∑ j, max ((E.state steps).budget j - 2 * dist i (E.location j)) 0) =
      ∑ j ∈ C, (E.finalBudget j - 2 * dist i (E.location j)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    change max (E.finalBudget j - 2 * dist i (E.location j)) 0 = _
    by_cases hc : E.Contributor i j
    · rw [ite_eq_left hc, max_eq_left (sub_nonneg.mpr hc.le)]
    · rw [ite_eq_right hc, max_eq_right (sub_nonpos.mpr (not_lt.mp hc))]
  rw [heq]
  by_cases hC : C.Nonempty
  · exact E.contributor_dual_bound hv hv1 hlam i hi C hC
      (fun _ hj => (Finset.mem_filter.mp hj).2)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hC, Finset.sum_empty]
    exact hlam.le

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RegularCardBounds
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CountedHistoryExecution
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma regular_card_bounds (loc : D → X) (F : Finset X) (v lam eta : ℝ)
    (s s' : ExecutionState D X) (h : AtomicStep loc F v lam eta s s') :
    (s.opened ∩ F).card ≤ (s'.opened ∩ F).card ∧
    (s'.opened ∩ F).card ≤ (s.opened ∩ F).card+1 := by
  constructor
  · apply Finset.card_le_card
    intro x hx
    exact Finset.mem_inter.mpr ⟨h.opened_subset (Finset.mem_inter.mp hx).1,
      (Finset.mem_inter.mp hx).2⟩
  · have hi (Q : Finset X) (i : X) : (insert i Q ∩ F).card ≤ (Q ∩ F).card+1 := by
      calc
        (insert i Q ∩ F).card ≤ (insert i (Q ∩ F)).card := by
          apply Finset.card_le_card
          intro x hx
          rcases Finset.mem_inter.mp hx with ⟨hx,hF⟩
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hx,hF⟩)
        _ ≤ (Q ∩ F).card+1 := Finset.card_insert_le _ _
    cases h with
    | regular i W tau hiF hW hb hp hd => exact hi s.opened i
    | free i => exact hi s.opened i
    | update hm => exact Nat.le_succ _

lemma count_increases (c : ℕ → ℕ) (n : ℕ)
    (hc : ∀ k, k < n → c k ≤ c (k+1) ∧ c (k+1) ≤ c k+1) :
    ((Finset.range n).filter (fun k => c k < c (k+1))).card+c 0 = c n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hind := ih (fun k hk => hc k (by omega))
    have hstep := hc n (by omega)
    have hn : n ∉ (Finset.range n).filter (fun k => c k < c (k+1)) := by simp
    rw [Finset.range_add_one,Finset.filter_insert]
    by_cases hinc : c n < c (n+1)
    · rw [ite_eq_left hinc,Finset.card_insert_of_notMem hn]
      omega
    · rw [ite_eq_right hinc]
      omega

theorem valid_counted_execution (loc : D → X) (F B : Finset X) (v lam eta : ℝ)
    (T : List (List X)) (hFB : Disjoint F B)
    (hfar : ∀ j i, i ∈ F → 1 ≤ dist i (loc j))
    (h : PhaseHistoryTransfer.History loc F B v lam eta 0 ∅ T)
    (hterm : ∀ j, ¬activeAt loc (1-3*v) ((1+v^2)^T.length)
      (PhaseHistoryTransfer.after ∅ T) j) :
    ∃ steps : ℕ, ∃ E : ValidExecution D X steps v lam eta, ∃ paid : Finset ℕ,
      E.location = loc ∧ E.regular = F ∧
      (E.state steps).opened = PhaseHistoryTransfer.after ∅ T ∧
      (E.state steps).phase = (1+v^2)^T.length ∧
      paid ⊆ Finset.range steps ∧
      (∀ n ∈ paid, CertifiedRegularStep E.location E.regular v lam eta
        (E.state n) (E.state (n+1))) ∧
      paid.card = (PhaseHistoryTransfer.after ∅ T ∩ F).card := by
  obtain ⟨last,hpath,hopen,hphase⟩ := history_replay loc F B ∅ v lam eta 0 T hFB h
    (initialState D X) rfl (by simp [initialState])
  have hphase' : last.phase = (1+v^2)^T.length := by simpa using hphase
  obtain ⟨steps,state,hzero,hend,hsteps⟩ := HistoryExecution.path_states hpath
  let E : ValidExecution D X steps v lam eta :=
    { location := loc
      regular := F
      far_initially := hfar
      state := state
      initial := hzero
      transition := fun n hn => (hsteps n hn).1
      terminated := by intro j; simpa only [hend,hopen,hphase'] using hterm j }
  let c : ℕ → ℕ := fun n => ((state n).opened ∩ F).card
  let paid := (Finset.range steps).filter (fun n => c n < c (n+1))
  have hc : ∀ k, k < steps → c k ≤ c (k+1) ∧ c (k+1) ≤ c k+1 := by
    intro k hk
    exact regular_card_bounds loc F v lam eta (state k) (state (k+1)) (hsteps k hk).1
  have hcard := count_increases c steps hc
  have hzeroC : c 0 = 0 := by simp [c,hzero,initialState]
  have hendC : c steps = (PhaseHistoryTransfer.after ∅ T ∩ F).card := by
    simp only [c,hend,hopen]
  refine ⟨steps,E,paid,rfl,rfl,?_,?_,Finset.filter_subset _ _,?_,?_⟩
  · simpa only [E,hend] using hopen
  · simpa only [E,hend] using hphase'
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hn,hinc⟩
    exact (hsteps n (Finset.mem_range.mp hn)).2 hinc
  · simpa only [hzeroC,hendC,Nat.add_zero] using hcard

end MetricKMedianRecovery.CountedHistoryExecution

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_ValidExecutionClusterStrictness
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

theorem valid_execution_cluster_strictness
    {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    {steps : ℕ} (v lam eta T : ℝ) (E : ValidExecution D X steps v lam eta)
    (C : Finset D) (hC : C.Nonempty) (i : X) (hi : i ∈ E.regular)
    (hv : 0 < v) (hv1 : v < 1/6) (hlam : 0 < lam) (hT : 0 < T)
    (hP : 0 < ∑ j ∈ C, dist i (E.location j))
    (hprice : lam ≤ T*(∑ j ∈ C, dist i (E.location j)))
    (hsmall : v^2 ≤ strictnessGap T/(6*(T+2))) :
    (∑ j ∈ C, (E.state steps).budget j) ≤
      lam+(2-strictnessGap T/2)*(∑ j ∈ C, dist i (E.location j)) := by
  classical
  let e : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  let incl : C ↪ D := Function.Embedding.subtype _
  let cluster := e.toEmbedding.trans incl
  have hd : (∑ j, dist i (E.location (cluster j))) = ∑ j ∈ C, dist i (E.location j) := by
    calc
      _ = ∑ j : C, dist i (E.location j.val) := Equiv.sum_comp e _
      _ = _ := Finset.sum_coe_sort C (fun j => dist i (E.location j))
  have hb : (∑ j, (E.state steps).budget (cluster j)) = ∑ j ∈ C, (E.state steps).budget j := by
    calc
      _ = ∑ j : C, (E.state steps).budget j.val := Equiv.sum_comp e _
      _ = _ := Finset.sum_coe_sort C ((E.state steps).budget)
  have hq : 0 < Fintype.card C := by simpa only [Fintype.card_coe] using Finset.card_pos.mpr hC
  have h := valid_execution_bounded_price_strictness_s238 v lam eta T E cluster i hq hi
    hv hv1 hlam hT (hd ▸ hP) (hd ▸ hprice) hsmall
  simpa only [hb,hd,strictnessGap] using h

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_FinalBudgetPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.HistoryCompatibleCertificate
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma final_budget_pos {steps : ℕ} {v lam eta : ℝ}
    (E : ValidExecution D X steps v lam eta) (hvsmall : v < 1/6) (j : D) :
    0 < (E.state steps).budget j := by
  rw [E.budget_frozen (Nat.succ_le_of_lt (E.removal j).isLt) le_rfl j (E.removal_inactive j)]
  exact (E.phase_pos _ (E.removal j).isLt.le).trans_le
    ((E.transition _ (E.removal j).isLt).active_budget_lower hvsmall
      (E.phase_pos _ (E.removal j).isLt.le).le j (E.removal_active j))

theorem compatible_certificate_s238_oai (loc : D → X) (F B : Finset X) (v lam eta : ℝ)
    (T : List (List X)) (hFB : Disjoint F B)
    (hfar : ∀ j i, i ∈ F → 1 ≤ dist i (loc j))
    (h : PhaseHistoryTransfer.History loc F B v lam eta 0 ∅ T)
    (hterm : ∀ j, ¬activeAt loc (1-3*v) ((1+v^2)^T.length)
      (PhaseHistoryTransfer.after ∅ T) j)
    (hv : 0 < v) (hv1 : v < 1/6) (hlam : 0 < lam) :
    ∃ alpha : D → ℝ,
      (∀ j, 0 < alpha j) ∧
      (∀ i ∈ F, (∑ j, max (alpha j-2*dist i (loc j)) 0) ≤ lam) ∧
      ((1-3*v)*(∑ j, nearestDistance (loc j) (PhaseHistoryTransfer.after ∅ T)) +
        ((PhaseHistoryTransfer.after ∅ T ∩ F).card:ℝ)*(lam-(Fintype.card D:ℝ)*eta) ≤
          ∑ j, alpha j) ∧
      (∀ (C : Finset D), C.Nonempty → ∀ i ∈ F, ∀ b : ℝ, 0 < b →
        0 < (∑ j ∈ C, dist i (loc j)) →
        lam ≤ b*(∑ j ∈ C, dist i (loc j)) →
        v^2 ≤ strictnessGap b/(6*(b+2)) →
        (∑ j ∈ C, alpha j) ≤ lam+(2-strictnessGap b/2)*(∑ j ∈ C, dist i (loc j))) := by
  obtain ⟨steps,E,paid,hloc,hF,hopen,_,hpaid,hcert,hcount⟩ :=
    CountedHistoryExecution.valid_counted_execution loc F B v lam eta T hFB hfar h hterm
  refine ⟨(E.state steps).budget,final_budget_pos E hv1,?_,?_,?_⟩
  · intro i hi
    have hiE : i ∈ E.regular := by simpa only [hF] using hi
    simpa only [hloc] using valid_execution_final_dual v lam eta E hv hv1 hlam i hiE
  · simpa only [hloc,hopen,hcount] using valid_execution_payment v lam eta E paid hpaid hcert hv1
  · intro C hC i hi b hb hP hprice hsmall
    have hiE : i ∈ E.regular := by simpa only [hF] using hi
    have hPE : 0 < ∑ j ∈ C, dist i (E.location j) := by simpa only [hloc] using hP
    have hpriceE : lam ≤ b*(∑ j ∈ C, dist i (E.location j)) := by simpa only [hloc] using hprice
    simpa only [hloc] using valid_execution_cluster_strictness v lam eta b E C hC i hiE
      hv hv1 hlam hb hPE hpriceE hsmall

end MetricKMedianRecovery.HistoryCompatibleCertificate

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.MetricKMedianRecovery.HistoryCompatibleCertificate.compatible_certificate_s238_oai.{u_1, u_2} := @OAI.MetricKMedianRecovery.HistoryCompatibleCertificate.compatible_certificate_s238_oai.{u_1, u_2}
