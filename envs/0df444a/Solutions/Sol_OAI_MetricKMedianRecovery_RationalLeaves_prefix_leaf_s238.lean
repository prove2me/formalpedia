-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.RationalLeaves.prefix_leaf_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:31:16.645103+00:00
-- url     : https://prove2.me/submissions/28cace3d-b082-4e55-93e5-11dd17c8605a

import Mathlib
import Definitions.Def_Q238K017
import Definitions.Def_Q238K018
import Definitions.Def_Q238K021

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
namespace Entry
variable {loc : D → X} {F B Q Q' : Finset X} {v z lam eta : ℝ} {i : X}
lemma mem (h : Entry loc F B Q v z lam eta i) : i ∈ F ∪ B := by
  rcases h.2 with h|h
  · exact Finset.mem_union_right _ h
  · exact Finset.mem_union_left _ h.1
end Entry

namespace Prefix
variable {loc : D → X} {F B Q Q' : Finset X} {v z lam eta : ℝ} {H G : List X}

lemma append (h : Prefix loc F B v z lam eta Q H)
    (hG : Prefix loc F B v z lam eta (Q ∪ H.toFinset) G) :
    Prefix loc F B v z lam eta Q (H++G) := by
  induction h with
  | nil => simpa using hG
  | @cons Q i H hi ht ih =>
    apply Prefix.cons hi
    apply ih
    simpa only [List.toFinset_cons,Finset.union_insert,Finset.insert_union] using hG

lemma opened_subset (h : Prefix loc F B v z lam eta Q H) : H.toFinset ⊆ F ∪ B := by
  intro i hi
  induction h with
  | nil => simp at hi
  | cons ha ht ih =>
    simp only [List.toFinset_cons,Finset.mem_insert] at hi
    rcases hi with rfl|hi
    · exact ha.mem
    · exact ih hi

end Prefix

end PhaseSequence
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_BaselineDual
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PriceTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X]

lemma baseline_dual_le (loc : D → X) (Q : Finset X) (t z : ℝ) (i : X) (a : D)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (ha : activeAt loc t z Q a) :
    openingDual loc t z Q i (fun _ => z) a ≤ bidRow loc t z Q i := by
  classical
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : activeAt loc t z Q j
  · simp only [hj,↓reduceIte,clippedAt_of_active loc t z Q j ht hj]
    exact le_rfl
  · simp only [hj,↓reduceIte,clippedAt_of_inactive loc t z Q j ht hj]
    exact max_le_max (capped_triangle_row loc t z Q i a j ht ht1
      (inactive_nonempty loc t z Q j hj) (fun f hf => (ha f hf).le)) le_rfl

theorem tight_dual_openable (loc : D → X) (F Q : Finset X) (v z lam : ℝ)
    (tau : D → ℝ) (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z)
    (hbox : ∀ j, activeAt loc (1-3*v) z Q j →
      z ≤ tau j ∧ tau j ≤ (1+v^2)*z ∧ ∀ f ∈ Q, tau j ≤ (1-3*v)*dist (loc j) f)
    (i : X) (a : D) (ha : activeAt loc (1-3*v) z Q a)
    (htight : openingDual loc (1-3*v) z Q i tau a = lam)
    (hrows : ∀ k ∈ F, ∀ b, activeAt loc (1-3*v) z Q b →
      openingDual loc (1-3*v) z Q k tau b ≤ lam) :
    etaOpenable loc F Q (1-3*v) (1+v^2) v z lam 0 i := by
  classical
  let newtau : D → ℝ := fun j => if dist i (loc j) ≤ v*z then tau j else z
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have ht1 : 1-3*v ≤ 1 := by linarith only [hv]
  have hK : z ≤ (1+v^2)*z := by nlinarith only [mul_nonneg (sq_nonneg v) hz.le]
  have hsmall : ∀ j, activeAt loc (1-3*v) z Q j → newtau j ≤ tau j := by
    intro j hj
    dsimp only [newtau]
    split_ifs
    · exact le_rfl
    · exact (hbox j hj).1
  have hadm : admissibleBids loc (1-3*v) (1+v^2) v z Q i newtau := by
    intro j hj
    refine ⟨?_,?_,?_,?_⟩
    · dsimp only [newtau]; split_ifs
      · exact (hbox j hj).1
      · exact le_rfl
    · exact (hsmall j hj).trans (hbox j hj).2.1
    · intro f hf
      exact (hsmall j hj).trans ((hbox j hj).2.2 f hf)
    · intro hfar
      simp only [newtau,ite_eq_right (not_le.mpr hfar)]
  have hpay : openingDual loc (1-3*v) z Q i tau a ≤
      openingPayment loc (1-3*v) z Q i newtau := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : activeAt loc (1-3*v) z Q j
    · simp only [hj,↓reduceIte]
      apply max_le_max _ le_rfl
      dsimp only [newtau]
      split_ifs with hnear
      · have hd := mul_le_mul_of_nonneg_right ht1 (dist_nonneg (x:=i) (y:=loc j))
        linarith only [hd]
      · have hfar : v*z ≤ dist i (loc j) := (not_le.mp hnear).le
        have hm := mul_le_mul_of_nonneg_left hfar (by positivity : 0 ≤ 3*v)
        have hb := (hbox j hj).2.1
        nlinarith only [hm,hb,mul_nonneg (sq_nonneg v) hz.le]
    · simp only [hj,↓reduceIte]
      have hh := capped_triangle_row loc (1-3*v) (tau a) Q i a j ht ht1
        (inactive_nonempty loc (1-3*v) z Q j hj) (hbox a ha).2.2
      have hd := mul_le_mul_of_nonneg_right ht1 (dist_nonneg (x:=i) (y:=loc j))
      exact max_le_max (by linarith only [hh,hd]) le_rfl
  refine ⟨newtau,hadm,?_,?_⟩
  · simpa only [mul_zero,sub_zero,htight] using hpay
  · intro k hk b hb
    apply le_trans _ (hrows k hk b hb)
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : activeAt loc (1-3*v) z Q j
    · simp only [hj,↓reduceIte]
      exact max_le_max (sub_le_sub_right (hsmall j hj) _) le_rfl
    · simp only [hj,↓reduceIte]
      exact max_le_max (by linarith only [hsmall b hb]) le_rfl

lemma continuous_payment (loc : D → X) (Q : Finset X) (t z : ℝ) (i : X)
    (tau : ℝ → D → ℝ) (hc : ∀ j, Continuous (fun x => tau x j)) :
    Continuous (fun x => openingPayment loc t z Q i (tau x)) := by
  classical
  unfold openingPayment
  apply continuous_finsetSum
  intro j _
  by_cases hj : activeAt loc t z Q j
  · simp only [hj,↓reduceIte]
    exact ((hc j).sub continuous_const).max continuous_const
  · simp only [hj,↓reduceIte]
    exact continuous_const

lemma continuous_dual (loc : D → X) (Q : Finset X) (t z : ℝ) (i : X) (a : D)
    (tau : ℝ → D → ℝ) (hc : ∀ j, Continuous (fun x => tau x j)) :
    Continuous (fun x => openingDual loc t z Q i (tau x) a) := by
  classical
  unfold openingDual
  apply continuous_finsetSum
  intro j _
  by_cases hj : activeAt loc t z Q j
  · simp only [hj,↓reduceIte]
    exact ((hc j).sub continuous_const).max continuous_const
  · simp only [hj,↓reduceIte]
    exact (((hc a).sub continuous_const).sub continuous_const).max continuous_const

theorem payment_produces_openable (loc : D → X) (F Q : Finset X) (v z lam : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hbase : ∀ i ∈ F, bidRow loc (1-3*v) z Q i ≤ lam)
    (i : X) (hi : i ∈ F) (tau : D → ℝ)
    (hadm : admissibleBids loc (1-3*v) (1+v^2) v z Q i tau)
    (hpaid : lam ≤ openingPayment loc (1-3*v) z Q i tau) :
    ∃ k ∈ F, etaOpenable loc F Q (1-3*v) (1+v^2) v z lam 0 k := by
  classical
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have ht1 : 1-3*v ≤ 1 := by linarith only [hv]
  have hK : z ≤ (1+v^2)*z := by nlinarith only [mul_nonneg (sq_nonneg v) hz.le]
  let bids : ℝ → D → ℝ := fun x j => z+x*(tau j-z)
  have hbids : ∀ x ∈ Set.Icc (0:ℝ) 1,
      admissibleBids loc (1-3*v) (1+v^2) v z Q i (bids x) := by
    intro x hx j hj
    obtain ⟨hlo,hhi,hcap,hfar⟩ := hadm j hj
    dsimp only [bids]
    have hxlo := mul_nonneg hx.1 (sub_nonneg.mpr hlo)
    have hxhi := mul_le_mul_of_nonneg_right hx.2 (sub_nonneg.mpr hlo)
    refine ⟨by linarith only [hxlo],by linarith only [hxhi,hhi],?_,?_⟩
    · intro f hf
      linarith only [hxhi,hcap f hf]
    · intro hh
      rw [hfar hh]
      ring
  have hb0 : bids 0 = fun _ => z := by funext j; simp [bids]
  have hb1 : bids 1 = tau := by funext j; simp [bids]
  have hbcont : ∀ j, Continuous (fun x => bids x j) := by
    intro j
    exact continuous_const.add (continuous_id.mul continuous_const)
  have hd0 : ∀ k ∈ F, ∀ a, activeAt loc (1-3*v) z Q a →
      openingDual loc (1-3*v) z Q k (bids 0) a ≤ lam := by
    intro k hk a ha
    rw [hb0]
    exact (baseline_dual_le loc Q (1-3*v) z k a ht ht1 ha).trans (hbase k hk)
  by_cases hp0 : lam ≤ openingPayment loc (1-3*v) z Q i (bids 0)
  · exact ⟨i,hi,bids 0,hbids 0 ⟨le_rfl,by norm_num⟩,by simpa using hp0,hd0⟩
  let Idx := Unit ⊕ (↥F × D)
  let row : ℝ → Idx → ℝ := fun x r => match r with
    | .inl _ => openingPayment loc (1-3*v) z Q i (bids x)
    | .inr (k,a) => if activeAt loc (1-3*v) z Q a then
        openingDual loc (1-3*v) z Q k (bids x) a else 0
  have hrowcont : ∀ r, Continuous (fun x => row x r) := by
    intro r
    cases r with
    | inl => exact continuous_payment loc Q (1-3*v) z i bids hbcont
    | inr r =>
      dsimp only [row]
      split_ifs
      · exact continuous_dual loc Q (1-3*v) z r.1 r.2 bids hbcont
      · exact continuous_const
  have hu : (Finset.univ : Finset Idx).Nonempty := ⟨Sum.inl (),Finset.mem_univ _⟩
  let M : ℝ → ℝ := fun x => Finset.univ.sup' hu (row x)
  have hcont : Continuous M := Continuous.finset_sup'_apply hu (fun r _ => hrowcont r)
  have hM0 : M 0 ≤ lam := by
    apply Finset.sup'_le hu
    intro r _
    cases r with
    | inl => exact (lt_of_not_ge hp0).le
    | inr r =>
      dsimp only [row]
      split_ifs with ha
      · exact hd0 r.1 r.1.property r.2 ha
      · exact hlam.le
  have hM1 : lam ≤ M 1 := by
    calc
      _ ≤ row 1 (.inl ()) := by simpa only [row,hb1] using hpaid
      _ ≤ M 1 := Finset.le_sup' (row 1) (Finset.mem_univ (Sum.inl ()))
  obtain ⟨x,hx,hMx⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1)
    hcont.continuousOn ⟨hM0,hM1⟩
  obtain ⟨r,_,hr⟩ := Finset.exists_mem_eq_sup' hu (row x)
  have heq : row x r = lam := hr.symm.trans hMx
  have hrows : ∀ k ∈ F, ∀ a, activeAt loc (1-3*v) z Q a →
      openingDual loc (1-3*v) z Q k (bids x) a ≤ lam := by
    intro k hk a ha
    have hh := (Finset.le_sup' (row x) (Finset.mem_univ (Sum.inr (⟨k,hk⟩,a)))).trans_eq hMx
    simpa only [row,ite_eq_left ha] using hh
  cases r with
  | inl => exact ⟨i,hi,bids x,hbids x hx,by simpa only [row,mul_zero,sub_zero] using heq.ge,hrows⟩
  | inr r =>
    dsimp only [row] at heq
    split_ifs at heq with ha
    · refine ⟨r.1,r.1.property,tight_dual_openable loc F Q v z lam (bids x) hv hvsmall hz ?_
        r.1 r.2 ha heq hrows⟩
      intro j hj
      exact ⟨(hbids x hx j hj).1,(hbids x hx j hj).2.1,(hbids x hx j hj).2.2.1⟩
    · exact (hlam.ne heq).elim

end MetricKMedianRecovery.PriceTransfer

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_ClippedBid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace ClippingTransfer
variable {D X : Type*} [PseudoMetricSpace X]

lemma active_transfer (loc : D → X) (t z : ℝ) (W W' : Finset X)
    (hW : W.Nonempty) (hW' : W'.Nonempty) (ht : 0 ≤ t)
    (hr : ∀ j, nearestDistance (loc j) W' ≤ nearestDistance (loc j) W)
    (j : D) (ha : activeAt loc t z W' j) : activeAt loc t z W j := by
  apply (activeAt_iff loc t z W j ht hW).mpr
  exact ((activeAt_iff loc t z W' j ht hW').mp ha).trans_le (mul_le_mul_of_nonneg_left (hr j) ht)

lemma bid_cap (loc : D → X) (t K v z : ℝ) (W : Finset X) (hW : W.Nonempty)
    (i : X) (tau : D → ℝ) (hb : admissibleBids loc t K v z W i tau)
    (j : D) (ha : activeAt loc t z W j) : tau j ≤ t*nearestDistance (loc j) W := by
  obtain ⟨f,hf,he⟩ := nearestDistance_attained (loc j) W hW
  simpa only [he] using (hb j ha).2.2.1 f hf

end ClippingTransfer
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_OpenPaymentZero
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PriceTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X]

lemma open_payment_zero (loc : D → X) (Q : Finset X) (t K v z : ℝ) (i : X)
    (hi : i ∈ Q) (ht : 0 ≤ t) (tau : D → ℝ)
    (hb : admissibleBids loc t K v z Q i tau) :
    openingPayment loc t z Q i tau = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : activeAt loc t z Q j
  · simp only [hj,↓reduceIte]
    apply max_eq_right
    have hh := (hb j hj).2.2.1 i hi
    rw [dist_comm (loc j) i] at hh
    linarith only [hh]
  · simp only [hj,↓reduceIte]
    apply max_eq_right
    have hh := mul_le_mul_of_nonneg_left (nearestDistance_le_mem (loc j) Q i hi) ht
    rw [dist_comm (loc j) i] at hh
    linarith only [hh]

theorem maximal_payment_lt (loc : D → X) (F Q : Finset X) (v z lam : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hbase : ∀ i ∈ F, bidRow loc (1-3*v) z Q i ≤ lam)
    (hmax : ∀ i ∈ F, i ∉ Q → ¬etaOpenable loc F Q (1-3*v) (1+v^2) v z lam 0 i)
    (i : X) (hi : i ∈ F) (tau : D → ℝ)
    (hadm : admissibleBids loc (1-3*v) (1+v^2) v z Q i tau) :
    openingPayment loc (1-3*v) z Q i tau < lam := by
  by_contra hn
  obtain ⟨k,hk,hopen⟩ := payment_produces_openable loc F Q v z lam
    hv hvsmall hz hlam hbase i hi tau hadm (le_of_not_gt hn)
  by_cases hkQ : k ∈ Q
  · obtain ⟨b,hb,hp,_⟩ := hopen
    have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
    have he := open_payment_zero loc Q (1-3*v) (1+v^2) v z k hkQ ht b hb
    simp only [mul_zero,sub_zero,he] at hp
    exact (not_le_of_gt hlam) hp
  · exact hmax k hk hkQ hopen

theorem lift_payment (loc : D → X) (Q Q' : Finset X) (t K v z : ℝ)
    (hQ : Q.Nonempty) (hQ' : Q'.Nonempty) (ht : 0 ≤ t) (hK : z ≤ K*z)
    (hr : ∀ j, nearestDistance (loc j) Q' ≤ nearestDistance (loc j) Q)
    (i : X) (tau : D → ℝ) (hb : admissibleBids loc t K v z Q' i tau) :
    ∃ tauOld : D → ℝ, admissibleBids loc t K v z Q i tauOld ∧
      openingPayment loc t z Q' i tau ≤ openingPayment loc t z Q i tauOld := by
  classical
  let tauOld : D → ℝ := fun j => if activeAt loc t z Q' j then tau j else z
  have hadm : admissibleBids loc t K v z Q i tauOld := by
    intro j hj
    by_cases hj' : activeAt loc t z Q' j
    · simp only [tauOld,ite_eq_left hj']
      refine ⟨(hb j hj').1,(hb j hj').2.1,?_,(hb j hj').2.2.2⟩
      intro f hf
      exact ((ClippingTransfer.bid_cap loc t K v z Q' hQ' i tau hb j hj').trans
        (mul_le_mul_of_nonneg_left (hr j) ht)).trans
        (mul_le_mul_of_nonneg_left (nearestDistance_le_mem (loc j) Q f hf) ht)
    · simp only [tauOld,ite_eq_right hj']
      exact ⟨le_rfl,hK,fun f hf => (hj f hf).le,fun _ => trivial⟩
  refine ⟨tauOld,hadm,?_⟩
  apply Finset.sum_le_sum
  intro j _
  by_cases hj' : activeAt loc t z Q' j
  · have hj := ClippingTransfer.active_transfer loc t z Q Q' hQ hQ' ht hr j hj'
    simp only [hj',hj,↓reduceIte,tauOld]
    exact le_rfl
  · by_cases hj : activeAt loc t z Q j
    · simp only [hj',hj,↓reduceIte,tauOld]
      apply max_le_max _ le_rfl
      apply sub_le_sub_right
      exact not_lt.mp (fun hh => hj' ((activeAt_iff loc t z Q' j ht hQ').mpr hh))
    · simp only [hj',hj,↓reduceIte]
      exact max_le_max (sub_le_sub_right (mul_le_mul_of_nonneg_left (hr j) ht) _) le_rfl

theorem maximal_shrink (loc : D → X) (F Q Q' : Finset X) (v z lam lam' : ℝ)
    (hQ : Q.Nonempty) (hQ' : Q'.Nonempty)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hbase : ∀ i ∈ F, bidRow loc (1-3*v) z Q i ≤ lam)
    (hmax : ∀ i ∈ F, i ∉ Q → ¬etaOpenable loc F Q (1-3*v) (1+v^2) v z lam 0 i)
    (hm : lam ≤ lam') (hr : ∀ j, nearestDistance (loc j) Q' ≤ nearestDistance (loc j) Q) :
    ∀ i ∈ F, i ∉ Q' → ¬etaOpenable loc F Q' (1-3*v) (1+v^2) v z lam' 0 i := by
  intro i hi _ hop
  obtain ⟨tau,hb,hp,_⟩ := hop
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have hK : z ≤ (1+v^2)*z := by nlinarith only [mul_nonneg (sq_nonneg v) hz.le]
  obtain ⟨old,hadm,hpay⟩ := lift_payment loc Q Q' (1-3*v) (1+v^2) v z hQ hQ' ht hK hr i tau hb
  have hh := maximal_payment_lt loc F Q v z lam hv hvsmall hz hlam hbase hmax i hi old hadm
  simp only [mul_zero,sub_zero] at hp
  exact (not_lt_of_ge ((hm.trans hp).trans hpay)) hh
end MetricKMedianRecovery.PriceTransfer

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ImagePhaseUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma History.after_subset {loc : D → X} {F B Q : Finset X} {v lam eta : ℝ}
    {q : ℕ} {T : List (List X)} (h : History loc F B v lam eta q Q T)
    (hQ : Q ⊆ F ∪ B) : after Q T ⊆ F ∪ B := by
  induction h with
  | nil => exact hQ
  | cons hhead htail ih =>
    exact ih (Finset.union_subset hQ hhead.1.opened_subset)

lemma advance_rows (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ) (q : ℕ)
    (H : List X) (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (hhead : PhaseSequence.Valid loc F B Q v ((1+v^2)^q) lam eta H) :
    ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^(q+1)) (Q ∪ H.toFinset) i ≤ lam := by
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have hrow' : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) (Q ∪ H.toFinset) i ≤ lam := by
    intro i hi
    exact (bidRow_antitone_open loc (1-3*v) ((1+v^2)^q) Q (Q ∪ H.toFinset) i ht
      Finset.subset_union_left).trans (hrow i hi)
  have hz : 0 < (1+v^2)^q := by positivity
  simpa only [pow_succ,mul_comm] using
    phase_update_no_overbid loc F (Q ∪ H.toFinset) v ((1+v^2)^q) lam
      hv hvsmall hz hlam hrow' hhead.2

end MetricKMedianRecovery.PhaseHistoryTransfer

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MaximalSuperset
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.MaximalPrefixSelection
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [DecidableEq X] in

theorem maximal_superset (loc : D → X) (F Q Q' : Finset X) (v z lam lam' : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hbase : ∀ i ∈ F, bidRow loc (1-3*v) z Q i ≤ lam)
    (hmax : PhaseSequence.Maximal loc F Q v z lam)
    (hprice : lam ≤ lam') (hQQ : Q ⊆ Q') :
    PhaseSequence.Maximal loc F Q' v z lam' := by
  classical
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have hK : z ≤ (1+v^2)*z := by nlinarith only [mul_nonneg (sq_nonneg v) hz.le]
  by_cases hQ : Q.Nonempty
  · exact PriceTransfer.maximal_shrink loc F Q Q' v z lam lam' hQ (hQ.mono hQQ)
      hv hvsmall hz hlam hbase hmax hprice (fun j => nearestDistance_antitone (loc j) Q Q' hQ hQQ)
  have he : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
  subst Q
  intro i hi _ hop
  obtain ⟨tau,hb,hp,_⟩ := hop
  have hactive (j : D) : activeAt loc (1-3*v) z ∅ j := by simp [activeAt]
  let old : D → ℝ := fun j => if activeAt loc (1-3*v) z Q' j then tau j else z
  have hadm : admissibleBids loc (1-3*v) (1+v^2) v z ∅ i old := by
    intro j _
    by_cases hj : activeAt loc (1-3*v) z Q' j
    · simp only [old,ite_eq_left hj]
      exact ⟨(hb j hj).1,(hb j hj).2.1,by simp,(hb j hj).2.2.2⟩
    · simp only [old,ite_eq_right hj]
      exact ⟨le_rfl,hK,by simp,fun _ => trivial⟩
  have hpay : openingPayment loc (1-3*v) z Q' i tau ≤
      openingPayment loc (1-3*v) z ∅ i old := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : activeAt loc (1-3*v) z Q' j
    · simp only [hj,hactive j,↓reduceIte,old]
      exact le_rfl
    · have hn : Q'.Nonempty := inactive_nonempty loc (1-3*v) z Q' j hj
      have hz' : (1-3*v)*nearestDistance (loc j) Q' ≤ z := by
        exact not_lt.mp (fun hh => hj ((activeAt_iff loc (1-3*v) z Q' j ht hn).mpr hh))
      simp only [hj,hactive j,↓reduceIte,old]
      exact max_le_max (sub_le_sub_right hz' _) le_rfl
  have hlt := PriceTransfer.maximal_payment_lt loc F ∅ v z lam hv hvsmall hz hlam
    hbase hmax i hi old hadm
  simp only [mul_zero,sub_zero] at hp
  exact (not_lt_of_ge ((hprice.trans hp).trans hpay)) hlt

end MetricKMedianRecovery.MaximalPrefixSelection

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_EntryFreeMono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeSurgery
open PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma entry_free_mono {loc : D → X} {F B B' Q : Finset X} {v z lam eta : ℝ} {i : X}
    (h : Entry loc F B Q v z lam eta i) (hB : B ⊆ B') :
    Entry loc F B' Q v z lam eta i := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with hi | ⟨hi,W,hW,hWF,hop⟩
  · exact Or.inl (hB hi)
  · exact Or.inr ⟨hi,W,hW,hWF.trans (Finset.union_subset_union_right hB),hop⟩

lemma prefix_free_mono {loc : D → X} {F B B' Q : Finset X} {v z lam eta : ℝ}
    {H : List X} (h : Prefix loc F B v z lam eta Q H) (hB : B ⊆ B') :
    Prefix loc F B' v z lam eta Q H := by
  induction h with
  | nil Q => exact Prefix.nil Q
  | cons hi ht ih => exact Prefix.cons (entry_free_mono hi hB) ih

theorem append_free (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) z Q i ≤ lam)
    (H : List X) (hH : Valid loc F B Q v z lam eta H)
    (f : X) (hf : f ∉ Q ∪ H.toFinset) :
    Valid loc F (insert f B) Q v z lam eta (H++[f]) := by
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  refine ⟨(prefix_free_mono hH.1 (Finset.subset_insert _ _)).append
    (Prefix.cons ⟨hf,Or.inl (Finset.mem_insert_self _ _)⟩ (Prefix.nil _)),?_⟩
  apply MaximalPrefixSelection.maximal_superset loc F (Q ∪ H.toFinset)
    (Q ∪ (H++[f]).toFinset) v z lam lam hv hvsmall hz hlam
  · intro i hi
    exact (bidRow_antitone_open loc (1-3*v) z Q (Q ∪ H.toFinset) i ht
      Finset.subset_union_left).trans (hrow i hi)
  · exact hH.2
  · exact le_rfl
  · simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil]
    exact Finset.union_subset_union_right Finset.subset_union_left

end MetricKMedianRecovery.PhaseMergeSurgery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalLeaves
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [PseudoMetricSpace V]

attribute [local instance] metric

variable [DecidableEq V]

omit [PseudoMetricSpace V] in
lemma fresh (F : Finset V) (B : Finset (Label V)) (key : ℕ) (hB : Before key B)
    (i : V) (s : ℚ) : leaf key i s ∉ F.image original ∪ B := by
  intro h
  rcases Finset.mem_union.mp h with h|h
  · obtain ⟨x,_,hx⟩ := Finset.mem_image.mp h
    cases hx
  · exact (lt_irrefl key) (hB (key,i,s) h)

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_PrefixFreeMono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CommonPrefixTransfer
open PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma prefix_free_mono (loc : D → X) (F B B' Q : Finset X)
    (v z lam eta : ℝ) (H : List X) (hBB : B ⊆ B')
    (hh : PhaseSequence.Prefix loc F B v z lam eta Q H) :
    PhaseSequence.Prefix loc F B' v z lam eta Q H := by
  induction hh with
  | nil Q => exact PhaseSequence.Prefix.nil Q
  | @cons Q i H hi htail ih =>
    apply PhaseSequence.Prefix.cons _ ih
    refine ⟨hi.1,?_⟩
    rcases hi.2 with hb|⟨hF,W,hQ,hW,hop⟩
    · exact Or.inl (hBB hb)
    · exact Or.inr ⟨hF,W,hQ,hW.trans (Finset.union_subset_union_right hBB),hop⟩

lemma history_free_mono (loc : D → X) (F B B' Q : Finset X)
    (v lam eta : ℝ) (q : ℕ) (T : List (List X)) (hBB : B ⊆ B')
    (hh : History loc F B v lam eta q Q T) : History loc F B' v lam eta q Q T := by
  induction hh with
  | nil q Q => exact History.nil q Q
  | @cons q Q H T hhead htail ih =>
    exact History.cons ⟨prefix_free_mono loc F B B' Q v _ lam eta H hBB hhead.1,hhead.2⟩ ih

lemma history_append (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q : ℕ) (P T : List (List X)) (hp : History loc F B v lam eta q Q P)
    (ht : History loc F B v lam eta (q+P.length) (after Q P) T) :
    History loc F B v lam eta q Q (P++T) := by
  induction hp with
  | nil q Q => simpa only [List.nil_append,List.length_nil,Nat.add_zero,after] using ht
  | @cons q Q H P hhead htail ih =>
    apply History.cons hhead
    apply ih
    simpa only [after,List.length_cons,Nat.add_right_comm,Nat.add_assoc] using ht

end MetricKMedianRecovery.CommonPrefixTransfer

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_PrefixData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeInvariant
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion
universe uD uX uY
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] [PseudoMetricSpace X] in
lemma after_append (Q : Finset X) (P T : List (List X)) :
    after Q (P++T) = after (after Q P) T := by
  induction P generalizing Q with
  | nil => rfl
  | cons H P ih => exact ih _

lemma PrefixData.after_subset {loc : D → X} {F B : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : PrefixData loc F B v lam eta q P) :
    after ∅ P ⊆ F ∪ B := h.history.after_subset (Finset.empty_subset _)

lemma PrefixData.mono_free {loc : D → X} {F B B' : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : PrefixData loc F B v lam eta q P) (hB : B ⊆ B') :
    PrefixData loc F B' v lam eta q P :=
  ⟨h.length_eq,CommonPrefixTransfer.history_free_mono loc F B B' ∅ v lam eta 0 P hB h.history,
    h.free_bound,h.row⟩

lemma PrefixData.append_phase {loc : D → X} {F B : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : PrefixData loc F B v lam eta q P)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (H : List X) (hh : Valid loc F B (after ∅ P) v ((1+v^2)^q) lam eta H)
    (hfree : (H.toFinset \ F).card ≤ 3) :
    PrefixData loc F B v lam eta (q+1) (P++[H]) := by
  refine ⟨by simp only [List.length_append,List.length_singleton,h.length_eq],?_,?_,?_⟩
  · apply CommonPrefixTransfer.history_append loc F B ∅ v lam eta 0 P [H] h.history
    simpa only [Nat.zero_add,h.length_eq] using History.cons hh (History.nil _ _)
  · intro G hG
    rcases List.mem_append.mp hG with hG | hG
    · exact h.free_bound G hG
    · simpa only [List.mem_singleton.mp hG] using hfree
  · simpa only [after_append,after] using
      advance_rows loc F B (after ∅ P) v lam eta q H hv hvsmall hlam h.row hh

end MetricKMedianRecovery.PhaseMergeInvariant

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeafReplay
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves

open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] metric

lemma append_leaf (loc : Fin d → V) (F : Finset V) (B Q : Finset (Label V))
    (key : ℕ) (i : V) (s : ℚ) (H : List (Label V)) (v lam eta : ℝ) (q : ℕ)
    (hB : Before key B) (hQ : Q⊆F.image original∪B)
    (hv : 0<v) (hv1 : v<1/6) (hlam : 0<lam)
    (hrow : ∀ x∈F.image original,bidRow (fun j=>original (loc j)) (1-3*v) ((1+v^2)^q) Q x≤lam)
    (hH : PhaseMergeRefinement.Good (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta H) :
    Valid (fun j=>original (loc j)) (F.image original) (insert (leaf key i s) B) Q v ((1+v^2)^q) lam eta (H++[leaf key i s]) ∧
      ((H++[leaf key i s]).toFinset \ F.image original).card≤3 := by
  have hfresh := fresh F B key hB i s
  have hf : leaf key i s∉Q∪H.toFinset := fun he=>hfresh ((Finset.union_subset hQ hH.1.1.opened_subset) he)
  refine ⟨PhaseMergeSurgery.append_free _ _ _ _ _ _ _ _ hv hv1 (by positivity) hlam hrow H hH.1 _ hf,?_⟩
  have hfF : leaf key i s∉F.image original := fun he=>hfresh (Finset.mem_union_left _ he)
  have hfH : leaf key i s∉H.toFinset := fun he=>hf (Finset.mem_union_right _ he)
  simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.union_insert,Finset.union_empty]
  rw [Finset.insert_sdiff_of_notMem _ hfF,Finset.card_insert_of_notMem
    (fun he=>hfH (Finset.mem_sdiff.mp he).1)]
  have hh := hH.2
  omega

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledLeaf
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
open PhaseSequence PhaseHistoryTransfer PhaseMergeInvariant PhaseMergeRefinement
variable {V : Type*} [DecidableEq V] {d : ℕ}

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma prefix_leaf_s238_oai {loc : Fin d → V} {F : Finset V} {B : Finset (Label V)}
    {v lam eta : ℝ} {q : ℕ} {P : List (List (Label V))}
    (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
    (key : ℕ) (hB : Before key B) (i : V) (s : ℚ) (hv : 0<v) (hv1 : v<1/6) (hlam : 0<lam)
    (H : List (Label V))
    (hH : Good (fun j=>original (loc j)) (F.image original) B (after ∅ P) v ((1+v^2)^q) lam eta H) :
    PrefixData (fun j=>original (loc j)) (F.image original) (insert (leaf key i s) B) v lam eta (q+1)
      (P++[H++[leaf key i s]]) := by
  obtain ⟨hh,hcount⟩ := append_leaf (loc:=loc) F B (after ∅ P) key i s H v lam eta q hB hp.after_subset hv hv1 hlam hp.row hH
  exact (hp.mono_free (Finset.subset_insert _ _)).append_phase hv hv1 hlam _ hh hcount

end MetricKMedianRecovery.RationalLeaves

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.RationalLeaves.prefix_leaf_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.RationalLeaves.prefix_leaf_s238_oai.{u_1}
