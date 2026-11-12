-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.CanonicalMergeRefinement.regularChain_spec_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:35:13.730628+00:00
-- url     : https://prove2.me/submissions/6f96c558-4449-4120-afbd-8b54bba0095d

import Mathlib
import Definitions.Def_Q238L020
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalMergePath_advancePrefix_spec_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalMergeRefinement_refinePath_spec_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_BaselineDual
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MaximalSuperset
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
lemma mono (h : Entry loc F B Q v z lam eta i) (hQ : Q' ⊆ Q) :
    Entry loc F B Q' v z lam eta i := by
  refine ⟨fun hi => h.1 (hQ hi),?_⟩
  rcases h.2 with hb|⟨hi,W,hW,hWF,hop⟩
  · exact Or.inl hb
  · exact Or.inr ⟨hi,W,hQ.trans hW,hWF,hop⟩
end Entry

namespace Prefix
variable {loc : D → X} {F B Q Q' : Finset X} {v z lam eta : ℝ} {H G : List X}
lemma mono (h : Prefix loc F B v z lam eta Q H) (hQ : Q' ⊆ Q) :
    Prefix loc F B v z lam eta Q' H := by
  induction h generalizing Q' with
  | nil => exact Prefix.nil _
  | cons hi ht ih => exact Prefix.cons (hi.mono hQ) (ih (Finset.insert_subset_insert _ hQ))

lemma sublist (h : Prefix loc F B v z lam eta Q H) (hGH : G.Sublist H) :
    Prefix loc F B v z lam eta Q G := by
  induction hGH generalizing Q with
  | slnil => exact Prefix.nil _
  | cons a hGH ih =>
    cases h with
    | cons hi ht => exact (ih ht).mono (Finset.subset_insert _ _)
  | cons_cons a hGH ih =>
    cases h with
    | cons hi ht => exact Prefix.cons hi (ih ht)

lemma append (h : Prefix loc F B v z lam eta Q H)
    (hG : Prefix loc F B v z lam eta (Q ∪ H.toFinset) G) :
    Prefix loc F B v z lam eta Q (H++G) := by
  induction h with
  | nil => simpa using hG
  | @cons Q i H hi ht ih =>
    apply Prefix.cons hi
    apply ih
    simpa only [List.toFinset_cons,Finset.union_insert,Finset.insert_union] using hG

lemma disjoint (h : Prefix loc F B v z lam eta Q H) : Disjoint Q H.toFinset := by
  induction h with
  | nil => simp
  | @cons Q i H hi ht ih =>
    rw [List.toFinset_cons,Finset.disjoint_insert_right]
    exact ⟨hi.1,Finset.disjoint_of_subset_left (Finset.subset_insert _ _) ih⟩

lemma nodup (h : Prefix loc F B v z lam eta Q H) : H.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | @cons Q i H hi ht ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih⟩
    intro hm
    exact Finset.disjoint_left.mp ht.disjoint (Finset.mem_insert_self _ _)
      (List.mem_toFinset.mpr hm)
end Prefix

end PhaseSequence
end MetricKMedianRecovery

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

lemma prefix_append_iff {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {H G : List X} : Prefix loc F B v z lam eta Q (H++G) ↔
      Prefix loc F B v z lam eta Q H ∧
        Prefix loc F B v z lam eta (Q ∪ H.toFinset) G := by
  constructor
  · intro h
    induction H generalizing Q with
    | nil => exact ⟨Prefix.nil Q,by simpa using h⟩
    | cons i H ih =>
      cases h with
      | cons hi ht =>
        obtain ⟨hH,hG⟩ := ih ht
        refine ⟨Prefix.cons hi hH,?_⟩
        simpa only [List.toFinset_cons,Finset.union_insert,Finset.insert_union] using hG
  · rintro ⟨hH,hG⟩
    exact hH.append hG

end MetricKMedianRecovery.PhaseMergeSurgery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pool
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergePath
open PhaseSequence PhaseMergeSurgery
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [PseudoMetricSpace X] in
lemma subset_pool (F B : Finset X) (copy : X → X) : B ⊆ pool F B copy :=
  Finset.subset_union_left

lemma regular_good {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {H : List X} (hH : Valid loc F B Q v z lam eta H) (hreg : ∀ k ∈ H, k ∈ F) :
    Good loc F B Q copy v z lam eta H := by
  refine ⟨⟨prefix_free_mono hH.1 (subset_pool F B copy),hH.2⟩,?_⟩
  have hs : H.toFinset ⊆ F := fun k hk => hreg k (List.mem_toFinset.mp hk)
  simp only [Finset.sdiff_eq_empty_iff_subset.mpr hs,Finset.card_empty,Nat.zero_le]

lemma regular_length {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ} {H : List X}
    (hH : Prefix loc F B v z lam eta Q H) (hreg : ∀ k ∈ H, k ∈ F) : H.length ≤ F.card := by
  rw [← List.toFinset_card_of_nodup hH.nodup]
  exact Finset.card_le_card (fun k hk => hreg k (List.mem_toFinset.mp hk))

end MetricKMedianRecovery.PhaseMergePath

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergePath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergePath
open PhaseSequence PhaseMergeSurgery PhaseMergePath
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma Path.append {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {H J K : List X} {T U : List (List X)} (h : Path loc F B Q copy v z lam eta H T J)
    (h' : Path loc F B Q copy v z lam eta J U K) :
    Path loc F B Q copy v z lam eta H (T++U) K := by
  induction h with
  | nil => exact h'
  | cons h e t ih => exact .cons h e (ih h')

omit [PseudoMetricSpace X] in
lemma deleteSuffix_length (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    (C : List X) (i : X) (U E : List X) :
    (deleteSuffix complete Q copy C i U E).2.length = U.length := by
  induction U generalizing E with
  | nil => rfl
  | cons u U ih => simp only [deleteSuffix,List.length_cons,ih]

omit [PseudoMetricSpace X] in
lemma advancePrefix_length (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    (C U : List X) (i : X) :
    (advancePrefix complete Q copy C U i).2.length=U.length+2 := by
  simp only [advancePrefix,List.length_cons,List.length_append,List.length_nil,
    deleteSuffix_length]

 theorem matchPrefix_spec (loc : D → X) (F B Q : Finset X) (copy : X → X)
    (v z lam eta : ℝ) (complete : Finset X → List X)
    (hc : CorrectCompletion loc F v z lam complete)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z)
    (hlam : 0 < lam) (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (hfresh : ∀ i ∈ F, copy i ∉ F ∪ B)
    (hco : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (C U T : List X) (hCr : ∀ k ∈ C, k ∈ F) (hUr : ∀ k ∈ U, k ∈ F)
    (hTr : ∀ k ∈ T, k ∈ F)
    (htarget : Prefix loc F B v z lam eta Q (C++T))
    (hcur : Valid loc F B Q v z lam eta (C++U)) :
    let r := matchPrefix complete Q copy C U T
    r.2.length ≤ T.length*(F.card+2) ∧ (∀ k ∈ r.1, k ∈ F) ∧
      Valid loc F B Q v z lam eta (C++T++r.1) ∧
      Path loc F B Q copy v z lam eta (C++U) r.2 (C++T++r.1) := by
  induction T generalizing C U with
  | nil =>
    refine ⟨by simp [matchPrefix],hUr,?_,?_⟩
    · simpa only [matchPrefix,List.append_nil] using hcur
    · simp only [matchPrefix,List.append_nil]
      apply Path.nil
      apply regular_good hcur
      intro k hk
      exact (List.mem_append.mp hk).elim (hCr k) (hUr k)
  | cons i T ih =>
    have hiF : i ∈ F := hTr i (List.mem_cons_self ..)
    have hiB : i ∉ B := fun hi => Finset.disjoint_left.mp hdis hiF hi
    have hTr' : ∀ k ∈ T, k ∈ F := fun k hk => hTr k (List.mem_cons_of_mem _ hk)
    obtain ⟨hC,hIT⟩ := prefix_append_iff.mp htarget
    cases hIT with
    | cons hi hT =>
      let a := advancePrefix complete Q copy C U i
      obtain ⟨hGr,hvG,hw⟩ := advancePrefix_spec_s238r loc F B Q copy v z lam eta complete hc
        hv hvsmall hz hlam heta hQ hrow C U i hiF hiB (hfresh i hiF) (hco i hiF)
        hC hi hCr hUr hcur
      have hCi : ∀ k ∈ C++[i], k ∈ F := by
        intro k hk
        rcases List.mem_append.mp hk with hk | hk
        · exact hCr k hk
        · simpa only [List.mem_singleton.mp hk] using hiF
      have htarget' : Prefix loc F B v z lam eta Q ((C++[i])++T) := by
        simpa only [List.append_assoc,List.singleton_append] using htarget
      obtain ⟨hm,hJ,hvJ,hwJ⟩ := ih (C++[i]) a.1 hCi hGr hTr' htarget'
        (by simpa only [a,List.append_assoc,List.singleton_append] using hvG)
      have hUlen : U.length ≤ F.card := by
        have hh := regular_length hcur.1 (fun k hk => (List.mem_append.mp hk).elim (hCr k) (hUr k))
        simp only [List.length_append] at hh
        omega
      refine ⟨?_,hJ,?_,?_⟩
      · change (a.2 ++ (matchPrefix complete Q copy (C++[i]) a.1 T).2).length ≤ _
        rw [List.length_append]
        have ha : a.2.length = U.length+2 := advancePrefix_length ..
        rw [ha,List.length_cons,Nat.add_mul,one_mul]
        omega
      · simpa only [matchPrefix,List.append_assoc,List.singleton_append] using hvJ
      · have hh := hw.append (by simpa only [a,List.append_assoc,List.singleton_append] using hwJ)
        simpa only [matchPrefix,List.append_assoc,List.singleton_append] using hh

omit [PseudoMetricSpace X] [DecidableEq X] in
lemma pruneSuffix_length (C U : List X) : (pruneSuffix C U).length=U.length := by
  induction U with
  | nil => rfl
  | cons u U ih => simp only [pruneSuffix,List.length_cons,ih]

 theorem pruneSuffix_spec (loc : D → X) (F B Q : Finset X) (copy : X → X)
    (v z lam eta : ℝ) (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z)
    (hlam : 0 < lam) (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (C U : List X) (hCr : ∀ k ∈ C, k ∈ F) (hUr : ∀ k ∈ U, k ∈ F)
    (htarget : Valid loc F B Q v z lam eta C)
    (hcur : Valid loc F B Q v z lam eta (C++U)) :
    Path loc F B Q copy v z lam eta (C++U) (pruneSuffix C U) C := by
  induction U with
  | nil =>
    simp only [List.append_nil,pruneSuffix]
    exact Path.nil (regular_good htarget hCr)
  | cons u U ih =>
    have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
    have hp : Prefix loc F B v z lam eta Q (C++U) :=
      hcur.1.sublist ((List.Sublist.cons u (List.Sublist.refl U)).append_left C)
    have hm : Maximal loc F (Q ∪ (C++U).toFinset) v z lam := by
      apply MaximalPrefixSelection.maximal_superset loc F (Q ∪ C.toFinset) _ v z lam lam
        hv hvsmall hz hlam
      · intro k hk
        exact (bidRow_antitone_open loc (1-3*v) z Q (Q ∪ C.toFinset) k ht
          Finset.subset_union_left).trans (hrow k hk)
      · exact htarget.2
      · exact le_rfl
      · simp only [List.toFinset_append]
        exact Finset.union_subset_union_right Finset.subset_union_left
    have hUr' : ∀ k ∈ U, k ∈ F := fun k hk => hUr k (List.mem_cons_of_mem u hk)
    have hw := ih hUr' ⟨hp,hm⟩
    have hgood : Good loc F B Q copy v z lam eta (C++u::U) := by
      apply regular_good hcur
      intro k hk
      exact (List.mem_append.mp hk).elim (hCr k) (hUr k)
    have hs := Step.remove (loc := loc) (F := F) (B := B) (Q := Q) (copy := copy)
      (v := v) (z := z) (lam := lam) C U [] u (hUr u (List.mem_cons_self ..))
      (Prefix.nil _) (by simp)
    simpa only [pruneSuffix,List.append_nil] using Path.cons hgood hs (by simpa only [List.append_nil] using hw)

 theorem regularPath_spec (loc : D → X) (F B Q : Finset X) (copy : X → X)
    (v z lam eta : ℝ) (complete : Finset X → List X)
    (hc : CorrectCompletion loc F v z lam complete)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z)
    (hlam : 0 < lam) (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (hfresh : ∀ i ∈ F, copy i ∉ F ∪ B)
    (hco : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (H J : List X) (hHr : ∀ k ∈ H, k ∈ F) (hJr : ∀ k ∈ J, k ∈ F)
    (hH : Valid loc F B Q v z lam eta H) (hJ : Valid loc F B Q v z lam eta J) :
    let T := regularPath complete Q copy H J
    T.length ≤ F.card*(F.card+3) ∧ Path loc F B Q copy v z lam eta J T H := by
  let r := matchPrefix complete Q copy [] J H
  obtain ⟨hn,hGr,hHG,hw⟩ := matchPrefix_spec loc F B Q copy v z lam eta complete hc
    hv hvsmall hz hlam heta hQ hdis hrow hfresh hco [] J H (by simp) hJr hHr
      (by simpa only [List.nil_append] using hH.1) (by simpa only [List.nil_append] using hJ)
  simp only [List.nil_append] at hHG hw
  have hw' := pruneSuffix_spec loc F B Q copy v z lam eta hv hvsmall hz hlam hrow H r.1 hHr hGr hH hHG
  have hHlen := regular_length hH.1 hHr
  have hGlen : r.1.length ≤ F.card := by
    change (matchPrefix complete Q copy [] J H).1.length ≤ F.card
    have hh := regular_length hHG.1 (fun k hk => (List.mem_append.mp hk).elim (hHr k) (hGr k))
    simp only [List.length_append] at hh
    omega
  refine ⟨?_,hw.append hw'⟩
  change (r.2++pruneSuffix H r.1).length ≤ _
  rw [List.length_append,pruneSuffix_length]
  calc
    r.2.length+r.1.length ≤ F.card*(F.card+2)+F.card :=
      Nat.add_le_add (hn.trans (Nat.mul_le_mul_right _ hHlen)) hGlen
    _ = F.card*(F.card+3) := by ring

end MetricKMedianRecovery.CanonicalMergePath

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeRefine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeRefinement
open PhaseSequence PhaseMergeSurgery PhaseMergePath PhaseMergeRefinement
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

 theorem regularChain_spec_s238r_oai (loc : D → X) (F B Q : Finset X) (R : List X) (copy spare : X → X)
    (v z lam eta : ℝ) (complete : Finset X → List X)
    (hcomplete : CanonicalMergePath.CorrectCompletion loc F v z lam complete)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (heta : 0 ≤ eta) (hR : ∀ i∈F,i∈R) (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (hc : ∀ i ∈ F, copy i ∉ F ∪ B)
    (hd : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (hs : ∀ i ∈ F, spare i ∉ F ∪ pool F B copy)
    (he : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (spare i))
    (H G : List X) (hH : Valid loc F B Q v z lam eta H)
    (hG : Valid loc F B Q v z lam eta G)
    (hHr : ∀ i ∈ H, i ∈ F) (hGr : ∀ i ∈ G, i ∈ F) :
    let T := regularChain F R complete Q copy spare H G
    T.length ≤ F.card*(F.card+3)*(F.card+2) ∧
      EPath loc F (pool F (pool F B copy) spare) Q v z lam eta H T G := by
  obtain ⟨hn,hp⟩ := CanonicalMergePath.regularPath_spec loc F B Q copy v z lam eta complete hcomplete
    hv hvsmall hz hlam heta hQ hdis hrow hc hd G H hGr hHr hG hH
  obtain ⟨hm,ht⟩ := refinePath_spec_s238r loc F B Q R copy spare v z lam eta hv hvsmall hz hlam
    hR hQ hrow hc hd hs he hp
  exact ⟨hm.trans (Nat.mul_le_mul_right (F.card+2) hn),ht⟩

end MetricKMedianRecovery.CanonicalMergeRefinement

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.MetricKMedianRecovery.CanonicalMergeRefinement.regularChain_spec_s238r_oai.{u_1, u_2} := @OAI.MetricKMedianRecovery.CanonicalMergeRefinement.regularChain_spec_s238r_oai.{u_1, u_2}
