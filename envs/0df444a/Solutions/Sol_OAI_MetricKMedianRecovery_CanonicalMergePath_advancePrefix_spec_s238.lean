-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.CanonicalMergePath.advancePrefix_spec_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:18:42.440437+00:00
-- url     : https://prove2.me/submissions/518850d9-8169-4ac5-aab9-c834f9df1fa0

import Mathlib
import Definitions.Def_Q238K022

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_NearestInsertEqual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CoincidentCopy
variable {D X : Type*} [PseudoMetricSpace X] [DecidableEq X]

lemma nearest_insert_equal (x : X) (Q : Finset X) (i f : X)
    (h : dist x i = dist x f) :
    nearestDistance x (insert i Q) = nearestDistance x (insert f Q) := by
  have hh (i f : X) (h : dist x i = dist x f) :
      nearestDistance x (insert i Q) ≤ nearestDistance x (insert f Q) := by
    obtain ⟨g,hg,he⟩ := nearestDistance_attained x (insert f Q) (Finset.insert_nonempty _ _)
    rw [he]
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact (nearestDistance_le_mem x (insert i Q) i (Finset.mem_insert_self _ _)).trans h.le
    · exact nearestDistance_le_mem x (insert i Q) g (Finset.mem_insert_of_mem hg)
  exact le_antisymm (hh i f h) (hh f i h.symm)

lemma active_insert_equal (loc : D → X) (t z : ℝ) (Q : Finset X) (i f : X)
    (h : ∀ j, dist (loc j) i = dist (loc j) f) (j : D) :
    activeAt loc t z (insert i Q) j ↔ activeAt loc t z (insert f Q) j := by
  simp only [activeAt,Finset.forall_mem_insert,h j]

lemma admissible_insert_equal (loc : D → X) (t K v z : ℝ) (Q : Finset X) (i f k : X)
    (h : ∀ j, dist (loc j) i = dist (loc j) f) (tau : D → ℝ) :
    admissibleBids loc t K v z (insert i Q) k tau ↔
      admissibleBids loc t K v z (insert f Q) k tau := by
  simp only [admissibleBids,active_insert_equal loc t z Q i f h,
    Finset.forall_mem_insert,h]

variable [Fintype D]

lemma payment_insert_equal (loc : D → X) (t z : ℝ) (Q : Finset X) (i f k : X)
    (h : ∀ j, dist (loc j) i = dist (loc j) f) (tau : D → ℝ) :
    openingPayment loc t z (insert i Q) k tau = openingPayment loc t z (insert f Q) k tau := by
  classical
  simp only [openingPayment,active_insert_equal loc t z Q i f h,
    nearest_insert_equal _ _ _ _ (h _)]

lemma dual_insert_equal (loc : D → X) (t z : ℝ) (Q : Finset X) (i f k : X)
    (h : ∀ j, dist (loc j) i = dist (loc j) f) (tau : D → ℝ) (a : D) :
    openingDual loc t z (insert i Q) k tau a = openingDual loc t z (insert f Q) k tau a := by
  classical
  simp only [openingDual,active_insert_equal loc t z Q i f h]

theorem openable_insert_equal (loc : D → X) (F Q : Finset X) (t K v z lam eta : ℝ)
    (i f k : X) (h : ∀ j, dist (loc j) i = dist (loc j) f) :
    etaOpenable loc F (insert i Q) t K v z lam eta k ↔
      etaOpenable loc F (insert f Q) t K v z lam eta k := by
  simp only [etaOpenable,admissible_insert_equal loc t K v z Q i f _ h,
    payment_insert_equal loc t z Q i f _ h,dual_insert_equal loc t z Q i f _ h,
    active_insert_equal loc t z Q i f h]

omit [DecidableEq X] in

lemma payment_zero (loc : D → X) (t K v z : ℝ) (Q : Finset X) (i f : X)
    (hf : f ∈ Q) (h : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ t) (tau : D → ℝ) (hb : admissibleBids loc t K v z Q i tau) :
    openingPayment loc t z Q i tau = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j _
  change max ((if activeAt loc t z Q j then tau j else t*nearestDistance (loc j) Q)
    -t*dist i (loc j)) 0 = 0
  apply max_eq_right
  by_cases hj : activeAt loc t z Q j
  · rw [ite_eq_left hj]
    have hh := (hb j hj).2.2.1 f hf
    rw [← h j,dist_comm (loc j) i] at hh
    linarith only [hh]
  · rw [ite_eq_right hj]
    have hh := mul_le_mul_of_nonneg_left (nearestDistance_le_mem (loc j) Q f hf) ht
    rw [← h j,dist_comm (loc j) i] at hh
    linarith only [hh]

omit [DecidableEq X] in
lemma not_openable (loc : D → X) (F Q : Finset X) (t K v z lam eta : ℝ)
    (i f : X) (hf : f ∈ Q) (h : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ t) (hlam : 0 < lam-(Fintype.card D:ℝ)*eta) :
    ¬etaOpenable loc F Q t K v z lam eta i := by
  rintro ⟨tau,hb,hpay,_⟩
  rw [payment_zero loc t K v z Q i f hf h ht tau hb] at hpay
  exact (not_lt_of_ge hpay) hlam

end MetricKMedianRecovery.CoincidentCopy

end OAI
end

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
lemma mem (h : Entry loc F B Q v z lam eta i) : i ∈ F ∪ B := by
  rcases h.2 with h|h
  · exact Finset.mem_union_right _ h
  · exact Finset.mem_union_left _ h.1
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

omit [DecidableEq X] in
lemma exact_opening_eta {loc : D → X} {F W : Finset X} {v z lam eta : ℝ} {i : X}
    (h : etaOpenable loc F W (1-3*v) (1+v^2) v z lam 0 i) (heta : 0 ≤ eta) :
    etaOpenable loc F W (1-3*v) (1+v^2) v z lam eta i := by
  obtain ⟨tau,hb,hp,hd⟩ := h
  refine ⟨tau,hb,?_,hd⟩
  have hn : 0 ≤ (Fintype.card D:ℝ)*eta := mul_nonneg (Nat.cast_nonneg _) heta
  simp only [mul_zero,sub_zero] at hp
  exact (sub_le_self lam hn).trans hp

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

lemma prefix_exact_eta {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {H : List X} (h : Prefix loc F B v z lam 0 Q H) (heta : 0 ≤ eta) :
    Prefix loc F B v z lam eta Q H := by
  induction h with
  | nil Q => exact Prefix.nil Q
  | cons hi ht ih =>
    refine Prefix.cons ⟨hi.1,?_⟩ ih
    rcases hi.2 with hi | ⟨hi,W,hW,hWF,hop⟩
    · exact Or.inl hi
    · exact Or.inr ⟨hi,W,hW,hWF,exact_opening_eta hop heta⟩

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

lemma exact_prefix_avoids_copy (loc : D → X) (F B Q : Finset X) (v z lam : ℝ)
    (i f : X) (hiB : i ∉ B) (hf : f ∈ Q)
    (hco : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam) (H : List X)
    (hH : Prefix loc F B v z lam 0 Q H) : i ∉ H := by
  induction hH with
  | nil => simp
  | @cons Q k H hk hH ih =>
    have hki : k ≠ i := by
      intro he
      subst k
      rcases hk.2 with hi | ⟨_,W,hW,_,hop⟩
      · exact hiB hi
      · exact CoincidentCopy.not_openable loc F W (1-3*v) (1+v^2) v z lam 0 i f
          (hW hf) hco ht (by simpa only [mul_zero,sub_zero] using hlam) hop
    simpa only [List.mem_cons,not_or] using
      And.intro (Ne.symm hki) (ih (Finset.mem_insert_of_mem hf))

theorem prefix_replace_open_copy (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (i f : X) (hiF : i ∈ F) (hf : f ∈ Q) (hiQ : i ∉ Q)
    (hco : ∀ j, dist (loc j) i = dist (loc j) f)
    (H : List X) (hiH : i ∉ H) (hH : Prefix loc F (insert f B) v z lam eta Q H) :
    Prefix loc F B v z lam eta (insert i (Q.erase f)) H := by
  induction hH with
  | nil => exact Prefix.nil _
  | @cons Q k H hk hH ih =>
    have hki : k ≠ i := by
      intro e
      exact hiH (List.mem_cons.mpr (Or.inl e.symm))
    have hkf : k ≠ f := by
      intro e
      exact hk.1 (e.symm ▸ hf)
    have hin : i ∉ H := fun h => hiH (List.mem_cons_of_mem k h)
    have hiQ' : i ∉ insert k Q := by
      simp only [Finset.mem_insert,not_or]
      exact ⟨Ne.symm hki,hiQ⟩
    apply Prefix.cons
    · refine ⟨?_,?_⟩
      · simp only [Finset.mem_insert,Finset.mem_erase,not_or]
        exact ⟨hki,fun h => hk.1 h.2⟩
      · rcases hk.2 with hb | ⟨hkF,W,hW,hWF,hop⟩
        · exact Or.inl ((Finset.mem_insert.mp hb).resolve_left hkf)
        · have hfW : f ∈ W := hW hf
          refine Or.inr ⟨hkF,insert i (W.erase f),?_,?_,?_⟩
          · exact Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hW)
          · apply Finset.insert_subset (Finset.mem_union_left _ hiF)
            intro x hx
            obtain ⟨hxf,hxW⟩ := Finset.mem_erase.mp hx
            rcases Finset.mem_union.mp (hWF hxW) with hxF | hxB
            · exact Finset.mem_union_left _ hxF
            · exact Finset.mem_union_right _ ((Finset.mem_insert.mp hxB).resolve_left hxf)
          · have he : insert f (W.erase f) = W := Finset.insert_erase hfW
            rw [← he] at hop
            exact (CoincidentCopy.openable_insert_equal loc F (W.erase f) (1-3*v)
              (1+v^2) v z lam eta f i k (fun j => (hco j).symm)).mp hop
    · have hh := ih (Finset.mem_insert_of_mem hf) hiQ' hin
      simpa only [Finset.erase_insert_of_ne hkf,Finset.insert_comm] using hh

theorem regularize (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (C G : List X) (i f : X) (hiF : i ∈ F) (hfF : f ∉ F)
    (hfQ : f ∉ Q ∪ C.toFinset) (hiG : i ∉ G)
    (hco : ∀ j, dist (loc j) i = dist (loc j) f)
    (hC : Prefix loc F B v z lam eta Q C)
    (hi : Entry loc F B (Q ∪ C.toFinset) v z lam eta i)
    (hold : Valid loc F (insert f B) Q v z lam eta (C++f::G)) :
    Valid loc F B Q v z lam eta (C++i::G) := by
  have hs := (prefix_append_iff.mp hold.1).2
  cases hs with
  | cons hfree hG =>
    have hiQ : i ∉ insert f (Q ∪ C.toFinset) := by
      simp only [Finset.mem_insert,not_or]
      exact ⟨fun he => hfF (he ▸ hiF),hi.1⟩
    have hnew := prefix_replace_open_copy loc F B (insert f (Q ∪ C.toFinset))
      v z lam eta i f hiF (Finset.mem_insert_self _ _) hiQ hco G hiG hG
    have hnew' : Prefix loc F B v z lam eta (insert i (Q ∪ C.toFinset)) G := by
      simpa only [Finset.erase_insert hfQ] using hnew
    refine ⟨hC.append (Prefix.cons hi hnew'),?_⟩
    have hmax : Maximal loc F (insert f (Q ∪ C.toFinset ∪ G.toFinset)) v z lam := by
      simpa only [List.toFinset_append,List.toFinset_cons,Finset.union_insert,
        Finset.insert_union,Finset.union_assoc] using hold.2
    have hm : Maximal loc F (insert i (Q ∪ C.toFinset ∪ G.toFinset)) v z lam := by
      intro k hk hkn hop
      have hkf : k ≠ f := fun he => hfF (he ▸ hk)
      have hkQ : k ∉ Q ∪ C.toFinset ∪ G.toFinset :=
        fun hh => hkn (Finset.mem_insert_of_mem hh)
      exact hmax k hk (by simpa only [Finset.mem_insert,not_or] using And.intro hkf hkQ)
        ((CoincidentCopy.openable_insert_equal loc F (Q ∪ C.toFinset ∪ G.toFinset)
          (1-3*v) (1+v^2) v z lam 0 f i k (fun j => (hco j).symm)).mpr hop)
    simpa only [List.toFinset_append,List.toFinset_cons,Finset.union_insert,
      Finset.insert_union,Finset.union_assoc] using hm

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

omit [PseudoMetricSpace X] in
lemma insert_subset_pool {F B : Finset X} {copy : X → X} {i : X} (hi : i ∈ F) :
    insert (copy i) B ⊆ pool F B copy :=
  Finset.insert_subset (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
    (subset_pool F B copy)

lemma Walk.last_good {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {n : ℕ} {H G : List X} (h : Walk loc F B Q copy v z lam eta n H G) :
    Good loc F B Q copy v z lam eta G := by
  induction h with
  | nil h => exact h
  | cons _ _ _ ih => exact ih

lemma regular_good {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {H : List X} (hH : Valid loc F B Q v z lam eta H) (hreg : ∀ k ∈ H, k ∈ F) :
    Good loc F B Q copy v z lam eta H := by
  refine ⟨⟨prefix_free_mono hH.1 (subset_pool F B copy),hH.2⟩,?_⟩
  have hs : H.toFinset ⊆ F := fun k hk => hreg k (List.mem_toFinset.mp hk)
  simp only [Finset.sdiff_eq_empty_iff_subset.mpr hs,Finset.card_empty,Nat.zero_le]

lemma one_copy_good {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {H : List X} {i : X} (hi : i ∈ F)
    (hH : Valid loc F (insert (copy i) B) Q v z lam eta H)
    (hreg : ∀ k ∈ H, k ∈ F ∨ k = copy i) :
    Good loc F B Q copy v z lam eta H := by
  refine ⟨⟨prefix_free_mono hH.1 (insert_subset_pool hi),hH.2⟩,?_⟩
  have hs : H.toFinset \ F ⊆ {copy i} := by
    intro k hk
    obtain ⟨hkH,hkF⟩ := Finset.mem_sdiff.mp hk
    exact Finset.mem_singleton.mpr ((hreg k (List.mem_toFinset.mp hkH)).resolve_left hkF)
  exact (Finset.card_le_card hs).trans (by simp)

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

lemma CorrectCompletion.retaining {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {complete : Finset X → List X} (hc : CorrectCompletion loc F v z lam complete)
    (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B) (H : List X)
    (hH : Prefix loc F B v z lam eta Q H) (i f : X) (hiB : i ∉ B)
    (hf : f ∈ Q ∪ H.toFinset) (hco : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam) :
    let G := complete (Q ∪ H.toFinset)
    (∀ k ∈ G, k ∈ F) ∧ i ∉ G ∧ Prefix loc F B v z lam 0 (Q ∪ H.toFinset) G ∧
      Valid loc F B Q v z lam eta (H++G) := by
  obtain ⟨⟨hG,hm⟩,hr⟩ := hc B (Q ∪ H.toFinset) (Finset.union_subset hQ hH.opened_subset)
  refine ⟨hr,exact_prefix_avoids_copy loc F B (Q ∪ H.toFinset) v z lam i f
    hiB hf hco ht hlam _ hG,hG,hH.append (prefix_exact_eta hG heta),?_⟩
  simpa only [List.toFinset_append,←Finset.union_assoc] using hm

lemma Path.toWalk {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {H J : List X} {T : List (List X)} (h : Path loc F B Q copy v z lam eta H T J) :
    Walk loc F B Q copy v z lam eta T.length H J := by
  induction h with
  | nil h => exact .nil h
  | cons h e t ih => exact .cons h e ih

lemma Path.append {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {H J K : List X} {T U : List (List X)} (h : Path loc F B Q copy v z lam eta H T J)
    (h' : Path loc F B Q copy v z lam eta J U K) :
    Path loc F B Q copy v z lam eta H (T++U) K := by
  induction h with
  | nil => exact h'
  | cons h e t ih => exact .cons h e (ih h')

theorem deleteSuffix_spec (loc : D → X) (F B Q : Finset X) (copy : X → X)
    (v z lam eta : ℝ) (complete : Finset X → List X)
    (hc : CorrectCompletion loc F v z lam complete) (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam) (C U E : List X) (i : X)
    (hiF : i ∈ F) (hiB : i ∉ B) (hif : i ≠ copy i)
    (hco : ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (hC : ∀ k ∈ C, k ∈ F) (hU : ∀ k ∈ U, k ∈ F) (hE : ∀ k ∈ E, k ∈ F)
    (hiE : i ∉ E)
    (hvalid : Valid loc F (insert (copy i) B) Q v z lam eta (C++U++copy i::E)) :
    let r := deleteSuffix complete Q copy C i U E
    (∀ k ∈ r.1, k ∈ F) ∧ i ∉ r.1 ∧
      Valid loc F (insert (copy i) B) Q v z lam eta (C++copy i::r.1) ∧
      Path loc F B Q copy v z lam eta (C++U++copy i::E) r.2 (C++copy i::r.1) := by
  induction U generalizing E with
  | nil =>
    have hv' : Valid loc F (insert (copy i) B) Q v z lam eta (C++copy i::E) := by
      simpa only [List.append_nil] using hvalid
    refine ⟨hE,hiE,hv',?_⟩
    simp only [deleteSuffix,List.append_nil]
    apply Path.nil
    apply one_copy_good hiF hv'
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact Or.inl (hC k hk)
    · rcases List.mem_cons.mp hk with rfl | hk
      · exact Or.inr rfl
      · exact Or.inl (hE k hk)
  | cons u U ih =>
    have huF : u ∈ F := hU u (List.mem_cons_self ..)
    have hUr : ∀ k ∈ U, k ∈ F := fun k hk => hU k (List.mem_cons_of_mem _ hk)
    have hsub : (C++U++copy i::E).Sublist (C++(u::U)++copy i::E) := by
      simpa only [List.append_assoc,List.cons_append] using
        (List.Sublist.cons u (List.Sublist.refl (U++copy i::E))).append_left C
    have hret := hvalid.1.sublist hsub
    have hf : copy i ∈ Q ∪ (C++U++copy i::E).toFinset := by simp
    have hiB' : i ∉ insert (copy i) B := by simpa only [Finset.mem_insert,not_or] using ⟨hif,hiB⟩
    have hQ' : Q ⊆ F ∪ insert (copy i) B :=
      hQ.trans (Finset.union_subset_union_right (Finset.subset_insert _ _))
    let A := complete (Q ∪ (C++U++copy i::E).toFinset)
    obtain ⟨hAreg,hiA,hA,hvA⟩ := hc.retaining heta hQ' (C++U++copy i::E) hret i (copy i) hiB' hf hco ht hlam
    have hEA : ∀ k ∈ E++A, k ∈ F := by
      intro k hk
      exact (List.mem_append.mp hk).elim (hE k) (hAreg k)
    have hiEA : i ∉ E++A := by simpa only [List.mem_append,not_or] using ⟨hiE,hiA⟩
    have hvEA : Valid loc F (insert (copy i) B) Q v z lam eta (C++U++copy i::(E++A)) := by
      simpa only [A,List.append_assoc,List.cons_append] using hvA
    obtain ⟨hG,hiG,hvG,hw⟩ := ih (E++A) hUr hEA hiEA hvEA
    refine ⟨hG,hiG,hvG,?_⟩
    have hg : Good loc F B Q copy v z lam eta (C++(u::U)++copy i::E) := by
      apply one_copy_good hiF hvalid
      intro k hk
      simp only [List.mem_append,List.mem_cons] at hk
      rcases hk with (hk | hk) | hk | hk
      · exact Or.inl (hC k hk)
      · exact Or.inl (hU k (List.mem_cons.mpr hk))
      · exact Or.inr hk
      · exact Or.inl (hE k hk)
    have hs := Step.remove (loc := loc) (F := F) (B := B) (Q := Q) (copy := copy)
      (v := v) (z := z) (lam := lam) C (U++copy i::E) A u huF
      (by simpa only [A,List.append_assoc] using prefix_free_mono hA (insert_subset_pool hiF)) hAreg
    apply Path.cons hg
    · simpa only [A,List.append_assoc,List.cons_append] using hs
    · exact hw

lemma Path.last_good {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {H J : List X} {T : List (List X)} (h : Path loc F B Q copy v z lam eta H T J) :
    Good loc F B Q copy v z lam eta J := h.toWalk.last_good

 theorem advancePrefix_spec_s238_oai (loc : D → X) (F B Q : Finset X) (copy : X → X)
    (v z lam eta : ℝ) (complete : Finset X → List X)
    (hc : CorrectCompletion loc F v z lam complete)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z)
    (hlam : 0 < lam) (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (C U : List X) (i : X) (hiF : i ∈ F) (hiB : i ∉ B)
    (hfresh : copy i ∉ F ∪ B) (hco : ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (hC : Prefix loc F B v z lam eta Q C)
    (hi : Entry loc F B (Q ∪ C.toFinset) v z lam eta i)
    (hCr : ∀ k ∈ C, k ∈ F) (hUr : ∀ k ∈ U, k ∈ F)
    (hcur : Valid loc F B Q v z lam eta (C++U)) :
    let r := advancePrefix complete Q copy C U i
    (∀ k ∈ r.1, k ∈ F) ∧ Valid loc F B Q v z lam eta (C++i::r.1) ∧
      Path loc F B Q copy v z lam eta (C++U) r.2 (C++i::r.1) := by
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have hfF : copy i ∉ F := fun hf => hfresh (Finset.mem_union_left _ hf)
  have hir : i ≠ copy i := fun he => hfF (he ▸ hiF)
  have hr : ∀ k ∈ C++U, k ∈ F := by
    intro k hk
    exact (List.mem_append.mp hk).elim (hCr k) (hUr k)
  have hf : copy i ∉ Q ∪ (C++U).toFinset := by
    intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · exact hfresh (hQ hm)
    · exact hfF (hr _ (List.mem_toFinset.mp hm))
  have happ := append_free loc F B Q v z lam eta hv hvsmall hz hlam hrow (C++U) hcur (copy i) hf
  let r := deleteSuffix complete Q copy C i U []
  obtain ⟨hGr,hiG,hvalid,hw⟩ := deleteSuffix_spec loc F B Q copy v z lam eta complete hc
    heta hQ ht hlam C U [] i hiF hiB hir hco hCr hUr (by simp) (by simp) happ
  have hfC : copy i ∉ Q ∪ C.toFinset := by
    intro hm
    apply hf
    rcases Finset.mem_union.mp hm with hm | hm
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (by simpa only [List.toFinset_append] using Finset.mem_union_left U.toFinset hm)
  have hvG := regularize loc F B Q v z lam eta C r.1 i (copy i) hiF hfF hfC hiG hco hC hi hvalid
  have hCG : ∀ k ∈ C++i::r.1, k ∈ F := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact hCr k hk
    · rcases List.mem_cons.mp hk with rfl | hk
      · exact hiF
      · exact hGr k hk
  have hi' : i ∉ Q ∪ (C++r.1).toFinset := by
    simp only [List.toFinset_append,Finset.mem_union,not_or,List.mem_toFinset]
    exact ⟨fun h => hi.1 (Finset.mem_union_left _ h),
      fun h => hi.1 (Finset.mem_union_right _ (List.mem_toFinset.mpr h)),hiG⟩
  have hs := Step.replace (loc := loc) (B := B) (copy := copy) (v := v) (z := z)
    (lam := lam) C r.1 i hiF hi'
  have hw' := hw.append (Path.cons hw.last_good hs (Path.nil (regular_good hvG hCG)))
  have hw'' := Path.cons (regular_good hcur hr) (Step.add _ i hiF) hw'
  exact ⟨hGr,hvG,hw''⟩

end MetricKMedianRecovery.CanonicalMergePath

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.MetricKMedianRecovery.CanonicalMergePath.advancePrefix_spec_s238_oai.{u_1, u_2} := @OAI.MetricKMedianRecovery.CanonicalMergePath.advancePrefix_spec_s238_oai.{u_1, u_2}
