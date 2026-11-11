-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.CanonicalMergeRefinement.refinePath_spec_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:18:43.992774+00:00
-- url     : https://prove2.me/submissions/3cd29895-f141-48e3-b3ec-49042af179cf

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

theorem maximal_replace (loc : D → X) (F Q : Finset X) (v z lam : ℝ)
    (i f : X) (h : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (hmax : ∀ k ∈ F, k ∉ insert i Q →
      ¬etaOpenable loc F (insert i Q) (1-3*v) (1+v^2) v z lam 0 k) :
    ∀ k ∈ F, k ∉ insert f Q →
      ¬etaOpenable loc F (insert f Q) (1-3*v) (1+v^2) v z lam 0 k := by
  intro k hk hkn
  by_cases hki : k = i
  · subst k
    exact not_openable loc F (insert f Q) (1-3*v) (1+v^2) v z lam 0 i f
      (Finset.mem_insert_self _ _) h ht (by simpa only [mul_zero,sub_zero] using hlam)
  · intro hop
    have hn : k ∉ insert i Q := by
      simpa only [Finset.mem_insert,not_or] using ⟨hki,fun hkQ => hkn (Finset.mem_insert_of_mem hkQ)⟩
    exact hmax k hk hn ((openable_insert_equal loc F Q (1-3*v) (1+v^2) v z lam 0 i f k h).mpr hop)

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

theorem delete_suffix_with_copy (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (C T G R : List X) (i f : X) (hf : f ∉ Q ∪ (C++T++G).toFinset)
    (hco : ∀ j, dist (loc j) i = dist (loc j) f)
    (hbefore : Valid loc F B Q v z lam eta (C++i::T))
    (hafter : Prefix loc F B v z lam eta Q (C++T++G))
    (hRG : R.Sublist G) :
    Valid loc F (insert f B) Q v z lam eta ((C++T++R)++[f]) := by
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have hsub : (C++T++R).Sublist (C++T++G) := hRG.append_left (C++T)
  have hp := prefix_free_mono (hafter.sublist hsub) (Finset.subset_insert f B)
  have hf' : f ∉ Q ∪ (C++T++R).toFinset := by
    intro hm
    apply hf
    rcases Finset.mem_union.mp hm with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _
        (List.mem_toFinset.mpr (hsub.subset (List.mem_toFinset.mp h)))
  refine ⟨hp.append (Prefix.cons ⟨hf',Or.inl (Finset.mem_insert_self _ _)⟩ (Prefix.nil _)),?_⟩
  have hmax : Maximal loc F (insert i (Q ∪ C.toFinset ∪ T.toFinset)) v z lam := by
    simpa only [List.toFinset_append,List.toFinset_cons,Finset.union_insert,
      Finset.insert_union,Finset.union_assoc] using hbefore.2
  have hmax' := CoincidentCopy.maximal_replace loc F (Q ∪ C.toFinset ∪ T.toFinset)
    v z lam i f hco ht hlam hmax
  apply MaximalPrefixSelection.maximal_superset loc F
    (insert f (Q ∪ C.toFinset ∪ T.toFinset)) _ v z lam lam hv hvsmall hz hlam
  · intro k hk
    exact (bidRow_antitone_open loc (1-3*v) z Q _ k ht
      (fun x hx => Finset.mem_insert_of_mem
        (Finset.mem_union_left _ (Finset.mem_union_left _ hx)))).trans (hrow k hk)
  · exact hmax'
  · exact le_rfl
  · intro x hx
    simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
      Finset.mem_union,Finset.mem_insert,Finset.notMem_empty,or_false] at hx ⊢
    tauto

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

lemma Walk.first_good {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {n : ℕ} {H G : List X} (h : Walk loc F B Q copy v z lam eta n H G) :
    Good loc F B Q copy v z lam eta H := by
  cases h with
  | nil h => exact h
  | cons h _ _ => exact h

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

lemma Path.toWalk {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {H J : List X} {T : List (List X)} (h : Path loc F B Q copy v z lam eta H T J) :
    Walk loc F B Q copy v z lam eta T.length H J := by
  induction h with
  | nil h => exact .nil h
  | cons h e t ih => exact .cons h e ih

end MetricKMedianRecovery.CanonicalMergePath

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeRefine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeRefinement

section
open PhaseSequence PhaseMergeSurgery PhaseMergePath
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma Chain.last_good {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {n : ℕ} {H G : List X} (h : Chain loc F B Q v z lam eta n H G) :
    Good loc F B Q v z lam eta G := by
  induction h with
  | nil h => exact h
  | cons _ _ _ ih => exact ih

lemma Good.mono_free {loc : D → X} {F B B' Q : Finset X} {v z lam eta : ℝ}
    {H : List X} (h : Good loc F B Q v z lam eta H) (hB : B ⊆ B') :
    Good loc F B' Q v z lam eta H :=
  ⟨⟨prefix_free_mono h.1.1 hB,h.1.2⟩,h.2⟩

omit [Fintype D] [PseudoMetricSpace X] in
lemma cap_append {F : Finset X} {H G : List X} {f : X} (hsub : H.Sublist G)
    (hcap : (G.toFinset \ F).card ≤ 1) : ((H++[f]).toFinset \ F).card ≤ 2 := by
  have hs : (H++[f]).toFinset \ F ⊆ (G.toFinset \ F) ∪ {f} := by
    intro x hx
    obtain ⟨hxH,hxF⟩ := Finset.mem_sdiff.mp hx
    rcases List.mem_append.mp (List.mem_toFinset.mp hxH) with hxH | hxH
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
        ⟨List.mem_toFinset.mpr (hsub.subset hxH),hxF⟩)
    · exact Finset.mem_union_right _ (by simpa only [List.mem_singleton,Finset.mem_singleton] using hxH)
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  simp only [Finset.card_singleton] at hc
  omega

lemma entry_fresh {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {C T : List X} {i : X} (h : Prefix loc F B v z lam eta Q (C++i::T)) :
    i ∉ Q ∪ (C++T).toFinset := by
  have hiL : i ∈ C++i::T := List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hiQ : i ∉ Q := fun hi => Finset.disjoint_left.mp h.disjoint hi (List.mem_toFinset.mpr hiL)
  have hd := List.nodup_append.mp h.nodup
  have hiC : i ∉ C := fun hi => hd.2.2 i hi i (List.mem_cons_self ..) rfl
  have hiT := (List.nodup_cons.mp hd.2.1).1
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_append,not_or]
  exact ⟨hiQ,hiC,hiT⟩

end

open PhaseSequence PhaseMergeSurgery PhaseMergePath
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] in
lemma Edit.mono_free {loc : D → X} {F B B' Q : Finset X} {H G : List X}
    (h : Edit loc F B Q H G) (hB : B ⊆ B') : Edit loc F B' Q H G := by
  cases h with
  | freeAppend H i f hi hf hco => exact Edit.freeAppend H i f hi (hB hf) hco
  | paidDelete C T i hi => exact Edit.paidDelete C T i hi
  | coincident hc => exact Edit.coincident hc

lemma good_of_one {loc : D → X} {F B B' Q : Finset X} {copy : X → X}
    {v z lam eta : ℝ} {H : List X} (h : PhaseMergePath.Good loc F B Q copy v z lam eta H)
    (hB : pool F B copy ⊆ B') : Good loc F B' Q v z lam eta H :=
  ⟨⟨prefix_free_mono h.1.1 hB,h.1.2⟩,h.2.trans (by omega)⟩

end MetricKMedianRecovery.PhaseMergeRefinement

namespace MetricKMedianRecovery.CanonicalMergeRefinement
open PhaseSequence PhaseMergeSurgery PhaseMergePath PhaseMergeRefinement
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [PseudoMetricSpace X] [DecidableEq X] in
lemma mem_cuts {H C T : List X} {i : X} : (C,i,T)∈cuts H ↔ H=C++i::T := by
  constructor
  · intro h
    induction H generalizing C T i with
    | nil => simp only [cuts,List.not_mem_nil] at h
    | cons x H ih =>
      rcases List.mem_cons.mp h with h | h
      · cases h
        rfl
      · obtain ⟨⟨C',i',T'⟩,hp,he⟩ := List.mem_map.mp h
        cases he
        exact congrArg (List.cons x) (ih hp)
  · intro h
    subst H
    induction C with
    | nil => exact List.mem_cons_self ..
    | cons c C ih =>
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(C,i,T),ih,rfl⟩)

omit [PseudoMetricSpace X] in
lemma view_sound (F : Finset X) (R : List X) (copy : X → X) (H G : List X) (J : Jump X)
    (h : view F R copy H G=some J) : accepts F copy H G J := by
  have hh := List.find?_some h
  exact of_decide_eq_true hh

lemma view_exists {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam : ℝ}
    {H G : List X} (R : List X) (hR : ∀ i∈F,i∈R)
    (h : Step loc F B Q copy v z lam H G) :
    ∃ J,view F R copy H G=some J := by
  have hex : ∃ J∈candidates R H G, accepts F copy H G J := by
    cases h with
    | add H i hi =>
      refine ⟨.add i,?_,rfl,rfl,hi⟩
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr ⟨i,hR i hi,rfl⟩))
    | remove C T A i hi hA hreg =>
      refine ⟨.remove C T A i,?_,rfl,rfl,hi,hreg⟩
      apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨(C,i,T),mem_cuts.mpr rfl,?_⟩
      have hd : ((C++T)++A).drop ((C++i::T).length-1)=A := by
        have he : (C++i::T).length-1=(C++T).length := by simp only [List.length_append,List.length_cons]; omega
        rw [he,List.drop_left]
      simp only [hd]
    | replace C T i hi hin =>
      refine ⟨.replace C T i,?_,rfl,rfl,hi⟩
      exact List.mem_append_right _ (List.mem_map.mpr ⟨(C,i,T),mem_cuts.mpr rfl,rfl⟩)
  have hn : view F R copy H G ≠ none := by
    intro hn
    obtain ⟨J,hJ,hacc⟩ := hex
    have hh := List.find?_eq_none.mp hn J hJ
    exact hh (decide_eq_true hacc)
  exact Option.ne_none_iff_exists'.mp hn

lemma EPath.toChain {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {H J : List X} {T : List (List X)} (h : EPath loc F B Q v z lam eta H T J) :
    Chain loc F B Q v z lam eta T.length H J := by
  induction h with
  | nil h => exact .nil h
  | cons h e t ih => exact .cons h e ih

lemma EPath.last_good {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {H J : List X} {T : List (List X)} (h : EPath loc F B Q v z lam eta H T J) :
    PhaseMergeRefinement.Good loc F B Q v z lam eta J := h.toChain.last_good

lemma EPath.append {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {H J K : List X} {T U : List (List X)} (h : EPath loc F B Q v z lam eta H T J)
    (h' : EPath loc F B Q v z lam eta J U K) :
    EPath loc F B Q v z lam eta H (T++U) K := by
  induction h with
  | nil => exact h'
  | cons h e t ih => exact .cons h e (ih h')

lemma EPath.mono_free {loc : D → X} {F B B' Q : Finset X} {v z lam eta : ℝ}
    {H J : List X} {T : List (List X)} (h : EPath loc F B Q v z lam eta H T J)
    (hBB : B⊆B') : EPath loc F B' Q v z lam eta H T J := by
  induction h with
  | nil h => exact .nil (h.mono_free hBB)
  | cons h e t ih =>
    exact .cons (h.mono_free hBB)
      (e.elim (fun he => Or.inl (he.mono_free hBB)) (fun he => Or.inr (he.mono_free hBB))) ih

omit [PseudoMetricSpace X] [DecidableEq X] in
lemma growSuffix_length (C A : List X) (f : X) : (growSuffix C f A).length=A.length := by
  induction A with
  | nil => rfl
  | cons i A ih => simp only [growSuffix,List.length_append,List.length_cons,List.length_nil,ih]

 theorem growSuffix_spec (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (C A : List X) (f : X) (hreg : ∀ i∈A,i∈F)
    (hval : ∀ R : List X, R.Sublist A →
      PhaseMergeRefinement.Good loc F B Q v z lam eta ((C++R)++[f])) :
    EPath loc F B Q v z lam eta (C++[f]) (growSuffix C f A) ((C++A)++[f]) := by
  induction A with
  | nil => simpa only [growSuffix,List.append_nil] using EPath.nil (hval [] (List.Sublist.refl []))
  | cons i A ih =>
    have hi : i∈F := hreg i (List.mem_cons_self ..)
    have hg : ∀ R : List X, R.Sublist A →
        PhaseMergeRefinement.Good loc F B Q v z lam eta ((C++R)++[f]) :=
      fun R hR => hval R (List.Sublist.cons i hR)
    have ht := ih (fun j hj => hreg j (List.mem_cons_of_mem _ hj)) hg
    have hs := Edit.paidDelete (loc := loc) (B := B) (Q := Q) C (A++[f]) i hi
    have hs' : Adjacent loc F B Q ((C++A)++[f]) ((C++i::A)++[f]) :=
      Or.inr (by simpa only [List.append_assoc,List.cons_append] using hs)
    exact ht.append (.cons ht.last_good hs' (.nil (hval _ (List.Sublist.refl _))))

omit [PseudoMetricSpace X] [DecidableEq X] in
lemma removeVertices_length (C T A : List X) (f : X) :
    (removeVertices C T A f).length=A.length+2 := by
  simp only [removeVertices,List.length_cons,List.length_nil,List.length_append,growSuffix_length]

 theorem removeVertices_spec (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hQ : Q ⊆ F ∪ B) (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (C T A : List X) (i f : X) (hi : i ∈ F) (hf : f ∉ F ∪ B)
    (hco : ∀ j, dist (loc j) i = dist (loc j) f)
    (hreg : ∀ j ∈ A, j ∈ F)
    (hbefore : Valid loc F B Q v z lam eta (C++i::T))
    (hafter : Valid loc F B Q v z lam eta ((C++T)++A))
    (hcapb : ((C++i::T).toFinset \ F).card ≤ 1)
    (hcapa : (((C++T)++A).toFinset \ F).card ≤ 1) :
    EPath loc F (insert f B) Q v z lam eta (C++i::T)
      (removeVertices C T A f) ((C++T)++A) := by
  have hfF : f ∉ F := fun h => hf (Finset.mem_union_left _ h)
  have hfH : f ∉ Q ∪ ((C++T)++A).toFinset :=
    fun h => hf ((Finset.union_subset hQ hafter.1.opened_subset) h)
  have hval : ∀ R : List X, R.Sublist A →
      PhaseMergeRefinement.Good loc F (insert f B) Q v z lam eta (((C++T)++R)++[f]) := by
    intro R hR
    refine ⟨delete_suffix_with_copy loc F B Q v z lam eta hv hvsmall hz hlam hrow
      C T A R i f hfH hco hbefore hafter.1 hR,?_⟩
    exact cap_append (hR.append_left (C++T)) hcapa
  have hgrow := growSuffix_spec loc F (insert f B) Q v z lam eta (C++T) A f hreg hval
  have hgoodb : PhaseMergeRefinement.Good loc F (insert f B) Q v z lam eta (C++i::T) :=
    ⟨⟨prefix_free_mono hbefore.1 (Finset.subset_insert f B),hbefore.2⟩,by omega⟩
  have hgooda : PhaseMergeRefinement.Good loc F (insert f B) Q v z lam eta ((C++T)++A) :=
    ⟨⟨prefix_free_mono hafter.1 (Finset.subset_insert f B),hafter.2⟩,by omega⟩
  have hc : Coincident loc F Q (C++i::T) ((C++T)++[f]) := by
    refine ⟨i,f,Q ∪ (C++T).toFinset,hi,hfF,entry_fresh hbefore.1,?_,?_,?_,hco⟩
    · intro hh
      exact hfH ((Finset.union_subset_union_right (by
        intro x hx
        exact List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl (List.mem_toFinset.mp hx))) :
          (C++T).toFinset ⊆ ((C++T)++A).toFinset)) hh)
    · simp only [List.toFinset_append,List.toFinset_cons,Finset.union_insert]
    · simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.union_empty,
        Finset.union_insert]
  exact .cons hgoodb (Or.inl (.coincident hc)) (hgrow.append
    (.cons hgrow.last_good (Or.inr (.freeAppend _ i f hi (Finset.mem_insert_self _ _) hco)) (.nil hgooda)))

 theorem expand_spec (loc : D → X) (F B Q : Finset X) (copy spare : X → X)
    (v z lam eta : ℝ) (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hQ : Q ⊆ F ∪ B) (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (hc : ∀ i ∈ F, copy i ∉ F ∪ B)
    (hd : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (hs : ∀ i ∈ F, spare i ∉ F ∪ pool F B copy)
    (he : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (spare i))
    (H G : List X) (J : Jump X) (hacc : accepts F copy H G J)
    (hH : PhaseMergePath.Good loc F B Q copy v z lam eta H)
    (hG : PhaseMergePath.Good loc F B Q copy v z lam eta G) :
    (J.expand spare G).length ≤ F.card+2 ∧
      EPath loc F (pool F (pool F B copy) spare) Q v z lam eta H (J.expand spare G) G := by
  have hB1 : pool F B copy ⊆ pool F (pool F B copy) spare := subset_pool _ _ _
  have hQ1 : Q ⊆ F ∪ pool F B copy := hQ.trans (Finset.union_subset_union_right (subset_pool _ _ _))
  cases J with
  | add i =>
    simp only [accepts,Jump.source,Jump.target,Jump.labels] at hacc
    rcases hacc with ⟨_,rfl,hi⟩
    refine ⟨by simp only [Jump.expand,List.length_singleton]; omega,?_⟩
    exact .cons (good_of_one hH hB1) (Or.inl (.freeAppend H i (copy i) hi
      (hB1 (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩))) (hd i hi)))
      (.nil (good_of_one hG hB1))
  | remove C T A i =>
    simp only [accepts,Jump.source,Jump.target,Jump.labels] at hacc
    rcases hacc with ⟨rfl,rfl,hi,hreg⟩
    have hAr := (prefix_append_iff.mp hG.1.1).2
    have hAlen := regular_length hAr hreg
    refine ⟨?_,?_⟩
    · simpa only [Jump.expand,removeVertices_length] using Nat.add_le_add_right hAlen 2
    · have hh := removeVertices_spec loc F (pool F B copy) Q v z lam eta hv hvsmall hz hlam
        hQ1 hrow C T A i (spare i) hi (hs i hi) (he i hi) hreg hH.1 hG.1 hH.2 hG.2
      exact hh.mono_free (insert_subset_pool hi)
  | replace C T i =>
    simp only [accepts,Jump.source,Jump.target,Jump.labels] at hacc
    rcases hacc with ⟨rfl,rfl,hi⟩
    have hc' : Coincident loc F Q (C++i::T) (C++copy i::T) := by
      refine ⟨i,copy i,Q ∪ (C++T).toFinset,hi,?_,entry_fresh hG.1.1,entry_fresh hH.1.1,?_,?_,hd i hi⟩
      · intro hci
        exact hc i hi (Finset.mem_union_left _ hci)
      · simp only [List.toFinset_append,List.toFinset_cons,Finset.union_insert]
      · simp only [List.toFinset_append,List.toFinset_cons,Finset.union_insert]
    exact ⟨by simp only [Jump.expand,List.length_singleton]; omega,
      .cons (good_of_one hH hB1) (Or.inr (.coincident hc')) (.nil (good_of_one hG hB1))⟩

 theorem refinePath_spec_s238_oai (loc : D → X) (F B Q : Finset X) (R : List X) (copy spare : X → X)
    (v z lam eta : ℝ) (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hR : ∀ i∈F,i∈R) (hQ : Q ⊆ F ∪ B)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (hc : ∀ i ∈ F, copy i ∉ F ∪ B)
    (hd : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (hs : ∀ i ∈ F, spare i ∉ F ∪ pool F B copy)
    (he : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (spare i))
    {H G : List X} {T : List (List X)}
    (h : CanonicalMergePath.Path loc F B Q copy v z lam eta H T G) :
    (refinePath F R copy spare H T).length ≤ T.length*(F.card+2) ∧
      EPath loc F (pool F (pool F B copy) spare) Q v z lam eta H
        (refinePath F R copy spare H T) G := by
  have hB1 : pool F B copy ⊆ pool F (pool F B copy) spare := subset_pool _ _ _
  induction h with
  | nil hg => exact ⟨by simp only [refinePath,List.length_nil,Nat.zero_mul,Nat.le_refl],.nil (good_of_one hg hB1)⟩
  | @cons H G T J hg step tail ih =>
    obtain ⟨V,hV⟩ := view_exists R hR step
    have hacc := view_sound F R copy H G V hV
    have hG := tail.toWalk.first_good
    obtain ⟨hn,hp⟩ := expand_spec loc F B Q copy spare v z lam eta hv hvsmall hz hlam
      hQ hrow hc hd hs he H G V hacc hg hG
    simp only [refinePath,hV,List.length_append,List.length_cons]
    refine ⟨?_,hp.append ih.2⟩
    calc
      (V.expand spare G).length+(refinePath F R copy spare G T).length ≤
          (F.card+2)+T.length*(F.card+2) := Nat.add_le_add hn ih.1
      _ = (T.length+1)*(F.card+2) := by ring

end MetricKMedianRecovery.CanonicalMergeRefinement

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.MetricKMedianRecovery.CanonicalMergeRefinement.refinePath_spec_s238_oai.{u_1, u_2} := @OAI.MetricKMedianRecovery.CanonicalMergeRefinement.refinePath_spec_s238_oai.{u_1, u_2}
