-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.PhaseParameterAlignment.align_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:24:06.785845+00:00
-- url     : https://prove2.me/submissions/f86309bb-5435-450f-9c59-31e0579d1cbe

import Mathlib
import Definitions.Def_Q238K014
import Theorems.Thm_OAI_MetricKMedianRecovery_PhaseParameterTransfer_prefix_map_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_NearestImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LeafTransfer
variable {A X : Type*} [PseudoMetricSpace X] [DecidableEq X]

lemma nearest_images (W : Finset A) (hW : W.Nonempty) (r s : A → X) (p : X)
    (eps : ℝ) (hshrink : ∀ a ∈ W, dist p (s a) ≤ dist p (r a))
    (hloss : ∀ a ∈ W, dist p (r a) ≤ dist p (s a)+eps) :
    nearestDistance p (W.image s) ≤ nearestDistance p (W.image r) ∧
    nearestDistance p (W.image r) ≤ nearestDistance p (W.image s)+eps := by
  have hr : (W.image r).Nonempty := hW.image r
  have hs : (W.image s).Nonempty := hW.image s
  constructor
  · obtain ⟨x,hx,he⟩ := nearestDistance_attained p (W.image r) hr
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    rw [he]
    exact (nearestDistance_le_mem p (W.image s) (s a) (Finset.mem_image.mpr ⟨a,ha,rfl⟩)).trans
      (hshrink a ha)
  · obtain ⟨x,hx,he⟩ := nearestDistance_attained p (W.image s) hs
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    rw [he]
    exact (nearestDistance_le_mem p (W.image r) (r a) (Finset.mem_image.mpr ⟨a,ha,rfl⟩)).trans
      (hloss a ha)

end MetricKMedianRecovery.LeafTransfer

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

theorem maximal_price_mono (loc : D → X) (F Q : Finset X) (v z lam lam' : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hbase : ∀ i ∈ F, bidRow loc (1-3*v) z Q i ≤ lam)
    (hmax : ∀ i ∈ F, i ∉ Q → ¬etaOpenable loc F Q (1-3*v) (1+v^2) v z lam 0 i)
    (hm : lam ≤ lam') :
    ∀ i ∈ F, i ∉ Q → ¬etaOpenable loc F Q (1-3*v) (1+v^2) v z lam' 0 i := by
  intro i hi _ hop
  obtain ⟨tau,hb,hp,_⟩ := hop
  have hh := maximal_payment_lt loc F Q v z lam hv hvsmall hz hlam hbase hmax i hi tau hb
  simp only [mul_zero,sub_zero] at hp
  exact (not_lt_of_ge (hm.trans hp)) hh

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

theorem complete (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B) :
    ∃ H : List X, Prefix loc F B v z lam eta Q H ∧
      (∀ i ∈ H, i ∈ F) ∧ Maximal loc F (Q ∪ H.toFinset) v z lam := by
  classical
  generalize heq : (F \ Q).card = fuel
  induction fuel using Nat.strong_induction_on generalizing Q with
  | h fuel ih =>
    by_cases hmax : Maximal loc F Q v z lam
    · exact ⟨[],Prefix.nil Q,by simp,by simpa using hmax⟩
    · simp only [Maximal,not_forall,not_not] at hmax
      obtain ⟨i,hi,hin,hop⟩ := hmax
      have hmem : i ∈ F \ Q := Finset.mem_sdiff.mpr ⟨hi,hin⟩
      have he : F \ insert i Q = (F \ Q).erase i := by
        ext f
        simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_erase]
        tauto
      have hdrop : (F \ insert i Q).card < fuel := by
        rw [he,← heq]
        exact Finset.card_erase_lt_of_mem hmem
      have hQ' : insert i Q ⊆ F ∪ B :=
        Finset.insert_subset (Finset.mem_union_left B hi) hQ
      obtain ⟨H,hH,hreg,hmax⟩ := ih (F \ insert i Q).card hdrop (insert i Q) hQ' rfl
      refine ⟨i::H,Prefix.cons ⟨hin,Or.inr ⟨hi,Q,Finset.Subset.refl _,hQ,
        exact_opening_eta hop heta⟩⟩ hH,?_,?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl|hx
        · exact hi
        · exact hreg _ hx
      · simpa only [List.toFinset_cons,Finset.union_insert,Finset.insert_union] using hmax

end PhaseSequence
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeCompletion
open PhaseSequence PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

theorem exists_regular_history (loc : D → X) (F B Q : Finset X) (v lam : ℝ)
    (q n : ℕ) (hQ : Q ⊆ F ∪ B) :
    ∃ T : List (List X), T.length = n ∧ History loc F B v lam 0 q Q T ∧ Regular F T := by
  induction n generalizing q Q with
  | zero => exact ⟨[],rfl,History.nil _ _,by simp [Regular]⟩
  | succ n ih =>
    obtain ⟨H,hH,hreg,hmax⟩ := complete loc F B Q v ((1+v^2)^q) lam 0 le_rfl hQ
    obtain ⟨T,hT,hh,hR⟩ := ih (Q ∪ H.toFinset) (q+1) (Finset.union_subset hQ hH.opened_subset)
    refine ⟨H::T,by simp only [List.length_cons,hT],History.cons ⟨hH,hmax⟩ hh,?_⟩
    intro G hG
    rcases List.mem_cons.mp hG with rfl | hG
    · exact hreg
    · exact hR G hG

theorem attains_exists (loc : D → X) (F B Q : Finset X) (v lam : ℝ) (q n : ℕ)
    (hQ : Q ⊆ F ∪ B) : ∃ c, Attains loc F B Q v lam q n c := by
  obtain ⟨T,hT,hh,hr⟩ := exists_regular_history loc F B Q v lam q n hQ
  exact ⟨_,T,hT,hh,hr,rfl⟩

end MetricKMedianRecovery.PhaseMergeCompletion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_OpenableMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseParameterTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] [PseudoMetricSpace X] in
lemma image_regular_union {F B : Finset X} {r : X → X}
    (hfix : ∀ i ∈ F, r i = i) : (F ∪ B).image r ⊆ F ∪ B.image r := by
  intro x hx
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  rcases Finset.mem_union.mp hi with hi | hi
  · exact Finset.mem_union_left _ ((hfix i hi).symm ▸ hi)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)

theorem valid_map (loc : D → X) (F B Q : Finset X) (H : List X) (r : X → X)
    (v z lam lam' eta eps : ℝ) (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z)
    (hlam : 0 < lam) (heps : 0 ≤ eps) (hprice : lam ≤ lam')
    (herror : lam'-lam+(Fintype.card D:ℝ)*((1-3*v)*eps) ≤ (Fintype.card D:ℝ)*eta)
    (hinj : Function.Injective r) (hfix : ∀ i ∈ F, r i = i)
    (hQ : Q ⊆ F ∪ B)
    (hshrink : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) (r x) ≤ dist (loc j) x)
    (hloss : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) x ≤ dist (loc j) (r x)+eps)
    (hbase : ∀ i ∈ F, bidRow loc (1-3*v) z (Q ∪ H.toFinset) i ≤ lam)
    (hp : PhaseSequence.Valid loc F B Q v z lam 0 H) :
    PhaseSequence.Valid loc F (B.image r) (Q.image r) v z lam' eta (H.map r) := by
  refine ⟨prefix_map_s238 loc F B Q H r v z lam lam' eta eps hv hvsmall heps hprice herror
    hinj hfix hshrink hloss hp.1,?_⟩
  have hsub : Q ∪ H.toFinset ⊆ F ∪ B := Finset.union_subset hQ hp.1.opened_subset
  change ∀ i ∈ F, i ∉ Q.image r ∪ (H.map r).toFinset → _
  have hEq : Q.image r ∪ (H.map r).toFinset = (Q ∪ H.toFinset).image r := by
    ext x
    simp only [Finset.mem_union,Finset.mem_image,List.mem_toFinset,List.mem_map]
    aesop
  rw [hEq]
  by_cases hne : (Q ∪ H.toFinset).Nonempty
  · have hd (j : D) := LeafTransfer.nearest_images (Q ∪ H.toFinset) hne id r (loc j) eps
      (fun x hx => hshrink j x (hsub hx)) (fun x hx => hloss j x (hsub hx))
    simp only [Finset.image_id] at hd
    exact PriceTransfer.maximal_shrink loc F _ _ v z lam lam' hne (hne.image r)
      hv hvsmall hz hlam hbase hp.2 hprice (fun j => (hd j).1)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    have hh := PriceTransfer.maximal_price_mono loc F (Q ∪ H.toFinset) v z lam lam'
      hv hvsmall hz hlam hbase hp.2 hprice
    simpa only [he,Finset.image_empty] using hh

end MetricKMedianRecovery.PhaseParameterTransfer

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RegularMap
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseParameterAlignment
open PhaseSequence PhaseMergeCompletion PhaseCountCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] [PseudoMetricSpace X] [DecidableEq X] in
lemma regular_map_eq (F : Finset X) (G : List X) (r : X → X)
    (hfix : ∀ i ∈ F, r i = i) (hG : ∀ i ∈ G, i ∈ F) : G.map r = G := by
  have he : G.map r = G.map id := List.map_congr_left (fun i hi => hfix i (hG i hi))
  simpa only [List.map_id] using he

theorem align_s238_oai (loc : D → X) (F B Q : Finset X) (G : List X) (r : X → X)
    (v lam lam' eta eps : ℝ) (q n k a b : ℕ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam) (heps : 0 ≤ eps)
    (hprice : lam ≤ lam')
    (herror : lam'-lam+(Fintype.card D:ℝ)*((1-3*v)*eps) ≤ (Fintype.card D:ℝ)*eta)
    (hinj : Function.Injective r) (hfix : ∀ i ∈ F, r i = i)
    (hQ : Q ⊆ F ∪ B)
    (hshrink : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) (r x) ≤ dist (loc j) x)
    (hloss : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) x ≤ dist (loc j) (r x)+eps)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (hG : Valid loc F B Q v ((1+v^2)^q) lam 0 G)
    (hGr : ∀ i ∈ G, i ∈ F) (hab : Sandwich k a b) :
    Valid loc F (B.image r) (Q.image r) v ((1+v^2)^q) lam' eta G ∧
      ∃ c, Attains loc F (B.image r) (Q.image r ∪ G.toFinset) v lam' (q+1) n c ∧
        (c = k ∨ Sandwich k a c ∨ Sandwich k c b) := by
  have hbase : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) (Q ∪ G.toFinset) i ≤ lam := by
    intro i hi
    exact (bidRow_antitone_open loc (1-3*v) _ Q (Q ∪ G.toFinset) i
      (by linarith only [hvsmall]) Finset.subset_union_left).trans (hrow i hi)
  have hG' := PhaseParameterTransfer.valid_map loc F B Q G r v _ lam lam' eta eps
    hv hvsmall (by positivity) hlam heps hprice herror hinj hfix hQ hshrink hloss hbase hG
  rw [regular_map_eq F G r hfix hGr] at hG'
  refine ⟨hG',?_⟩
  have hQ' : Q.image r ⊆ F ∪ B.image r :=
    (Finset.image_subset_image hQ).trans (PhaseParameterTransfer.image_regular_union hfix)
  obtain ⟨c,hc⟩ := attains_exists loc F (B.image r) (Q.image r ∪ G.toFinset) v lam'
    (q+1) n (Finset.union_subset hQ' hG'.1.opened_subset)
  refine ⟨c,hc,?_⟩
  unfold Sandwich at hab ⊢
  omega

end MetricKMedianRecovery.PhaseParameterAlignment

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.MetricKMedianRecovery.PhaseParameterAlignment.align_s238_oai.{u_1, u_2} := @OAI.MetricKMedianRecovery.PhaseParameterAlignment.align_s238_oai.{u_1, u_2}
