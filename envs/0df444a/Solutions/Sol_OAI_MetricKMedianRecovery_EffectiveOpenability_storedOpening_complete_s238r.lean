-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.EffectiveOpenability.storedOpening_complete_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:35:14.783217+00:00
-- url     : https://prove2.me/submissions/ad13f835-3b73-4a39-ba9f-6e3139675e1f

import Mathlib
import Definitions.Def_Q238L020
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_Stored_exactSolve_eq_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_boundedRationalDecide_correct_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_LinearPayment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.OpenabilityLinearization
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X]

lemma near_bid_nonnegative (v z d tau : ℝ) (hv : 0 < v) (hv1 : v < 1/6)
    (hz : 0 ≤ z) (hd : 0 ≤ d) (hnear : d ≤ v*z) (htau : z ≤ tau) :
    0 ≤ tau-(1-3*v)*d := by
  have ht : 0 ≤ 1-3*v := by linarith
  have ht1 : 1-3*v ≤ 1 := by linarith
  have hd1 : d ≤ z := hnear.trans (by nlinarith)
  have hm : (1-3*v)*d ≤ d := by nlinarith
  linarith

lemma payment_eq_linear (loc : D → X) (W : Finset X) (v z : ℝ) (i : X) (tau : D → ℝ)
    (hv : 0 < v) (hv1 : v < 1/6) (hz : 0 ≤ z)
    (hb : admissibleBids loc (1-3*v) (1+v^2) v z W i tau) :
    openingPayment loc (1-3*v) z W i tau = linearPayment loc (1-3*v) v z W i tau := by
  classical
  unfold openingPayment linearPayment
  apply Finset.sum_congr rfl
  intro j _
  by_cases ha : activeAt loc (1-3*v) z W j
  · simp only [ite_eq_left ha]
    by_cases hn : dist i (loc j) ≤ v*z
    · rw [ite_eq_left hn,max_eq_left (near_bid_nonnegative v z _ _ hv hv1 hz dist_nonneg hn (hb j ha).1)]
    · rw [ite_eq_right hn,(hb j ha).2.2.2 (lt_of_not_ge hn)]
  · simp only [ite_eq_right ha]

lemma dual_eq (loc : D → X) (t z : ℝ) (W : Finset X) (i₀ : X) (tau : D → ℝ) (a : D) :
    openingDual loc t z W i₀ tau a = ∑ j, max (dualTerm loc t z W i₀ tau a j) 0 := by
  classical
  unfold openingDual dualTerm
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> rfl

theorem openable_iff_linear_feasible (loc : D → X) (F W : Finset X) (v z lam eta : ℝ) (i : X)
    (hv : 0 < v) (hv1 : v < 1/6) (hz : 0 ≤ z) :
    etaOpenable loc F W (1-3*v) (1+v^2) v z lam eta i ↔
      ∃ tau : D → ℝ, ∃ y : F → D → D → ℝ, Feasible loc F W v z lam eta i tau y := by
  classical
  constructor
  · rintro ⟨tau,hb,hp,hd⟩
    refine ⟨tau,(fun f a j => max (dualTerm loc (1-3*v) z W f tau a j) 0),hb,?_,?_⟩
    · rwa [←payment_eq_linear loc W v z i tau hv hv1 hz hb]
    · intro f a ha
      refine ⟨fun j => ⟨le_max_right _ _,le_max_left _ _⟩,?_⟩
      rw [←dual_eq]
      exact hd f f.property a ha
  · rintro ⟨tau,y,hb,hp,hd⟩
    refine ⟨tau,hb,?_,?_⟩
    · rwa [payment_eq_linear loc W v z i tau hv hv1 hz hb]
    · intro f hf a ha
      rw [dual_eq]
      have hy := hd ⟨f,hf⟩ a ha
      exact (Finset.sum_le_sum (fun j _ => max_le (hy.1 j).2 (hy.1 j).1)).trans hy.2

end MetricKMedianRecovery.OpenabilityLinearization

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_Nearest
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalOpenability
open RationalLinearFeasibility OpenabilityLinearization
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] [DecidableEq X] in
lemma nearest_cast (loc : D → X) (d : X → D → ℚ) (hd : ∀ f j, (d f j:ℝ)=dist f (loc j))
    (W : Finset X) (j : D) : (nearest d W j:ℝ)=nearestDistance (loc j) W := by
  classical
  unfold nearest nearestDistance
  split_ifs with h
  · obtain ⟨f,hf,he⟩ := Finset.exists_mem_eq_inf' h (fun f => d f j)
    have hmin : ∀ g ∈ W, d f j ≤ d g j := by
      intro g hg
      rw [←he]
      exact Finset.inf'_le _ hg
    apply le_antisymm
    · apply Finset.le_inf' h
      intro g hg
      rw [he,hd,dist_comm]
      have hh : (d f j:ℝ) ≤ (d g j:ℝ) := Rat.cast_le.mpr (hmin g hg)
      simpa only [hd,dist_comm] using hh
    · rw [he,hd,dist_comm]
      exact Finset.inf'_le _ hf
  · simp

omit [DecidableEq X] in
lemma payment_eval (loc : D → X) (d : X → D → ℚ) (hd : ∀ f j, (d f j:ℝ)=dist f (loc j))
    (F W : Finset X) (v z : ℚ) (i : X) (x : Variables D F → ℝ) :
    (paymentForm loc d F W v z i).realEval x =
      linearPayment loc (1-3*(v:ℝ)) (v:ℝ) (z:ℝ) W i (fun j => x (.inl j)) := by
  classical
  unfold paymentForm linearPayment
  rw [Form.realEval_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [Form.realEval_sub,Form.realEval_const,bid_eval]
  · push_cast
    rw [hd]
  · push_cast
    rw [hd]
  · push_cast
    rw [nearest_cast loc d hd,hd]

omit [DecidableEq X] in
lemma dual_eval (loc : D → X) (d : X → D → ℚ) (hd : ∀ f j, (d f j:ℝ)=dist f (loc j))
    (F W : Finset X) (v z : ℚ) (f : F) (a j : D) (x : Variables D F → ℝ) :
    (dualForm loc d F W v z f a j).realEval x =
      dualTerm loc (1-3*(v:ℝ)) (z:ℝ) W f (fun j => x (.inl j)) a j := by
  classical
  unfold dualForm dualTerm
  split_ifs <;> simp only [Form.realEval_sub,Form.realEval_const,bid_eval]
  · rw [hd]
  · push_cast
    rw [hd,hd]
    ring

omit [DecidableEq X] in
lemma system_iff (loc : D → X) (d : X → D → ℚ) (hd : ∀ f j, (d f j:ℝ)=dist f (loc j))
    (F W : Finset X) (v z lam eta : ℚ) (i : X) (x : Variables D F → ℝ) :
    (∀ k, (system loc d F W v z lam eta i k).realEval x ≤ 0) ↔
      Feasible loc F W (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i
        (fun j => x (.inl j)) (fun f a j => x (.inr (f,a,j))) := by
  classical
  have hcap (j : D) (f : X) : (((1-3*v)*d f j:ℚ):ℝ)=(1-3*(v:ℝ))*dist f (loc j) := by push_cast; rw [hd]
  have hphase : (((1+v^2)*z:ℚ):ℝ)=(1+(v:ℝ)^2)*(z:ℝ) := by push_cast; rfl
  have hpay : ((lam-(Fintype.card D:ℚ)*eta:ℚ):ℝ)=(lam:ℝ)-(Fintype.card D:ℝ)*(eta:ℝ) := by push_cast; rfl
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro j hj
      have hl := h (.lower j)
      have hu := h (.upper j)
      simp only [system,ite_eq_left hj,Form.realEval_sub,Form.realEval_const,bid_eval,hphase] at hl hu
      refine ⟨by linarith,by linarith,?_,?_⟩
      · intro f hf
        have hh := h (.cap j ⟨f,hf⟩)
        simp only [system,ite_eq_left hj,Form.realEval_sub,Form.realEval_const,bid_eval,hcap] at hh
        rw [dist_comm] at hh
        linarith
      · intro hf
        have hh := h (.far j)
        have ha : activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j ∧ (v:ℝ)*(z:ℝ)<dist i (loc j) := ⟨hj,hf⟩
        simp only [system,ite_eq_left ha,Form.realEval_sub,Form.realEval_const,bid_eval] at hh
        linarith
    · have hh := h .payment
      simp only [system,Form.realEval_sub,Form.realEval_const,payment_eval loc d hd,hpay] at hh
      linarith
    · intro f a ha
      refine ⟨?_,?_⟩
      · intro j
        have hl := h (.slackZero f a j)
        have ht := h (.slackTerm f a j)
        simp only [system,ite_eq_left ha,Form.realEval_sub,Form.realEval_const,slack_eval,Rat.cast_zero,zero_sub,
          dual_eval loc d hd] at hl ht
        constructor <;> linarith
      · have hh := h (.dual f a)
        simp only [system,ite_eq_left ha,Form.realEval_sub,Form.realEval_const,Form.realEval_sum,slack_eval] at hh
        linarith
  · rintro ⟨hb,hp,hdrow⟩ k
    cases k with
    | lower j =>
      by_cases ha : activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j
      · simpa only [system,ite_eq_left ha,Form.realEval_sub,Form.realEval_const,bid_eval,sub_nonpos] using (hb j ha).1
      · simp only [system,ite_eq_right ha,Form.realEval_const,Rat.cast_zero,le_refl]
    | upper j =>
      by_cases ha : activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j
      · simpa only [system,ite_eq_left ha,Form.realEval_sub,Form.realEval_const,bid_eval,hphase,sub_nonpos] using (hb j ha).2.1
      · simp only [system,ite_eq_right ha,Form.realEval_const,Rat.cast_zero,le_refl]
    | cap j f =>
      by_cases ha : activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j
      · simpa only [system,ite_eq_left ha,Form.realEval_sub,Form.realEval_const,bid_eval,hcap,sub_nonpos,dist_comm] using (hb j ha).2.2.1 f f.property
      · simp only [system,ite_eq_right ha,Form.realEval_const,Rat.cast_zero,le_refl]
    | far j =>
      by_cases ha : activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j ∧ (v:ℝ)*(z:ℝ)<dist i (loc j)
      · simp only [system,ite_eq_left ha,Form.realEval_sub,Form.realEval_const,bid_eval,(hb j ha.1).2.2.2 ha.2,sub_self,le_refl]
      · simp only [system,ite_eq_right ha,Form.realEval_const,Rat.cast_zero,le_refl]
    | payment => simpa only [system,Form.realEval_sub,Form.realEval_const,payment_eval loc d hd,hpay,sub_nonpos] using hp
    | slackZero f a j =>
      by_cases ha : activeAt loc (1-3*(v:ℝ)) (z:ℝ) W a
      · simpa only [system,ite_eq_left ha,Form.realEval_sub,Form.realEval_const,slack_eval,Rat.cast_zero,sub_nonpos] using (hdrow f a ha).1 j |>.1
      · simp only [system,ite_eq_right ha,Form.realEval_const,Rat.cast_zero,le_refl]
    | slackTerm f a j =>
      by_cases ha : activeAt loc (1-3*(v:ℝ)) (z:ℝ) W a
      · simpa only [system,ite_eq_left ha,Form.realEval_sub,slack_eval,dual_eval loc d hd,sub_nonpos] using (hdrow f a ha).1 j |>.2
      · simp only [system,ite_eq_right ha,Form.realEval_const,Rat.cast_zero,le_refl]
    | dual f a =>
      by_cases ha : activeAt loc (1-3*(v:ℝ)) (z:ℝ) W a
      · simpa only [system,ite_eq_left ha,Form.realEval_sub,Form.realEval_const,Form.realEval_sum,slack_eval,sub_nonpos] using (hdrow f a ha).2
      · simp only [system,ite_eq_right ha,Form.realEval_const,Rat.cast_zero,le_refl]

end MetricKMedianRecovery.RationalOpenability

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_EnumeratedRow
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility
variable {V R : Type*} [Fintype V] {n : ℕ}

lemma Form.enumeratedRow_realHolds (e : Fin n ≃ V) (f : Form V) (x : V → ℝ) :
    (f.enumeratedRow e).RealHolds (fun i => x (e i)) ↔ f.realEval x ≤ 0 := by
  unfold Row.RealHolds Row.realValue Form.enumeratedRow Form.realEval
  rw [e.sum_comp (fun v => (f.coeff v:ℝ)*x v),Rat.cast_neg]
  constructor <;> intro h <;> linarith

end MetricKMedianRecovery.RationalLinearFeasibility

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalLinearFeasibility RationalOpenability OpenabilityLinearization
variable {D X : Type*} [Fintype D] [DecidableEq D] [DecidableEq X]

omit [Fintype D] [DecidableEq D] [DecidableEq X] in
lemma active_iff [PseudoMetricSpace X] (loc : D → X) (d : X → D → ℚ)
    (hd : ∀ f j, (d f j:ℝ)=dist f (loc j)) (v z : ℚ) (W : Finset X) (j : D) :
    active d v z W j ↔ activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j := by
  have hh (f : X) : (((1-3*v)*d f j:ℚ):ℝ)=(1-3*(v:ℝ))*dist (loc j) f := by
    push_cast
    rw [hd,dist_comm]
  simp only [active,activeAt,←hh,Rat.cast_lt]

omit [Fintype D] in
lemma bid_eq (F : Type*) [DecidableEq F] (j : D) : bid F j=RationalOpenability.bid F j := by
  unfold bid RationalOpenability.bid
  exact congrArg (fun de : DecidableEq (Variables D F) => @Form.coord (Variables D F) de (.inl j))
    (Subsingleton.elim _ _)
omit [Fintype D] in
lemma slack_eq (F : Type*) [DecidableEq F] (f : F) (a j : D) : slack F f a j=RationalOpenability.slack f a j := by
  unfold slack RationalOpenability.slack
  exact congrArg (fun de : DecidableEq (Variables D F) => @Form.coord (Variables D F) de (.inr (f,a,j)))
    (Subsingleton.elim _ _)

lemma forms_eq [PseudoMetricSpace X] (loc : D → X) (d : X → D → ℚ)
    (hd : ∀ f j, (d f j:ℝ)=dist f (loc j)) (F W : Finset X) (v z lam eta : ℚ) (i : X) :
    forms d F W v z lam eta i=system loc d F W v z lam eta i := by
  classical
  have ha (j : D) := active_iff loc d hd v z W j
  have hn (j : D) : d i j ≤ v*z ↔ dist i (loc j) ≤ (v:ℝ)*(z:ℝ) := by
    rw [←hd,←Rat.cast_mul]
    exact Rat.cast_le.symm
  have hf (j : D) : v*z<d i j ↔ (v:ℝ)*(z:ℝ)<dist i (loc j) := by
    rw [←hd,←Rat.cast_mul]
    exact Rat.cast_lt.symm
  have hp : payment d F W v z i=paymentForm loc d F W v z i := by
    simp only [payment,paymentForm,ha,hn,bid_eq]
  have hdu (f : F) (a j : D) : dual d F W v z f a j=dualForm loc d F W v z f a j := by
    simp only [dual,dualForm,ha,bid_eq]
  funext k
  cases k <;> simp only [forms,system,ha,hf,hp,hdu,bid_eq,slack_eq]

end MetricKMedianRecovery.EffectiveOpenability

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FacePoint
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

theorem exactSolve_complete {n : ℕ} (rows : List (Row n)) (B : ℕ)
    (hfeas : ∃ x : Fin n → ℝ, (∀ q∈rows,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
    ∃ x, exactSolve rows B=some x := by
  exact ⟨facePoint rows B,ite_eq_left ((boundedRationalDecide_correct_s238r rows B).mpr hfeas)⟩

end MetricKMedianRecovery.Ellipsoid

namespace MetricKMedianRecovery.OpenabilityLinearization
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X]

theorem normalize_bounded (loc : D → X) (F W : Finset X) (v z lam eta : ℝ) (i : X)
    (hz : 0 ≤ z) (tau : D → ℝ) (y : F → D → D → ℝ)
    (h : Feasible loc F W v z lam eta i tau y) :
    ∃ tau' : D → ℝ, ∃ y' : F → D → D → ℝ,
      Feasible loc F W v z lam eta i tau' y' ∧
      (∀ j, 0 ≤ tau' j ∧ tau' j ≤ (1+v^2)*z) ∧
      (∀ f a j, 0 ≤ y' f a j ∧ y' f a j ≤ (1+v^2)*z) := by
  classical
  let tau' : D → ℝ := fun j => if activeAt loc (1-3*v) z W j then tau j else 0
  let y' : F → D → D → ℝ := fun f a j => if activeAt loc (1-3*v) z W a then
    max (dualTerm loc (1-3*v) z W f tau' a j) 0 else 0
  have hK : 0 ≤ (1+v^2)*z := mul_nonneg (by positivity) hz
  have hbid : admissibleBids loc (1-3*v) (1+v^2) v z W i tau' := by
    intro j hj
    simpa only [tau',ite_eq_left hj] using h.1 j hj
  have ht : ∀ j, 0 ≤ tau' j ∧ tau' j ≤ (1+v^2)*z := by
    intro j
    by_cases ha : activeAt loc (1-3*v) z W j
    · simp only [tau',ite_eq_left ha]
      exact ⟨hz.trans (h.1 j ha).1,(h.1 j ha).2.1⟩
    · simp only [tau',ite_eq_right ha]
      exact ⟨le_rfl,hK⟩
  have hp : linearPayment loc (1-3*v) v z W i tau' = linearPayment loc (1-3*v) v z W i tau := by
    unfold linearPayment
    apply Finset.sum_congr rfl
    intro j _
    by_cases ha : activeAt loc (1-3*v) z W j
    · simp only [ite_eq_left ha,tau']
    · simp only [ite_eq_right ha]
  have hd : ∀ f : F, ∀ a, activeAt loc (1-3*v) z W a → ∀ j,
      dualTerm loc (1-3*v) z W f tau' a j = dualTerm loc (1-3*v) z W f tau a j := by
    intro f a ha j
    unfold dualTerm
    by_cases hj : activeAt loc (1-3*v) z W j
    · simp only [ite_eq_left hj,tau']
    · simp only [ite_eq_right hj,tau']
      rw [ite_eq_left ha]
  refine ⟨tau',y',⟨hbid,?_,?_⟩,ht,?_⟩
  · rw [hp]
    exact h.2.1
  · intro f a ha
    refine ⟨?_,?_⟩
    · intro j
      simp only [y',ite_eq_left ha]
      exact ⟨le_max_right _ _,le_max_left _ _⟩
    · calc
        ∑ j, y' f a j ≤ ∑ j, y f a j := by
          apply Finset.sum_le_sum
          intro j _
          simp only [y',ite_eq_left ha,hd f a ha]
          exact max_le ((h.2.2 f a ha).1 j).2 ((h.2.2 f a ha).1 j).1
        _ ≤ lam := (h.2.2 f a ha).2
  · intro f a j
    by_cases ha : activeAt loc (1-3*v) z W a
    · simp only [y',ite_eq_left ha]
      refine ⟨le_max_right _ _,max_le ?_ hK⟩
      unfold dualTerm
      split_ifs with hj
      · exact (sub_le_self _ dist_nonneg).trans (ht j).2
      · have hh := (ht a).2
        have h1 : 0 ≤ dist (f:X) (loc j) := dist_nonneg
        have h2 : 0 ≤ dist (f:X) (loc a) := dist_nonneg
        linarith
    · simp only [y',ite_eq_right ha]
      exact ⟨le_rfl,hK⟩

theorem openable_iff_bounded (loc : D → X) (F W : Finset X) (v z lam eta : ℝ) (i : X)
    (hv : 0<v) (hv1 : v<1/6) (hz : 0≤z) :
    etaOpenable loc F W (1-3*v) (1+v^2) v z lam eta i ↔
      ∃ tau : D → ℝ, ∃ y : F → D → D → ℝ,
        Feasible loc F W v z lam eta i tau y ∧
        (∀ j, 0 ≤ tau j ∧ tau j ≤ (1+v^2)*z) ∧
        (∀ f a j, 0 ≤ y f a j ∧ y f a j ≤ (1+v^2)*z) := by
  rw [openable_iff_linear_feasible loc F W v z lam eta i hv hv1 hz]
  constructor
  · rintro ⟨tau,y,h⟩
    exact normalize_bounded loc F W v z lam eta i hz tau y h
  · rintro ⟨tau,y,h,_,_⟩
    exact ⟨tau,y,h⟩

end MetricKMedianRecovery.OpenabilityLinearization

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid.Stored
open Matrix RationalLinearFeasibility
open scoped BigOperators

theorem exactSolve_complete {n : ℕ} (rows : List (Row n)) (B : ℕ)
    (hfeas : ∃ x : Fin n → ℝ, (∀ q∈rows,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
    ∃ x, exactSolve rows B=some x := by
  simpa only [exactSolve_eq_s238r] using Ellipsoid.exactSolve_complete rows B hfeas

end MetricKMedianRecovery.Ellipsoid.Stored

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_StoredForms
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility
open scoped BigOperators
variable {V R : Type*} [Fintype V] {n : ℕ}

lemma storedForms_complete (e : Fin n ≃ V) (rows : List R) (f : R → Form V) (B : ℕ)
    (x : V → ℝ) (hx : ∀ r∈rows,(f r).realEval x≤0) (hb : ∀ j,|x j|≤(B:ℝ)) :
    ∃ y,storedForms e rows f B=some y := by
  have hh : ∀ q∈rows.map (fun r => (f r).enumeratedRow e),q.RealHolds (fun i => x (e i)) := by
    intro q hq
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
    exact ((f r).enumeratedRow_realHolds e x).mpr (hx r hr)
  obtain ⟨y,hy⟩ := Ellipsoid.Stored.exactSolve_complete _ B ⟨fun i => x (e i),hh,fun i => hb (e i)⟩
  exact ⟨fun v => y (e.symm v),by simp only [storedForms,hy,Option.map_some]⟩

end MetricKMedianRecovery.RationalLinearFeasibility

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalLinearFeasibility RationalOpenability OpenabilityLinearization

lemma storedOpening_complete_s238r_oai {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ))
    (h : etaOpenable loc F W (1-3*(v:ℝ)) (1+(v:ℝ)^2) (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i) :
    ∃ x,storedOpening distance F W v z lam eta i=some x := by
  obtain ⟨tau,y,hf,ht,hy⟩ := (openable_iff_bounded loc F W (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i hv hv1 hz).mp h
  let x : Variables (Fin d) F → ℝ := Sum.elim tau (fun p => y p.1 p.2.1 p.2.2)
  have hx : ∀ k,(forms distance F W v z lam eta i k).realEval x≤0 := by
    rw [forms_eq loc distance hd]
    exact (system_iff loc distance hd F W v z lam eta i x).mpr hf
  have hb : ∀ j,|x j|≤(⌈(1+v^2)*z⌉₊:ℝ) := by
    intro j
    have hh : 0≤x j ∧ x j≤(1+(v:ℝ)^2)*(z:ℝ) := by
      cases j with
      | inl j => exact ht j
      | inr p => exact hy p.1 p.2.1 p.2.2
    rw [abs_of_nonneg hh.1]
    apply hh.2.trans
    have hb := Nat.le_ceil ((1+v^2)*z)
    exact_mod_cast hb
  exact storedForms_complete _ _ _ _ x (fun k _ => hx k) hb

end MetricKMedianRecovery.EffectiveOpenability

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.EffectiveOpenability.storedOpening_complete_s238r_oai := @OAI.MetricKMedianRecovery.EffectiveOpenability.storedOpening_complete_s238r_oai
