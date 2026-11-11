-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.RationalPhase.complete_spec_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:33:05.600611+00:00
-- url     : https://prove2.me/submissions/459565b8-88a5-44b7-8f73-9a84c7430109

import Mathlib
import Definitions.Def_Q238K022
import Theorems.Thm_OAI_MetricKMedianRecovery_RationalLinearFeasibility_storedForms_sound_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_RationalPhase_first_none_maximal_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Form
attribute [-simp] _root_.OAI.MetricKMedianRecovery.RationalOpenability.bid_eval _root_.OAI.MetricKMedianRecovery.RationalOpenability.slack_eval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility

namespace Form
variable {V I : Type*} [Fintype V]

lemma realEval_cast (f : Form V) (x : V → ℚ) : f.realEval (fun v => (x v:ℝ)) = (f.eval x:ℝ) := by
  simp [realEval,eval]

end Form

end MetricKMedianRecovery.RationalLinearFeasibility

end OAI
end

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CountedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

namespace OrdinaryProducer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

namespace PlainOpening
variable {loc : D → X} {F : Finset X} {v lam : ℝ} {s e : ExecutionState D X}
lemma remaining_drop (h : PlainOpening loc F v lam s e) :
    (F \ e.opened).card + 1 = (F \ s.opened).card := by
  obtain ⟨i,hi,hin,tau,_,_,_,rfl⟩ := h
  change (F \ insert i s.opened).card + 1 = _
  rw [Finset.sdiff_insert,Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨hi,hin⟩)]
  have hp := Finset.card_pos.mpr ⟨i,Finset.mem_sdiff.mpr ⟨hi,hin⟩⟩
  omega
end PlainOpening

end OrdinaryProducer
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_EnumeratedRow
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_KindRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.EffectiveOpenability

section
open RationalOpenability
variable {D W F : Type*}

lemma mem_kindRows (ds : List D) (ws : List W) (fs : List F)
    (hd : ∀ j, j∈ds) (hw : ∀ f, f∈ws) (hf : ∀ f, f∈fs) (k : Kind D W F) :
    k ∈ kindRows ds ws fs := by
  cases k <;> simp [kindRows,List.mem_append,List.mem_map,List.mem_flatMap,hd,hw,hf]

lemma mem_subtypeList {m : ℕ} (F : Finset (Fin m)) (f : F) : f∈subtypeList F := by
  exact List.mem_ofFn.mpr ⟨(F.orderIsoOfFin rfl).symm f,by simp⟩

end

open RationalOpenability OpenabilityLinearization

end MetricKMedianRecovery.EffectiveOpenability

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

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalLinearFeasibility RationalOpenability OpenabilityLinearization

lemma storedOpening_witness {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
    (x : Variables (Fin d) F → ℚ) (hx : storedOpening distance F W v z lam eta i=some x) :
    Feasible loc F W (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i
      (fun j => (x (.inl j):ℝ)) (fun f a j => (x (.inr (f,a,j)):ℝ)) := by
  have hs := (storedForms_sound_s238 _ _ _ _ x hx).1
  apply (system_iff loc distance hd F W v z lam eta i (fun j => (x j:ℝ))).mp
  intro k
  rw [←forms_eq loc distance hd,Form.realEval_cast]
  exact_mod_cast hs k (mem_kindRows _ _ _ (by simp) (mem_subtypeList W) (mem_subtypeList F) k)

end MetricKMedianRecovery.EffectiveOpenability

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability OrdinaryProducer OpenabilityLinearization

lemma update_get {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v : ℚ)
    (s : State m d) (e : Event m d) (j : Fin d) :
    (update distance v s e).budget[j] =
      if active distance v s.phase s.opened j then e.bid[j] else s.budget[j] := by
  simp only [update,Fin.getElem_fin,Vector.getElem_ofFn]

lemma update_real {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (v : ℚ) (s : State m d) (e : Event m d) :
    (update distance v s e).real=regularUpdate loc (1-3*(v:ℝ)) s.real e.facility s.opened
      (fun j => (e.bid[j]:ℝ)) := by
  classical
  change ExecutionState.mk (insert e.facility s.opened) (s.phase:ℝ)
      (fun j => (((update distance v s e).budget[j]:ℚ):ℝ)) =
    ExecutionState.mk (insert e.facility s.opened) (s.phase:ℝ)
      (fun j => if activeAt loc (1-3*(v:ℝ)) (s.phase:ℝ) s.opened j then
        if activeAt loc (1-3*(v:ℝ)) (s.phase:ℝ) s.opened j then (e.bid[j]:ℝ) else (s.phase:ℝ)
        else (s.budget[j]:ℝ))
  congr 1
  funext j
  rw [update_get]
  by_cases hj : active distance v s.phase s.opened j
  · simp only [ite_eq_left hj, ite_eq_left ((active_iff loc distance hd v s.phase s.opened j).mp hj)]
  · simp only [ite_eq_right hj, ite_eq_right (fun h => hj ((active_iff loc distance hd v s.phase s.opened j).mpr h))]

lemma first_some {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam : ℚ) (todo : List (Fin m)) (e : Event m d)
    (he : first distance F W v z lam todo=some e) :
    e.facility∈F ∧ e.facility∉W ∧ ∃ x,
      storedOpening distance F W v z lam 0 e.facility=some x ∧
      ∀ j : Fin d,e.bid[j]=x (.inl j) := by
  induction todo with
  | nil => cases he
  | cons i todo ih =>
    simp only [first] at he
    split at he
    next hi =>
      cases hx : storedOpening distance F W v z lam 0 i with
      | none => rw [hx] at he; exact ih he
      | some x =>
        rw [hx] at he
        have he' : (⟨i,Vector.ofFn (fun j => x (.inl j))⟩ : Event m d)=e := Option.some.inj he
        subst e
        exact ⟨hi.1,hi.2,x,hx,by intro j; simp⟩
    next hi => exact ih he

lemma first_plain {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F : Finset (Fin m)) (v lam : ℚ) (s : State m d) (todo : List (Fin m)) (e : Event m d)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(s.phase:ℝ))
    (he : first distance F s.opened v s.phase lam todo=some e) :
    PlainOpening loc F (v:ℝ) (lam:ℝ) s.real (update distance v s e).real := by
  obtain ⟨hi,hin,x,hx,he⟩ := first_some distance F s.opened v s.phase lam todo e he
  have hw := storedOpening_witness loc distance hd F s.opened v s.phase lam 0 e.facility x hx
  have htau : (fun j : Fin d => (e.bid[j]:ℝ))=(fun j => (x (.inl j):ℝ)) := by
    funext j
    rw [he j]
  refine ⟨e.facility,hi,hin,(fun j => (e.bid[j]:ℝ)),?_,?_,?_,update_real loc distance hd v s e⟩
  · rw [htau]
    exact hw.1
  · change (lam:ℝ) ≤ openingPayment loc (1-3*(v:ℝ)) (s.phase:ℝ) s.opened e.facility _
    rw [htau,payment_eq_linear loc s.opened (v:ℝ) (s.phase:ℝ) e.facility _ hv hv1 hz hw.1]
    simpa only [Rat.cast_zero,mul_zero,sub_zero] using hw.2.1
  · intro f hf a ha
    rw [htau,dual_eq]
    have hy := hw.2.2 ⟨f,hf⟩ a ha
    exact (Finset.sum_le_sum (fun j _ => max_le (hy.1 j).2 (hy.1 j).1)).trans hy.2

end MetricKMedianRecovery.RationalPhase

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinishSpec
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability OrdinaryProducer

theorem finish_spec {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F : Finset (Fin m)) (v lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6)
    (fuel : ℕ) (s : State m d) (hz : (0:ℝ)≤(s.phase:ℝ))
    (hfuel : (F\s.opened).card≤fuel) :
    let r := finish distance F v lam fuel s
    CountedTrace (PlainOpening loc F (v:ℝ) (lam:ℝ)) r.2.length s.real r.1.real ∧
    (F\r.1.opened).card+r.2.length=(F\s.opened).card ∧
    s.opened ⊆ r.1.opened ∧ r.1.opened ⊆ s.opened∪F ∧
    r.1.phase=s.phase ∧ PhaseMaximal loc F (v:ℝ) (lam:ℝ) r.1.real := by
  induction fuel generalizing s with
  | zero =>
    simp only [finish,List.length_nil,Nat.add_zero]
    refine ⟨.nil _,trivial,Finset.Subset.refl _,Finset.subset_union_left,trivial,?_⟩
    intro i hi hin
    have hh : i∈F\s.opened := Finset.mem_sdiff.mpr ⟨hi,hin⟩
    have hh' := Finset.card_pos.mpr ⟨i,hh⟩
    omega
  | succ fuel ih =>
    cases he : first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m => i)) with
    | none =>
      simp only [finish,he,List.length_nil,Nat.add_zero]
      exact ⟨.nil _,trivial,Finset.Subset.refl _,Finset.subset_union_left,trivial,
        first_none_maximal_s238 loc distance hd F v lam s hv hv1 hz he⟩
    | some e =>
      have hop := first_plain loc distance hd F v lam s _ e hv hv1 hz he
      have hdrop : (F\(update distance v s e).opened).card+1=(F\s.opened).card := hop.remaining_drop
      have hs := first_some distance F s.opened v s.phase lam _ e he
      obtain ⟨htrace,hcount,hlo,hhi,hphase,hmax⟩ :=
        ih (update distance v s e) hz (by omega)
      simp only [finish,he,List.length_cons]
      refine ⟨.cons hop htrace,by omega,?_,?_,hphase,hmax⟩
      · exact (Finset.subset_insert _ _).trans hlo
      · apply hhi.trans
        exact Finset.union_subset (Finset.insert_subset (Finset.mem_union_right _ hs.1)
          Finset.subset_union_left) Finset.subset_union_right

theorem complete_spec_s238_oai {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F : Finset (Fin m)) (v lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6)
    (s : State m d) (hz : (0:ℝ)≤(s.phase:ℝ)) :
    let r := finish distance F v lam F.card s
    CountedTrace (PlainOpening loc F (v:ℝ) (lam:ℝ)) r.2.length s.real r.1.real ∧
    r.2.length≤F.card ∧ (F\r.1.opened).card+r.2.length=(F\s.opened).card ∧
    s.opened ⊆ r.1.opened ∧ r.1.opened ⊆ s.opened∪F ∧
    r.1.phase=s.phase ∧ PhaseMaximal loc F (v:ℝ) (lam:ℝ) r.1.real := by
  have hf := Finset.card_le_card (Finset.sdiff_subset : F\s.opened⊆F)
  obtain ⟨ht,hc,hlo,hhi,hz',hm⟩ := finish_spec loc distance hd F v lam hv hv1 F.card s hz hf
  exact ⟨ht,by omega,hc,hlo,hhi,hz',hm⟩

end MetricKMedianRecovery.RationalPhase

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.RationalPhase.complete_spec_s238_oai := @OAI.MetricKMedianRecovery.RationalPhase.complete_spec_s238_oai
