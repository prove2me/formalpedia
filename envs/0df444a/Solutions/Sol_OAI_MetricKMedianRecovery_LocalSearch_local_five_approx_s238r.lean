-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.LocalSearch.local_five_approx_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:30:35.279404+00:00
-- url     : https://prove2.me/submissions/d666945e-7af6-4464-a620-2aa6ac0588ca

import Mathlib
import Definitions.Def_Q238L010

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ImageClass
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch

variable {B U : Type*} [Fintype B] [Fintype U]

lemma slot_allocation (psi : B → U) (hcard : Fintype.card B ≤ Fintype.card U) :
    ∃ slot : B ↪ U, ∀ b, ∃ c, psi c = psi b ∧ slot c = psi b := by
  classical
  let C : Finset U := Finset.univ.image psi
  have hchoose (u : C) : ∃ b : B, psi b = u.val := by
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp u.property
    exact ⟨b,hb⟩
  let rep : C → B := fun u => Classical.choose (hchoose u)
  have hrep (u : C) : psi (rep u) = u.val := Classical.choose_spec (hchoose u)
  let R : Finset B := Finset.univ.image rep
  have hinj : Set.InjOn psi R := by
    intro b hb c hc hbc
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hc
    have huv : u = v := Subtype.ext (by simpa only [hrep] using hbc)
    exact congrArg rep huv
  have hC : C.card ≤ Fintype.card B := (Finset.card_image_le).trans (by simp)
  obtain ⟨T,hCT,hTU,hT⟩ := Finset.exists_subsuperset_card_eq
    (s := C) (t := Finset.univ) (Finset.subset_univ _) hC (by simpa using hcard)
  have hRT : R.image psi ⊆ T := by
    intro u hu
    exact hCT (Finset.mem_image.mp hu |>.elim (fun b h =>
      Finset.mem_image.mpr ⟨b,Finset.mem_univ b,h.2⟩))
  obtain ⟨e,he⟩ := Finset.exists_equiv_extend_of_card_eq hT.symm hRT hinj
  refine ⟨e.toEmbedding.trans (Function.Embedding.subtype _),?_⟩
  intro b
  let u : C := ⟨psi b,Finset.mem_image.mpr ⟨b,Finset.mem_univ b,rfl⟩⟩
  refine ⟨rep u,hrep u,?_⟩
  change (e (rep u)).val = psi b
  rw [he _ (Finset.mem_image.mpr ⟨u,Finset.mem_univ u,rfl⟩),hrep]

omit [Fintype B] [Fintype U] in

lemma slot_class_preservation (psi : B → U) (slot : B ↪ U)
    (hslot : ∀ b, ∃ c, psi c = psi b ∧ slot c = psi b)
    {b c : B} (h : slot b = psi c) : psi b = psi c := by
  obtain ⟨d,hd,hds⟩ := hslot c
  have hbd : b = d := slot.injective (h.trans hds.symm)
  simpa [hbd] using hd

omit [Fintype U] in
lemma image_mem_class_slots [DecidableEq B] [DecidableEq U] (psi : B → U)
    (slot : B ↪ U) (hslot : ∀ b, ∃ c, psi c = psi b ∧ slot c = psi b) (b : B) :
    psi b ∈ (imageClass psi (psi b)).map slot := by
  obtain ⟨c,hc,hs⟩ := hslot b
  exact Finset.mem_map.mpr ⟨c,by simp [imageClass,hc],hs⟩

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_ExchangeIndex
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {B U : Type*} [Fintype B] [Fintype U] [DecidableEq B] [DecidableEq U]

omit [Fintype U] [DecidableEq B] in
lemma auxiliary_slot_mem (psi : B → U) (slot : B ↪ U) (b : B) (u : U) :
    slot b ∈ auxiliarySlots psi slot u ↔ psi b = u ∧ slot b ≠ u := by
  simp only [auxiliarySlots,Finset.mem_erase,classSlots,Finset.mem_map]
  constructor
  · rintro ⟨hne,c,hc,he⟩
    have hcb : c = b := slot.injective he
    exact ⟨by simpa only [hcb] using (Finset.mem_filter.mp hc).2,hne⟩
  · rintro ⟨hb,hne⟩
    exact ⟨hne,b,by simp [imageClass,hb],rfl⟩

omit [Fintype U] in
lemma auxiliary_card (psi : B → U) (slot : B ↪ U)
    (hslot : ∀ b, ∃ c, psi c = psi b ∧ slot c = psi b) (b : B) :
    (auxiliarySlots psi slot (psi b)).card = (imageClass psi (psi b)).card - 1 := by
  rw [auxiliarySlots,classSlots,Finset.card_erase_of_mem (image_mem_class_slots psi slot hslot b)]
  simp

omit [Fintype U] [DecidableEq B] in
lemma imageClass_pos (psi : B → U) (b : B) : 0 < (imageClass psi (psi b)).card := by
  apply Finset.card_pos.mpr
  exact ⟨b,by simp [imageClass]⟩

omit [Fintype U] [DecidableEq B] in
lemma exchangeWeight_nonneg (psi : B → U) (slot : B ↪ U) (e : ExchangeIndex B U) :
    0 ≤ exchangeWeight psi slot e := by
  cases e with
  | inl u => simp only [exchangeWeight]; split_ifs <;> norm_num
  | inr bs =>
    obtain ⟨b,s⟩ := bs
    simp only [exchangeWeight]
    split_ifs with h
    · have ht : (1:ℝ) < ((imageClass psi (psi b)).card:ℝ) := by exact_mod_cast (by omega : 1 < (imageClass psi (psi b)).card)
      positivity
    · rfl

omit [Fintype U] [DecidableEq B] in
lemma exchange_width (psi : B → U) (slot : B ↪ U) (e : ExchangeIndex B U)
    (he : 0 < exchangeWeight psi slot e) :
    (exchangeRemove psi slot e).card = (exchangeAdd psi e).card ∧
    (exchangeAdd psi e).card ≤ 5 := by
  cases e with
  | inl u =>
    simp only [exchangeWeight] at he
    split_ifs at he with h
    · simp [exchangeRemove,exchangeAdd,classSlots,h.2]
    · norm_num at he
  | inr bs => obtain ⟨b,s⟩ := bs; simp [exchangeRemove,exchangeAdd]

omit [Fintype U] [DecidableEq B] in
lemma exchange_preserves_image (psi : B → U) (slot : B ↪ U)
    (hslot : ∀ b, ∃ c, psi c = psi b ∧ slot c = psi b)
    (e : ExchangeIndex B U) (he : 0 < exchangeWeight psi slot e) (b : B)
    (hb : b ∉ exchangeAdd psi e) : psi b ∉ exchangeRemove psi slot e := by
  cases e with
  | inl u =>
    intro hm
    obtain ⟨c,hc,hcs⟩ := Finset.mem_map.mp hm
    have hp := slot_class_preservation psi slot hslot hcs
    have hcu := (Finset.mem_filter.mp hc).2
    apply hb
    simp [exchangeAdd,imageClass,← hcu,← hp]
  | inr bs =>
    obtain ⟨c,s⟩ := bs
    simp only [exchangeWeight] at he
    split_ifs at he with h
    · intro hm
      have hbs : psi b = s := Finset.mem_singleton.mp hm
      obtain ⟨d,hd,hds⟩ := Finset.mem_map.mp (Finset.mem_of_mem_erase h.2)
      have hdp : psi d = psi b := slot_class_preservation psi slot hslot (hds.trans hbs.symm)
      have hdc : psi d = psi c := (Finset.mem_filter.mp hd).2
      exact (Finset.ne_of_mem_erase h.2) (hbs.symm.trans (hdp.symm.trans hdc))
    · norm_num at he

lemma total_addition_weight (psi : B → U) (slot : B ↪ U)
    (hslot : ∀ b, ∃ c, psi c = psi b ∧ slot c = psi b) (b : B) :
    (∑ e : ExchangeIndex B U, if b ∈ exchangeAdd psi e then exchangeWeight psi slot e else 0) = 1 := by
  classical
  rw [Fintype.sum_sum_type]
  have hsmall : (∑ u : U, if b ∈ exchangeAdd psi (.inl u) then
      exchangeWeight psi slot (.inl u) else 0) =
      if (imageClass psi (psi b)).card ≤ 5 then (1:ℝ) else 0 := by
    simp only [exchangeAdd,imageClass,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ,ite_true, if_true,exchangeWeight]
    simp only [imageClass_pos psi b,true_and]
    rfl
  have hlarge : (∑ bs : B × U, if b ∈ exchangeAdd psi (.inr bs) then
      exchangeWeight psi slot (.inr bs) else 0) =
      if 5 < (imageClass psi (psi b)).card then (1:ℝ) else 0 := by
    rw [Fintype.sum_prod_type]
    simp only [exchangeAdd,Finset.mem_singleton]
    rw [Finset.sum_eq_single b]
    · simp only [ite_true, if_true,exchangeWeight]
      by_cases hb : 5 < (imageClass psi (psi b)).card
      · simp only [hb,true_and,ite_true, if_true]
        rw [← Finset.sum_filter]
        simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul,
          auxiliary_card psi slot hslot b]
        have hc : 1 ≤ (imageClass psi (psi b)).card := by omega
        rw [Nat.cast_sub hc]
        have ht : ((imageClass psi (psi b)).card:ℝ) - 1 ≠ 0 := by
          have ht : (1:ℝ) < ((imageClass psi (psi b)).card:ℝ) := by exact_mod_cast (by omega : 1 < (imageClass psi (psi b)).card)
          linarith
        simpa only [Nat.cast_one] using mul_one_div_cancel ht
      · simp [hb]
    · intros c _ hcb
      simp [Ne.symm hcb]
    · simp
  rw [hsmall,hlarge]
  by_cases hb : (imageClass psi (psi b)).card ≤ 5 <;> simp [hb,not_lt.mpr,lt_of_not_ge]

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ClassSlotsMem
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {B U : Type*} [Fintype B] [Fintype U] [DecidableEq B] [DecidableEq U]

omit [Fintype U] [DecidableEq B] in
lemma classSlots_mem (psi : B → U) (slot : B ↪ U) (b : B) (u : U) :
    slot b ∈ classSlots psi slot u ↔ psi b = u := by
  simp only [classSlots,Finset.mem_map,imageClass,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨c,hc,he⟩
    simpa only [slot.injective he] using hc
  · intro hb; exact ⟨b,hb,rfl⟩

omit [DecidableEq B] in
lemma removal_weight_at_slot (psi : B → U) (slot : B ↪ U) (b : B) :
    (∑ e : ExchangeIndex B U,
      if slot b ∈ exchangeRemove psi slot e then exchangeWeight psi slot e else 0) =
    (if (imageClass psi (psi b)).card ≤ 5 then (1:ℝ) else 0) +
    (if 5 < (imageClass psi (psi b)).card ∧ slot b ≠ psi b
      then ((imageClass psi (psi b)).card:ℝ)/((imageClass psi (psi b)).card-1) else 0) := by
  classical
  rw [Fintype.sum_sum_type]
  congr 1
  · simp only [exchangeRemove,classSlots_mem]
    rw [Finset.sum_ite_eq]
    simp [exchangeWeight,imageClass_pos psi b]
  · rw [Fintype.sum_prod_type]
    simp only [exchangeRemove,Finset.mem_singleton]
    simp_rw [Finset.sum_ite_eq,Finset.mem_univ,ite_true,exchangeWeight,auxiliary_slot_mem]
    have he (c : B) :
        (if 5 < (imageClass psi (psi c)).card ∧ psi b = psi c ∧ slot b ≠ psi c
          then 1 / ((imageClass psi (psi c)).card - (1:ℝ)) else 0) =
        (if psi c = psi b then
          (if 5 < (imageClass psi (psi b)).card ∧ slot b ≠ psi b
            then 1/((imageClass psi (psi b)).card-(1:ℝ)) else 0) else 0) := by
      by_cases hc : psi c = psi b
      · simp [hc]
      · simp [hc,Ne.symm hc]
    rw [Finset.sum_congr rfl (fun c _ => he c),← Finset.sum_filter]
    change (∑ _c ∈ imageClass psi (psi b),
      if 5 < (imageClass psi (psi b)).card ∧ slot b ≠ psi b
      then 1/((imageClass psi (psi b)).card-(1:ℝ)) else 0) = _
    rw [Finset.sum_const,nsmul_eq_mul]
    split_ifs <;> simp [div_eq_mul_inv]

omit [DecidableEq B] in
lemma removal_weight_le (psi : B → U) (slot : B ↪ U) (s : U) :
    (∑ e : ExchangeIndex B U,
      if s ∈ exchangeRemove psi slot e then exchangeWeight psi slot e else 0) ≤ (6/5:ℝ) := by
  classical
  by_cases hs : ∃ b, slot b = s
  · obtain ⟨b,rfl⟩ := hs
    rw [removal_weight_at_slot]
    by_cases ht : (imageClass psi (psi b)).card ≤ 5
    · simp only [ht,ite_true, if_true,not_lt.mpr ht,false_and,ite_false, if_false,add_zero]
      norm_num
    · have ht5 : 5 < (imageClass psi (psi b)).card := lt_of_not_ge ht
      simp only [ht,ite_false, if_false,zero_add,ht5,true_and]
      split_ifs
      · have ht6 : (6:ℝ) ≤ (imageClass psi (psi b)).card := by exact_mod_cast ht5
        have hpos : (0:ℝ) < (imageClass psi (psi b)).card-1 := by linarith
        apply (div_le_iff₀ hpos).mpr
        linarith
      · norm_num
  · have hz : (∑ e : ExchangeIndex B U,
        if s ∈ exchangeRemove psi slot e then exchangeWeight psi slot e else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      cases e with
      | inl u =>
        have hm : s ∉ classSlots psi slot u := by
          intro hm
          obtain ⟨b,_,hb⟩ := Finset.mem_map.mp hm
          exact hs ⟨b,hb⟩
        simp only [exchangeRemove,hm,ite_false, if_false]
      | inr bs =>
        obtain ⟨b,t⟩ := bs
        by_cases hst : s = t
        · subst t
          have hm : s ∉ auxiliarySlots psi slot (psi b) := by
            intro hm
            obtain ⟨c,_,hc⟩ := Finset.mem_map.mp (Finset.mem_of_mem_erase hm)
            exact hs ⟨c,hc⟩
          simp [exchangeRemove,exchangeWeight,hm]
        · simp [exchangeRemove,hst]
    rw [hz]
    norm_num

end MetricKMedianRecovery.LocalSearch

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

lemma connection_mono {S T : Finset V} (hS : S.Nonempty) (hST : S ⊆ T) (p : V) :
    connection T p ≤ connection S p := by
  simp only [connection,dite_eq_left hS,dite_eq_left (hS.mono hST)]
  exact Finset.le_inf' hS _ (fun _ hs => Finset.inf'_le _ (hST hs))
lemma cost_mono (D : Finset V) {S T : Finset V} (hS : S.Nonempty) (hST : S ⊆ T) :
    cost D T ≤ cost D S := Finset.sum_le_sum (fun p _ => connection_mono hS hST p)

variable [DecidableEq V]

lemma padded_not_worse (F D S T : Finset V) (hSF : S ⊆ F) (hTF : T ⊆ F)
    (hT : T.Nonempty) (hts : T.card ≤ S.card) :
    ∃ U ⊆ F, U.card = S.card ∧ T ⊆ U ∧ S \ U ⊆ S \ T ∧ U \ S ⊆ T \ S ∧
      cost D U ≤ cost D T := by
  obtain ⟨U,hTU,hU,hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_union_left : T ⊆ T ∪ S) hts
    (Finset.card_le_card (Finset.subset_union_right : S ⊆ T ∪ S))
  refine ⟨U,hU.trans (Finset.union_subset hTF hSF),hcard,hTU,?_,?_,cost_mono D hT hTU⟩
  · intro x hx
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
      fun hxt => (Finset.mem_sdiff.mp hx).2 (hTU hxt)⟩
  · intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxu,hxs⟩
    rcases Finset.mem_union.mp (hU hxu) with hxt | hxs'
    · exact Finset.mem_sdiff.mpr ⟨hxt,hxs⟩
    · exact (hxs hxs').elim

lemma local_min_le_smaller (F D S : Finset V) (w : ℕ) (hSF : S ⊆ F)
    (hlocal : WidthLocalMin F D S w) (T : Finset V) (hTF : T ⊆ F)
    (hT : T.Nonempty) (hcard : T.card ≤ S.card)
    (hremove : (S \ T).card ≤ w) (hadd : (T \ S).card ≤ w) : cost D S ≤ cost D T := by
  obtain ⟨U,hUF,hUS,_,hrem,hnew,hcost⟩ := padded_not_worse F D S T hSF hTF hT hcard
  exact (hlocal U hUF hUS ((Finset.card_le_card hrem).trans hremove)
    ((Finset.card_le_card hnew).trans hadd)).trans hcost

omit [PseudoMetricSpace V] in
lemma exchange_card_le (S R A : Finset V) (hRS : R ⊆ S) (hAR : A.card ≤ R.card) :
    ((S \ R) ∪ A).card ≤ S.card := by
  have hh := Finset.card_sdiff_add_card_eq_card hRS
  exact (Finset.card_union_le _ _).trans (by omega)
omit [PseudoMetricSpace V] in
lemma exchange_diff_bounds (S R A : Finset V) :
    S \ ((S \ R) ∪ A) ⊆ R ∧ ((S \ R) ∪ A) \ S ⊆ A := by
  constructor
  · intro x hx
    by_contra hn
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,hn⟩))
  · intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxu,hxs⟩
    rcases Finset.mem_union.mp hxu with hx | hx
    · exact (hxs (Finset.mem_sdiff.mp hx).1).elim
    · exact hx
lemma local_exchange (F D S : Finset V) (w : ℕ) (hSF : S ⊆ F)
    (hlocal : WidthLocalMin F D S w) (R A : Finset V)
    (hRS : R ⊆ S) (hAF : A ⊆ F) (hA : A.Nonempty)
    (hcard : A.card ≤ R.card) (hR : R.card ≤ w) (ha : A.card ≤ w) :
    cost D S ≤ cost D ((S \ R) ∪ A) := by
  have hd := exchange_diff_bounds S R A
  exact local_min_le_smaller F D S w hSF hlocal _
    (Finset.union_subset (Finset.sdiff_subset.trans hSF) hAF)
    (hA.mono Finset.subset_union_right) (exchange_card_le S R A hRS hcard)
    ((Finset.card_le_card hd.1).trans hR) ((Finset.card_le_card hd.2).trans ha)

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BadClientWeighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch

lemma bad_client_weighted {E : Type*} [Fintype E]
    (weight : E → ℝ) (add remove : E → Prop) [DecidablePred add] [DecidablePred remove] (change : E → ℝ)
    (hw : ∀ e, 0 ≤ weight e) (P S u : ℝ) (hP : 0 ≤ P)
    (hadd : (∑ e, if add e then weight e else 0) = 1)
    (hremove : (∑ e, if remove e then weight e else 0) ≤ u)
    (hchange : ∀ e, 0 < weight e → change e ≤
      (if add e then P-S else 0) + (if remove e then 2*P else 0)) :
    (∑ e, weight e * change e) ≤ (1+2*u)*P-S := by
  classical
  have hle : (∑ e, weight e*change e) ≤
      ∑ e, weight e*((if add e then P-S else 0)+(if remove e then 2*P else 0)) := by
    apply Finset.sum_le_sum
    intro e _
    rcases (hw e).eq_or_lt with he | he
    · simp only [← he,zero_mul,le_refl]
    · exact mul_le_mul_of_nonneg_left (hchange e he) (hw e)
  have he : (∑ e, weight e*((if add e then P-S else 0)+(if remove e then 2*P else 0))) =
      (∑ e, if add e then weight e else 0)*(P-S) +
      (∑ e, if remove e then weight e else 0)*(2*P) := by
    simp_rw [mul_add,Finset.sum_add_distrib,Finset.sum_mul]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro e _ <;> split_ifs <;> ring
  rw [he,hadd,one_mul] at hle
  have hh := mul_le_mul_of_nonneg_right hremove (by positivity : 0 ≤ 2*P)
  linarith

lemma good_client_weighted {E : Type*} [Fintype E]
    (weight : E → ℝ) (remove : E → Prop) [DecidablePred remove] (change : E → ℝ)
    (hw : ∀ e, 0 ≤ weight e) (P S u : ℝ) (hPS : S ≤ P)
    (hremove : (∑ e, if remove e then weight e else 0) ≤ u)
    (hchange : ∀ e, 0 < weight e → change e ≤ (if remove e then P-S else 0)) :
    (∑ e, weight e * change e) ≤ u*(P-S) := by
  classical
  calc
    (∑ e, weight e * change e) ≤ ∑ e, weight e*(if remove e then P-S else 0) := by
      apply Finset.sum_le_sum
      intro e _
      rcases (hw e).eq_or_lt with he | he
      · simp only [← he,zero_mul,le_refl]
      · exact mul_le_mul_of_nonneg_left (hchange e he) (hw e)
    _ = (∑ e, if remove e then weight e else 0)*(P-S) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> ring
    _ ≤ u*(P-S) := mul_le_mul_of_nonneg_right hremove (sub_nonneg.mpr hPS)

end MetricKMedianRecovery.LocalSearch
namespace MetricKMedianRecovery.LocalSearch
variable {V E : Type*} [PseudoMetricSpace V] [DecidableEq V] [Fintype E]

lemma bad_routing_change (S R A : Finset V) (hS : S.Nonempty) (p i : V)
    (hpreserve : i ∉ A → nearest S hS i ∉ R) :
    connection ((S \ R) ∪ A) p - connection S p ≤
      (if i ∈ A then dist p i - connection S p else 0) +
      (if nearest S hS p ∈ R then 2*dist p i else 0) := by
  by_cases hi : i ∈ A
  · have hc := connection_le (p := p) (Finset.mem_union_right (S \ R) hi)
    simp only [hi,ite_true, if_true]
    split_ifs <;> nlinarith [dist_nonneg (x := p) (y := i)]
  · simp only [hi,ite_false, if_false,zero_add]
    by_cases hp : nearest S hS p ∈ R
    · simp only [hp,ite_true, if_true]
      have hmem : nearest S hS i ∈ (S \ R) ∪ A := Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨nearest_mem S hS i,hpreserve hi⟩)
      have hc := connection_le (p := p) hmem
      have hnear : dist i (nearest S hS i) ≤ dist i (nearest S hS p) := by
        rw [nearest_distance]
        exact connection_le (nearest_mem S hS p)
      have ht1 := dist_triangle p i (nearest S hS i)
      have ht2 := dist_triangle i p (nearest S hS p)
      rw [dist_comm i p,nearest_distance] at ht2
      linarith
    · simp only [hp,ite_false, if_false]
      have hc := connection_le (p := p) (Finset.mem_union_left A
        (Finset.mem_sdiff.mpr ⟨nearest_mem S hS p,hp⟩))
      rw [nearest_distance] at hc
      linarith

lemma good_routing_change (S R A : Finset V) (hS : S.Nonempty) (p proxy : V)
    (hproxy : proxy ∈ S) (hkeep : proxy ∉ R) :
    connection ((S \ R) ∪ A) p - connection S p ≤
      (if nearest S hS p ∈ R then dist p proxy - connection S p else 0) := by
  by_cases hp : nearest S hS p ∈ R
  · simp only [hp,ite_true, if_true]
    exact sub_le_sub_right (connection_le (p := p) (Finset.mem_union_left A
      (Finset.mem_sdiff.mpr ⟨hproxy,hkeep⟩))) _
  · simp only [hp,ite_false, if_false]
    have hc := connection_le (p := p) (Finset.mem_union_left A
      (Finset.mem_sdiff.mpr ⟨nearest_mem S hS p,hp⟩))
    rw [nearest_distance] at hc
    linarith

theorem weighted_swap_family (F D S Ob Og : Finset V) (hS : S.Nonempty) (hSF : S ⊆ F)
    (hlocal : WidthLocalMin F D S 5) (assign proxy : V → V)
    (hassign : ∀ p ∈ D, assign p ∈ Ob ∨ assign p ∈ Og)
    (hproxy : ∀ i ∈ Og, proxy i ∈ S)
    (R A : E → Finset V) (w : E → ℝ) (u : ℝ)
    (hw : ∀ e, 0 ≤ w e)
    (hwidth : ∀ e, 0 < w e → R e ⊆ S ∧ A e ⊆ F ∧ (A e).Nonempty ∧
      (A e).card ≤ (R e).card ∧ (R e).card ≤ 5 ∧ (A e).card ≤ 5)
    (hadd : ∀ i ∈ Ob, (∑ e, if i ∈ A e then w e else 0) = 1)
    (hremove : ∀ s ∈ S, (∑ e, if s ∈ R e then w e else 0) ≤ u)
    (hkeep : ∀ e, 0 < w e → ∀ i ∈ Og, proxy i ∉ R e)
    (hpreserve : ∀ e, 0 < w e → ∀ i ∈ Ob, i ∉ A e → nearest S hS i ∉ R e) :
    0 ≤ ∑ p ∈ D, if assign p ∈ Ob then (1+2*u)*dist p (assign p)-connection S p
      else u*(dist p (proxy (assign p))-connection S p) := by
  classical
  have hnon : 0 ≤ ∑ e, w e*(cost D ((S \ R e) ∪ A e)-cost D S) := by
    apply Finset.sum_nonneg
    intro e _
    rcases (hw e).eq_or_lt with he | he
    · simp only [← he,zero_mul,le_refl]
    · obtain ⟨hrs,haf,ha,hcard,hr,hac⟩ := hwidth e he
      exact mul_nonneg (hw e) (sub_nonneg.mpr (local_exchange F D S 5 hSF hlocal
        (R e) (A e) hrs haf ha hcard hr hac))
  have hsum : (∑ e, w e*(cost D ((S \ R e) ∪ A e)-cost D S)) =
      ∑ p ∈ D, ∑ e, w e*(connection ((S \ R e) ∪ A e) p-connection S p) := by
    simp only [cost,← Finset.sum_sub_distrib,Finset.mul_sum]
    exact Finset.sum_comm
  rw [hsum] at hnon
  refine hnon.trans (Finset.sum_le_sum (fun p hp => ?_))
  by_cases hb : assign p ∈ Ob
  · simp only [hb,ite_true, if_true]
    exact bad_client_weighted w (fun e => assign p ∈ A e)
      (fun e => nearest S hS p ∈ R e) _ hw (dist p (assign p)) (connection S p) u
      dist_nonneg (hadd _ hb) (hremove _ (nearest_mem S hS p))
      (fun e he => bad_routing_change S (R e) (A e) hS p (assign p)
        (hpreserve e he _ hb))
  · simp only [hb,ite_false, if_false]
    have hg : assign p ∈ Og := (hassign p hp).resolve_left hb
    exact good_client_weighted w (fun e => nearest S hS p ∈ R e) _ hw
      (dist p (proxy (assign p))) (connection S p) u
      (connection_le (hproxy _ hg)) (hremove _ (nearest_mem S hS p))
      (fun e he => good_routing_change S (R e) (A e) hS p _ (hproxy _ hg) (hkeep e he _ hg))

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ExchangeAddNonempty
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch

variable {B U : Type*} [Fintype B] [Fintype U] [DecidableEq U]

omit [Fintype U] in
lemma exchange_add_nonempty (psi : B → U) (slot : B ↪ U) (e : ExchangeIndex B U)
    (he : 0 < exchangeWeight psi slot e) : (exchangeAdd psi e).Nonempty := by
  cases e with
  | inl u =>
    simp only [exchangeWeight] at he
    split_ifs at he with h
    · exact Finset.card_pos.mp h.1
    · norm_num at he
  | inr bs => obtain ⟨b,s⟩ := bs; exact Finset.singleton_nonempty b

end MetricKMedianRecovery.LocalSearch
namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

omit [PseudoMetricSpace V] [DecidableEq V] in
lemma mem_subtype_map (T : Finset V) (A : Finset ↥T) (x : ↥T) :
    x.val ∈ A.map (Function.Embedding.subtype _) ↔ x ∈ A := by
  constructor
  · intro h
    obtain ⟨y,hy,hxy⟩ := Finset.mem_map.mp h
    exact (Subtype.ext hxy : y = x) ▸ hy
  · intro h; exact Finset.mem_map.mpr ⟨x,h,rfl⟩

theorem protected_swap_sum (F D S Ob Og : Finset V) (hS : S.Nonempty) (hSF : S ⊆ F)
    (hlocal : WidthLocalMin F D S 5) (hbf : Ob ⊆ F)
    (hcard : Ob.card + Og.card ≤ S.card) (assign proxy : V → V)
    (hassign : ∀ p ∈ D, assign p ∈ Ob ∨ assign p ∈ Og)
    (hproxy : ∀ i ∈ Og, proxy i ∈ S) (hinj : Set.InjOn proxy Og) :
    0 ≤ ∑ p ∈ D, if assign p ∈ Ob then (1+2*(6/5:ℝ))*dist p (assign p)-connection S p
      else (6/5:ℝ)*(dist p (proxy (assign p))-connection S p) := by
  classical
  by_cases hb : Ob.Nonempty
  swap
  · have hempty : Ob = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
    apply Finset.sum_nonneg
    intro p hp
    have hg : assign p ∈ Og := (hassign p hp).resolve_left (by simp [hempty])
    simp only [hempty,Finset.notMem_empty,ite_false, if_false]
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr (connection_le (hproxy _ hg)))
  let Phi := Og.image proxy
  have hPhiS : Phi ⊆ S := by
    rintro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact hproxy i hi
  have hPhicard : Phi.card = Og.card := Finset.card_image_iff.mpr hinj
  let Uf := S \ Phi
  have hBU : Ob.card ≤ Uf.card := by
    dsimp [Uf]
    rw [Finset.card_sdiff_of_subset hPhiS,hPhicard]
    omega
  have hUne : Uf.Nonempty := Finset.card_pos.mp ((Finset.card_pos.mpr hb).trans_le hBU)
  let B := ↥Ob
  let U := ↥Uf
  let u0 : U := ⟨hUne.choose,hUne.choose_spec⟩
  let psi : B → U := fun b =>
    if h : nearest S hS b.val ∈ Uf then ⟨nearest S hS b.val,h⟩ else u0
  have hpsi (b : B) (hn : nearest S hS b.val ∉ Phi) :
      (psi b).val = nearest S hS b.val := by
    have hnU : nearest S hS b.val ∈ Uf := Finset.mem_sdiff.mpr ⟨nearest_mem S hS _,hn⟩
    simp only [psi,dite_eq_left hnU]
  obtain ⟨slot,hslot⟩ := slot_allocation psi (by simpa [B,U] using hBU)
  let R : ExchangeIndex B U → Finset V := fun e =>
    (exchangeRemove psi slot e).map (Function.Embedding.subtype _)
  let A : ExchangeIndex B U → Finset V := fun e =>
    (exchangeAdd psi e).map (Function.Embedding.subtype _)
  let w := exchangeWeight psi slot
  have hRU (e) : R e ⊆ Uf := by
    intro s hs
    obtain ⟨u,_,rfl⟩ := Finset.mem_map.mp hs
    exact u.property
  have hAB (e) : A e ⊆ Ob := by
    intro i hi
    obtain ⟨b,_,rfl⟩ := Finset.mem_map.mp hi
    exact b.property
  have hRm (e) (s : U) : s.val ∈ R e ↔ s ∈ exchangeRemove psi slot e :=
    mem_subtype_map Uf _ s
  have hAm (e) (b : B) : b.val ∈ A e ↔ b ∈ exchangeAdd psi e :=
    mem_subtype_map Ob _ b
  apply weighted_swap_family F D S Ob Og hS hSF hlocal assign proxy hassign hproxy
    R A w (6/5) (exchangeWeight_nonneg psi slot)
  · intro e he
    obtain ⟨hce,hwidth⟩ := exchange_width psi slot e he
    refine ⟨(hRU e).trans Finset.sdiff_subset,(hAB e).trans hbf,?_,?_,?_,?_⟩
    · exact (exchange_add_nonempty psi slot e he).map
    · simpa only [R,A,Finset.card_map] using hce.symm.le
    · simpa only [R,Finset.card_map,hce] using hwidth
    · simpa only [A,Finset.card_map] using hwidth
  · intro i hi
    have hm : ∀ e, i ∈ A e ↔ (⟨i,hi⟩ : B) ∈ exchangeAdd psi e :=
      fun e => hAm e ⟨i,hi⟩
    simp_rw [hm]
    exact total_addition_weight psi slot hslot ⟨i,hi⟩
  · intro s _
    by_cases hs : s ∈ Uf
    · have hm : ∀ e, s ∈ R e ↔ (⟨s,hs⟩ : U) ∈ exchangeRemove psi slot e :=
        fun e => hRm e ⟨s,hs⟩
      simp_rw [hm]
      exact removal_weight_le psi slot ⟨s,hs⟩
    · have hm : ∀ e, s ∉ R e := fun e h => hs (hRU e h)
      simp only [hm,ite_false, if_false,Finset.sum_const_zero]
      norm_num
  · intro e _ i hi hr
    exact (Finset.mem_sdiff.mp (hRU e hr)).2 (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
  · intro e he i hi hia hr
    have hn : nearest S hS i ∉ Phi := (Finset.mem_sdiff.mp (hRU e hr)).2
    let b : B := ⟨i,hi⟩
    have hnA : b ∉ exchangeAdd psi e := fun h => hia ((hAm e b).mpr h)
    have hmem : psi b ∈ exchangeRemove psi slot e := (hRm e (psi b)).mp (hpsi b hn ▸ hr)
    exact exchange_preserves_image psi slot hslot e he b hnA hmem

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_AllBadCostBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma all_bad_cost_bound (F D S O : Finset V) (hS : S.Nonempty) (hSF : S ⊆ F)
    (hlocal : WidthLocalMin F D S 5) (hOF : O ⊆ F) (hcard : O.card ≤ S.card)
    (assign : V → V) (hassign : ∀ p ∈ D, assign p ∈ O) :
    cost D S ≤ (17/5:ℝ)*(∑ p ∈ D, dist p (assign p)) := by
  have hs := protected_swap_sum F D S O ∅ hS hSF hlocal hOF (by simpa using hcard)
    assign id (fun p hp => Or.inl (hassign p hp)) (by simp) (by simp)
  have he : (∑ p ∈ D, if assign p ∈ O then
        (1+2*(6/5:ℝ))*dist p (assign p)-connection S p else
        (6/5:ℝ)*(dist p (id (assign p))-connection S p)) =
      (17/5:ℝ)*(∑ p ∈ D, dist p (assign p))-cost D S := by
    rw [cost,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [hassign p hp,ite_true, if_true]
    ring
  rw [he] at hs
  linarith

lemma local_five_approx_s238r_oai (F D S O : Finset V) (hS : S.Nonempty) (hO : O.Nonempty)
    (hSF : S ⊆ F) (hlocal : WidthLocalMin F D S 5) (hOF : O ⊆ F)
    (hcard : O.card ≤ S.card) : cost D S ≤ 5*cost D O := by
  have hs := all_bad_cost_bound F D S O hS hSF hlocal hOF hcard (nearest O hO)
    (fun p _ => nearest_mem O hO p)
  simp only [nearest_distance] at hs
  change cost D S ≤ (17/5:ℝ)*cost D O at hs
  nlinarith [cost_nonneg D O]

end MetricKMedianRecovery.LocalSearch

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.LocalSearch.local_five_approx_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.LocalSearch.local_five_approx_s238r_oai.{u_1}
