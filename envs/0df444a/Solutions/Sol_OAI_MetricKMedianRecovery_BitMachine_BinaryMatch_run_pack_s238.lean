-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.run_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:14:14.974659+00:00
-- url     : https://prove2.me/submissions/387e094a-0ff1-45a6-9352-938c3bcf5371

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K043
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryMatch_step_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalMergePath_advancePrefix_spec_s238

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

lemma Walk.first_good {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {n : ℕ} {H G : List X} (h : Walk loc F B Q copy v z lam eta n H G) :
    Good loc F B Q copy v z lam eta H := by
  cases h with
  | nil h => exact h
  | cons h _ _ => exact h

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
      obtain ⟨hGr,hvG,hw⟩ := advancePrefix_spec_s238 loc F B Q copy v z lam eta complete hc
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

end MetricKMedianRecovery.CanonicalMergePath

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations UnaryTake

namespace WordList

lemma cons_ne_nil (w ws : List Bool) : cons w ws≠[] := List.cons_ne_nil _ _

end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Step2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations
namespace WordList
lemma length_encode_append (xs ys : List (List Bool)) :
    (encode (xs++ys)).length=(encode xs).length+(encode ys).length := by
  induction xs with
  | nil => simp only [List.nil_append,encode,List.length_nil,Nat.zero_add]
  | cons x xs ih => simp only [List.cons_append,encode,length_cons,ih]; omega
lemma length_encode_drop (xs : List (List Bool)) (n : ℕ) :
    (encode (xs.drop n)).length ≤ (encode xs).length := by
  have h := length_encode_append (xs.take n) (xs.drop n)
  rw [List.take_append_drop] at h
  omega
namespace Fold

lemma length_pack (ws ctx a : List Bool) : (pack ws ctx a).length=2*ws.length+2*ctx.length+a.length+2 := by
  simp only [pack,pairBits_length]; omega
lemma step_nil (f : List Bool → List Bool) (ctx a : List Bool) :
    step f (pack (encode []) ctx a)=pack (encode []) ctx a := by
  simp only [step,items_pack,encode,ite_true, if_true]
lemma step_cons (f : List Bool → List Bool) (ctx a w : List Bool) (ws : List (List Bool)) :
    step f (pack (encode (w::ws)) ctx a)=pack (encode ws) ctx (operation f ctx a w) := by
  simp only [step,items_pack,encode,cons_ne_nil,ite_false, if_false,context_pack,head_cons,tail_cons,accum_pack,operation]
lemma iterate_pack (f : List Bool → List Bool) (ctx a : List Bool) (ws : List (List Bool)) (n : ℕ) :
    (step f)^[n] (pack (encode ws) ctx a)=
      pack (encode (ws.drop n)) ctx ((ws.take n).foldl (operation f ctx) a) := by
  induction n generalizing ws a with
  | zero => simp only [Function.iterate_zero_apply,List.drop_zero,List.take_zero,List.foldl_nil]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases ws with
    | nil =>
      rw [step_nil,Function.iterate_fixed (step_nil f ctx a)]
      rfl
    | cons w ws =>
      rw [step_cons,ih]
      simp only [List.drop_succ_cons,List.take_succ_cons,List.foldl_cons]

lemma run_encode (f : List Bool → List Bool) (R : Polynomial ℕ) (ctx a : List Bool)
    (ws : List (List Bool)) (B : ℕ)
    (hB : ∀ n,((ws.take n).foldl (operation f ctx) a).length ≤ B)
    (hR : 2*(encode ws).length+2*ctx.length+B+2 ≤ R.eval (pack (encode ws) ctx a).length) :
    run f R (pack (encode ws) ctx a)=ws.foldl (operation f ctx) a := by
  have he := BoundedIteration.polynomialRun_eq (step f) Polynomial.X R (pack (encode ws) ctx a) (by
    intro j _
    rw [iterate_pack,length_pack]
    have hd := length_encode_drop ws j
    have hb := hB j
    omega)
  simp only [run,Function.comp_apply,he,Polynomial.eval_X,iterate_pack,accum_pack]
  rw [List.take_of_length_le]
  have hw := length_le_encode ws
  rw [length_pack]
  omega
end Fold
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic
namespace WordList
lemma encode_le_bound (ws : List (List Bool)) (B : ℕ) (hB : ∀ w∈ws,w.length ≤ B) :
    (encode ws).length ≤ ws.length*(2*B+2) := by
  induction ws with
  | nil => simp only [encode,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons w ws ih =>
    have hw := hB w (List.mem_cons_self ..)
    have ht := ih (fun x hx=>hB x (List.mem_cons_of_mem _ hx))
    simp only [encode,length_cons,List.length_cons]
    nlinarith
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundedDecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations
namespace WordList
namespace Count
lemma operation_eq (ctx a w : List Bool) : Fold.operation op ctx a w=true::a := by
  simp only [Fold.operation,op,Function.comp_apply,Fold.accum,discardPrefix_pairBits]
lemma fold_op (ws : List (List Bool)) (a : List Bool) (ctx : List Bool) :
    ws.foldl (Fold.operation op ctx) a=List.replicate ws.length true++a := by
  induction ws generalizing a with
  | nil => simp only [List.foldl_nil,List.length_nil,List.replicate_zero,List.nil_append]
  | cons w ws ih =>
    simp only [List.foldl_cons,operation_eq,ih,List.length_cons]
    rw [←List.singleton_append,←List.append_assoc,←List.replicate_succ',List.replicate_succ]
lemma run_encode (ws : List (List Bool)) : run (encode ws)=List.replicate ws.length true := by
  unfold run
  rw [Fold.run_encode op (4*Polynomial.X+4) [] [] ws (encode ws).length]
  · simp only [fold_op,List.append_nil]
  · intro n
    simp only [fold_op,List.append_nil,List.length_replicate]
    have ht : (ws.take n).length ≤ ws.length := by simp only [List.length_take]; omega
    exact ht.trans (length_le_encode ws)
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
end Count
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList
lemma member_length {ws : List (List Bool)} {w : List Bool} (hw : w∈ws) : w.length≤(encode ws).length := by
  induction ws with
  | nil=>exact False.elim (List.not_mem_nil hw)
  | cons v vs ih=>
    rw [encode,length_cons]
    rcases List.mem_cons.mp hw with rfl|hw
    · omega
    · have h:=ih hw
      omega
end MetricKMedianRecovery.BitMachine.WordList
namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordList RationalLeaves
lemma length_labels_le {pointCount : ℕ} (xs : List (Label (Fin pointCount))) : xs.length≤(labels xs).length := by
  simpa only [List.length_map,labels] using length_le_encode (xs.map BinaryLabel.encode)
lemma member_labels_length {pointCount : ℕ} {xs : List (Label (Fin pointCount))} {x : Label (Fin pointCount)} (hx : x∈xs) :
    (BinaryLabel.encode x).length≤(labels xs).length :=
  member_length (List.mem_map.mpr ⟨x,hx,rfl⟩)
lemma card_setBits_le {pointCount : ℕ} (S : Finset (Label (Fin pointCount))) : S.card≤(setBits S).length := by
  simpa only [setBits,BinaryLabel.orderedSort,Finset.length_sort] using length_labels_le (BinaryLabel.orderedSort S)
lemma member_setBits_length {pointCount : ℕ} {S : Finset (Label (Fin pointCount))} {x : Label (Fin pointCount)} (hx : x∈S) :
    (BinaryLabel.encode x).length≤(setBits S).length :=
  member_labels_length ((Finset.mem_sort _).mpr hx)
lemma labels_length_bounded {m r B : ℕ} (xs : List (Label (Fin m))) (hn : xs.length ≤ r)
    (hB : ∀ x∈xs,(BinaryLabel.encode x).length≤B) :
    (labels xs).length ≤ r*(2*B+2) := by
  have h:=encode_le_bound (xs.map BinaryLabel.encode) B (by
    intro w hw
    obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hw
    exact hB x hx)
  simp only [List.length_map] at h
  exact h.trans (Nat.mul_le_mul_right _ hn)
lemma pack_F_bound {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    (setBits F).length≤(pack distance loc F Q v z lam).length :=
  member_length (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CappedFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.CappedFold
open WordOperations
lemma run_pack (f : List Bool → List Bool) (cap ctx a : List Bool) (ws : List (List Bool))
    (hB : ∀ n, ((ws.take n).foldl (Fold.operation f ctx) a).length ≤ cap.length) :
    run f (pairBits (cap,Fold.pack (encode ws) ctx a))=ws.foldl (Fold.operation f ctx) a := by
  unfold run
  rw [discardPrefix_pairBits,Fold.items_pack,Count.run_encode,BoundedIteration.run_eq]
  · simp only [List.length_replicate,Fold.iterate_pack,Fold.accum_pack,List.take_length]
  · intro j _
    rw [Fold.iterate_pack,Fold.length_pack,RepeatedAppend.length_copies,pairBits_length,Fold.length_pack]
    dsimp only at *
    have hws:=length_encode_drop ws j
    have hb:=hB j
    omega

lemma fold_encode {S A : Type*} (encS : S → List Bool) (encA : A → List Bool)
    (g : S → A → S) (f : List Bool → List Bool) (ctx : List Bool)
    (hf : ∀ s a,f (pairBits (ctx,pairBits (encA a,encS s)))=encS (g s a))
    (s : S) (xs : List A) :
    (xs.map encA).foldl (Fold.operation f ctx) (encS s)=encS (xs.foldl g s) := by
  induction xs generalizing s with
  | nil=>rfl
  | cons a xs ih=>
    simp only [List.map_cons,List.foldl_cons,Fold.operation,hf]
    exact ih (g s a)
lemma run_typed {S A : Type*} (encS : S → List Bool) (encA : A → List Bool)
    (g : S → A → S) (f : List Bool → List Bool) (ctx cap : List Bool)
    (hf : ∀ s a,f (pairBits (ctx,pairBits (encA a,encS s)))=encS (g s a))
    (s : S) (xs : List A) (hB : ∀ n,(encS ((xs.take n).foldl g s)).length ≤ cap.length) :
    run f (pairBits (cap,Fold.pack (encode (xs.map encA)) ctx (encS s)))=encS (xs.foldl g s) := by
  rw [run_pack]
  · exact fold_encode encS encA g f ctx hf s xs
  · intro n
    rw [←List.map_take,fold_encode encS encA g f ctx hf]
    exact hB n
end MetricKMedianRecovery.BitMachine.WordList.CappedFold

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PathBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergePath
open PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
lemma Good.length_bound {loc : D → X} {F B Q : Finset X} {copy : X → X}
    {v z lam eta : ℝ} {H : List X} (h : Good loc F B Q copy v z lam eta H) :
    H.length≤F.card+1 := by
  have hs : H.toFinset⊆F∪(H.toFinset\F) := by
    intro x hx
    by_cases hxF : x∈F
    · exact Finset.mem_union_left _ hxF
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx,hxF⟩)
  have hl := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  rw [List.toFinset_card_of_nodup h.1.1.nodup] at hl
  exact hl.trans (Nat.add_le_add_left h.2 F.card)
lemma Step.preserves {loc : D → X} {F B Q : Finset X} {copy : X → X}
    {v z lam : ℝ} {H G : List X} (h : Step loc F B Q copy v z lam H G)
    {P : X → Prop} (hF : ∀ x∈F,P x) (hc : ∀ x∈F,P (copy x)) (hH : ∀ x∈H,P x) :
    ∀ x∈G,P x := by
  cases h with
  | add H i hi=>
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact hH x hx
    · obtain rfl:=List.mem_singleton.mp hx
      exact hc i hi
  | remove C T A i hi hA hreg=>
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · rcases List.mem_append.mp hx with hx|hx
      · exact hH x (List.mem_append_left _ hx)
      · exact hH x (List.mem_append_right _ (List.mem_cons_of_mem _ hx))
    · exact hF x (hreg x hx)
  | replace C T i hi hn=>
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact hH x (List.mem_append_left _ hx)
    · rcases List.mem_cons.mp hx with rfl|hx
      · exact hF x hi
      · exact hH x (List.mem_append_right _ (List.mem_cons_of_mem _ hx))
end MetricKMedianRecovery.PhaseMergePath

namespace MetricKMedianRecovery.CanonicalMergePath
open PhaseSequence PhaseMergePath
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
lemma Path.vertices_good {loc : D → X} {F B Q : Finset X} {copy : X → X}
    {v z lam eta : ℝ} {H J : List X} {T : List (List X)}
    (h : Path loc F B Q copy v z lam eta H T J) :
    ∀ G∈T,Good loc F B Q copy v z lam eta G := by
  induction h with
  | nil=>intro G hG; exact False.elim (List.not_mem_nil hG)
  | cons _ _ ht ih=>
    intro G hG
    rcases List.mem_cons.mp hG with rfl|hG
    · exact ht.toWalk.first_good
    · exact ih G hG
lemma Path.vertices_mem {loc : D → X} {F B Q : Finset X} {copy : X → X}
    {v z lam eta : ℝ} {H J : List X} {T : List (List X)}
    (h : Path loc F B Q copy v z lam eta H T J)
    {P : X → Prop} (hF : ∀ x∈F,P x) (hc : ∀ x∈F,P (copy x)) (hH : ∀ x∈H,P x) :
    ∀ G∈T,∀ x∈G,P x := by
  induction h with
  | nil=>intro G hG; exact False.elim (List.not_mem_nil hG)
  | cons _ e _ ih=>
    have hG:=e.preserves hF hc hH
    intro G hm
    rcases List.mem_cons.mp hm with rfl|hm
    · exact hG
    · exact ih hG G hm
end MetricKMedianRecovery.CanonicalMergePath

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMatch
open CanonicalMergePath PhaseSequence PhaseMergePath
variable {X D : Type*} [DecidableEq X]
lemma fold_result (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    (C U : List X) (V : List (List X)) (T : List X) :
    T.foldl (step complete Q copy) ⟨C,U,V⟩=
      ⟨C++T,(matchPrefix complete Q copy C U T).1,V++(matchPrefix complete Q copy C U T).2⟩ := by
  induction T generalizing C U V with
  | nil=>simp only [List.foldl_nil,List.append_nil,matchPrefix]
  | cons i T ih=>
    simp only [List.foldl_cons,step]
    rw [ih]
    simp only [matchPrefix,List.append_assoc,List.singleton_append]

variable [Fintype D] [PseudoMetricSpace X]
lemma fold_bounds (loc : D → X) (F B Q : Finset X) (copy : X → X)
    (v z lam eta : ℝ) (complete : Finset X → List X)
    (hc : CorrectCompletion loc F v z lam complete)
    (hv : 0<v) (hvsmall : v<1/6) (hz : 0<z) (hlam : 0<lam) (heta : 0≤eta)
    (hQ : Q⊆F∪B) (hdis : Disjoint F B)
    (hrow : ∀ k∈F,bidRow loc (1-3*v) z Q k≤lam)
    (hfresh : ∀ i∈F,copy i∉F∪B) (hco : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy i))
    (C U T : List X) (hCr : ∀ i∈C,i∈F) (hUr : ∀ i∈U,i∈F) (hTr : ∀ i∈T,i∈F)
    (htarget : Prefix loc F B v z lam eta Q (C++T)) (hcur : Valid loc F B Q v z lam eta (C++U))
    {P : X → Prop} (hF : ∀ x∈F,P x) (hcopy : ∀ x∈F,P (copy x)) :
    let s:=T.foldl (step complete Q copy) ⟨C,U,[]⟩
    s.front.length≤F.card ∧ s.rest.length≤F.card ∧ s.vertices.length≤T.length*(F.card+2) ∧
    (∀ H∈s.vertices,H.length≤F.card+1) ∧
    (∀ x∈s.front,P x) ∧ (∀ x∈s.rest,P x) ∧ (∀ H∈s.vertices,∀ x∈H,P x) := by
  rw [fold_result,List.nil_append]
  dsimp only
  obtain ⟨hlen,hreg,hvalid,hpath⟩:=matchPrefix_spec loc F B Q copy v z lam eta complete hc
    hv hvsmall hz hlam heta hQ hdis hrow hfresh hco C U T hCr hUr hTr htarget hcur
  have hCT : ∀ x∈C++T,x∈F := fun x hx=>(List.mem_append.mp hx).elim (hCr x) (hTr x)
  have hbound:=regular_length hvalid.1 (fun x hx=>(List.mem_append.mp hx).elim (hCT x) (hreg x))
  simp only [List.length_append] at hbound
  refine ⟨by simp only [List.length_append]; omega,by omega,hlen,?_,?_,?_,?_⟩
  · exact fun H hH=>(hpath.vertices_good H hH).length_bound
  · exact fun x hx=>hF x (hCT x hx)
  · exact fun x hx=>hF x (hreg x hx)
  · exact hpath.vertices_mem hF hcopy (fun x hx=>hF x ((List.mem_append.mp hx).elim (hCr x) (hUr x)))
end MetricKMedianRecovery.CanonicalMatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchSize
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMatch
open WordOperations WordList RationalLeaves CanonicalMatch CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

lemma accBits_bound {m N : ℕ} {s : Acc (Label (Fin m))}
    (hC : s.front.length≤N) (hU : s.rest.length≤N) (hV : s.vertices.length≤N*(N+2))
    (hW : ∀ H∈s.vertices,H.length≤N+1)
    (hmC : ∀ x∈s.front,(BinaryLabel.encode x).length≤N)
    (hmU : ∀ x∈s.rest,(BinaryLabel.encode x).length≤N)
    (hmV : ∀ H∈s.vertices,∀ x∈H,(BinaryLabel.encode x).length≤N) :
    (accBits s).length ≤ capacityPoly.eval N := by
  have hC':=BinaryFiniteContext.labels_length_bounded s.front hC hmC
  have hU':=BinaryFiniteContext.labels_length_bounded s.rest hU hmU
  have hV':=(encode_le_bound (s.vertices.map labels) ((N+1)*(2*N+2)) (by
    intro w hw
    obtain ⟨H,hH,rfl⟩:=List.mem_map.mp hw
    exact BinaryFiniteContext.labels_length_bounded H (hW H hH) (hmV H hH)))
  simp only [List.length_map] at hV'
  have hhist : (historyBits s.vertices).length≤N*(N+2)*(2*((N+1)*(2*N+2))+2) :=
    hV'.trans (Nat.mul_le_mul_right _ hV)
  simp only [capacityPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_one,Polynomial.eval_X,accBits,length_encode,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  simp only [Nat.mul_assoc] at *
  omega
lemma pack_bounds {m : ℕ} (base : List Bool) (key : ℕ) (F : Finset (Label (Fin m)))
    (C U T : List (Label (Fin m))) :
    base.length≤(pack base key F C U T).length ∧
    (labels ((BinaryLabel.orderedSort F).map (copy key))).length≤(pack base key F C U T).length ∧
    (labels T).length≤(pack base key F C U T).length := by
  have hb : base.length≤(contextBits base key F).length := member_length (List.mem_cons_self ..)
  have hc : (labels ((BinaryLabel.orderedSort F).map (copy key))).length≤(contextBits base key F).length :=
    member_length (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  simp only [pack,Fold.length_pack]
  omega

lemma run_pack_s238_oai {m d : ℕ} [PseudoMetricSpace (Label (Fin m))]
    (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F B Q : Finset (Label (Fin m))) (v z lam : ℚ) (eta : ℝ) (key : ℕ)
    (hc : CorrectCompletion loc F (v:ℝ) z lam (FiniteLabelContinuation.complete loc (rows distance) F v z lam))
    (hv : (0:ℝ)<v) (hvsmall : (v:ℝ)<1/6) (hz : (0:ℝ)<z) (hlam : (0:ℝ)<lam) (heta : 0≤eta)
    (hQ : Q⊆F∪B) (hdis : Disjoint F B)
    (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) z Q i≤lam)
    (hfresh : ∀ i∈F,copy key i∉F∪B) (hco : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy key i))
    (C U T : List (Label (Fin m))) (hCr : ∀ i∈C,i∈F) (hUr : ∀ i∈U,i∈F) (hTr : ∀ i∈T,i∈F)
    (htarget : Prefix loc F B v z lam eta Q (C++T)) (hcur : Valid loc F B Q v z lam eta (C++U)) :
    run (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key F C U T)=
      accBits ⟨C++T,(matchPrefix (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) C U T).1,
        (matchPrefix (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) C U T).2⟩ := by
  let base:=BinaryFiniteContext.pack distance loc F Q v z lam
  let x:=pack base key F C U T
  let N:=x.length
  obtain ⟨hb,hcopy,hT⟩:=pack_bounds base key F C U T
  have hFB : (setBits F).length≤N := (BinaryFiniteContext.pack_F_bound distance loc F Q v z lam).trans hb
  have hFcard : F.card≤N := (BinaryFiniteContext.card_setBits_le F).trans hFB
  have hTlen : T.length≤N := (BinaryFiniteContext.length_labels_le T).trans hT
  have hFm : ∀ i∈F,(BinaryLabel.encode i).length≤N :=
    fun i hi=>(BinaryFiniteContext.member_setBits_length hi).trans hFB
  have hcm : ∀ i∈F,(BinaryLabel.encode (copy key i)).length≤N := by
    intro i hi
    apply (BinaryFiniteContext.member_labels_length ?_).trans hcopy
    exact List.mem_map.mpr ⟨i,(Finset.mem_sort _).mpr hi,rfl⟩
  have ht:=CappedFold.run_typed accBits BinaryLabel.encode
    (CanonicalMatch.step (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key)) step
    (contextBits base key F) (capacity.word x) (step_pack_s238 distance loc F Q v z lam key) (⟨C,U,[]⟩ : Acc (Label (Fin m))) T
  have heq:=ht (by
    intro n
    rw [capacity.word_length]
    obtain ⟨hC,hU,hV,hW,hmC,hmU,hmV⟩:=CanonicalMatch.fold_bounds loc F B Q (copy key)
      v z lam eta _ hc hv hvsmall hz hlam heta hQ hdis hrow hfresh hco C U (T.take n) hCr hUr
      (fun i hi=>hTr i (List.mem_of_mem_take hi))
      (htarget.sublist ((List.take_sublist n T).append_left C)) hcur hFm hcm
    apply accBits_bound (hC.trans hFcard) (hU.trans hFcard) _ _ hmC hmU hmV
    · apply hV.trans
      exact Nat.mul_le_mul ((by simp only [List.length_take]; exact (Nat.min_le_right n T.length).trans hTlen))
        (Nat.add_le_add_right hFcard 2)
    · exact fun H hH=>(hW H hH).trans (Nat.add_le_add_right hFcard 1))
  change run x = _ at heq
  rw [CanonicalMatch.fold_result,List.nil_append] at heq
  exact heq
end MetricKMedianRecovery.BitMachine.BinaryMatch

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.run_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.run_pack_s238_oai
