-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.step_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:13:22.739203+00:00
-- url     : https://prove2.me/submissions/784afb60-1ccf-48f8-957c-d29d4d12e850

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K043
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryDelete_step_pack_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_StoredForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability OrdinaryProducer OpenabilityLinearization

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

end MetricKMedianRecovery.RationalPhase

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteContinuation
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteLabelContinuation
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing
variable {X : Type*} [LinearOrder X] {d : ℕ}

lemma image_select (loc : Fin d → X) (F Q S : Finset X)
    (hS : ∀ x∈S,x∈alphabet loc F Q) : (select loc F Q S).image (embed loc F Q)=S := by
  ext x
  simp only [Finset.mem_image,mem_select]
  constructor
  · rintro ⟨i,hi,rfl⟩; exact hi
  · intro hx
    refine ⟨index loc F Q x (hS x hx),?_,embed_index ..⟩
    simpa only [embed_index] using hx

end MetricKMedianRecovery.FiniteLabelContinuation

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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionBound
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
lemma finish_events {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (fuel : ℕ) (s : State m d) :
    (finish distance F v lam fuel s).2.length≤fuel ∧
      ∀ e∈(finish distance F v lam fuel s).2,e.facility∈F := by
  induction fuel generalizing s with
  | zero=>simp only [finish,List.length_nil,List.not_mem_nil,false_implies,implies_true,and_true,Nat.zero_le]
  | succ n ih=>
    rw [finish]
    split
    next h=>simp only [List.length_nil,List.not_mem_nil,false_implies,implies_true,and_true,Nat.zero_le]
    next e he=>
      obtain ⟨hlen,hmem⟩:=ih (update distance v s e)
      refine ⟨by simpa only [List.length_cons] using Nat.succ_le_succ hlen,?_⟩
      intro t ht
      rcases List.mem_cons.mp ht with rfl|ht
      · exact (first_some distance F s.opened v s.phase lam _ t he).1
      · exact hmem t ht
lemma completion_events {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F Q : Finset (Fin m))
    (v z lam : ℚ) :
    (completion distance F v z lam Q).length≤F.card ∧
      ∀ i∈completion distance F v z lam Q,i∈F := by
  obtain ⟨hlen,hmem⟩:=finish_events distance F v lam F.card ⟨Q,z,Vector.replicate d 0⟩
  refine ⟨by simpa only [completion,List.length_map] using hlen,?_⟩
  intro i hi
  obtain ⟨e,he,rfl⟩:=List.mem_map.mp hi
  exact hmem e he
end MetricKMedianRecovery.RationalPhase

namespace MetricKMedianRecovery.FiniteLabelContinuation
variable {X : Type*} [LinearOrder X] {d : ℕ}
lemma select_card (loc : Fin d → X) (F Q : Finset X) : (select loc F Q F).card=F.card := by
  have h: (select loc F Q F).image (embed loc F Q)=F :=
    image_select loc F Q F (fun x hx=>(mem_alphabet loc F Q x).mpr (Or.inl hx))
  exact (Finset.card_image_of_injective (select loc F Q F) (embed loc F Q).injective).symm.trans (congrArg Finset.card h)
lemma complete_events (loc : Fin d → X) (distance : X → Fin d → ℚ) (F Q : Finset X) (v z lam : ℚ) :
    (complete loc distance F v z lam Q).length≤F.card ∧
      ∀ i∈complete loc distance F v z lam Q,i∈F := by
  obtain ⟨hn,hm⟩:=RationalPhase.completion_events (rows loc F Q distance) (select loc F Q F)
    (select loc F Q Q) v z lam
  refine ⟨by simpa only [complete,List.length_map,select_card] using hn,?_⟩
  intro i hi
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hi
  exact (mem_select loc F Q F j).mp (hm j hj)
end MetricKMedianRecovery.FiniteLabelContinuation

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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FiniteMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations BinaryArithmetic RationalLeaves
lemma copied_pack {m : ℕ} (key : ℕ) (x : Label (Fin m)) :
    copied (pairBits (key.bits,encode x))=encode (copy key x) := by
  simp only [copied,extractPrefix_pairBits,discardPrefix_pairBits,levelWords_encode,value_bits,parentWords_encode]
  cases x with
  | inl i=>rfl
  | inr c=>simp only [level,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false, if_false,copy,Sum.elim_inr]

end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
lemma labels_cons {m : ℕ} (x : Label (Fin m)) (xs : List (Label (Fin m))) :
    labels (x::xs)=WordList.cons (BinaryLabel.encode x) (labels xs) := rfl
lemma labels_nil {m : ℕ} : labels ([] : List (Label (Fin m)))=[] := rfl

end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteMachine
open WordOperations WordList RationalLeaves PhaseSequence
open BinaryFiniteContext (labels setBits)
lemma historyBits_append {m : ℕ} (hs gs : List (List (Label (Fin m)))) :
    historyBits (hs++gs)=historyBits hs++historyBits gs := by
  simp only [historyBits,List.map_append,encode_append]
lemma historyBits_cons {m : ℕ} (H : List (Label (Fin m))) (hs : List (List (Label (Fin m)))) :
    historyBits (H::hs)=WordList.cons (labels H) (historyBits hs) := rfl
lemma historyBits_nil {m : ℕ} : historyBits ([] : List (List (Label (Fin m))))=[] := rfl
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_DeleteFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalDelete
open PhaseSequence CanonicalMergePath
variable {X : Type*} [DecidableEq X]

lemma fold_result (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    (C : List X) (i : X) (U E : List X) (V : List (List X)) :
    U.foldl (step complete Q C (copy i)) ⟨U,E,V⟩=
      ⟨[],(deleteSuffix complete Q copy C i U E).1,V++(deleteSuffix complete Q copy C i U E).2⟩ := by
  induction U generalizing E V with
  | nil=>simp only [List.foldl_nil,deleteSuffix,List.append_nil]
  | cons u U ih=>
    simp only [List.foldl_cons,step,List.tail_cons]
    rw [ih]
    simp only [deleteSuffix,List.append_assoc,List.singleton_append]

lemma Bounds.step {complete : Finset X → List X} {Q : Finset X} {C : List X} {ci : X}
    {P : X → Prop} {N n : ℕ} {s : Acc X} (hs : Bounds P N n s)
    (hC : C.length≤N) (hCm : ∀ x∈C,P x) (hi : P ci)
    (hc : ∀ W,(complete W).length≤N ∧ ∀ x∈complete W,P x) (a : X) :
    Bounds P N (n+1) (step complete Q C ci s a) := by
  let U:=s.remaining.tail
  let A:=complete (Q∪(C++U++ci::s.extras).toFinset)
  have hu : U.length≤N := (by simpa only [U,List.length_tail] using (Nat.sub_le s.remaining.length 1).trans hs.remaining)
  have ha : A.length≤N ∧ ∀ x∈A,P x := hc _
  have he : (s.extras++A).length≤N+(n+1)*N := by
    rw [List.length_append]
    have h:=hs.extras
    simp only [Nat.add_mul,one_mul] at *
    omega
  have hm : ∀ x∈C++U++ci::(s.extras++A),P x := by
    intro x hx
    simp only [List.mem_append,List.mem_cons] at hx
    rcases hx with (hx|hx)|hx|hx|hx
    · exact hCm x hx
    · exact hs.rem_mem x (List.mem_of_mem_tail hx)
    · simpa only [hx] using hi
    · exact hs.ext_mem x hx
    · exact ha.2 x hx
  refine ⟨hu,he,?_,?_,?_,?_,?_⟩
  · change (s.vertices++[_]).length≤_
    simp only [List.length_append,List.length_singleton]
    have h:=hs.vertices
    simp only [Nat.add_mul,one_mul] at *
    omega
  · intro H hH
    change H∈s.vertices++[_] at hH
    rcases List.mem_append.mp hH with hH|hH
    · exact (hs.vertex H hH).trans (by simp only [Nat.add_mul,one_mul]; omega)
    · obtain rfl:=List.mem_singleton.mp hH
      change (C++U++ci::(s.extras++A)).length≤_
      simp only [List.length_append,List.length_cons]
      have hh:=hs.extras
      simp only [Nat.add_mul,one_mul] at *
      omega
  · intro x hx
    exact hs.rem_mem x (List.mem_of_mem_tail hx)
  · intro x hx
    exact (List.mem_append.mp hx).elim (hs.ext_mem x) (ha.2 x)
  · intro H hH
    rcases List.mem_append.mp hH with hH|hH
    · exact hs.vert_mem H hH
    · obtain rfl:=List.mem_singleton.mp hH
      exact hm

lemma Bounds.fold {complete : Finset X → List X} {Q : Finset X} {C : List X} {ci : X}
    {P : X → Prop} {N n : ℕ} {s : Acc X} (hs : Bounds P N n s)
    (hC : C.length≤N) (hCm : ∀ x∈C,P x) (hi : P ci)
    (hc : ∀ W,(complete W).length≤N ∧ ∀ x∈complete W,P x) (xs : List X) :
    Bounds P N (n+xs.length) (xs.foldl (CanonicalDelete.step complete Q C ci) s) := by
  induction xs generalizing n s with
  | nil=>simpa only [List.length_nil,Nat.add_zero,List.foldl_nil] using hs
  | cons a xs ih=>
    simpa only [List.length_cons,List.foldl_cons,Nat.add_assoc,Nat.add_comm 1] using
      ih (hs.step hC hCm hi hc a)
end MetricKMedianRecovery.CanonicalDelete

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_DeleteSize
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDelete
open WordOperations WordList RationalLeaves CanonicalDelete
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

lemma accBits_bound {m N n : ℕ} {s : Acc (Label (Fin m))}
    (hs : Bounds (fun x=>(BinaryLabel.encode x).length≤N) N n s) (hn : n≤N) :
    (accBits s).length ≤ capacityPoly.eval N := by
  have he : s.extras.length≤N+N*N := hs.extras.trans (Nat.add_le_add_left (Nat.mul_le_mul_right N hn) N)
  have hv : s.vertices.length≤2*N := hs.vertices.trans (by omega)
  have hw : ∀ H∈s.vertices,H.length≤3*N+1+N*N := fun H hH=>
    (hs.vertex H hH).trans (Nat.add_le_add_left (Nat.mul_le_mul_right N hn) _)
  have hr:=BinaryFiniteContext.labels_length_bounded s.remaining hs.remaining hs.rem_mem
  have he':=BinaryFiniteContext.labels_length_bounded s.extras he hs.ext_mem
  have hV:=encode_le_bound (s.vertices.map labels) ((3*N+1+N*N)*(2*N+2)) (by
    intro w hw'
    obtain ⟨H,hH,rfl⟩:=List.mem_map.mp hw'
    exact BinaryFiniteContext.labels_length_bounded H (hw H hH) (hs.vert_mem H hH))
  simp only [List.length_map] at hV
  have hV':(historyBits s.vertices).length≤(2*N)*(2*((3*N+1+N*N)*(2*N+2))+2) :=
    hV.trans (Nat.mul_le_mul_right _ hv)
  simp only [capacityPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X,
    accBits,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  omega

lemma pack_bounds {m : ℕ} (base : List Bool) (C : List (Label (Fin m))) (ci : Label (Fin m))
    (U E : List (Label (Fin m))) :
    base.length≤(pack base C ci U E).length ∧
    (labels C).length≤(pack base C ci U E).length ∧
    (BinaryLabel.encode ci).length≤(pack base C ci U E).length ∧
    (labels U).length≤(pack base C ci U E).length ∧
    (labels E).length≤(pack base C ci U E).length := by
  have hb : base.length≤(contextBits base (labels C) (BinaryLabel.encode ci)).length :=
    member_length (List.mem_cons_self ..)
  have hC : (labels C).length≤(contextBits base (labels C) (BinaryLabel.encode ci)).length :=
    member_length (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hi : (BinaryLabel.encode ci).length≤(contextBits base (labels C) (BinaryLabel.encode ci)).length :=
    member_length (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hE : (labels E).length≤(accBits (⟨U,E,[]⟩ : Acc (Label (Fin m)))).length :=
    member_length (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  simp only [pack,Fold.length_pack]
  omega

lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (copy : Label (Fin m) → Label (Fin m))
    (C : List (Label (Fin m))) (i : Label (Fin m)) (U E : List (Label (Fin m))) :
    run (pack (BinaryFiniteContext.pack distance loc F Q v z lam) C (copy i) U E)=
      accBits ⟨[],(CanonicalMergePath.deleteSuffix
        (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q copy C i U E).1,
        (CanonicalMergePath.deleteSuffix
        (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q copy C i U E).2⟩ := by
  let base:=BinaryFiniteContext.pack distance loc F Q v z lam
  let x:=pack base C (copy i) U E
  let N:=x.length
  obtain ⟨hb,hC,hi,hU,hE⟩:=pack_bounds base C (copy i) U E
  have hc : ∀ W,(FiniteLabelContinuation.complete loc (rows distance) F v z lam W).length≤N ∧
      ∀ j∈FiniteLabelContinuation.complete loc (rows distance) F v z lam W,(BinaryLabel.encode j).length≤N := by
    intro W
    obtain ⟨hlen,hmem⟩:=FiniteLabelContinuation.complete_events loc (rows distance) F W v z lam
    have hF : (setBits F).length≤N := (BinaryFiniteContext.pack_F_bound distance loc F Q v z lam).trans hb
    exact ⟨hlen.trans ((BinaryFiniteContext.card_setBits_le F).trans hF),
      fun j hj=>(BinaryFiniteContext.member_setBits_length (hmem j hj)).trans hF⟩
  have hClen : C.length≤N := (BinaryFiniteContext.length_labels_le C).trans hC
  have hUlen : U.length≤N := (BinaryFiniteContext.length_labels_le U).trans hU
  have hCm : ∀ j∈C,(BinaryLabel.encode j).length≤N :=
    fun j hj=>(BinaryFiniteContext.member_labels_length hj).trans hC
  have hs : Bounds (fun j=>(BinaryLabel.encode j).length≤N) N 0 (⟨U,E,[]⟩ : Acc (Label (Fin m))) := by
    refine ⟨hUlen,?_,?_,?_,?_,?_,?_⟩
    · simpa only [Nat.zero_mul,Nat.add_zero] using (BinaryFiniteContext.length_labels_le E).trans hE
    · exact Nat.zero_le _
    · intro H hH; exact False.elim (List.not_mem_nil hH)
    · exact fun j hj=>(BinaryFiniteContext.member_labels_length hj).trans hU
    · exact fun j hj=>(BinaryFiniteContext.member_labels_length hj).trans hE
    · intro H hH; exact False.elim (List.not_mem_nil hH)
  have ht:=CappedFold.run_typed accBits BinaryLabel.encode
    (CanonicalDelete.step (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q C (copy i)) step
    (contextBits base (labels C) (BinaryLabel.encode (copy i))) (capacity.word x)
    (fun s a=>step_pack_s238 distance loc F Q v z lam C (copy i) a s) (⟨U,E,[]⟩ : Acc (Label (Fin m))) U
  have heq:=ht (by
    intro n
    rw [capacity.word_length]
    apply accBits_bound
    · simpa only [Nat.zero_add] using hs.fold hClen hCm hi hc (U.take n)
    · simp only [List.length_take]; exact (Nat.min_le_right n U.length).trans hUlen)
  change run x = _ at heq
  rw [CanonicalDelete.fold_result,List.nil_append] at heq
  exact heq
end MetricKMedianRecovery.BitMachine.BinaryDelete

namespace MetricKMedianRecovery.BitMachine.BinaryAdvance
open WordOperations WordList RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

lemma deleted_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (copy : Label (Fin m) → Label (Fin m))
    (C U : List (Label (Fin m))) (i : Label (Fin m)) :
    deleted (pack (BinaryFiniteContext.pack distance loc F Q v z lam) C U i (copy i))=
    BinaryDelete.accBits ⟨[],(CanonicalMergePath.deleteSuffix
      (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q copy C i U []).1,
      (CanonicalMergePath.deleteSuffix (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q copy C i U []).2⟩ := by
  unfold deleted deletionInput pack
  simp only [Function.comp_apply,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  exact BinaryDelete.run_pack distance loc F Q v z lam copy C i U []
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (copy : Label (Fin m) → Label (Fin m))
    (C U : List (Label (Fin m))) (i : Label (Fin m)) :
    run (pack (BinaryFiniteContext.pack distance loc F Q v z lam) C U i (copy i))=
    encode [labels (CanonicalMergePath.advancePrefix
      (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q copy C U i).1,
      historyBits (CanonicalMergePath.advancePrefix
      (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q copy C U i).2] := by
  simp only [run,vertices,lastVertex,firstVertex,suffix,Function.comp_apply,deleted_pack]
  simp only [pack,BinaryDelete.accBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  simp only [CanonicalMergePath.advancePrefix,BinaryFiniteContext.labels_append,BinaryFiniteContext.labels_cons,
    BinaryFiniteContext.labels_nil,BinaryFiniteMachine.historyBits_cons,BinaryFiniteMachine.historyBits_append,
    BinaryFiniteMachine.historyBits_nil]
end MetricKMedianRecovery.BitMachine.BinaryAdvance

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchFold
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMatch
open WordOperations WordList RationalLeaves CanonicalMatch
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

attribute [local irreducible] BinaryLabel.copied
attribute [local irreducible] advanced

lemma advanced_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (key : ℕ)
    (s : Acc (Label (Fin m))) (a : Label (Fin m)) :
    advanced (pairBits (contextBits (BinaryFiniteContext.pack distance loc F Q v z lam) key F,
      pairBits (BinaryLabel.encode a,accBits s)))=
      encode [labels (CanonicalMergePath.advancePrefix
        (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) s.front s.rest a).1,
        historyBits (CanonicalMergePath.advancePrefix
        (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) s.front s.rest a).2] := by
  unfold advanced advancingInput copied cf sf item contextBits accBits
  simp only [Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryLabel.copied_pack]
  exact BinaryAdvance.run_pack distance loc F Q v z lam (copy key) s.front s.rest a
lemma step_pack_s238_oai {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (key : ℕ)
    (s : Acc (Label (Fin m))) (a : Label (Fin m)) :
    step (pairBits (contextBits (BinaryFiniteContext.pack distance loc F Q v z lam) key F,
      pairBits (BinaryLabel.encode a,accBits s)))=
      accBits (CanonicalMatch.step (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) s a) := by
  simp only [step,front,rest,vertices,Function.comp_apply,advanced_pack]
  simp only [sf,item,extractPrefix_pairBits,discardPrefix_pairBits,accBits,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  simp only [CanonicalMatch.step,BinaryFiniteContext.labels_append,BinaryFiniteContext.labels_cons,
    BinaryFiniteContext.labels_nil,BinaryFiniteMachine.historyBits_append]
end MetricKMedianRecovery.BitMachine.BinaryMatch

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.step_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.step_pack_s238_oai
