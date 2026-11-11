-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.run_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:51:36.794342+00:00
-- url     : https://prove2.me/submissions/b9354d28-85ff-4906-a8c6-a59530786371

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K022
import Definitions.Def_Q238K030
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryLocalSearch_iterate_pack_s238

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic
namespace RationalMin
open WordList

lemma fold_lower (qs : List ℚ) (a u : ℚ) (ha : u≤a) (hq : ∀ q∈qs,u≤q) : u≤qs.foldl min a := by
  induction qs generalizing a with
  | nil=>exact ha
  | cons q qs ih=>
    rw [List.foldl_cons]
    exact ih (min a q) (le_min ha (hq q (by simp))) (by intro r hr; exact hq r (by simp [hr]))
lemma fold_le_init (qs : List ℚ) (a : ℚ) : qs.foldl min a≤a := by
  induction qs generalizing a with
  | nil=>exact le_rfl
  | cons q qs ih=>exact (ih (min a q)).trans (min_le_left a q)
lemma fold_le_mem (qs : List ℚ) (a q : ℚ) (hq : q∈qs) : qs.foldl min a≤q := by
  induction qs generalizing a with
  | nil=>simp only [List.not_mem_nil] at hq
  | cons r rs ih=>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hq with rfl|hq
    · exact (fold_le_init rs (min a q)).trans (min_le_right a q)
    · exact ih (min a r) hq
lemma minimum_lower (qs : List ℚ) (u : ℚ) (hne : qs≠[]) (hu : ∀q∈qs,u≤q) : u ≤ minimum qs := by
  cases qs with
  | nil=>exact (hne rfl).elim
  | cons q qs=>
    apply fold_lower
    · exact hu q (by simp)
    · exact hu
lemma minimum_le_mem (qs : List ℚ) (q : ℚ) (hq : q∈qs) : minimum qs≤q := fold_le_mem qs _ q hq
end RationalMin
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
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_StateBits2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordList RationalLeaves
lemma labels_length {m r B : ℕ} (xs : List (Label (Fin m))) (hn : xs.length ≤ r)
    (hB : ∀ x∈xs,(BinaryLabel.encode x).length≤B) :
    (labels xs).length ≤ r*(2*B+2) := by
  have h:=encode_le_bound (xs.map BinaryLabel.encode) B (by
    intro w hw
    obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hw
    exact hB x hx)
  simp only [List.length_map] at h
  exact h.trans (Nat.mul_le_mul_right _ hn)
lemma setBits_length {m r B : ℕ} (S : Finset (Label (Fin m))) (hn : S.card ≤ r)
    (hB : ∀ x∈S,(BinaryLabel.encode x).length≤B) :
    (setBits S).length ≤ r*(2*B+2) := by
  apply labels_length _ (by simpa only [BinaryLabel.orderedSort,Finset.length_sort] using hn)
  intro x hx
  exact hB x (Finset.mem_sort _ |>.mp hx)
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ClassSlotsMem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

variable [DecidableEq V]

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

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SmallSubsets
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [DecidableEq V]

lemma mem_smallSubsets (S R : Finset V) (w : ℕ) :
    R ∈ smallSubsets S w ↔ R ⊆ S ∧ R.card ≤ w := by
  simp only [smallSubsets,Finset.mem_biUnion,Finset.mem_range,Finset.mem_powersetCard]
  constructor
  · rintro ⟨r,hr,hRS,hR⟩
    exact ⟨hRS,by omega⟩
  · rintro ⟨hRS,hR⟩
    exact ⟨R.card,by omega,hRS,rfl⟩

lemma candidate_mem_self (F S : Finset V) (w : ℕ) : S ∈ exchangeCandidates F S w := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨(∅,∅),?_,by simp⟩,rfl⟩
  apply Finset.mem_product.mpr
  constructor <;> apply (mem_smallSubsets _ _ w).mpr <;> simp

lemma candidate_properties (F S T : Finset V) (w : ℕ) (hSF : S ⊆ F)
    (hT : T ∈ exchangeCandidates F S w) :
    T ⊆ F ∧ T.card = S.card ∧ (S \ T).card ≤ w ∧ (T \ S).card ≤ w := by
  rcases Finset.mem_filter.mp hT with ⟨hm,hcard⟩
  rcases Finset.mem_image.mp hm with ⟨⟨R,A⟩,hra,rfl⟩
  rcases Finset.mem_product.mp hra with ⟨hr,ha⟩
  rcases (mem_smallSubsets _ _ _).mp hr with ⟨hRS,hrc⟩
  rcases (mem_smallSubsets _ _ _).mp ha with ⟨hAF,hac⟩
  have hdiff := exchange_diff_bounds S R A
  exact ⟨Finset.union_subset (Finset.sdiff_subset.trans hSF) hAF,hcard,
    (Finset.card_le_card hdiff.1).trans hrc,(Finset.card_le_card hdiff.2).trans hac⟩

lemma candidate_of_exchange (F S T : Finset V) (w : ℕ) (hTF : T ⊆ F)
    (hcard : T.card = S.card) (hR : (S \ T).card ≤ w) (hA : (T \ S).card ≤ w) :
    T ∈ exchangeCandidates F S w := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨(S \ T,T \ S),?_,?_⟩,hcard⟩
  · exact Finset.mem_product.mpr ⟨(mem_smallSubsets _ _ _).mpr ⟨Finset.sdiff_subset,hR⟩,
      (mem_smallSubsets _ _ _).mpr ⟨Finset.sdiff_subset.trans hTF,hA⟩⟩
  · ext x
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [DecidableEq V]

lemma mem_widthLists (fs : List V) (w : ℕ) (R : Finset V) :
    R ∈ widthLists fs w ↔ R ⊆ fs.toFinset ∧ R.card ≤ w := by
  induction w generalizing R with
  | zero =>
    constructor
    · intro h
      have he : R = ∅ := by simpa only [widthLists,List.mem_singleton] using h
      subst R
      simp
    · rintro ⟨_,hc⟩
      have he : R = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hc)
      simp only [widthLists,List.mem_singleton,he]
  | succ w ih =>
    simp only [widthLists,List.mem_append,List.mem_flatMap,List.mem_map]
    constructor
    · rintro (h | ⟨i,hi,T,hT,rfl⟩)
      · exact ⟨(ih R).mp h |>.1, Nat.le_succ_of_le ((ih R).mp h |>.2)⟩
      · rcases (ih T).mp hT with ⟨hTF,hTw⟩
        exact ⟨Finset.insert_subset (List.mem_toFinset.mpr hi) hTF,
          (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hTw 1)⟩
    · rintro ⟨hRF,hRw⟩
      by_cases hc : R.card ≤ w
      · exact Or.inl ((ih R).mpr ⟨hRF,hc⟩)
      · have hR : R.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨i,hi⟩ := hR
        refine Or.inr ⟨i,List.mem_toFinset.mp (hRF hi),R.erase i,?_,Finset.insert_erase hi⟩
        apply (ih (R.erase i)).mpr
        exact ⟨Finset.erase_subset _ _ |>.trans hRF,by rw [Finset.card_erase_of_mem hi]; omega⟩

omit [DecidableEq V] in
lemma listBest_mem (rank : V → ℕ) (seed : V) (xs : List V) :
    listBest rank seed xs = seed ∨ listBest rank seed xs ∈ xs := by
  induction xs generalizing seed with
  | nil => exact Or.inl rfl
  | cons a xs ih =>
    unfold listBest
    rcases ih (if rank a < rank seed then a else seed) with h | h
    · rw [h]
      split_ifs
      · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem _ h)

omit [DecidableEq V] in
lemma listBest_le (rank : V → ℕ) (seed : V) (xs : List V) :
    rank (listBest rank seed xs) ≤ rank seed ∧ ∀ a ∈ xs, rank (listBest rank seed xs) ≤ rank a := by
  induction xs generalizing seed with
  | nil => simp [listBest]
  | cons a xs ih =>
    have hh := ih (if rank a < rank seed then a else seed)
    have hs : rank (if rank a < rank seed then a else seed) ≤ rank seed := by
      split_ifs with h
      · exact h.le
      · exact le_rfl
    have ha : rank (if rank a < rank seed then a else seed) ≤ rank a := by
      split_ifs with h
      · exact le_rfl
      · exact le_of_not_gt h
    refine ⟨hh.1.trans hs,?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hh.1.trans ha
    · exact hh.2 b hb

lemma mem_exchangeList (fs : List V) (S T : Finset V) (w : ℕ) (hSF : S ⊆ fs.toFinset) :
    T ∈ exchangeList fs S w ↔ T ∈ exchangeCandidates fs.toFinset S w := by
  simp only [exchangeList,List.mem_filter,List.mem_flatMap,List.mem_map,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨R,hR,A,hA,rfl⟩,hcard⟩
    rcases (mem_widthLists fs w R).mp hR with ⟨_,hRw⟩
    rcases (mem_widthLists fs w A).mp hA with ⟨hAF,hAw⟩
    have hd := exchange_diff_bounds S R A
    exact candidate_of_exchange _ _ _ _
      (Finset.union_subset (Finset.sdiff_subset.trans hSF) hAF) hcard
      ((Finset.card_le_card hd.1).trans hRw) ((Finset.card_le_card hd.2).trans hAw)
  · intro h
    have hp := candidate_properties _ _ _ _ hSF h
    refine ⟨⟨S \ T,(mem_widthLists fs w _).mpr ⟨Finset.sdiff_subset.trans hSF,hp.2.2.1⟩,
      T \ S,(mem_widthLists fs w _).mpr ⟨Finset.sdiff_subset.trans hp.1,hp.2.2.2⟩,?_⟩,hp.2.1⟩
    ext i
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto

lemma executableStep_mem (fs : List V) (rank : Finset V → ℕ) (w : ℕ) (S : Finset V)
    (hSF : S ⊆ fs.toFinset) : executableStep fs rank w S ∈ exchangeCandidates fs.toFinset S w := by
  rcases listBest_mem rank S (exchangeList fs S w) with h | h
  · change listBest rank S (exchangeList fs S w) ∈ _
    rw [h]
    exact candidate_mem_self fs.toFinset S w
  · exact (mem_exchangeList fs S _ w hSF).mp h

lemma executableStep_mono (fs : List V) (rank : Finset V → ℕ) (w : ℕ) (S : Finset V) :
    rank (executableStep fs rank w S) ≤ rank S := (listBest_le ..).1

lemma executableDescent_properties (fs : List V) (rank : Finset V → ℕ) (w n : ℕ)
    (S : Finset V) (hSF : S ⊆ fs.toFinset) :
    executableDescent fs rank w n S ⊆ fs.toFinset ∧
      (executableDescent fs rank w n S).card = S.card ∧
      rank (executableDescent fs rank w n S) ≤ rank S := by
  induction n generalizing S with
  | zero => exact ⟨hSF,rfl,le_rfl⟩
  | succ n ih =>
    have hp := candidate_properties _ _ _ _ hSF (executableStep_mem fs rank w S hSF)
    have hh := ih (executableStep fs rank w S) hp.1
    exact ⟨hh.1,hh.2.1.trans hp.2.1,hh.2.2.trans (executableStep_mono ..)⟩

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalBest
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalSearch
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_encode)
lemma length_bound {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Label (Fin m)))
    (S T : Finset (Label (Fin m))) (n : ℕ) (hT : T⊆fs.toFinset) :
    (pack distance fs T).length ≤ capPoly.eval (pairBits (List.replicate n true,pack distance fs S)).length := by
  let L := (pairBits (List.replicate n true,pack distance fs S)).length
  have hparts : (Rectangular.encode distance).length ≤ L ∧ d ≤ L ∧ (labels fs).length ≤ L := by
    simp only [L,pack,pairBits_length,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      List.length_cons,List.length_nil,List.length_replicate]
    omega
  have hc : T.card ≤ L :=
    (Finset.card_le_card hT).trans ((List.toFinset_card_le fs).trans ((BinaryFiniteContext.length_labels_le fs).trans hparts.2.2))
  have hs : (setBits T).length ≤ L*(2*L+2) :=
    BinaryFiniteContext.setBits_length T hc (fun i hi=>
      (BinaryFiniteContext.member_labels_length (List.mem_toFinset.mp (hT hi))).trans hparts.2.2)
  change (pack distance fs T).length ≤ capPoly.eval L
  simp only [pack,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil,List.length_replicate,capPoly,
    Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  nlinarith [hparts.1,hparts.2.1,hparts.2.2]
lemma run_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Label (Fin m)))
    (S : Finset (Label (Fin m))) (w n : ℕ) (hS : S⊆fs.toFinset) :
    run w (pairBits (List.replicate n true,pack distance fs S))=setBits
      (LocalSearch.executableDescent fs (fun T=>⌈BinaryLocalCost.cost distance T⌉₊) w n S) := by
  let x := pairBits (List.replicate n true,pack distance fs S)
  have hbound : ∀ j,((step w)^[j] (pack distance fs S)).length ≤ capPoly.eval x.length := by
    intro j
    rw [iterate_pack_s238]
    exact length_bound distance fs S _ n
      (LocalSearch.executableDescent_properties fs (fun T=>⌈BinaryLocalCost.cost distance T⌉₊) w j S hS).1
  simp only [run,Function.comp_apply,iterationInput,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [BoundedIteration.run_eq]
  · rw [List.length_replicate,iterate_pack_s238]
    simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  · intro j _
    rw [capacity.word_length]
    exact hbound j
end MetricKMedianRecovery.BitMachine.BinaryLocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalTransport
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
lemma widthLists_map (f : V→W) (fs : List V) (w : ℕ) :
    widthLists (fs.map f) w=(widthLists fs w).map (Finset.image f) := by
  induction w with
  | zero=>simp only [widthLists,List.map_cons,List.map_nil,Finset.image_empty]
  | succ w ih=>
    simp only [widthLists,ih,List.map_append,List.flatMap_map,List.map_flatMap,List.map_map]
    congr 1
    apply congrArg (fun g=>fs.flatMap g)
    funext i
    apply List.map_congr_left
    intro S _
    exact (Finset.image_insert f i S).symm
lemma exchangeList_map (f : V→W) (hf : Function.Injective f) (fs : List V) (S : Finset V) (w : ℕ) :
    exchangeList (fs.map f) (S.image f) w=(exchangeList fs S w).map (Finset.image f) := by
  simp only [exchangeList,widthLists_map,List.flatMap_map,List.map_map,Function.comp_def]
  have he : (widthLists fs w).flatMap (fun R=>(widthLists fs w).map (fun A=>(S.image f \ R.image f) ∪ A.image f))=
      (widthLists fs w).flatMap (fun R=>(widthLists fs w).map (fun A=>((S\R) ∪ A).image f)) := by
    apply congrArg (fun g=>(widthLists fs w).flatMap g)
    funext R
    apply List.map_congr_left
    intro A _
    rw [Finset.image_union,Finset.image_sdiff S R hf]
  rw [he]
  have hm : (widthLists fs w).flatMap (fun R=>(widthLists fs w).map (fun A=>((S\R) ∪ A).image f))=
      ((widthLists fs w).flatMap (fun R=>(widthLists fs w).map (fun A=>(S\R) ∪ A))).map (Finset.image f) := by
    simp only [List.map_flatMap,List.map_map,Function.comp_def]
  rw [hm,List.filter_map]
  simp only [Function.comp_def,Finset.card_image_of_injective _ hf]
omit [DecidableEq V] [DecidableEq W] in
lemma listBest_map (f : V→W) (r : V→ℕ) (s : W→ℕ) (h : ∀ a,s (f a)=r a)
    (a : V) (xs : List V) : listBest s (f a) (xs.map f)=f (listBest r a xs) := by
  induction xs generalizing a with
  | nil=>rfl
  | cons b xs ih=>
    simp only [List.map_cons,listBest,h]
    split_ifs <;> exact ih _
lemma executableStep_map (f : V→W) (hf : Function.Injective f) (fs : List V)
    (r : Finset V→ℕ) (s : Finset W→ℕ) (h : ∀ T,s (T.image f)=r T) (S : Finset V) (w : ℕ) :
    executableStep (fs.map f) s w (S.image f)=(executableStep fs r w S).image f := by
  rw [executableStep,exchangeList_map f hf]
  exact listBest_map (Finset.image f) r s h S _
lemma executableDescent_map (f : V→W) (hf : Function.Injective f) (fs : List V)
    (r : Finset V→ℕ) (s : Finset W→ℕ) (h : ∀ T,s (T.image f)=r T) (S : Finset V) (w n : ℕ) :
    executableDescent (fs.map f) s w n (S.image f)=(executableDescent fs r w n S).image f := by
  induction n generalizing S with
  | zero=>rfl
  | succ n ih=>rw [executableDescent,executableStep_map f hf fs r s h,ih]; rfl
end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_LocalIntegral
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalCost
open RationalLeaves
lemma connection_nat {m d : ℕ} (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
    (S : Finset (Fin m)) (j : Fin d) :
    connection (fun i j=>(δ (loc j) i:ℚ)) (S.image original) j=(LocalSearch.natConnection δ S (loc j):ℚ) := by
  by_cases hS : S.Nonempty
  · obtain ⟨i,hi,hei⟩:=Finset.exists_mem_eq_inf' hS (δ (loc j))
    rw [LocalSearch.natConnection,dite_eq_left hS,hei]
    apply le_antisymm
    · apply RationalMin.minimum_le_mem
      exact List.mem_map.mpr ⟨original i,(Finset.mem_sort _).mpr (Finset.mem_image.mpr ⟨i,hi,rfl⟩),rfl⟩
    · apply RationalMin.minimum_lower
      · intro hempty
        have hm : (δ (loc j) i:ℚ) ∈ (BinaryLabel.orderedSort (S.image original)).map
            (fun a=>rows (fun i j=>(δ (loc j) i:ℚ)) a j) :=
          List.mem_map.mpr ⟨original i,(Finset.mem_sort _).mpr (Finset.mem_image.mpr ⟨i,hi,rfl⟩),rfl⟩
        rw [hempty] at hm
        exact List.not_mem_nil hm
      · intro q hq
        obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hq
        obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp ((Finset.mem_sort _).mp ha)
        change (δ (loc j) i:ℚ) ≤ δ (loc j) b
        exact_mod_cast (show δ (loc j) i ≤ δ (loc j) b by rw [←hei]; exact Finset.inf'_le _ hb)
  · have he : S=∅:=Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    rw [LocalSearch.natConnection,dite_eq_right hS]
    simp only [connection,Finset.image_empty,BinaryLabel.orderedSort,Finset.sort_empty,List.map_nil,
      RationalMin.minimum,List.head?_nil,Option.getD_none,List.foldl_nil,Nat.cast_zero]
lemma cost_nat {m d : ℕ} (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
    (hloc : Function.Injective loc) (S : Finset (Fin m)) :
    cost (fun i j=>(δ (loc j) i:ℚ)) (S.image original)=
      (LocalSearch.natCost δ (Finset.univ.image loc) S:ℚ) := by
  simp only [cost,connection_nat,LocalSearch.natCost,Nat.cast_sum]
  rw [Finset.sum_image (fun a _ b _ hab=>hloc hab)]
lemma rank_nat {m d : ℕ} (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
    (hloc : Function.Injective loc) (S : Finset (Fin m)) :
    ⌈cost (fun i j=>(δ (loc j) i:ℚ)) (S.image original)⌉₊=
      LocalSearch.natCost δ (Finset.univ.image loc) S := by
  rw [cost_nat δ loc hloc,Nat.ceil_natCast]
end MetricKMedianRecovery.BitMachine.BinaryLocalCost

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalFuel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalSearch
open WordOperations WordList RationalLeaves
open BinaryFiniteContext (labels setBits)
lemma run_input_length (w : ℕ) (u v x : List Bool) (h : u.length=v.length) :
    run w (pairBits (u,x))=run w (pairBits (v,x)) := by
  simp only [run,Function.comp_apply,iterationInput,extractPrefix_pairBits,discardPrefix_pairBits,
    BoundedIteration.run_pair,capacity.word_length,pairBits_length,h]
lemma run_word {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Label (Fin m)))
    (S : Finset (Label (Fin m))) (w : ℕ) (u : List Bool) (hS : S⊆fs.toFinset) :
    run w (pairBits (u,pack distance fs S))=setBits
      (LocalSearch.executableDescent fs (fun T=>⌈BinaryLocalCost.cost distance T⌉₊) w u.length S) := by
  rw [run_input_length w u (List.replicate u.length true) _ (List.length_replicate ..).symm]
  exact run_pack distance fs S w u.length hS
end MetricKMedianRecovery.BitMachine.BinaryLocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalRefineMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalRefine
open RationalLeaves WordOperations WordList Polynomial
lemma run_pack_s238_oai {m d : ℕ} (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
    (hloc : Function.Injective loc) (fs : List (Fin m)) (S : Finset (Fin m)) (hS : S⊆fs.toFinset) :
    run (pack (fun i j=>(δ (loc j) i:ℚ)) fs S)=BinaryFiniteContext.setBits
      ((LocalSearch.executableDescent fs (LocalSearch.natCost δ (Finset.univ.image loc)) 5
        (BinaryLocalAnchor.fuelPoly.eval (pack (fun i j=>(δ (loc j) i:ℚ)) fs S).length) S).image original) := by
  rw [run,pack,BinaryLocalSearch.run_word]
  · rw [BinaryLocalAnchor.fuel.word_length,LocalSearch.executableDescent_map original original.injective fs _ _
      (BinaryLocalCost.rank_nat δ loc hloc)]
  · intro a ha
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp ha
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨b,List.mem_toFinset.mp (hS hb),rfl⟩)
end MetricKMedianRecovery.BitMachine.BinaryLocalRefine

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.run_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.run_pack_s238_oai
