-- Prove2me | solution 1 for OAI.CommonBasesFPRAS.MachineCode.Effect.safe_algorithmHistory
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T01:26:49.197309+00:00
-- url     : https://prove2.me/submissions/17f0013d-4e64-4a98-86b6-898dade09477

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_OAIQ2Mt000
import Theorems.Thm_OAI_CommonBasesFPRAS_MachineCode_Effect_safe_historyTick

section
-- module Solutions.OAIQ2_Mat.MatroidCounting_CommonBases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CommonBasesFPRAS

section

section
open scoped RealInnerProductSpace BigOperators Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

open scoped BigOperators Classical

open Set

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
namespace FiniteChain
open scoped BigOperators Classical
variable {X : Type*} [sectionInstance101 : Fintype X]
universe u

omit sectionInstance101 in
lemma Sample.toList_length [Fintype X] {k : ℕ} (v : Sample X k) : v.toList.length=k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg Nat.succ (ih v.2)
end FiniteChain
open scoped BigOperators Classical

end

open scoped BigOperators Classical

section ActualSize
open scoped BigOperators Classical
lemma indicator_list_sum {X : Type*} (P : X → Prop) (l : List X) :
    (l.map (fun x => if P x then (1:ℚ) else 0)).sum=(l.countP (fun x => decide (P x)):ℚ) := by
  induction l with
  | nil => simp
  | cons x l ih => by_cases hx : P x <;> simp [hx,ih,add_comm]
variable {Γ : Type*} [sectionInstance118 : Fintype Γ] [sectionInstance119 : DecidableEq Γ]
omit sectionInstance118 sectionInstance119 in
lemma rationalTypeRatio [Fintype Γ] [DecidableEq Γ] (gs : List (Γ × Γ)) (l : List (Set Γ)) (p r : Γ × Γ) :
    rationalEmpirical (rationalPlain gs (fun _ => 1)) l /
      rationalEmpirical (rationalDefect gs p r) l =
      (l.countP (fun S => decide (PlainState gs S)):ℚ)/
        (l.countP (fun S => decide (DefectState gs p r S)):ℚ) := by
  unfold rationalEmpirical rationalPlain rationalDefect
  rw [indicator_list_sum,indicator_list_sum]
  by_cases hz : l.length=0
  · have he : l=[] := List.length_eq_zero_iff.mp hz
    simp [he]
  · exact div_div_div_cancel_right₀ (by exact_mod_cast hz : (l.length:ℚ)≠0) _ _
end ActualSize

open scoped BigOperators Classical

namespace DrawTree
variable {A B C : Type*}
lemma bind_assoc (t : DrawTree A) (f : A → DrawTree B) (g : B → DrawTree C) :
    (t.bind f).bind g=t.bind (fun a => (f a).bind g) := by
  induction t with
  | leaf a => rfl
  | draw v k ih => simp only [bind,ih]
end DrawTree
open scoped BigOperators Classical
open scoped BigOperators Classical

open scoped BigOperators Classical

section GreedyOracle
variable {α : Type*} [sectionInstance120 : DecidableEq α]

lemma greedyOracle_correct (M : Matroid α) (O : Finset α → Bool)
    (hO : ∀ I,O I = true ↔ M.Indep (I : Set α)) (l : List α)
    (hE : ∀ a ∈ l,a ∈ M.E) : M.IsBasis (greedyOracle O l : Set α) (l.toFinset : Set α) := by
  induction l with
  | nil => simp [greedyOracle]
  | cons a l ih =>
    have hi := ih (fun x hx => hE x (by simp [hx]))
    have ha := hE a (by simp)
    simp only [greedyOracle]
    split_ifs with h
    · have hind := (hO _).mp h
      apply hind.isBasis_of_subset_of_subset_closure
      · simpa only [List.toFinset_cons,Finset.coe_insert] using Set.insert_subset_insert hi.subset
      · simp only [List.toFinset_cons,Finset.coe_insert]
        apply Set.insert_subset
        · simpa only [Finset.coe_insert] using M.subset_closure _ hind.subset_ground (Finset.mem_insert_self a _)
        · exact hi.subset_closure.trans (M.closure_mono (by simp))
    · apply hi.indep.isBasis_of_subset_of_subset_closure
      · exact hi.subset.trans (by simp)
      · simp only [List.toFinset_cons,Finset.coe_insert]
        apply Set.insert_subset
        · apply hi.indep.mem_closure_iff'.mpr
          refine ⟨ha,?_⟩
          intro hind
          exfalso
          exact h ((hO _).mpr (by simpa using hind))
        · exact hi.subset_closure

lemma greedyOracle_rank (M : Matroid α) (O : Finset α → Bool)
    (hO : ∀ I,O I = true ↔ M.Indep (I : Set α)) (l : List α)
    (hE : ∀ a ∈ l,a ∈ M.E) :
    (greedyOracle O l).card = (M.eRk (l.toFinset : Set α)).toNat := by
  have h := (greedyOracle_correct M O hO l hE).encard_eq_eRk
  simpa using congrArg ENat.toNat h
end GreedyOracle

open scoped Classical

lemma queryFinset_exact {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (which : Bool) (I : Finset (Fin n)) :
    queryFinset O which I = true ↔ (if which then M₂ else M₁).Indep (I : Set (Fin n)) := by
  have h := hO which (fun i => decide (i ∈ I))
  have he : {i : Fin n | decide (i ∈ I) = true} = (I : Set (Fin n)) := by ext i; simp
  rw [he] at h
  exact h
lemma rankOracle_correct {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (which : Bool) (S : Finset (Fin n)) :
    rankOracle O which S = ((if which then M₂ else M₁).eRk (S : Set (Fin n))).toNat := by
  have hE : (if which then M₂ else M₁).E = Set.univ := by cases which <;> simpa
  have h := greedyOracle_rank (if which then M₂ else M₁) (queryFinset O which)
    (queryFinset_exact M₁ M₂ O hO which) ((List.finRange n).filter (fun i => decide (i ∈ S)))
    (by intro i _; simp [hE])
  have hs : (((List.finRange n).filter (fun i => decide (i ∈ S))).toFinset : Set (Fin n)) = S := by
    ext i; simp
  rw [hs] at h
  exact h

open scoped Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

section
namespace DrawTree
open scoped BigOperators Classical
variable {A B : Type*}

lemma Reindexed.refl (t : DrawTree A) : Reindexed t t := by
  induction t with
  | leaf a => exact .leaf a
  | draw v k ih => exact .draw v k k (Equiv.refl _) ih
lemma Reindexed.symm {t u : DrawTree A} (h : Reindexed t u) : Reindexed u t := by
  induction h with
  | leaf a => exact .leaf a
  | draw v k l e h ih =>
    apply Reindexed.draw v l k e.symm
    intro i
    simpa using ih (e.symm i)
lemma Reindexed.bind {t u : DrawTree A} {k l : A → DrawTree B}
    (ht : Reindexed t u) (hk : ∀ a,Reindexed (k a) (l a)) :
    Reindexed (t.bind k) (u.bind l) := by
  induction ht with
  | leaf a => exact hk a
  | draw v a b e h ih => exact .draw v _ _ e ih
lemma Reindexed.map {t u : DrawTree A} (h : Reindexed t u) (f : A → B) :
    Reindexed (t.map f) (u.map f) := h.bind (fun a => .leaf (f a))
lemma uniformVia_reindexed (A : Type*) [Fintype A] [Nonempty A]
    (e : Fin (Fintype.card A) ≃ A) : Reindexed (uniformVia A e) (uniformChoice A) := by
  let h : Fintype.card A-1+1=Fintype.card A := by have hh := Fintype.card_pos (α := A); omega
  let c := finCongr h
  let p := c.trans (e.trans ((Fintype.equivFin A).trans c.symm))
  apply Reindexed.draw _ _ _ p
  intro i
  have he : (Fintype.equivFin A).symm (Fin.cast h (p i))=e (Fin.cast h i) := by simp [p,c]
  simpa only [he] using Reindexed.leaf (e (Fin.cast h i))
lemma Reindexed.all {t u : DrawTree A} (h : Reindexed t u) (P : A → Prop)
    (ht : All P t) : All P u := by
  induction h with
  | leaf a => exact ht
  | draw v k l e h ih =>
    intro i
    simpa using ih (e.symm i) (ht (e.symm i))
end DrawTree

open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (r : ℕ) (O : IndependenceOracle n) (N L : ℕ)
local notation "GS" => pairedSlots n
lemma canonicalMetropolis_reindexed (w : ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) →
    ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ℚ) (f : Set (Fin n ⊕ Fin n) → ℚ)
    (S : ChainIndex GS) : DrawTree.Reindexed (canonicalMetropolis n hn w f S)
      (rationalMetropolis GS (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n) w f S) := by
  let : Nonempty (ExchangeChoice S.val) := Fintype.card_pos_iff.mp (by
    rw [exchangeChoice_card GS (pairedSlots_fresh n) (pairedSlots_cover n),pairedSlots_length]; positivity)
  apply (DrawTree.Reindexed.refl (DrawTree.bernoulli (1/2))).bind
  intro lazy
  cases lazy with
  | true => exact .leaf S
  | false =>
    apply (DrawTree.uniformVia_reindexed _ (canonicalExchangeEnumeration n S.val)).bind
    intro a; exact .refl _

end

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

section

variable {k n : ℕ}
lemma incrementBits_correct (xs : List Bool) : binaryValue (incrementBits xs)=binaryValue xs+1 := by
  induction xs with
  | nil => simp [incrementBits,leadingOnes,carryTail,binaryValue]
  | cons x xs ih =>
    cases x with
    | false => simp [incrementBits,leadingOnes,carryTail,binaryValue,Nat.add_comm]
    | true =>
      have he : incrementBits (true::xs)=false::incrementBits xs := by simp [incrementBits,leadingOnes,carryTail,List.replicate_succ]
      rw [he,binaryValue,binaryValue,ih]
      simp; omega

end

open scoped Classical

section

variable {k n : ℕ}
lemma wordGreedy_length (W : List Bool → Bool) (xs ps : List Bool) :
    (wordGreedy W xs ps).length=xs.length+ps.length := by
  induction xs generalizing ps with
  | nil => simp [wordGreedy]
  | cons b xs ih => simp [wordGreedy,ih,Nat.add_comm,Nat.add_left_comm]

end

section

variable {n : ℕ}
lemma wordSet_zero_succ (m : ℕ) (ps : List Bool) :
    wordSet n (List.replicate (m+1) false++ps)=wordSet n (List.replicate m false++false::ps) := by
  congr 1
  rw [List.replicate_add,List.replicate_one,List.append_assoc,List.singleton_append]
lemma wordSet_bit (as ps : List Bool) (h : as.length<n) :
    wordSet n (as++true::ps)=insert (⟨as.length,h⟩ : Fin n) (wordSet n (as++false::ps)) := by
  ext i
  simp only [wordSet,Set.mem_ofPred_eq,Set.mem_insert_iff,Fin.ext_iff]
  by_cases hi : i.val<as.length
  · rw [List.getElem?_append_left hi,List.getElem?_append_left hi]
    have hh : ¬i.val=as.length := by omega
    simp [hh]
  · have hle : as.length≤ i.val := by omega
    rw [List.getElem?_append_right hle,List.getElem?_append_right hle]
    by_cases he : i.val=as.length
    · simp [he]
    · obtain ⟨j,hj⟩ : ∃j,i.val-as.length=j+1 := ⟨i.val-as.length-1,by omega⟩
      simp [he,hj]
lemma wordSet_zero_subset (xs ps : List Bool) :
    wordSet n (List.replicate xs.length false++ps) ⊆ wordSet n (xs++ps) := by
  intro i hi
  simp only [wordSet,Set.mem_ofPred_eq] at *
  by_cases h : i.val<xs.length
  · rw [List.getElem?_append_left (by simpa using h),List.getElem?_replicate] at hi
    simp [h] at hi
  · have hle : xs.length≤ i.val := by omega
    rw [List.getElem?_append_right (by simpa using hle)] at hi
    rw [List.getElem?_append_right hle]
    simpa using hi
lemma wordSet_ofFn (f : Fin n → Bool) : wordSet n (List.ofFn f)={i | f i=true} := by
  ext i
  simp [wordSet]
lemma wordSet_zeros (m : ℕ) : wordSet n (List.replicate m false)=∅ := by
  ext i
  simp only [wordSet,Set.mem_ofPred_eq,List.getElem?_replicate,Set.mem_empty_iff_false,iff_false]
  split_ifs <;> simp

theorem wordGreedy_basis (M : Matroid (Fin n)) (hE : M.E=Set.univ)
    (W : List Bool → Bool) (hW : ∀l,l.length=n → (W l=true ↔ M.Indep (wordSet n l)))
    (xs ps : List Bool) (hn : xs.length+ps.length=n)
    (hI : M.Indep (wordSet n (List.replicate xs.length false++ps))) :
    M.IsBasis (wordSet n (wordGreedy W xs ps)) (wordSet n (xs.reverse++ps)) := by
  induction xs generalizing ps with
  | nil => simpa [wordGreedy] using hI.isBasis_self
  | cons b xs ih =>
    have hlen : xs.length+(b::ps).length=n := by simp only [List.length_cons] at *; omega
    have ha : xs.length<n := by simp only [List.length_cons] at hn; omega
    let a : Fin n := ⟨xs.length,ha⟩
    have hI' : M.Indep (wordSet n (List.replicate xs.length false++false::ps)) := by
      simpa only [List.length_cons,wordSet_zero_succ] using hI
    have hbit : wordSet n (List.replicate xs.length false++true::ps)=
        insert a (wordSet n (List.replicate xs.length false++false::ps)) := by
      simpa [a] using wordSet_bit (n:=n) (List.replicate xs.length false) ps (by simpa using ha)
    have hbit' : wordSet n (xs.reverse++true::ps)=insert a (wordSet n (xs.reverse++false::ps)) := by
      simpa [a] using wordSet_bit (n:=n) xs.reverse ps (by simpa using ha)
    have hqueryLen : (List.replicate xs.length false++true::ps).length=n := by
      simp only [List.length_append,List.length_replicate,List.length_cons]
      simp only [List.length_cons] at hn
      omega
    cases b with
    | false => simpa [wordGreedy,List.reverse_cons,List.append_assoc] using ih (false::ps) hlen hI'
    | true =>
      cases hq : W (List.replicate xs.length false++true::ps) with
      | true =>
        have hJ := (hW _ hqueryLen).mp hq
        simpa [wordGreedy,hq,List.reverse_cons,List.append_assoc] using ih (true::ps) hlen hJ
      | false =>
        have hJ := ih (false::ps) (by simpa using hlen) hI'
        have han : ¬M.Indep (insert a (wordSet n (List.replicate xs.length false++false::ps))) := by
          rw [←hbit]
          intro h
          have := (hW _ hqueryLen).mpr h
          simp [hq] at this
        have hac : a ∈ M.closure (wordSet n (List.replicate xs.length false++false::ps)) :=
          hI'.mem_closure_iff'.mpr ⟨by simp [hE],fun h => (han h).elim⟩
        have hsub : wordSet n (List.replicate xs.length false++false::ps) ⊆ wordSet n (xs.reverse++false::ps) := by
          simpa using wordSet_zero_subset (n:=n) xs.reverse (false::ps)
        have hac' : a ∈ M.closure (wordSet n (wordGreedy W xs (false::ps))) := by
          rw [hJ.closure_eq_closure]
          exact M.closure_mono hsub hac
        have hB := hJ.indep.isBasis_of_subset_of_subset_closure
          (hJ.subset.trans (Set.subset_insert a _)) (Set.insert_subset hac' hJ.subset_closure)
        simpa [wordGreedy,hq,List.reverse_cons,List.append_assoc,hbit'] using hB

end

section

variable {k n : ℕ}
lemma incrementBits_length (ys : List Bool) : (incrementBits ys).length≤ys.length+1 := by
  induction ys with
  | nil => simp [incrementBits,leadingOnes,carryTail]
  | cons b ys ih =>
    cases b <;> simp only [incrementBits,leadingOnes,carryTail,List.length_append,List.length_replicate,
      List.length_cons] at * <;> omega

lemma popcount_value (xs ys : List Bool) :
    binaryValue (popcountBits xs ys)=binaryValue ys+xs.count true := by
  induction xs generalizing ys with
  | nil => simp [popcountBits]
  | cons b xs ih => cases b <;> simp [popcountBits,ih,incrementBits_correct,_root_.Nat.add_comm,_root_.Nat.add_assoc]

end

section
open scoped BigOperators Classical
variable {k n : ℕ}
lemma count_ofFn (n : ℕ) (f : Fin n → Bool) :
    (List.ofFn f).count true=∑i,if f i then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,Fin.sum_univ_succ]
    cases hf : f 0 <;> simp [ih,Nat.add_comm]
lemma wordSet_card (xs : List Bool) (hn : xs.length=n) :
    Fintype.card (wordSet n xs)=xs.count true := by
  subst n
  let f : Fin xs.length → Bool := fun i => xs[i.val]
  have hf : List.ofFn f=xs := List.ofFn_getElem
  have hs : wordSet xs.length xs=wordSet xs.length (List.ofFn f) := congrArg (wordSet xs.length) hf.symm
  rw [hs,wordSet_ofFn,Fintype.card_subtype,Finset.card_filter]
  have hc := count_ofFn xs.length f
  rw [hf] at hc
  exact hc.symm
lemma wordGreedy_rank (M : Matroid (Fin n)) (hE : M.E=Set.univ)
    (W : List Bool → Bool) (hW : ∀l,l.length=n → (W l=true ↔ M.Indep (wordSet n l)))
    (xs : List Bool) (hn : xs.length=n) :
    (wordGreedy W xs []).count true=(M.eRk (wordSet n xs.reverse)).toNat := by
  have h := wordGreedy_basis M hE W hW xs [] (by simpa using hn)
    (by simp [wordSet_zeros])
  simp only [List.append_nil] at h
  have hh := h.encard_eq_eRk
  rw [Set.encard_eq_coe_toFinset_card] at hh
  have hc : (wordSet n (wordGreedy W xs [])).toFinset.card=(wordGreedy W xs []).count true := by
    rw [Set.toFinset_card]
    exact wordSet_card _ (by simpa [wordGreedy_length] using hn)
  rw [hc] at hh
  simpa using congrArg ENat.toNat hh

end

section

variable {k n : ℕ}

lemma binaryValue_append (xs ys : List Bool) :
    binaryValue (xs++ys)=binaryValue xs+2^xs.length*binaryValue ys := by
  induction xs with
  | nil => simp [binaryValue]
  | cons x xs ih =>
    simp only [List.cons_append,binaryValue,ih,List.length_cons,pow_succ]
    ring

end

variable {k n : ℕ}
lemma bitFrame_length (bs : List Bool) : (bitFrame bs).length=2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [bitFrame,ih]; omega

end

namespace MachineCode

@[simp] lemma pair_length (x y : Word) : (pair x y).length=2*x.length+1+y.length := by
  simp [pair,bitFrame_length]

lemma strip_length (x : Word) : (stripZeros x).length≤x.length := by
  induction x with
  | nil => rfl
  | cons b xs ih => cases b <;> simp only [stripZeros,List.length_cons] <;> omega
lemma strip_append (x y : Word) : stripZeros (x++y)=if stripZeros x=[] then stripZeros y else stripZeros x++y := by
  induction x with
  | nil => simp [stripZeros]
  | cons b xs ih =>
    cases b <;> simp [stripZeros,ih]
    rfl

lemma normal_length (x : Word) : (normalWord x).length≤x.length := by
  simpa only [normalWord,List.length_reverse] using strip_length x.reverse
lemma normalWord_cons (b : Bool) (xs : Word) :
    normalWord (b::xs)=if normalWord xs=[] then (if b then [true] else []) else b::normalWord xs := by
  simp only [normalWord,List.reverse_cons,strip_append]
  by_cases h : stripZeros xs.reverse=[]
  · simp [h]; cases b <;> rfl
  · simp [h,List.reverse_eq_nil_iff]

lemma binaryValue_bits (n : ℕ) : binaryValue n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp [binaryValue,ih,Nat.bit]
    omega
lemma normalWord_eq_bits (xs : Word) : normalWord xs=(binaryValue xs).bits := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    rw [normalWord_cons,ih]
    by_cases hz : binaryValue xs=0
    · cases b <;> simp [binaryValue,hz]
    · have hb : (binaryValue xs).bits≠[] := by
        intro h
        have he := binaryValue_bits (binaryValue xs)
        rw [h] at he
        exact hz he.symm
      cases b with
      | false => simp [binaryValue,hb,Nat.bit0_bits _ hz]
      | true =>
        simp only [ite_true,ite_eq_right hb,binaryValue]
        rw [Nat.add_comm 1, Nat.bit1_bits]
@[simp] lemma normalWord_bits (n : ℕ) : normalWord n.bits=n.bits := by
  rw [normalWord_eq_bits,binaryValue_bits]

lemma popcountBits_length (xs ys : Word) : (popcountBits xs ys).length≤xs.length+ys.length := by
  induction xs generalizing ys with
  | nil => simp [popcountBits]
  | cons b xs ih =>
    cases b with
    | false => simpa only [popcountBits,Bool.false_eq_true,ite_false,List.length_cons] using
        (ih ys).trans (by omega)
    | true =>
      have h := ih (incrementBits ys)
      have hi := incrementBits_length ys
      simp only [popcountBits,ite_true,List.length_cons]
      omega
lemma rankBits_length {n : ℕ} (O : IndependenceOracle n) (which : Bool) (x : Word) :
    (rankBits which O x).length≤x.length := by
  simpa only [rankBits,wordGreedy_length,List.length_nil,Nat.add_zero] using
    popcountBits_length (wordGreedy (wordOracle which O) x []) []

lemma rankWord_correct {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (which : Bool) (x : Word) (hx : x.length=n) :
    rankWord O which x=((if which then M₂ else M₁).eRk (wordSet n x)).toNat := by
  simp only [rankWord,rankBits,popcount_value,binaryValue,Nat.zero_add]
  have hr := wordGreedy_rank (if which then M₂ else M₁) (by cases which <;> assumption)
    (wordOracle which O) (fun l _ => hO which (fun i => l[i.val]?.getD false)) x.reverse
    (by simpa only [List.length_reverse] using hx)
  simpa only [List.reverse_reverse] using hr
open scoped Classical in
lemma rankWord_eq_rankOracle {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (which : Bool) (x : Word) (hx : x.length=n) :
    rankWord O which x=rankOracle O which (wordSet n x).toFinset := by
  classical
  rw [rankWord_correct M₁ M₂ O hO hE₁ hE₂ which x hx,
    rankOracle_correct M₁ M₂ O hO hE₁ hE₂ which,Set.coe_toFinset]


lemma foldValue_eq_foldl {a b : DataType} (f : Value (.prod a b) → Option (Value b))
    (g : Value b → Value a → Value b) (hf : ∀ x z, f (x,z)=some (g z x))
    (xs : List (Value a)) (z : Value b) : foldValue f xs z=some (xs.foldl g z) := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih => simp [foldValue,hf,ih]

namespace Expression
variable {n : ℕ} (O : IndependenceOracle n)
lemma run_listReverse {a : DataType} (xs : List (Value a)) :
    run O listReverse xs=some xs.reverse := by
  simp only [listReverse,run]
  have h := foldValue_eq_foldl (fun p : Value (.prod a (.list a)) => some (p.1::p.2))
    (fun zs x => x::zs) (fun _ _ => rfl) xs []
  simpa using h
lemma run_mapStep {a b c : DataType} (p : Expression (.prod a c) b)
    (f : Value a → Value c → Value b) (hp : ∀ x z, run O p (x,z)=some (f x z))
    (x : Value a) (xs : List (Value b)) (z : Value c) :
    run O (mapStep p) (x,(xs,z))=some (f x z::xs,z) := by
  simp [mapStep,run,hp]
lemma run_mapWith {a b c : DataType} (p : Expression (.prod a c) b)
    (f : Value a → Value c → Value b) (hp : ∀ x z, run O p (x,z)=some (f x z))
    (xs : List (Value a)) (z : Value c) :
    run O (mapWith p) (xs,z)=some (xs.map (fun x => f x z)) := by
  have hf : ∀ (ys : List (Value a)) (acc : List (Value b)),
      foldValue (run O (mapStep p)) ys (acc,z)=some ((ys.map (fun x => f x z)).reverse++acc,z) := by
    intro ys
    induction ys with
    | nil => intro acc; rfl
    | cons x ys ih => intro acc; simp [foldValue,run_mapStep O p f hp,ih,List.append_assoc]
  simp [mapWith,run,hf,run_listReverse]
lemma run_listLength {a : DataType} (xs : List (Value a)) :
    run O listLength xs=some xs.length := by
  have hf : ∀ (ys : List (Value a)) (z : ℕ),
      foldValue (fun p : Value (.prod a .nat) => some (p.2+1)) ys z=some (z+ys.length) := by
    intro ys
    induction ys with
    | nil => intro z; simp [foldValue]
    | cons x ys ih => intro z; simpa [foldValue,ih] using congrArg some (by omega : z+1+ys.length=z+(ys.length+1))
  simp [listLength,run,hf]
lemma run_wordLength (xs : Word) : run O wordLength xs=some xs.length := by
  simp [wordLength,run,run_listLength]
lemma run_wordRepeatStep (b : Bool) (w : Word) :
    run O wordRepeatStep (b,w)=some (if b then false::(w++w) else w++w) := by
  cases b <;> rfl
lemma unary_value (xs : List Bool) (w : Word) :
    ∃ out, foldValue (run O wordRepeatStep) xs.reverse w=some out ∧
      out.length=2^xs.length*w.length+binaryValue xs := by
  induction xs generalizing w with
  | nil => exact ⟨w,rfl,by simp [binaryValue]⟩
  | cons b xs ih =>
    obtain ⟨u,hu,hl⟩ := ih w
    have happ : ∀ (ys zs : List Bool) v,
        foldValue (run O wordRepeatStep) (ys++zs) v=
          (foldValue (run O wordRepeatStep) ys v).bind (foldValue (run O wordRepeatStep) zs) := by
      intro ys
      induction ys with
      | nil => intros; rfl
      | cons y ys ih => intros; simp [foldValue,ih,Option.bind_assoc]
    refine ⟨(if b then false::(u++u) else u++u),?_,?_⟩
    · rw [List.reverse_cons,happ,hu]
      simp only [Option.bind_some,foldValue]
      rw [run_wordRepeatStep]; rfl
    · cases b <;> simp [List.length_append,hl,binaryValue,Nat.pow_succ] <;> ring
lemma run_unary (m : ℕ) : ∃ w,run O unary m=some w ∧ w.length=m := by
  obtain ⟨w,hw,hlen⟩ := unary_value O m.bits []
  refine ⟨w,?_,?_⟩
  · simpa [unary,run] using hw
  · simpa [binaryValue_bits] using hlen
end Expression

@[simp] lemma width_pair {a b : DataType} (x : Value a) (y : Value b) :
    width (a:=.prod a b) (x,y)=2*width x+1+width y := by simp [width,encode]
@[simp] lemma width_cons {a : DataType} (x : Value a) (xs : List (Value a)) :
    width (a:=.list a) (x::xs)=2*width x+2+width (a:=.list a) xs := by
  simp [width,encode,words]; omega
lemma list_length_le_width {a : DataType} (xs : List (Value a)) :
    xs.length≤width (a:=.list a) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.length_cons,width_cons]; omega

lemma safe_input {n S : ℕ} {O : IndependenceOracle n} {a b : DataType}
    {p : Expression a b} {x : Value a} (h : Safe O S p x) : width x≤S := by
  cases p <;> exact h.1
lemma safe_output {n S : ℕ} {O : IndependenceOracle n} {a b : DataType}
    {p : Expression a b} {x : Value a} (h : Safe O S p x) {y : Value b}
    (hr : run O p x=some y) : width y≤S := by
  cases p <;> exact h.2.1 y hr

lemma foldSafe_mono {A B : Type*} (p q : A×B → Prop) (f : A×B → Option B)
    (hpq : ∀ x,p x → q x) (xs : List A) (z : B) (h : FoldSafe p f xs z) :
    FoldSafe q f xs z := by
  induction xs generalizing z with
  | nil => trivial
  | cons x xs ih => exact ⟨hpq _ h.1,fun y hy => ih y (h.2 y hy)⟩
lemma safe_mono {n S T : ℕ} {O : IndependenceOracle n} {a b : DataType}
    (p : Expression a b) (x : Value a) (h : Safe O S p x) (hST : S≤T) : Safe O T p x := by
  induction p with
  | compose p q ihp ihq =>
    exact ⟨h.1.trans hST,fun y hy => (h.2.1 y hy).trans hST,
      ihp _ h.2.2.1,fun y hy => ihq _ (h.2.2.2 y hy)⟩
  | both p q ihp ihq =>
    exact ⟨h.1.trans hST,fun y hy => (h.2.1 y hy).trans hST,ihp _ h.2.2.1,ihq _ h.2.2.2⟩
  | branch p q ihp ihq =>
    refine ⟨h.1.trans hST,fun y hy => (h.2.1 y hy).trans hST,?_⟩
    rcases x with ⟨v,x⟩
    cases v <;> simp only [Bool.false_eq_true,ite_false,ite_true] at *
    · exact ihp _ h.2.2
    · exact ihq _ h.2.2
  | fold p ih =>
    exact ⟨h.1.trans hST,fun y hy => (h.2.1 y hy).trans hST,
      foldSafe_mono _ _ _ (fun x hx => ih x hx) _ _ h.2.2⟩
  | _ => exact ⟨h.1.trans hST,fun y hy => (h.2.1 y hy).trans hST,trivial⟩

lemma safe_compose {n S : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression a b) (q : Expression b c) (x : Value a)
    (hp : Safe O S p x) (hq : ∀ y,run O p x=some y → Safe O S q y) :
    Safe O S (.compose p q) x := by
  refine ⟨safe_input hp,?_,hp,hq⟩
  intro z hz
  simp only [run] at hz
  cases he : run O p x with
  | none => simp [he] at hz
  | some y =>
    simp only [he,Option.bind_some] at hz
    exact safe_output (hq y he) hz
lemma safe_both {n S : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression a b) (q : Expression a c) (x : Value a)
    (hp : Safe O S p x) (hq : Safe O S q x) :
    Safe O (3*S+1) (.both p q) x := by
  have hS : S≤3*S+1 := by omega
  refine ⟨(safe_input hp).trans hS,?_,safe_mono p x hp hS,safe_mono q x hq hS⟩
  intro z hz
  simp only [run] at hz
  cases he : run O p x with
  | none => simp [he] at hz
  | some y =>
    simp only [he] at hz
    cases hf : run O q x with
    | none => simp [hf] at hz
    | some w =>
      simp only [hf,] at hz
      have hh : (y,w)=z := Option.some.inj hz
      cases hh
      have hy := safe_output hp he
      have hw := safe_output hq hf
      rw [width_pair]
      omega
namespace SizePolynomial
lemma monotone (p : SizePolynomial) : Monotone p.eval := by
  intro x y h
  induction p with
  | constant c => rfl
  | input => exact h
  | add p q ihp ihq => exact Nat.add_le_add ihp ihq
  | mul p q ihp ihq => exact Nat.mul_le_mul ihp ihq
lemma eval_subst (p q : SizePolynomial) (x : ℕ) : (p.subst q).eval x=p.eval (q.eval x) := by
  induction p <;> simp_all [subst,eval]
end SizePolynomial

lemma controlled_compose {a b c : DataType} (p : Expression a b) (q : Expression b c)
    (hp : Controlled p) (hq : Controlled q) : Controlled (.compose p q) := by
  obtain ⟨f,hf⟩ := hp
  obtain ⟨g,hg⟩ := hq
  refine ⟨.add f (g.subst f),fun O x => ?_⟩
  apply safe_compose O p q x
  · exact safe_mono p x (hf O x) (by simp only [SizePolynomial.eval]; omega)
  · intro y hy
    have h := safe_output (hf O x) hy
    apply safe_mono q y (hg O y)
    rw [SizePolynomial.eval,SizePolynomial.eval_subst]
    exact (g.monotone h).trans (Nat.le_add_left _ _)
lemma controlled_both {a b c : DataType} (p : Expression a b) (q : Expression a c)
    (hp : Controlled p) (hq : Controlled q) : Controlled (.both p q) := by
  obtain ⟨f,hf⟩ := hp
  obtain ⟨g,hg⟩ := hq
  refine ⟨.add (.mul (.constant 3) (.add f g)) (.constant 1),fun O x => ?_⟩
  apply safe_both O p q x
  · exact safe_mono p x (hf O x) (Nat.le_add_right _ _)
  · exact safe_mono q x (hg O x) (Nat.le_add_left _ _)
lemma controlled_branch {a b : DataType} (p q : Expression a b)
    (hp : Controlled p) (hq : Controlled q) : Controlled (.branch p q) := by
  obtain ⟨f,hf⟩ := hp
  obtain ⟨g,hg⟩ := hq
  refine ⟨.add .input (.add f g),fun O x => ?_⟩
  rcases x with ⟨v,x⟩
  have hw : width x≤width (a:=.prod .bool a) (v,x) := by rw [width_pair]; omega
  have hp' : Safe O (width (a:=.prod .bool a) (v,x)+
      (f.eval (width (a:=.prod .bool a) (v,x))+g.eval (width (a:=.prod .bool a) (v,x)))) p x :=
    safe_mono p x (hf O x) ((f.monotone hw).trans (by omega))
  have hq' : Safe O (width (a:=.prod .bool a) (v,x)+
      (f.eval (width (a:=.prod .bool a) (v,x))+g.eval (width (a:=.prod .bool a) (v,x)))) q x :=
    safe_mono q x (hg O x) ((g.monotone hw).trans (by omega))
  refine ⟨by simp only [SizePolynomial.eval]; omega,?_,?_⟩
  · intro y hy
    cases v
    · exact safe_output hp' hy
    · exact safe_output hq' hy
  · cases v
    · exact hp'
    · exact hq'

lemma bits_length_mono {a b : ℕ} (h : a≤b) : a.bits.length≤b.bits.length := by
  simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h
lemma bits_length_le_value (a : ℕ) : a.bits.length≤a := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr a.lt_two_pow_self
lemma bits_length_add (a b : ℕ) : (a+b).bits.length≤a.bits.length+b.bits.length+1 := by
  simp only [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have hpa : 1≤2^a.size := Nat.one_le_pow _ _ (by decide)
  have hpb : 1≤2^b.size := Nat.one_le_pow _ _ (by decide)
  rw [pow_succ,pow_add]
  nlinarith
lemma bits_length_mul (a b : ℕ) : (a*b).bits.length≤a.bits.length+b.bits.length := by
  simp only [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  rw [pow_add]
  calc
    a*b≤(2^a.size)*b := Nat.mul_le_mul_right _ (Nat.lt_size_self a).le
    _ < (2^a.size)*(2^b.size) := Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self b) (by positivity)
lemma bits_length_binaryValue (x : Word) : (binaryValue x).bits.length≤x.length := by
  rw [←normalWord_eq_bits]
  exact normal_length x
lemma width_list_bool (x : Word) : width (a:=.list .bool) x=4*x.length := by
  induction x with
  | nil => rfl
  | cons b xs ih =>
    rw [width_cons (a:=.bool),width_bool,ih,List.length_cons]
    omega
lemma width_list_append {a : DataType} (x y : List (Value a)) :
    width (a:=.list a) (x++y)=width (a:=.list a) x+width (a:=.list a) y := by
  induction x with
  | nil => simp
  | cons z x ih => simp only [List.cons_append,width_cons,ih]; omega
lemma width_list_reverse {a : DataType} (x : List (Value a)) :
    width (a:=.list a) x.reverse=width (a:=.list a) x := by
  induction x with
  | nil => rfl
  | cons z x ih => simp only [List.reverse_cons,width_list_append,width_cons,width_nil,ih]; omega
lemma width_list_member {a : DataType} (x : Value a) (xs : List (Value a)) (h : x∈xs) :
    width x≤width (a:=.list a) xs := by
  induction xs with
  | nil => cases h
  | cons z zs ih =>
    simp only [List.mem_cons] at h
    cases h with
    | inl h => subst x; rw [width_cons]; omega
    | inr h => have hi := ih h; rw [width_cons]; omega

lemma safe_atomic {n S : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (p : Expression a b) (x : Value a) (ha : Atomic p) (hx : width x≤S)
    (hy : ∀ y,run O p x=some y → width y≤S) : Safe O S p x := by
  cases p <;> first | contradiction | exact ⟨hx,hy,trivial⟩
lemma atomic_width {n : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (p : Expression a b) (x : Value a) (ha : Atomic p) (y : Value b) (hy : run O p x=some y) :
    width y≤8*(width x+constantWidth p+1) := by
  cases p with
  | compose | both | branch | fold => contradiction
  | ident => cases hy; simp only [constantWidth]; omega
  | constant z => cases hy; simp only [constantWidth]; omega
  | fst =>
    rcases x with ⟨u,v⟩
    cases hy
    simp only [width_pair,constantWidth]; omega
  | snd =>
    rcases x with ⟨u,v⟩
    cases hy
    simp only [width_pair,constantWidth]; omega
  | @cons a =>
    rcases x with ⟨u,v⟩
    cases hy
    rw [width_pair (a := a) (b := .list a)]
    simp only [width_cons,constantWidth]; omega
  | consBit =>
    rcases x with ⟨u,v⟩
    cases hy
    rw [width_pair (a := .bool) (b := .word)]
    simp only [width_word,List.length_cons,width_bool,constantWidth]; omega
  | append =>
    rcases x with ⟨u,v⟩
    cases hy
    rw [width_pair (a := .word) (b := .word)]
    simp only [width_word,List.length_append,constantWidth]; omega
  | reverse =>
    cases hy
    simp only [width_word,List.length_reverse,constantWidth]; omega
  | toList =>
    cases hy
    rw [width_list_bool]
    simp only [width_word,constantWidth]; omega
  | toBits =>
    cases hy
    simp only [width_word,width_nat,constantWidth]; omega
  | toNat =>
    cases hy
    have h := bits_length_binaryValue x
    simp only [width_word,width_nat,constantWidth]; omega
  | add =>
    rcases x with ⟨u,v⟩
    cases hy
    have h := bits_length_add u v
    rw [width_pair (a := .nat) (b := .nat)]
    simp only [width_nat,constantWidth]; omega
  | mul =>
    rcases x with ⟨u,v⟩
    cases hy
    have h := bits_length_mul u v
    rw [width_pair (a := .nat) (b := .nat)]
    simp only [width_nat,constantWidth]; omega
  | sub =>
    rcases x with ⟨u,v⟩
    simp only [run] at hy
    split_ifs at hy with hv
    · cases hy
      have h := bits_length_mono (Nat.sub_le u v)
      rw [width_pair (a := .nat) (b := .nat)]
      simp only [width_nat,constantWidth]; omega
  | less =>
    simp only [width_bool,constantWidth]; omega
  | divRem =>
    rcases x with ⟨u,v⟩
    simp only [run] at hy
    split_ifs at hy with hv
    · cases hy
      have h₁ := bits_length_mono (Nat.mod_le v u)
      have h₂ := bits_length_mono (Nat.div_le_self v u)
      simp only [width_pair (a := .nat) (b := .nat),width_nat,constantWidth]; omega
  | query b => simp only [width_bool,constantWidth]; omega
  | rank b =>
    simp only [run] at hy
    split_ifs at hy with hx
    · cases hy
      have h₁ := bits_length_binaryValue (rankBits b O x.reverse)
      have h₂ := rankBits_length O b x.reverse
      simp only [List.length_reverse] at h₂
      simp only [width_nat,width_word,constantWidth,rankWord]; omega
lemma controlled_atomic {a b : DataType} (p : Expression a b) (ha : Atomic p) : Controlled p := by
  refine ⟨.mul (.constant 8) (.add (.add .input (.constant (constantWidth p))) (.constant 1)),fun O x => ?_⟩
  apply safe_atomic O p x ha
  · dsimp [SizePolynomial.eval]; omega
  · exact fun y hy => atomic_width O p x ha y hy

lemma foldSafe_prefix {A B : Type*} (ok : A×B → Prop) (f : A×B → Option B)
    (xs : List A) (z : B)
    (h : ∀ pre x post,xs=pre++x::post → ∀ y,foldValue f pre z=some y → ok (x,y)) :
    FoldSafe ok f xs z := by
  induction xs generalizing z with
  | nil => trivial
  | cons x xs ih =>
    refine ⟨h [] x xs rfl z rfl,?_⟩
    intro y hy
    apply ih y
    intro pre a post he w hw
    apply h (x::pre) a post (by simpa using congrArg (List.cons x) he) w
    simp only [foldValue,hy,Option.bind_some]
    exact hw

lemma controlled_fold {a b : DataType} (p : Expression (.prod a b) b)
    (hp : Controlled p) (g : SizePolynomial)
    (hg : ∀ {n : ℕ} (O : IndependenceOracle n) (xs : List (Value a)) (z : Value b)
      (pre post : List (Value a)),xs=pre++post → ∀ y,foldValue (run O p) pre z=some y →
      width y≤g.eval (width (a:=.prod (.list a) b) (xs,z))) :
    Controlled (.fold p) := by
  obtain ⟨f,hf⟩ := hp
  let vP : SizePolynomial := .add (.add (.mul (.constant 2) .input) (.constant 1)) g
  let h : SizePolynomial := .add (.add .input g) (f.subst vP)
  refine ⟨h,fun O x => ?_⟩
  rcases x with ⟨xs,z⟩
  have hS : width (a:=.prod (.list a) b) (xs,z)≤h.eval (width (a:=.prod (.list a) b) (xs,z)) := by
    dsimp [h,SizePolynomial.eval]; omega
  have hgS : g.eval (width (a:=.prod (.list a) b) (xs,z))≤h.eval (width (a:=.prod (.list a) b) (xs,z)) := by
    dsimp [h,SizePolynomial.eval]; omega
  refine ⟨hS,?_,?_⟩
  · intro y hy
    exact (hg O xs z xs [] (by simp) y hy).trans hgS
  · apply foldSafe_prefix
    intro pre v post he y hy
    have hay : width y≤g.eval (width (a:=.prod (.list a) b) (xs,z)) := hg O xs z pre (v::post) he y hy
    have ha : width (a:=a) v≤width (a:=.prod (.list a) b) (xs,z) := by
      have hm : v∈xs := by rw [he]; simp
      have ha := width_list_member v xs hm
      rw [width_pair]; omega
    have hinput : width (a:=.prod a b) (v,y)≤vP.eval (width (a:=.prod (.list a) b) (xs,z)) := by
      rw [width_pair]
      dsimp [vP,SizePolynomial.eval]
      omega
    apply safe_mono p (v,y) (hf O (v,y))
    exact (f.monotone hinput).trans (by
      dsimp only [h,SizePolynomial.eval]
      rw [SizePolynomial.eval_subst]
      omega)

lemma mod_double_lt (a b : ℕ) (hb : 0<b) (hba : b≤a) : 2*(a%b)<a := by
  have hr := Nat.mod_lt a hb
  have hd := Nat.div_pos hba hb
  have hm := Nat.mul_le_mul_left b hd
  have he := Nat.mod_add_div a b
  omega
lemma mod_size_lt (a b : ℕ) (hb : 0<b) (hba : b≤a) : (a%b).size<a.size := by
  have ha : 0<a := lt_of_lt_of_le hb hba
  by_cases hz : a%b=0
  · simpa [hz] using Nat.size_pos.mpr ha
  · have h := Nat.size_le_size (Nat.le_of_lt (mod_double_lt a b hb hba))
    have hs : (2*(a%b)).size=(a%b).size+1 := by
      have he : 2*(a%b)=Nat.bit false (a%b) := by simp [Nat.bit_val]
      rw [he,Nat.size_bit (by simpa [Nat.bit_val] using hz)]
    rw [hs] at h
    omega

lemma gcdSteps_zero (k a : ℕ) : gcdSteps k (a,0)=(a,0) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [gcdSteps,gcdStep] using ih
lemma gcdSteps_done (k a b : ℕ) (hba : b≤a) (hk : a.size+b.size≤k) :
    gcdSteps k (a,b)=(Nat.gcd a b,0) := by
  induction k generalizing a b with
  | zero =>
    have ha : a=0 := Nat.size_eq_zero.mp (by omega)
    have hb : b=0 := Nat.size_eq_zero.mp (by omega)
    simp [ha,hb,gcdSteps]
  | succ k ih =>
    by_cases hb : b=0
    · subst b; simp [gcdSteps_zero]
    · have hb' := Nat.pos_of_ne_zero hb
      have hl := mod_size_lt a b hb' hba
      have hs := Nat.size_le_size hba
      have hh := ih b (a%b) (Nat.le_of_lt (Nat.mod_lt a hb')) (by omega)
      simp only [gcdSteps,gcdStep,hb,ite_false]
      rw [hh,Nat.gcd_comm b (a%b),←Nat.gcd_rec,Nat.gcd_comm b a]

namespace Expression
lemma run_sortPair {n : ℕ} (O : IndependenceOracle n) (a b : ℕ) :
    run O sortPair (a,b)=some (if a<b then (b,a) else (a,b)) := by
  simp only [sortPair,applyIf,swap,run]
  by_cases h : a<b <;> simp [h]
lemma run_gcdStepCode {n : ℕ} (O : IndependenceOracle n) (a b : ℕ) :
    run O gcdStepCode (a,b)=some (gcdStep (a,b)) := by
  by_cases hb : b=0 <;>
    simp [gcdStepCode,applyIf,run,swap,natEqZero,natMod,natDivRem,gcdStep,hb]
lemma fold_gcdStepCode {n : ℕ} (O : IndependenceOracle n) (xs : List Bool) (p : ℕ × ℕ) :
    foldValue (run O (Expression.snd (a:=.bool) >>> gcdStepCode)) xs p=some (gcdSteps xs.length p) := by
  induction xs generalizing p with
  | nil => rfl
  | cons b xs ih =>
    rcases p with ⟨a,c⟩
    change ((run O gcdStepCode (a,c)).bind fun p =>
      foldValue (run O (Expression.snd (a:=.bool) >>> gcdStepCode)) xs p)=_
    rw [run_gcdStepCode,Option.bind_some,ih]
    rfl
lemma run_gcdCode {n : ℕ} (O : IndependenceOracle n) (a b : ℕ) :
    run O gcdCode (a,b)=some (Nat.gcd a b) := by
  unfold gcdCode
  have hs := run_sortPair O a b
  simp only [run]
  rw [hs]
  simp only [Option.bind_some]
  by_cases hab : a<b
  · simp only [hab,ite_true]
    change ((foldValue (run O (Expression.snd (a:=.bool) >>> gcdStepCode)) (b.bits++a.bits) (b,a)).bind
      fun p => some p.1)=some (Nat.gcd a b)
    rw [fold_gcdStepCode]
    simp only [List.length_append,Nat.size_eq_bits_len]
    rw [gcdSteps_done _ _ _ (Nat.le_of_lt hab) (by rfl)]
    simp [Nat.gcd_comm]
  · simp only [hab,ite_false]
    change ((foldValue (run O (Expression.snd (a:=.bool) >>> gcdStepCode)) (a.bits++b.bits) (a,b)).bind
      fun p => some p.1)=some (Nat.gcd a b)
    rw [fold_gcdStepCode]
    simp only [List.length_append,Nat.size_eq_bits_len]
    rw [gcdSteps_done _ _ _ (Nat.le_of_not_gt hab) (by rfl)]
    rfl
end Expression

open Expression
lemma controlled_onLeft {a b c : DataType} (p : Expression a b) (hp : Controlled p) :
    Controlled (onLeft (c:=c) p) := by unfold onLeft; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_onRight {a b c : DataType} (p : Expression a b) (hp : Controlled p) :
    Controlled (onRight (c:=c) p) := by unfold onRight; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_swap {a b : DataType} : Controlled (Expression.swap (a:=a) (b:=b)) := by unfold Expression.swap; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_letIn {a b c : DataType} (p : Expression a b) (q : Expression (.prod a b) c)
    (hp : Controlled p) (hq : Controlled q) : Controlled (letIn p q) := by unfold letIn; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_applyIf {a b : DataType} (p : Expression a .bool) (q r : Expression a b)
    (hp : Controlled p) (hq : Controlled q) (hr : Controlled r) : Controlled (applyIf p q r) := by
  unfold applyIf; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_boolNot : Controlled boolNot := by unfold boolNot; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_boolAnd : Controlled boolAnd := by unfold boolAnd; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_natEqZero : Controlled natEqZero := by unfold natEqZero; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_natSub : Controlled natSub := by unfold natSub; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_natDivRem : Controlled natDivRem := by unfold natDivRem; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_natDiv : Controlled natDiv := by unfold natDiv; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_natMod : Controlled natMod := by unfold natMod; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_listReverse {a : DataType} : Controlled (listReverse (a:=a)) := by
  unfold listReverse
  apply controlled_compose
  · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
  · apply controlled_fold _ (controlled_atomic (cons (a:=a)) trivial) (.mul (.constant 2) .input)
    intro n O xs z pre post he y hy
    have hh := foldValue_eq_foldl (run O (cons (a:=a))) (fun z x => x::z) (fun _ _ => rfl) pre z
    rw [hh] at hy
    cases hy
    rw [List.foldl_flip_cons_eq_append',width_list_append,width_list_reverse]
    have hp : width (a:=.list a) pre≤width (a:=.list a) xs := by rw [he,width_list_append]; omega
    rw [width_pair (a:=.list a) (b:=.list a)]
    dsimp [SizePolynomial.eval]
    omega
lemma foldl_succ {A : Type*} (l : List A) (z : ℕ) : l.foldl (fun z _ => z+1) z=z+l.length := by
  induction l generalizing z with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons,ih,List.length_cons]; omega
lemma controlled_listLength {a : DataType} : Controlled (listLength (a:=a)) := by
  unfold listLength
  apply controlled_compose
  · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
  · apply controlled_fold _ (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) (.mul (.constant 2) .input)
    intro n O xs z pre post he y hy
    have hh := foldValue_eq_foldl (run O (both (snd (a:=a)) (constant 1) >>> Expression.add)) (fun z (_ : Value a) => z+1) (fun _ _ => rfl) pre z
    rw [hh] at hy
    cases hy
    have hv := foldl_succ pre z
    rw [hv,width_nat]
    have hbits := bits_length_add z pre.length
    have hlen := bits_length_le_value pre.length
    have hx := list_length_le_width xs
    have hp : pre.length≤xs.length := by rw [he,List.length_append]; omega
    rw [width_pair (a:=.list a) (b:=.nat),width_nat]
    dsimp [SizePolynomial.eval]
    omega
lemma controlled_wordLength : Controlled wordLength := by
  exact controlled_compose _ _ (controlled_atomic _ trivial) controlled_listLength
lemma gcdSteps_max (k a b : ℕ) : (gcdSteps k (a,b)).1≤ max a b ∧ (gcdSteps k (a,b)).2≤ max a b := by
  induction k generalizing a b with
  | zero => exact ⟨Nat.le_max_left _ _,Nat.le_max_right _ _⟩
  | succ k ih =>
    by_cases hb : b=0
    · simpa [hb,gcdStep,gcdSteps] using ih a 0
    · have hi := ih b (a%b)
      have hle : max b (a%b)≤ max a b := max_le (Nat.le_max_right _ _) ((Nat.mod_le _ _).trans (Nat.le_max_left _ _))
      simpa [gcdSteps,gcdStep,hb] using And.intro (hi.1.trans hle) (hi.2.trans hle)
lemma controlled_gcd : Controlled gcdCode := by
  unfold gcdCode
  apply controlled_compose
  · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
  · apply controlled_compose
    · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
    · apply controlled_compose
      · apply controlled_fold _ (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) (.mul (.constant 4) .input)
        intro n O xs z pre post he y hy
        rcases z with ⟨a,b⟩
        rw [fold_gcdStepCode] at hy
        cases hy
        have hh := gcdSteps_max pre.length a b
        have h₁ := bits_length_mono hh.1
        have h₂ := bits_length_mono hh.2
        have hm : (max a b).bits.length≤a.bits.length+b.bits.length := by
          rcases le_total a b with h|h
          · rw [max_eq_right h]; omega
          · rw [max_eq_left h]; omega
        rw [width_pair (a:=.nat) (b:=.nat),width_pair (a:=.list .bool) (b:=.prod .nat .nat),
          width_pair (a:=.nat) (b:=.nat)]
        simp only [width_nat,SizePolynomial.eval]
        omega
      · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)

open Expression

lemma polySafe_of_controlled {a b : DataType} (p : Expression a b) (hp : Controlled p)
    (R : ℕ → Value a → Prop) (g : SizePolynomial) (hg : ∀ S x,R S x → width x≤g.eval S) :
    PolySafe p R := by
  obtain ⟨f,hf⟩ := hp
  refine ⟨f.subst g,fun O S x hx => ?_⟩
  apply safe_mono p x (hf O x)
  rw [SizePolynomial.eval_subst]
  exact f.monotone (hg S x hx)
lemma polySafe_compose {a b c : DataType} (p : Expression a b) (q : Expression b c)
    (R : ℕ → Value a → Prop) (Q : ℕ → Value b → Prop)
    (hp : PolySafe p R) (hq : PolySafe q Q)
    (h : ∀ {n : ℕ} (O : IndependenceOracle n) S x,R S x → ∀ y,run O p x=some y → Q S y) :
    PolySafe (p >>> q) R := by
  obtain ⟨f,hf⟩ := hp
  obtain ⟨g,hg⟩ := hq
  refine ⟨.add f g,fun O S x hx => ?_⟩
  apply safe_compose O p q x
  · exact safe_mono p x (hf O S x hx) (Nat.le_add_right _ _)
  · intro y hy
    exact safe_mono q y (hg O S y (h O S x hx y hy)) (Nat.le_add_left _ _)
lemma polySafe_both {a b c : DataType} (p : Expression a b) (q : Expression a c)
    (R : ℕ → Value a → Prop) (hp : PolySafe p R) (hq : PolySafe q R) :
    PolySafe (.both p q) R := by
  obtain ⟨f,hf⟩ := hp
  obtain ⟨g,hg⟩ := hq
  refine ⟨.add (.mul (.constant 3) (.add f g)) (.constant 1),fun O S x hx => ?_⟩
  apply safe_both O p q x
  · exact safe_mono p x (hf O S x hx) (Nat.le_add_right _ _)
  · exact safe_mono q x (hg O S x hx) (Nat.le_add_left _ _)
lemma polySafe_fold {a b : DataType} (p : Expression (.prod a b) b)
    (R : ℕ → Value (.prod (.list a) b) → Prop) (Q : ℕ → Value (.prod a b) → Prop)
    (hp : PolySafe p Q) (g : SizePolynomial)
    (hinput : ∀ S x,R S x → width x≤g.eval S)
    (hacc : ∀ {n : ℕ} (O : IndependenceOracle n) S xs z,R S (xs,z) →
      ∀ pre post,xs=pre++post → ∀ y,foldValue (run O p) pre z=some y → width y≤g.eval S)
    (hstep : ∀ {n : ℕ} (O : IndependenceOracle n) S xs z,R S (xs,z) →
      ∀ pre x post,xs=pre++x::post → ∀ y,foldValue (run O p) pre z=some y → Q S (x,y)) :
    PolySafe (.fold p) R := by
  obtain ⟨f,hf⟩ := hp
  refine ⟨.add f g,fun O S x hx => ?_⟩
  obtain ⟨xs,z⟩ := x
  refine ⟨(hinput S (xs,z) hx).trans (Nat.le_add_left _ _),?_,?_⟩
  · intro y hy
    exact (hacc O S xs z hx xs [] (by simp) y hy).trans (Nat.le_add_left _ _)
  · apply foldSafe_prefix
    intro pre x post he y hy
    exact safe_mono p (x,y) (hf O S (x,y) (hstep O S xs z hx pre x post he y hy))
      (Nat.le_add_right _ _)
lemma polySafe_controlled {a b : DataType} (p : Expression a b)
    (hp : PolySafe p (fun S x => width x≤S)) : Controlled p := by
  obtain ⟨f,hf⟩ := hp
  exact ⟨f,fun O x => hf O (width x) x le_rfl⟩

lemma run_mapStep_partial {n : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression (.prod a c) b) (x : Value a) (zs : List (Value b)) (ctx : Value c) :
    run O (mapStep p) (x,(zs,ctx))=(run O p (x,ctx)).map (fun v => (v::zs,ctx)) := by
  simp only [mapStep,run,bind_pure_comp,Option.bind_some]
  cases he : run O p (x,ctx) <;> simp [he]
lemma fold_mapStep_bound {n : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression (.prod a c) b) (xs : List (Value a)) (zs : List (Value b)) (ctx : Value c)
    (U : ℕ) (hu : ∀ x∈xs,∀ v,run O p (x,ctx)=some v → width v≤U)
    (y : Value (.prod (.list b) c)) (hy : foldValue (run O (mapStep p)) xs (zs,ctx)=some y) :
    width (a:=.list b) y.1≤width (a:=.list b) zs+xs.length*(2*U+2) ∧ y.2=ctx := by
  induction xs generalizing zs with
  | nil => cases hy; simp
  | cons x xs ih =>
    rw [foldValue,run_mapStep_partial] at hy
    cases he : run O p (x,ctx) with
    | none => simp [he] at hy
    | some v =>
      simp only [he,Option.map_some,Option.bind_some] at hy
      have hv := hu x (by simp) v he
      have hh := ih (v::zs) (fun x hx => hu x (by simp [hx])) hy
      rw [width_cons] at hh
      refine ⟨?_,hh.2⟩
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
lemma controlled_mapStep {a b c : DataType} (p : Expression (.prod a c) b) (hp : Controlled p) :
    Controlled (mapStep p) := by unfold mapStep; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_mapFold {a b c : DataType} (p : Expression (.prod a c) b) (hp : Controlled p) :
    Controlled (.fold (mapStep p)) := by
  obtain ⟨f,hf⟩ := hp
  let s : SizePolynomial := .add (.mul (.constant 3) .input) (.constant 1)
  let g : SizePolynomial := .mul (.add (.mul (.constant 4) .input) (.constant 3))
    (.add (.mul (.constant 2) (f.subst s)) (.constant 3))
  apply controlled_fold _ (controlled_mapStep p ⟨f,hf⟩) g
  intro n O xs z pre post he y hy
  rcases z with ⟨zs,ctx⟩
  let W := width (a:=.prod (.list a) (.prod (.list b) c)) (xs,(zs,ctx))
  have hx : width (a:=.list a) xs≤W := by dsimp [W]; rw [width_pair (a:=.list a) (b:=.prod (.list b) c)]; omega
  have hzs : width (a:=.list b) zs≤W := by dsimp [W]; rw [width_pair (a:=.list a) (b:=.prod (.list b) c),width_pair (a:=.list b) (b:=c)]; omega
  have hc : width ctx≤W := by dsimp [W]; rw [width_pair (a:=.list a) (b:=.prod (.list b) c),width_pair (a:=.list b) (b:=c)]; omega
  have hl : pre.length≤W := by
    have hh := list_length_le_width xs
    have he' := congrArg List.length he
    simp only [List.length_append] at he'
    omega
  let U := f.eval (3*W+1)
  have hh := fold_mapStep_bound O p pre zs ctx U (by
    intro x hxp v hv
    have hxx : x∈xs := by rw [he]; exact List.mem_append_left post hxp
    have hxb := (width_list_member x xs hxx).trans hx
    apply (safe_output (hf O (x,ctx)) hv).trans
    apply f.monotone
    rw [width_pair (a:=a) (b:=c)]
    omega) y hy
  have hm := Nat.mul_le_mul_right (2*U+2) hl
  have hy' : width (a:=.list b) y.1≤W+W*(2*U+2) := by omega
  change width y≤g.eval W
  have hw : width y=2*width (a:=.list b) y.1+1+width ctx := by
    obtain ⟨ys,vctx⟩ := y
    change width (a:=.prod (.list b) c) (ys,vctx)=2*width (a:=.list b) ys+1+width ctx
    rw [width_pair,show vctx=ctx from hh.2]
  rw [hw]
  simp only [g,SizePolynomial.eval,SizePolynomial.eval_subst]
  change _≤(4*W+3)*(2*U+3)
  nlinarith
lemma controlled_mapWith {a b c : DataType} (p : Expression (.prod a c) b) (hp : Controlled p) :
    Controlled (mapWith p) := by
  unfold mapWith
  apply controlled_compose
  · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
  · apply controlled_compose
    · exact controlled_mapFold p hp
    · apply controlled_compose
      · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
      · exact controlled_listReverse

lemma rationalPair_div (a b : ℕ) : rationalPair ((a:ℚ)/(b:ℚ))=normalizePair a b := by
  have he : (a:ℚ)/(b:ℚ)=mkRat (a:ℤ) b := by
    simp only [Rat.mkRat_eq_divInt,Rat.divInt_eq_div,Int.cast_natCast]
  rw [he]
  by_cases hb : b=0 <;>
    simp [rationalPair,normalizePair,Rat.num_mkRat,Rat.den_mkRat,hb,Nat.gcd_comm,Int.natAbs_ediv_of_nonneg]
lemma rationalPair_value {q : ℚ} (hq : 0≤q) :
    ((rationalPair q).1:ℚ)/((rationalPair q).2:ℚ)=q := by
  dsimp [rationalPair]
  have hnum : 0≤q.num := Rat.num_nonneg.mpr hq
  have he : (q.num.natAbs:ℚ)=(q.num:ℚ) := by
    have hnat : (q.num.natAbs:ℤ)=q.num := Int.natAbs_of_nonneg hnum
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℚ)) hnat
  rw [he]
  exact Rat.num_div_den q
lemma rationalPair_den (q : ℚ) : 0<(rationalPair q).2 := q.den_pos

namespace Expression
lemma run_applyIf {n : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (p : Expression a .bool) (q r : Expression a b) (x : Value a) :
    run O (applyIf p q r) x=(run O p x).bind (fun t => if t then run O r x else run O q x) := by
  simp [applyIf,run,Option.bind_assoc]
lemma run_letIn {n : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression a b) (q : Expression (.prod a b) c) (x : Value a) :
    run O (letIn p q) x=(run O p x).bind (fun y => run O q (x,y)) := by
  simp [letIn,run,Option.bind_assoc]

lemma run_normalizeRat {n : ℕ} (O : IndependenceOracle n) (a b : ℕ) :
    run O normalizeRat (a,b)=some (normalizePair a b) := by
  rw [normalizeRat,run_applyIf]
  change ((run O natEqZero b).bind fun t => if t then some (0,1) else _)=_
  rw [run_natEqZero]
  by_cases hb : b=0
  · simp [hb,normalizePair]
  · simp only [hb,decide_false,Option.bind_some,Bool.false_eq_true,ite_false]
    rw [run_letIn,run_gcdCode]
    change (do
      let x ← run O natDiv (Nat.gcd a b,a)
      let y ← run O natDiv (Nat.gcd a b,b)
      pure (x,y))=some (normalizePair a b)
    rw [run_natDiv O _ _,run_natDiv O _ _]
    simp [normalizePair,hb]
lemma run_normalizeRat_pair {n : ℕ} (O : IndependenceOracle n) (a b : ℕ) :
    run O normalizeRat (a,b)=some (rationalPair ((a:ℚ)/(b:ℚ))) := by
  rw [rationalPair_div]
  exact run_normalizeRat O a b
lemma run_ratAdd_raw {n : ℕ} (O : IndependenceOracle n) (a b c d : ℕ) :
    run O ratAdd ((a,b),(c,d))=some (normalizePair (a*d+c*b) (b*d)) := by
  change run O normalizeRat (a*d+c*b,b*d)=_
  exact run_normalizeRat O _ _
lemma run_ratMul_raw {n : ℕ} (O : IndependenceOracle n) (a b c d : ℕ) :
    run O ratMul ((a,b),(c,d))=some (normalizePair (a*c) (b*d)) := by
  change run O normalizeRat (a*c,b*d)=_
  exact run_normalizeRat O _ _
lemma run_ratDiv_raw {n : ℕ} (O : IndependenceOracle n) (a b c d : ℕ) :
    run O ratDiv ((a,b),(c,d))=some (normalizePair (a*d) (c*b)) := by
  change run O normalizeRat (a*d,c*b)=_
  exact run_normalizeRat O _ _
lemma run_ratMul {n : ℕ} (O : IndependenceOracle n) (q r : ℚ) (hq : 0≤q) (hr : 0≤r) :
    run O ratMul (rationalPair q,rationalPair r)=some (rationalPair (q*r)) := by
  rw [run_ratMul_raw,←rationalPair_div]
  congr 2
  conv_rhs => rw [←rationalPair_value hq,←rationalPair_value hr]
  push_cast
  ring
lemma run_ratDiv {n : ℕ} (O : IndependenceOracle n) (q r : ℚ) (hq : 0≤q) (hr : 0≤r) :
    run O ratDiv (rationalPair q,rationalPair r)=some (rationalPair (q/r)) := by
  rw [run_ratDiv_raw,←rationalPair_div]
  congr 2
  conv_rhs => rw [←rationalPair_value hq,←rationalPair_value hr]
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring
lemma run_ratMinOne {n : ℕ} (O : IndependenceOracle n) (q : ℚ) (hq : 0≤q) :
    run O ratMinOne (rationalPair q)=some (rationalPair (min 1 q)) := by
  have hv := rationalPair_value hq
  have hd : (0:ℚ)<(rationalPair q).2 := by exact_mod_cast rationalPair_den q
  have hcmp : (rationalPair q).2<(rationalPair q).1 ↔ (1:ℚ)<q := by
    conv_rhs => rw [←hv,lt_div_iff₀ hd,one_mul]
    norm_cast
  by_cases h : 1<q
  · have he := hcmp.mpr h
    simp only [ratMinOne,run_applyIf]
    change (if decide ((rationalPair q).2 < (rationalPair q).1) then some (1,1) else some (rationalPair q))=_
    rw [ite_eq_left (by simpa using he),min_eq_left (le_of_lt h)]
    rfl
  · have he : ¬(rationalPair q).2<(rationalPair q).1 := mt hcmp.mp h
    simp only [ratMinOne,run_applyIf]
    change (if decide ((rationalPair q).2 < (rationalPair q).1) then some (1,1) else some (rationalPair q))=_
    rw [ite_eq_right (by simpa using he),min_eq_right (le_of_not_gt h)]

lemma foldValue_iterate {n : ℕ} (O : IndependenceOracle n) {a : DataType} (p : Expression a a)
    (f : Value a → Value a) (hp : ∀ x,run O p x=some (f x)) (xs : List Bool) (z : Value a) :
    foldValue (run O (Expression.snd (a:=.bool) >>> p)) xs z=some ((f^[xs.length]) z) := by
  induction xs generalizing z with
  | nil => rfl
  | cons b xs ih =>
    change ((run O p z).bind fun y => foldValue (run O (Expression.snd (a:=.bool) >>> p)) xs y)=_
    rw [hp,Option.bind_some,ih]
    rfl
lemma run_iterateWord {n : ℕ} (O : IndependenceOracle n) {a : DataType} (p : Expression a a)
    (f : Value a → Value a) (hp : ∀ x,run O p x=some (f x)) (w : Word) (z : Value a) :
    run O (iterateWord p) (w,z)=some ((f^[w.length]) z) := by
  change foldValue (run O (Expression.snd (a:=.bool) >>> p)) w z=_
  exact foldValue_iterate O p f hp w z
lemma run_iterateNat {n : ℕ} (O : IndependenceOracle n) {a : DataType} (p : Expression a a)
    (f : Value a → Value a) (hp : ∀ x,run O p x=some (f x)) (k : ℕ) (z : Value a) :
    run O (iterateNat p) (k,z)=some ((f^[k]) z) := by
  obtain ⟨w,hw,hlen⟩ := run_unary O k
  simp only [iterateNat,onLeft,run,Option.bind_some]
  rw [hw]
  change run O (iterateWord p) (w,z)=_
  rw [run_iterateWord O p f hp,hlen]
lemma run_fromList {n : ℕ} (O : IndependenceOracle n) (xs : List Bool) :
    run O fromList xs=some xs := by
  simp only [fromList,run]
  rw [run_listReverse]
  change foldValue (run O consBit) xs.reverse []=some xs
  have hh := foldValue_eq_foldl (run O consBit) (fun z x => x::z) (fun _ _ => rfl) xs.reverse []
  simpa using hh

lemma rangeStep_iterate (k : ℕ) : (rangeStep^[k]) (0,[])=(k,(List.range k).reverse) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih]; simp [rangeStep,List.range_succ]
lemma run_rangeCode {n : ℕ} (O : IndependenceOracle n) (k : ℕ) :
    run O rangeCode k=some (List.range k) := by
  have hh := run_iterateNat O rangeStepCode rangeStep (fun _ => rfl) k (0,[])
  change ((run O (iterateNat rangeStepCode) (k,(0,[]))).bind fun p => run O listReverse p.2)=_
  rw [hh,rangeStep_iterate,Option.bind_some,run_listReverse,List.reverse_reverse]

lemma run_splitStep {n : ℕ} (O : IndependenceOracle n) {a : DataType} (x : Value a)
    (k : ℕ) (u v : List (Value a)) : run O splitStep (x,(k,(u,v)))=some (splitStepValue (x,(k,(u,v)))) := by
  rw [splitStep,run_applyIf]
  change ((run O natEqZero k).bind fun t => if t then _ else _)=_
  rw [run_natEqZero]
  by_cases hk : k=0
  · subst k; rfl
  · simp only [hk,decide_false,Option.bind_some,Bool.false_eq_true,ite_false]
    change ((run O natSub (k,1)).bind fun j => some (j,(x::u,v)))=_
    rw [run_natSub]
    simp [splitStepValue,hk]
lemma fold_splitStep {n : ℕ} (O : IndependenceOracle n) {a : DataType} (xs : List (Value a))
    (k : ℕ) (u v : List (Value a)) :
    foldValue (run O splitStep) xs (k,(u,v))=
      some (k-xs.length,((xs.take k).reverse++u,(xs.drop k).reverse++v)) := by
  induction xs generalizing k u v with
  | nil => simp [foldValue]
  | cons x xs ih =>
    rw [foldValue,run_splitStep]
    cases k with
    | zero => simpa [splitStepValue,List.append_assoc] using ih 0 u (x::v)
    | succ k => simpa [splitStepValue,List.append_assoc] using ih k (x::u) v
lemma run_splitAtCode {n : ℕ} (O : IndependenceOracle n) {a : DataType} (xs : List (Value a)) (k : ℕ) :
    run O splitAtCode (xs,k)=some (xs.take k,xs.drop k) := by
  change ((foldValue (run O splitStep) xs (k,([],[]))).bind fun p => do
    let x ← run O listReverse p.2.1
    let y ← run O listReverse p.2.2
    pure (x,y))=_
  rw [fold_splitStep]
  simp only [List.append_nil,Option.bind_some]
  rw [run_listReverse,run_listReverse]
  simp
lemma run_takeCode {n : ℕ} (O : IndependenceOracle n) {a : DataType} (xs : List (Value a)) (k : ℕ) :
    run O takeCode (xs,k)=some (xs.take k) := by
  change ((run O splitAtCode (xs,k)).bind fun p => some p.1)=_
  rw [run_splitAtCode]; rfl
lemma run_dropCode {n : ℕ} (O : IndependenceOracle n) {a : DataType} (xs : List (Value a)) (k : ℕ) :
    run O dropCode (xs,k)=some (xs.drop k) := by
  change ((run O splitAtCode (xs,k)).bind fun p => some p.2)=_
  rw [run_splitAtCode]; rfl

lemma run_compose {n : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression a b) (q : Expression b c) (x : Value a) :
    run O (p >>> q) x=(run O p x).bind (run O q) := rfl
lemma run_both {n : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression a b) (q : Expression a c) (x : Value a) :
    run O (both p q) x=(run O p x).bind (fun y => (run O q x).map (fun z => (y,z))) := by
  simp only [run]
  congr 1
  funext y
  cases run O q x <;> rfl

lemma foldLast_append {A : Type*} (xs ys : List A) (d : A) :
    foldLast (xs++ys) d=foldLast ys (foldLast xs d) := by
  induction xs generalizing d with
  | nil => rfl
  | cons x xs ih => exact ih x
lemma foldLast_reverse {A : Type*} (xs : List A) (d : A) :
    foldLast xs.reverse d=xs.headD d := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [List.reverse_cons,foldLast_append,foldLast]
lemma run_headD {n : ℕ} (O : IndependenceOracle n) {a} (xs : List (Value a)) (d : Value a) :
    run O headD (xs,d)=some (xs.headD d) := by
  have hf : ∀ (ys : List (Value a)) (z : Value a),
      foldValue (run O (fst (b:=a))) ys z=some (foldLast ys z) := by
    intro ys
    induction ys with
    | nil => intro z; rfl
    | cons y ys ih => intro z; exact ih y
  simp only [headD,onLeft,run,run_listReverse]
  change foldValue (run O (fst (b:=a))) xs.reverse d=_
  rw [hf,foldLast_reverse]
lemma run_getDCode {n : ℕ} (O : IndependenceOracle n) {a} (xs : List (Value a)) (k : ℕ) (d : Value a) :
    run O getDCode ((xs,k),d)=some (xs.getD k d) := by
  simp [getDCode,run]
  rw [run_dropCode O xs k]
  change run O headD (xs.drop k,d)=_
  rw [run_headD]
  congr 1
  induction k generalizing xs with
  | zero => cases xs <;> rfl
  | succ k ih => cases xs with
    | nil => rfl
    | cons x xs => exact ih xs
lemma run_boolOr {n : ℕ} (O : IndependenceOracle n) (x y : Bool) :
    run O boolOr (x,y)=some (x||y) := by cases x <;> rfl
lemma run_natEqual {n : ℕ} (O : IndependenceOracle n) (x y : ℕ) :
    run O natEqual (x,y)=some (decide (x=y)) := by
  simp [natEqual,run,swap]
  rw [run_boolOr]
  simp only [Option.bind_some]
  congr 1
  by_cases h : x=y
  · subst y; simp
  · have hn : x<y ∨ y<x := by omega
    rcases hn with hh|hh <;> simp [h,hh]
lemma run_listAll {n : ℕ} (O : IndependenceOracle n) (xs : List Bool) :
    run O listAll xs=some (xs.all id) := by
  have hf : ∀ (ys : List Bool) (z : Bool),
      foldValue (run O boolAnd) ys z=some (z && ys.all id) := by
    intro ys
    induction ys with
    | nil => intro z; cases z <;> rfl
    | cons y ys ih =>
      intro z
      change ((run O boolAnd (y,z)).bind (foldValue (run O boolAnd) ys))=_
      rw [run_boolAnd,Option.bind_some,ih]
      cases z <;> cases y <;> simp
  change foldValue (run O boolAnd) xs true=_
  simpa using hf xs true
lemma run_filterStep {n : ℕ} (O : IndependenceOracle n) {a b} (p : Expression (.prod a b) .bool)
    (f : Value a → Value b → Bool) (hp : ∀ x z,run O p (x,z)=some (f x z))
    (x : Value a) (ys : List (Value a)) (z : Value b) :
    run O (filterStep p) (x,(ys,z))=some ((if f x z then x::ys else ys),z) := by
  simp only [filterStep,run_both,run_applyIf]
  change ((run O p (x,z)).bind fun t => if t then some (x::ys) else some ys).bind
    (fun v => (some z).map (fun w => (v,w)))=_
  rw [hp]
  cases f x z <;> rfl
lemma run_filterWith {n : ℕ} (O : IndependenceOracle n) {a b} (p : Expression (.prod a b) .bool)
    (f : Value a → Value b → Bool) (hp : ∀ x z,run O p (x,z)=some (f x z))
    (xs : List (Value a)) (z : Value b) :
    run O (filterWith p) (xs,z)=some (xs.filter (fun x => f x z)) := by
  have hf : ∀ (ys acc : List (Value a)),
      foldValue (run O (filterStep p)) ys (acc,z)=some ((ys.filter (fun x => f x z)).reverse++acc,z) := by
    intro ys
    induction ys with
    | nil => intro acc; rfl
    | cons y ys ih =>
      intro acc
      rw [foldValue,run_filterStep O p f hp,Option.bind_some]
      cases h : f y z <;> simp [h,ih,List.append_assoc]
  change ((foldValue (run O (filterStep p)) xs ([],z)).bind fun yz => run O listReverse yz.1)=_
  rw [hf]
  change run O listReverse ((xs.filter (fun x => f x z)).reverse++[])=_
  rw [List.append_nil,run_listReverse,List.reverse_reverse]

lemma run_powCode {n : ℕ} (O : IndependenceOracle n) (a k : ℕ) :
    run O powCode (a,k)=some (a^k) := by
  let f : ℕ×ℕ → ℕ×ℕ := fun z => (z.1,z.1*z.2)
  have hi : ∀ j v,(f^[j]) (a,v)=(a,a^j*v) := by
    intro j
    induction j with
    | zero => intro v; simp [f]
    | succ j ih => intro v; rw [Function.iterate_succ_apply',ih]; simp [f,pow_succ]; ring
  have hh := run_iterateNat O powStepCode f (fun _ => rfl) k (a,1)
  simp [powCode,run,hh,hi]

lemma run_ratPowCode {n : ℕ} (O : IndependenceOracle n) (q : ℚ) (hq : 0≤q) (k : ℕ) :
    run O ratPowCode (rationalPair q,k)=some (rationalPair (q^k)) := by
  simp [ratPowCode,run]
  rw [run_powCode O _ _,run_powCode O _ _]
  change run O normalizeRat ((rationalPair q).1^k,(rationalPair q).2^k)=_
  rw [run_normalizeRat_pair]
  congr 2
  conv_rhs => rw [←rationalPair_value hq]
  push_cast
  rw [div_pow]
end Expression

open Expression
lemma width_take {a : DataType} (xs : List (Value a)) (k : ℕ) :
    width (a:=.list a) (xs.take k)≤width (a:=.list a) xs := by
  have hh := width_list_append (xs.take k) (xs.drop k)
  rw [List.take_append_drop] at hh
  omega
lemma width_drop {a : DataType} (xs : List (Value a)) (k : ℕ) :
    width (a:=.list a) (xs.drop k)≤width (a:=.list a) xs := by
  have hh := width_list_append (xs.take k) (xs.drop k)
  rw [List.take_append_drop] at hh
  omega
lemma controlled_fromList : Controlled fromList := by
  unfold fromList
  apply controlled_compose
  · exact controlled_both _ _ controlled_listReverse (controlled_atomic _ trivial)
  · apply controlled_fold consBit (controlled_atomic _ trivial) (.mul (.constant 2) .input)
    intro n O xs z pre post he y hy
    have hh := foldValue_eq_foldl (run O consBit) (fun z x => x::z) (fun _ _ => rfl) pre z
    rw [hh] at hy
    cases hy
    rw [List.foldl_flip_cons_eq_append',width_word,List.length_append,List.length_reverse]
    have hp : pre.length≤xs.length := by rw [he,List.length_append]; omega
    rw [width_pair (a:=.list .bool) (b:=.word),width_list_bool,width_word]
    dsimp [SizePolynomial.eval]
    omega
lemma controlled_splitStep {a : DataType} : Controlled (splitStep (a:=a)) := by unfold splitStep; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_splitFold {a : DataType} : Controlled (.fold (splitStep (a:=a))) := by
  apply controlled_fold splitStep controlled_splitStep (.mul (.constant 8) .input)
  intro n O xs z pre post he y hy
  rcases z with ⟨k,u,v⟩
  rw [fold_splitStep] at hy
  cases hy
  have hpre : width (a:=.list a) pre≤width (a:=.list a) xs := by rw [he,width_list_append]; omega
  have ht := width_take (a:=a) pre k
  have hd := width_drop (a:=a) pre k
  have hk := bits_length_mono (Nat.sub_le k pre.length)
  simp only [width_pair (a:=.nat) (b:=.prod (.list a) (.list a)),
    width_pair (a:=.list a) (b:=.list a),width_nat,width_list_append,width_list_reverse,
    width_pair (a:=.list a) (b:=SplitState a),SizePolynomial.eval]
  omega
lemma controlled_splitAt {a : DataType} : Controlled (splitAtCode (a:=a)) := by
  have hf := controlled_splitFold (a:=a)
  have hr := controlled_listReverse (a:=a)
  unfold splitAtCode
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma controlled_take {a : DataType} : Controlled (takeCode (a:=a)) :=
  controlled_compose _ _ controlled_splitAt (controlled_atomic _ trivial)
lemma controlled_drop {a : DataType} : Controlled (dropCode (a:=a)) :=
  controlled_compose _ _ controlled_splitAt (controlled_atomic _ trivial)
lemma fold_fst_mem {A : Type*} (xs : List A) (z y : A)
    (hy : foldValue (fun p : A×A => some p.1) xs z=some y) : y=z ∨ y∈xs := by
  induction xs generalizing z with
  | nil => cases hy; exact Or.inl rfl
  | cons x xs ih =>
    change foldValue (fun p : A×A => some p.1) xs x=some y at hy
    rcases ih x hy with h|h
    · exact Or.inr (by simp [h])
    · exact Or.inr (by simp [h])
lemma controlled_headD {a : DataType} : Controlled (headD (a:=a)) := by
  unfold headD
  apply controlled_compose
  · exact controlled_onLeft _ controlled_listReverse
  · apply controlled_fold (Expression.fst (a:=a) (b:=a)) (controlled_atomic _ trivial) (.mul (.constant 2) .input)
    intro n O xs z pre post he y hy
    have hh := fold_fst_mem pre z y hy
    have hw : width y≤width z+width (a:=.list a) xs := by
      rcases hh with hh|hh
      · subst y; omega
      · have hm : y∈xs := by rw [he]; exact List.mem_append_left post hh
        have hb := width_list_member y xs hm
        omega
    rw [width_pair (a:=.list a) (b:=a)]
    dsimp [SizePolynomial.eval]
    omega
lemma controlled_getD {a : DataType} : Controlled (getDCode (a:=a)) := by
  have hd := controlled_drop (a:=a)
  have hh := controlled_headD (a:=a)
  unfold getDCode
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma controlled_boolOr : Controlled boolOr := by unfold boolOr; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_natEqual : Controlled natEqual := by unfold natEqual; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_listAll : Controlled listAll := by
  unfold listAll
  apply controlled_compose
  · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
  · apply controlled_fold boolAnd controlled_boolAnd (.add .input (.constant 1))
    intro n O xs z pre post he y hy
    simp only [width_bool,SizePolynomial.eval]
    omega

open Expression
lemma wordDouble_length_le (w : Word) (b : Bool) : w.length≤(wordDouble w b).length := by
  cases b <;> simp [wordDouble,List.length_append] ; omega
lemma wordDouble_fold_length_le (xs : List Bool) (z : Word) : z.length≤(xs.foldl wordDouble z).length := by
  induction xs generalizing z with
  | nil => rfl
  | cons b xs ih => exact (wordDouble_length_le z b).trans (ih (wordDouble z b))
lemma wordDouble_prefix_length_le (pre post : List Bool) (z : Word) :
    (pre.foldl wordDouble z).length≤((pre++post).foldl wordDouble z).length := by
  rw [List.foldl_append]
  exact wordDouble_fold_length_le post _
lemma fold_wordDouble {n : ℕ} (O : IndependenceOracle n) (xs : List Bool) (z : Word) :
    foldValue (run O wordRepeatStep) xs z=some (xs.foldl wordDouble z) := by
  apply foldValue_eq_foldl
  intro b w
  exact run_wordRepeatStep O b w
lemma controlled_wordRepeatStep : Controlled wordRepeatStep := by unfold wordRepeatStep; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma polySafe_wordRepeatFold : PolySafe (.fold wordRepeatStep)
    (fun S x => x.1.length≤S ∧ (x.1.foldl wordDouble x.2).length≤S) := by
  apply polySafe_fold wordRepeatStep _ (fun S x => width x≤5*S+4)
    (polySafe_of_controlled wordRepeatStep controlled_wordRepeatStep _
      (.add (.mul (.constant 5) .input) (.constant 4)) (by intros; assumption))
    (.add (.mul (.constant 10) .input) (.constant 4))
  · intro S x hx
    obtain ⟨xs,z⟩ := x
    dsimp only [Prod.fst,Prod.snd] at hx
    have hh := wordDouble_fold_length_le xs z
    rw [width_pair (a:=.list .bool) (b:=.word),width_list_bool,width_word]
    dsimp [SizePolynomial.eval]
    omega
  · intro n O S xs z hx pre post he y hy
    dsimp only [Prod.fst,Prod.snd] at hx
    rw [fold_wordDouble] at hy
    cases hy
    have hh := wordDouble_prefix_length_le pre post z
    rw [←he] at hh
    rw [width_word]
    dsimp [SizePolynomial.eval]
    omega
  · intro n O S xs z hx pre b post he y hy
    dsimp only [Prod.fst,Prod.snd] at hx
    rw [fold_wordDouble] at hy
    cases hy
    have hh := wordDouble_prefix_length_le pre (b::post) z
    rw [←he] at hh
    rw [width_pair (a:=.bool) (b:=.word),width_bool,width_word]
    omega
lemma polySafe_unary : PolySafe unary (fun S x => x≤S) := by
  unfold unary
  apply polySafe_compose _ _ _ _
    (polySafe_of_controlled _ (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ .input (by
      intro S x hx
      exact (bits_length_le_value x).trans hx)) polySafe_wordRepeatFold
  intro n O S x hx y hy
  cases hy
  obtain ⟨w,hw,hlen⟩ := unary_value O x.bits []
  rw [fold_wordDouble] at hw
  have hwe : (x.bits.reverse.foldl wordDouble [])=w := Option.some.inj hw
  refine ⟨?_,?_⟩
  · simpa only [List.length_reverse] using (bits_length_le_value x).trans hx
  · rw [hwe,hlen]
    simpa only [List.length_nil,mul_zero,zero_add,binaryValue_bits] using hx

lemma wordSet_not {n : ℕ} (x : Word) (hx : x.length=n) :
    wordSet n (x.map Bool.not)=(wordSet n x)ᶜ := by
  ext i
  simp only [wordSet,Set.mem_ofPred_eq,Set.mem_compl_iff]
  have hi : i.val<x.length := by omega
  rw [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem (by simpa using hi),List.getElem_map]
  cases x[i.val] <;> simp

namespace Expression

lemma run_wordGet {n : ℕ} (O : IndependenceOracle n) (x : Word) (j : ℕ) :
    run O wordGet (x,j)=some (x[j]?.getD false) := by
  change run O (getDCode (a:=.bool)) ((x,j),false)=_
  exact run_getDCode O (a:=.bool) x j false
lemma run_wordNot {n : ℕ} (O : IndependenceOracle n) (x : Word) :
    run O wordNot x=some (x.map Bool.not) := by
  change ((run O (mapWith (c:=.unit) (fst >>> boolNot)) (x,())).bind (run O fromList))=_
  rw [run_mapWith O _ (fun b (_ : Unit) => !b) (by intro b z; exact run_boolNot O b)]
  change run O fromList (x.map Bool.not)=_
  exact run_fromList O _
lemma run_wordCount {n : ℕ} (O : IndependenceOracle n) (x : Word) :
    run O wordCount x=some (x.count true) := by
  have hf : ∀ (xs : Word) k,foldValue (run O wordCountStep) xs k=some (k+xs.count true) := by
    intro xs
    induction xs with
    | nil => intro k; simp [foldValue]
    | cons b xs ih =>
      intro k
      cases b with
      | false =>
        change foldValue (run O wordCountStep) xs k=some (k+(false::xs).count true)
        rw [ih]; simp
      | true =>
        change foldValue (run O wordCountStep) xs (k+1)=some (k+(true::xs).count true)
        rw [ih]; simp [Nat.add_comm,Nat.add_left_comm]
  change foldValue (run O wordCountStep) x 0=_
  simpa using hf x 0

lemma run_deficiencyCode {n : ℕ} (O : IndependenceOracle n) (r : ℕ) (x y : Word)
    (hx : x.length=n) (hy : y.length=n) :
    run O deficiencyCode (r,(x,y))=
      some (n+r-(rankWord O false x+y.count true+rankWord O true (y.map Bool.not))) := by
  simp only [deficiencyCode,run_compose,run_both]
  simp [run,run_wordLength,run_wordCount,run_wordNot,hx,hy]
  rw [run_natSub]
end Expression

open scoped Classical in
lemma deficiencyCode_source {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r : ℕ) (x y : Word) (hx : x.length=n) (hy : y.length=n) :
    run O Expression.deficiencyCode (r,(x,y))=some (oracleDeficiency n r O (representedState n (x,y))) := by
  rw [Expression.run_deficiencyCode O r x y hx hy]
  unfold oracleDeficiency pairedDeficiencyOracle
  rw [representedState_preinl,representedState_preinr,
    rankWord_eq_rankOracle M₁ M₂ O hO hE₁ hE₂ false x hx,
    rankWord_eq_rankOracle M₁ M₂ O hO hE₁ hE₂ true (y.map Bool.not) (by simpa using hy),
    wordSet_not y hy]
  rw [Set.toFinset_compl]
  have hc : (wordSet n y).toFinset.card=y.count true := by
    simpa using wordSet_card y hy
  simp only [hc]

lemma foldValue_append {A B : Type*} (f : A×B → Option B) (xs ys : List A) (z : B) :
    foldValue f (xs++ys) z=(foldValue f xs z).bind (foldValue f ys) := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append,foldValue,ih,Option.bind_assoc]

namespace Expression
lemma run_wordTake {n : ℕ} (O : IndependenceOracle n) (x : Word) (k : ℕ) :
    run O wordTake (x,k)=some (x.take k) := by
  change ((run O (takeCode (a:=.bool)) (x,k)).bind (run O fromList))=_
  rw [run_takeCode]; exact run_fromList O _
lemma run_rejectStep {n : ℕ} (O : IndependenceOracle n) (x : Word) (v k : ℕ) (z : Bool×ℕ) :
    run O rejectStep (x,((v,k),z))=some ((v,k),
      if binaryValue (x.take k).reverse<v then (true,binaryValue (x.take k).reverse) else z) := by
  simp only [rejectStep,run_both,run_letIn,run_compose,run_fst,run_snd,run_constant,
    run_reverse,run_toNat,run_applyIf,Option.bind_some,Option.map_some]
  rw [run_wordTake O x k]
  by_cases h : binaryValue (x.take k).reverse<v <;> simp [run,h]
lemma fold_reject {n : ℕ} (O : IndependenceOracle n) (v k : ℕ) (xs : List Word) (z : Bool×ℕ) :
    foldValue (run O rejectStep) xs.reverse ((v,k),z)=
      some ((v,k),match rejectValue v k xs with | none => z | some y => (true,y)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons,foldValue_append,ih]
    simp only [Option.bind_some,foldValue]
    rw [run_rejectStep]
    simp only [Option.bind_some]
    change _=some ((v,k),match rejectValue v k (x::xs) with | none => z | some y => (true,y))
    simp only [rejectValue]
    split_ifs <;> rfl
lemma run_rejectCode {n : ℕ} (O : IndependenceOracle n) (xs : List Word) (v k : ℕ) :
    run O rejectCode (xs,(v,k))=some (optionData 0 (rejectValue v k xs)) := by
  simp only [rejectCode,run_compose,run_both,run_fst,run_snd,run_constant,Option.bind_some,
    run_listReverse,Option.map_some]
  change ((foldValue (run O rejectStep) xs.reverse ((v,k),(false,0))).bind fun z => some z.2)=_
  rw [fold_reject]
  cases rejectValue v k xs <;> rfl
end Expression

lemma binaryValue_ofFn_reverse (h : ℕ) (bits : BitWord h) :
    binaryValue (List.ofFn bits).reverse=(wordEquiv h bits).val := by
  induction h with
  | zero => simp [wordEquiv,binaryValue]
  | succ h ih =>
    rw [List.ofFn_succ,List.reverse_cons,binaryValue_append]
    simp only [List.length_reverse,List.length_ofFn,ih,binaryValue]
    simp [wordEquiv,Equiv.trans_apply,Fin.consEquiv,finProdFinEquiv,finTwoEquiv]
    cases bits 0 <;> simp <;> rfl

lemma bankEval_bind {A B : Type*} (t : DrawTree A) (f : A → DrawTree B) (bank : Bank) :
    bankEval (t.bind f) bank=
      match bankEval t bank with
      | (none,rest) => (none,rest)
      | (some a,rest) => bankEval (f a) rest := by
  induction t generalizing bank with
  | leaf a => rfl
  | draw v k ih =>
    cases bank with
    | nil => rfl
    | cons rows bank =>
      simp only [DrawTree.bind,bankEval]
      split <;> first | rfl | exact ih _ bank
lemma bankEval_map {A B : Type*} (t : DrawTree A) (f : A → B) (bank : Bank) :
    bankEval (t.map f) bank=((bankEval t bank).1.map f,(bankEval t bank).2) := by
  rw [DrawTree.map,bankEval_bind]
  cases bankEval t bank with
  | mk o rest => cases o <;> rfl

open Expression

namespace Expression
lemma clog_two_size_pred (v : ℕ) : Nat.clog 2 v=(v-1).size := by
  apply Nat.le_antisymm
  · apply (Nat.clog_le_iff_le_pow (by norm_num)).mpr
    have h := Nat.lt_size_self (v-1)
    omega
  · apply Nat.size_le.mpr
    have h := Nat.le_pow_clog (by norm_num : 1<2) v
    have hp : 0<2^(Nat.clog 2 v) := by positivity
    omega

lemma run_clogCode {n : ℕ} (O : IndependenceOracle n) (v : ℕ) :
    run O clogCode v=some (Nat.clog 2 v) := by
  simp only [clogCode,run_compose,run_both,run_ident,run_constant,Option.bind_some,Option.map_some]
  rw [run_natSub]
  change run O wordLength (v-1).bits=_
  rw [run_wordLength,Nat.size_eq_bits_len,clog_two_size_pred]

end Expression
open Expression
namespace Effect

lemma run_pure {n : ℕ} (O : IndependenceOracle n) {a b} (p : Expression a b)
    (x : Value a) (y : Value b) (bank : Bank) (hp : run O p x=some y) :
    run O (pure p) (x,bank)=some (optionalValue b (some y),bank) := by
  simp only [pure,run_both,run_compose,run_fst,run_snd,run_constant,
    Option.bind_some,hp,Option.map_some]
  rfl
lemma run_bind {n : ℕ} (O : IndependenceOracle n) {a b c} (p : Effect a b) (q : Effect b c)
    (x : Value a) (bank rest : Bank) (y : Option (Value b))
    (hp : run O p (x,bank)=some (optionalValue b y,rest)) :
    run O (bind p q) (x,bank)=
      match y with
      | none => some (optionalValue c none,rest)
      | some z => run O q (z,rest) := by
  cases y <;> dsimp only <;> rw [bind,run_compose,hp,Option.bind_some,run_applyIf] <;> rfl
lemma run_keep {n : ℕ} (O : IndependenceOracle n) {a b} (p : Effect a b)
    (x : Value a) (bank rest : Bank) (y : Value b)
    (hp : run O p (x,bank)=some (optionalValue b (some y),rest)) :
    run O (keep p) (x,bank)=some (optionalValue (.prod a b) (some (x,y)),rest) := by
  rw [keep,run_letIn,hp]
  rfl
lemma run_draw {n : ℕ} (O : IndependenceOracle n) (v : ℕ) (bank : Bank) :
    run O draw (v,bank)=some (optionData 0
      (Expression.rejectValue v (Nat.clog 2 v) (bank.headD [])),bank.drop 1) := by
  simp only [draw,run_both,run_compose,run_fst,run_snd,run_ident,run_constant,Option.bind_some,Option.map_some]
  rw [run_headD,run_clogCode,run_dropCode]
  simp only [Option.bind_some,Option.map_some]
  rw [run_rejectCode]
  rfl

lemma realizes_pure {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b : DataType}
    (p : Expression a b) (encode : A → Value b) (x : Value a) (y : A)
    (hp : run O p x=some (encode y)) : Realizes O (pure p) encode x (.leaf y) := by
  intro bank
  exact run_pure O p x (encode y) bank hp

lemma realizes_bind {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b c : DataType}
    (p : Effect a b) (q : Effect b c) (ea : A → Value b) (eb : B → Value c)
    (x : Value a) (t : DrawTree A) (f : A → DrawTree B)
    (hp : Realizes O p ea x t) (hq : ∀ y,Realizes O q eb (ea y) (f y)) :
    Realizes O (bind p q) eb x (t.bind f) := by
  intro bank
  rw [bankEval_bind]
  cases ht : bankEval t bank with
  | mk out rest =>
    have hh := hp bank
    rw [ht] at hh
    cases out with
    | none => exact run_bind O p q x bank rest none hh
    | some y =>
      rw [run_bind O p q x bank rest (some (ea y)) hh]
      exact hq y rest

lemma realizes_keep {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b : DataType}
    (p : Effect a b) (ea : A → Value b) (x : Value a) (t : DrawTree A)
    (hp : Realizes O p ea x t) :
    Realizes O (keep p) (fun y => (x,ea y)) x t := by
  intro bank
  have hh := hp bank
  cases ht : bankEval t bank with
  | mk out rest =>
    rw [ht] at hh
    cases out with
    | none => rw [keep,run_letIn,hh]; rfl
    | some y => exact run_keep O p x bank rest (ea y) hh

lemma realizes_letIn {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b c : DataType}
    (p : Effect a b) (q : Effect (.prod a b) c) (ea : A → Value b) (eb : B → Value c)
    (x : Value a) (t : DrawTree A) (f : A → DrawTree B)
    (hp : Realizes O p ea x t) (hq : ∀ y,Realizes O q eb (x,ea y) (f y)) :
    Realizes O (letIn p q) eb x (t.bind f) :=
  realizes_bind O (keep p) q _ eb x t f (realizes_keep O p ea x t hp) hq

lemma realizes_draw {n : ℕ} (O : IndependenceOracle n) (v : ℕ) :
    Realizes O draw Fin.val (v+1) (.draw v DrawTree.leaf) := by
  intro bank
  rw [run_draw]
  cases bank with
  | nil => rfl
  | cons rows bank =>
    simp only [bankEval]
    split
    · rename_i hi
      simp only [List.headD_cons,List.drop_succ_cons,List.drop_zero,hi,Option.map_none]
      rfl
    · rename_i i hi
      simp only [List.headD_cons,List.drop_succ_cons,List.drop_zero,hi,Option.map_some]
      rfl

lemma run_precompose {n : ℕ} (O : IndependenceOracle n) {a b c} (p : Expression a b)
    (q : Effect b c) (x : Value a) (y : Value b) (bank : Bank)
    (hp : run O p x=some y) : run O (precompose p q) (x,bank)=run O q (y,bank) := by
  simp only [precompose,onLeft,run_compose,run_both,run_fst,run_snd,Option.bind_some,hp,Option.map_some]

lemma realizes_precompose {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b c}
    (p : Expression a b) (q : Effect b c) (ea : A → Value c) (x : Value a) (y : Value b)
    (t : DrawTree A) (hp : run O p x=some y) (hq : Realizes O q ea y t) :
    Realizes O (precompose p q) ea x t := by
  intro bank
  rw [run_precompose O p q x y bank hp]
  exact hq bank

lemma run_choose {n : ℕ} (O : IndependenceOracle n) {a b} (test : Expression a .bool)
    (p q : Effect a b) (x : Value a) (bank : Bank) (v : Bool)
    (ht : run O test x=some v) :
    run O (choose test p q) (x,bank)=if v then run O q (x,bank) else run O p (x,bank) := by
  rw [choose,run_applyIf]
  change ((run O test x).bind fun v => if v then _ else _)=_
  rw [ht,Option.bind_some]

lemma realizes_map {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b c}
    (p : Effect a b) (q : Expression b c) (ea : A → Value b) (eb : B → Value c)
    (x : Value a) (t : DrawTree A) (f : A → B)
    (hp : Realizes O p ea x t) (hq : ∀ y,run O q (ea y)=some (eb (f y))) :
    Realizes O (map p q) eb x (t.map f) :=
  realizes_bind O p (pure q) ea eb x t (fun y => .leaf (f y)) hp
    (fun y => realizes_pure O q eb (ea y) (f y) (hq y))
end Effect

lemma iterateM_some {A : Type*} (f : A → Option A) (x : A) (h : f x=some x) (k : ℕ) :
    iterateM f k x=some x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterateM,h,Option.bind_some,ih]
namespace Expression
lemma run_iterateNatM {n : ℕ} (O : IndependenceOracle n) {a : DataType}
    (p : Expression a a) (k : ℕ) (x : Value a) :
    run O (iterateNat p) (k,x)=iterateM (run O p) k x := by
  have hf : ∀ (w : Word) (z : Value a),
      foldValue (run O (Expression.snd (a:=.bool) >>> p)) w z=iterateM (run O p) w.length z := by
    intro w
    induction w with
    | nil => intro z; rfl
    | cons b w ih =>
      intro z
      change ((run O p z).bind (foldValue (run O (Expression.snd (a:=.bool) >>> p)) w))=_
      simp only [List.length_cons,iterateM]
      congr 1
      funext v
      exact ih v
  obtain ⟨w,hw,hlen⟩ := run_unary O k
  simp only [iterateNat,onLeft,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [hw]
  change foldValue (run O (Expression.snd (a:=.bool) >>> p)) w x=_
  rw [hf,hlen]
end Expression
namespace Effect

lemma run_loopStep_none {n : ℕ} (O : IndependenceOracle n) {a} (p : Effect a a) (bank : Bank) :
    run O (loopStep p) (optionalValue a none,bank)=some (optionalValue a none,bank) := rfl
lemma run_loopStep_some {n : ℕ} (O : IndependenceOracle n) {a} (p : Effect a a)
    (x : Value a) (bank : Bank) :
    run O (loopStep p) (optionalValue a (some x),bank)=run O p (x,bank) := rfl
lemma run_repeat {n : ℕ} (O : IndependenceOracle n) {a} (p : Effect a a)
    (k : ℕ) (x : Value a) (bank : Bank) :
    run O (repeatCode p) ((k,x),bank)=iterateM (run O (loopStep p)) k (optionalValue a (some x),bank) := by
  change run O (iterateNat (loopStep p)) (k,(optionalValue a (some x),bank))=_
  exact run_iterateNatM O _ _ _

lemma realizes_repeat {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a}
    (p : Effect a a) (ea : A → Value a) (f : A → DrawTree A)
    (hp : ∀ x,Realizes O p ea (ea x) (f x)) (k : ℕ) (x : A) :
    Realizes O (repeatCode p) ea (k,ea x) (treeRepeat f k x) := by
  intro bank
  rw [run_repeat]
  induction k generalizing x bank with
  | zero => rfl
  | succ k ih =>
    rw [iterateM,run_loopStep_some,hp x bank,Option.bind_some,treeRepeat,bankEval_bind]
    cases ht : bankEval (f x) bank with
    | mk out rest =>
      cases out with
      | none =>
        simpa only [Option.map_none] using iterateM_some (run O (loopStep p))
          (optionalValue a none,rest) (run_loopStep_none O p rest) k
      | some y => exact ih y rest

end Effect
end MachineCode

namespace DrawTree
variable {A B : Type*}
lemma Reindexed.trans {t u v : DrawTree A} (h : Reindexed t u) (g : Reindexed u v) :
    Reindexed t v := by
  induction h generalizing v with
  | leaf a => cases g; exact .leaf a
  | draw m k l e h ih =>
    cases g with
    | draw _ _ z f gz =>
      exact .draw m k z (e.trans f) (fun i => ih i (gz (e i)))
end DrawTree
namespace MachineCode
open Expression
namespace Effect

lemma Realizes.law {n : ℕ} {O : IndependenceOracle n} {A : Type*} {a b} {p : Effect a b}
    {e : A → Value b} {x : Value a} {t : DrawTree A} (h : Realizes O p e x t) :
    RealizesLaw O p e x t := ⟨t,.refl t,h⟩
lemma RealizesLaw.reindex {n : ℕ} {O : IndependenceOracle n} {A : Type*} {a b}
    {p : Effect a b} {e : A → Value b} {x : Value a} {t u : DrawTree A}
    (h : RealizesLaw O p e x u) (ht : DrawTree.Reindexed t u) : RealizesLaw O p e x t := by
  rcases h with ⟨v,hv,hp⟩
  exact ⟨v,ht.trans hv,hp⟩
lemma law_bind {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b c}
    (p : Effect a b) (q : Effect b c) (ea : A → Value b) (eb : B → Value c)
    (x : Value a) (t : DrawTree A) (f : A → DrawTree B)
    (hp : RealizesLaw O p ea x t) (hq : ∀ y,RealizesLaw O q eb (ea y) (f y)) :
    RealizesLaw O (bind p q) eb x (t.bind f) := by
  classical
  rcases hp with ⟨u,hu,hp⟩
  choose g hg hq using hq
  exact ⟨u.bind g,hu.bind hg,realizes_bind O p q ea eb x u g hp hq⟩
lemma law_letIn {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b c}
    (p : Effect a b) (q : Effect (.prod a b) c) (ea : A → Value b) (eb : B → Value c)
    (x : Value a) (t : DrawTree A) (f : A → DrawTree B)
    (hp : RealizesLaw O p ea x t) (hq : ∀ y,RealizesLaw O q eb (x,ea y) (f y)) :
    RealizesLaw O (letIn p q) eb x (t.bind f) := by
  classical
  rcases hp with ⟨u,hu,hp⟩
  choose g hg hq using hq
  exact ⟨u.bind g,hu.bind hg,realizes_letIn O p q ea eb x u g hp hq⟩
lemma law_precompose {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b c}
    (p : Expression a b) (q : Effect b c) (ea : A → Value c) (x : Value a) (y : Value b)
    (t : DrawTree A) (hp : run O p x=some y) (hq : RealizesLaw O q ea y t) :
    RealizesLaw O (precompose p q) ea x t := by
  rcases hq with ⟨u,hu,hq⟩
  exact ⟨u,hu,realizes_precompose O p q ea x y u hp hq⟩
lemma law_map {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b c}
    (p : Effect a b) (q : Expression b c) (ea : A → Value b) (eb : B → Value c)
    (x : Value a) (t : DrawTree A) (f : A → B)
    (hp : RealizesLaw O p ea x t) (hq : ∀ y,run O q (ea y)=some (eb (f y))) :
    RealizesLaw O (map p q) eb x (t.map f) := by
  rcases hp with ⟨u,hu,hp⟩
  exact ⟨u.map f,hu.map f,realizes_map O p q ea eb x u f hp hq⟩
lemma law_choose {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b}
    (test : Expression a .bool) (p q : Effect a b) (ea : A → Value b)
    (x : Value a) (t : DrawTree A) (v : Bool) (ht : run O test x=some v)
    (h : RealizesLaw O (if v then q else p) ea x t) :
    RealizesLaw O (choose test p q) ea x t := by
  rcases h with ⟨u,hu,hp⟩
  refine ⟨u,hu,fun bank => ?_⟩
  rw [run_choose O test p q x bank v ht]
  cases v <;> exact hp bank
end Effect
end MachineCode

namespace DrawTree
variable {A B C : Type*}
lemma bind_leaf (t : DrawTree A) : t.bind leaf=t := by
  induction t with
  | leaf a => rfl
  | draw v f ih => simp only [bind,ih]
lemma map_bind (t : DrawTree A) (f : A → B) (g : B → DrawTree C) :
    (t.map f).bind g=t.bind (fun a => g (f a)) := by
  rw [DrawTree.map,bind_assoc]
  rfl
lemma bind_map (t : DrawTree A) (f : A → DrawTree B) (g : B → C) :
    (t.bind f).map g=t.bind (fun a => (f a).map g) := bind_assoc t f _
lemma map_map (t : DrawTree A) (f : A → B) (g : B → C) :
    (t.map f).map g=t.map (g ∘ f) := map_bind t f _
end DrawTree
namespace MachineCode

open Expression

namespace Effect

lemma law_some {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b} (p : Effect a b)
    (ea : A → Value b) (x : Value a) (t : DrawTree A) (h : RealizesLaw O p ea x t) :
    RealizesLaw O (someCode p) (optionEncode ea) x (t.map some) :=
  law_map O p _ ea (optionEncode ea) x t some h (fun _ => rfl)
lemma law_none {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b} (ea : A → Value b) (x : Value a) :
    RealizesLaw O (noneCode (a:=a) (b:=b)) (optionEncode ea) x (.leaf none) :=
  (realizes_pure O _ _ _ none rfl).law
lemma law_optionContinue {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b}
    (q : Effect a (Optional b)) (ea : A → Value a) (eb : B → Value b)
    (f : A → DrawTree (Option B)) (x : Option A)
    (hq : ∀ y,RealizesLaw O q (optionEncode eb) (ea y) (f y)) :
    RealizesLaw O (optionContinue q) (optionEncode eb) (optionEncode ea x)
      (match x with | none => .leaf none | some y => f y) := by
  unfold optionContinue
  cases x with
  | none => exact law_choose O _ _ _ _ _ _ false rfl (law_none O eb _)
  | some y =>
    exact law_choose O _ _ _ _ _ _ true rfl
      (law_precompose O snd q _ _ _ _ rfl (hq y))
lemma law_optionBind {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b c}
    (p : Effect a (Optional b)) (q : Effect b (Optional c))
    (ea : A → Value b) (eb : B → Value c) (x : Value a)
    (t : DrawTree (Option A)) (f : A → DrawTree (Option B))
    (hp : RealizesLaw O p (optionEncode ea) x t)
    (hq : ∀ y,RealizesLaw O q (optionEncode eb) (ea y) (f y)) :
    RealizesLaw O (optionBind p q) (optionEncode eb) x (t.optionBind f) :=
  law_bind O p (optionContinue q) (optionEncode ea) (optionEncode eb) x t _ hp
    (fun y => law_optionContinue O q ea eb f y hq)

lemma law_repeat {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a}
    (p : Effect a a) (ea : A → Value a) (f : A → DrawTree A)
    (hp : ∀ x,RealizesLaw O p ea (ea x) (f x)) (k : ℕ) (x : A) :
    RealizesLaw O (repeatCode p) ea (k,ea x) (treeRepeat f k x) := by
  classical
  choose g hg hp using hp
  have hh : ∀ k x, DrawTree.Reindexed (treeRepeat f k x) (treeRepeat g k x) := by
    intro k
    induction k with
    | zero => intro x; exact .leaf x
    | succ k ih => intro x; exact (hg x).bind ih
  exact ⟨treeRepeat g k x,hh k x,realizes_repeat O p ea g hp k x⟩
lemma treeRepeat_succ_last {A : Type*} (f : A → DrawTree A) (k : ℕ) (x : A) :
    treeRepeat f (k+1) x=(treeRepeat f k x).bind f := by
  induction k generalizing x with
  | zero => exact DrawTree.bind_leaf (f x)
  | succ k ih =>
    change (f x).bind (treeRepeat f (k+1))=((f x).bind (treeRepeat f k)).bind f
    rw [DrawTree.bind_assoc]
    congr 1
    funext y
    exact ih y
lemma treeRepeat_option {A : Type*} (f : A → DrawTree (Option A)) (k : ℕ) (x : A) :
    treeRepeat (fun u => match u with | none => .leaf none | some a => f a) k (some x)=
      DrawTree.iterate f k x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [treeRepeat_succ_last,ih]; rfl

lemma law_iterate {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a}
    (p : Effect a (Optional a)) (ea : A → Value a) (f : A → DrawTree (Option A))
    (hp : ∀ x,RealizesLaw O p (optionEncode ea) (ea x) (f x)) (k : ℕ) (x : A) :
    RealizesLaw O (iterateCode p) (optionEncode ea) (k,ea x) (DrawTree.iterate f k x) := by
  unfold iterateCode
  apply law_precompose O _ _ _ _ (k,optionEncode ea (some x)) _ rfl
  rw [←treeRepeat_option]
  apply law_repeat
  intro u
  exact law_optionContinue O p ea ea f u hp
end Effect

lemma polySafe_reparam {a b : DataType} (p : Expression a b) (R : ℕ → Value a → Prop)
    (hp : PolySafe p R) (g : SizePolynomial) : PolySafe p (fun S x => R (g.eval S) x) := by
  obtain ⟨f,hf⟩ := hp
  exact ⟨f.subst g,fun O S x hx => by rw [SizePolynomial.eval_subst]; exact hf O _ x hx⟩
lemma polySafe_post {a b c : DataType} (p : Expression a b) (q : Expression b c)
    (R : ℕ → Value a → Prop) (hp : PolySafe p R) (hq : Controlled q) : PolySafe (p >>> q) R := by
  obtain ⟨f,hf⟩ := hp
  apply polySafe_compose p q R (fun S y => width y≤f.eval S) ⟨f,hf⟩
    (polySafe_of_controlled q hq _ f (by intros; assumption))
  intro n O S x hx y hy
  exact safe_output (hf O S x hx) hy
lemma foldValue_iterateM {n : ℕ} (O : IndependenceOracle n) {a : DataType}
    (p : Expression a a) (xs : List Bool) (z : Value a) :
    foldValue (run O (Expression.snd (a:=.bool) >>> p)) xs z=iterateM (run O p) xs.length z := by
  induction xs generalizing z with
  | nil => rfl
  | cons b xs ih => simp only [foldValue,run_compose,run_snd,Option.bind_some,List.length_cons,iterateM]; simp_rw [ih]

lemma polySafe_iterateNat {a : DataType} (p : Expression a a)
    (R : ℕ → Value (.prod .nat a) → Prop) (Q : ℕ → Value a → Prop)
    (hp : PolySafe p Q) (g : SizePolynomial)
    (hinput : ∀ S k z,R S (k,z) → k+width (a:=a) z≤g.eval S)
    (hacc : ∀ {n : ℕ} (O : IndependenceOracle n) S k z,R S (k,z) →
      ∀ j,j≤k → ∀ y,iterateM (run O p) j z=some y → width (a:=a) y≤g.eval S)
    (hbody : ∀ {n : ℕ} (O : IndependenceOracle n) S k z,R S (k,z) →
      ∀ j,j<k → ∀ y,iterateM (run O p) j z=some y → Q S y) :
    PolySafe (iterateNat p) R := by
  let T : SizePolynomial := .add (.mul (.constant 12) g) (.constant 4)
  have hnatwidth : ∀ S x,R S x → width x≤T.eval S := by
    intro S x hx
    obtain ⟨k,z⟩ := x
    have hh : k+width (a:=a) z≤g.eval S := hinput S k z hx
    have hb := bits_length_le_value k
    rw [width_pair (a:=.nat) (b:=a),width_nat]
    dsimp [T,SizePolynomial.eval]
    have h₁ := Nat.mul_le_mul_left 2 hh
    omega
  have hu : PolySafe (onLeft (c:=a) unary) R := by
    unfold onLeft
    apply polySafe_both
    · apply polySafe_compose _ _ R (fun S k => k≤g.eval S)
        (polySafe_of_controlled Expression.fst (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) R T hnatwidth)
        (polySafe_reparam unary (fun S k => k≤S) polySafe_unary g)
      intro n O S x hx y hy
      obtain ⟨k,z⟩ := x
      simp only [run_fst, Option.some.injEq] at hy
      subst y
      have hh : k+width (a:=a) z≤g.eval S := hinput S k z hx
      exact (Nat.le_add_right k (width (a:=a) z)).trans hh
    · exact polySafe_of_controlled Expression.snd (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) R T hnatwidth
  let Rw : ℕ → Value (.prod .word a) → Prop := fun S x => R S (x.1.length,x.2)
  let Rl : ℕ → Value (.prod (.list .bool) a) → Prop := fun S x => R S (x.1.length,x.2)
  have hw : ∀ S x,Rw S x → width x≤T.eval S := by
    intro S x hx
    obtain ⟨w,z⟩ := x
    have hh : w.length+width (a:=a) z≤g.eval S := hinput S w.length z hx
    rw [width_pair (a:=.word) (b:=a),width_word]
    dsimp [T,SizePolynomial.eval]
    omega
  have hfold : PolySafe (.fold (snd >>> p)) Rl := by
    refine polySafe_fold (Expression.snd (a:=.bool) >>> p) Rl
      (fun S x => width x≤T.eval S ∧ Q S x.2) ?_ T ?_ ?_ ?_
    · apply polySafe_compose _ _ _ Q
        (polySafe_of_controlled Expression.snd (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ T (by intro S x hx; exact hx.1)) hp
      intro n O S x hx y hy
      cases hy
      exact hx.2
    · intro S x hx
      obtain ⟨xs,z⟩ := x
      have hh : xs.length+width (a:=a) z≤g.eval S := hinput S xs.length z hx
      rw [width_pair (a:=.list .bool) (b:=a),width_list_bool]
      dsimp [T,SizePolynomial.eval]
      omega
    · intro n O S xs z hx pre post he y hy
      rw [foldValue_iterateM] at hy
      have hj : pre.length≤xs.length := by rw [he,List.length_append]; omega
      have hh := hacc O S xs.length z hx pre.length hj y hy
      dsimp [T,SizePolynomial.eval]
      omega
    · intro n O S xs z hx pre b post he y hy
      rw [foldValue_iterateM] at hy
      have hj : pre.length<xs.length := by rw [he,List.length_append,List.length_cons]; omega
      have hh := hacc O S xs.length z hx pre.length hj.le y hy
      refine ⟨?_,hbody O S xs.length z hx pre.length hj y hy⟩
      rw [width_pair (a:=.bool) (b:=a),width_bool]
      dsimp [T,SizePolynomial.eval]
      omega
  unfold iterateNat iterateWord
  apply polySafe_compose _ _ R Rw hu
  · apply polySafe_compose _ _ Rw Rl
      (polySafe_of_controlled _ (by unfold onLeft; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) Rw T hw) hfold
    intro n O S x hx y hy
    cases hy
    exact hx
  · intro n O S x hx y hy
    obtain ⟨k,z⟩ := x
    obtain ⟨w,hw,hk⟩ := run_unary O k
    simp only [onLeft,run_both,run_compose,run_fst,run_snd,Option.bind_some,hw,Option.map_some] at hy
    cases hy
    change R S (w.length,z)
    rwa [hk]

lemma iterateM_total {A : Type*} (p : A → Option A) (f : A → A)
    (hp : ∀ x,p x=some (f x)) (k : ℕ) (x : A) : iterateM p k x=some ((f^[k]) x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [iterateM,hp,Option.bind_some,ih,Function.iterate_succ_apply]
lemma width_list_le {a : DataType} (xs : List (Value a)) (S : ℕ)
    (hs : ∀ x∈xs,width (a:=a) x≤S) : width (a:=.list a) xs≤xs.length*(2*S+2) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hs x (by simp)
    have hh := ih (fun y hy => hs y (by simp [hy]))
    rw [width_cons (a:=a),List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
lemma width_range (k : ℕ) : width (a:=.list .nat) (List.range k)≤k*(2*k+2) := by
  simpa only [List.length_range] using width_list_le (a:=.nat) (List.range k) k (by
    intro x hx
    exact (bits_length_le_value x).trans (List.mem_range.mp hx).le)
lemma width_rangeState (k : ℕ) : width (a:=.prod .nat (.list .nat)) (k,(List.range k).reverse)≤4*(k+1)^2 := by
  rw [width_pair (a:=.nat) (b:=.list .nat),width_nat,width_list_reverse (a:=.nat)]
  have h := width_range k
  have h' := bits_length_le_value k
  nlinarith
lemma controlled_rangeStep : Controlled rangeStepCode := by unfold rangeStepCode; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma polySafe_rangeCode : PolySafe rangeCode (fun S k => k≤S) := by
  let g : SizePolynomial := .mul (.constant 10) (.mul (.add .input (.constant 1)) (.add .input (.constant 1)))
  have hg (S : ℕ) : g.eval S=10*(S+1)^2 := by simp [g,SizePolynomial.eval,pow_two]
  let R : ℕ → Value (.prod .nat (.prod .nat (.list .nat))) → Prop := fun S x => x.1≤S ∧ x.2=(0,[])
  have hi : PolySafe (iterateNat rangeStepCode) R := by
    refine polySafe_iterateNat rangeStepCode R (fun S z => width z≤g.eval S)
      (polySafe_of_controlled _ controlled_rangeStep _ g (by intros; assumption)) g ?_ ?_ ?_
    · intro S k z hx
      dsimp [R] at hx
      rcases hx with ⟨hk,rfl⟩
      rw [hg]
      change k+1≤10*(S+1)^2
      exact (Nat.add_le_add_right hk 1).trans (by nlinarith)
    · intro n O S k z hx j hj y hy
      dsimp [R] at hx
      rcases hx with ⟨hk,rfl⟩
      rw [iterateM_total (run O rangeStepCode) rangeStep (fun _ => rfl),rangeStep_iterate] at hy
      cases hy
      apply (width_rangeState j).trans
      rw [hg]
      have hjk : Nat.le j S := hj.trans hk
      exact (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.add_le_add_right hjk 1) 2)).trans
        (Nat.mul_le_mul_right _ (by decide : 4≤10))
    · intro n O S k z hx j hj y hy
      dsimp [R] at hx
      rcases hx with ⟨hk,rfl⟩
      rw [iterateM_total (run O rangeStepCode) rangeStep (fun _ => rfl),rangeStep_iterate] at hy
      cases hy
      apply (width_rangeState j).trans
      rw [hg]
      have hjk : Nat.le j S := hj.le.trans hk
      exact (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.add_le_add_right hjk 1) 2)).trans
        (Nat.mul_le_mul_right _ (by decide : 4≤10))
  unfold rangeCode
  apply polySafe_compose _ _ _ R
    (polySafe_of_controlled _ (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ .input (by
      intro S k hk
      exact (bits_length_le_value k).trans hk))
    (polySafe_post _ _ R hi (controlled_compose _ _ (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) controlled_listReverse))
  intro n O S x hx y hy
  cases hy
  exact ⟨hx,rfl⟩
lemma controlled_wordRange : Controlled (wordLength >>> rangeCode) := by
  apply polySafe_controlled
  apply polySafe_compose _ _ _ (fun S k => k≤S)
    (polySafe_of_controlled _ controlled_wordLength _ .input (by intros; assumption)) polySafe_rangeCode
  intro n O S x hx y hy
  rw [run_wordLength] at hy
  cases hy
  exact hx

lemma run_filterStep_partial {n : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (p : Expression (.prod a b) .bool) (x : Value a) (ys : List (Value a)) (z : Value b) :
    run O (filterStep p) (x,(ys,z))=(run O p (x,z)).map (fun t => ((if t then x::ys else ys),z)) := by
  simp only [filterStep,run_both,run_applyIf,run_compose,run_fst,run_snd,Option.bind_some,Option.map_some]
  cases he : run O p (x,z) with
  | none => rfl
  | some t => cases t <;> rfl
lemma fold_filterStep_bound {n : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (p : Expression (.prod a b) .bool) (xs ys : List (Value a)) (z : Value b)
    (v : Value (.prod (.list a) b)) (hv : foldValue (run O (filterStep p)) xs (ys,z)=some v) :
    width (a:=.list a) v.1≤width (a:=.list a) xs+width (a:=.list a) ys ∧ v.2=z := by
  induction xs generalizing ys with
  | nil => cases hv; simp
  | cons x xs ih =>
    rw [foldValue,run_filterStep_partial] at hv
    cases he : run O p (x,z) with
    | none => simp [he] at hv
    | some t =>
      simp only [he,Option.map_some,Option.bind_some] at hv
      cases t with
      | false =>
        have hh := ih ys hv
        rw [width_cons (a:=a)]
        exact ⟨by omega,hh.2⟩
      | true =>
        have hh := ih (x::ys) hv
        rw [width_cons (a:=a)] at hh ⊢
        exact ⟨by omega,hh.2⟩
lemma controlled_filterStep {a b : DataType} (p : Expression (.prod a b) .bool) (hp : Controlled p) :
    Controlled (filterStep p) := by unfold filterStep; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_filterFold {a b : DataType} (p : Expression (.prod a b) .bool) (hp : Controlled p) :
    Controlled (.fold (filterStep p)) := by
  apply controlled_fold _ (controlled_filterStep p hp) (.mul (.constant 3) .input)
  intro n O xs z pre post he y hy
  obtain ⟨ys,ctx⟩ := z
  have hh := fold_filterStep_bound O p pre ys ctx y hy
  have hpre : width (a:=.list a) pre≤width (a:=.list a) xs := by rw [he,width_list_append]; omega
  obtain ⟨out,outctx⟩ := y
  dsimp only [Prod.fst,Prod.snd] at hh
  rw [width_pair (a:=.list a) (b:=b),width_pair (a:=.list a) (b:=.prod (.list a) b),
    width_pair (a:=.list a) (b:=b),hh.2]
  dsimp [SizePolynomial.eval]
  omega
lemma controlled_filterWith {a b : DataType} (p : Expression (.prod a b) .bool) (hp : Controlled p) :
    Controlled (filterWith p) := by
  unfold filterWith
  have hf := controlled_filterFold p hp
  have hr := controlled_listReverse (a:=a)
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)

open scoped Classical
lemma stateEncode_get_right {n : ℕ} (S : Set (Fin n⊕Fin n)) (i : Fin n) :
    (stateEncode S).2[i.val]?.getD false=decide (Sum.inr i∈S) := by simp [stateEncode]

namespace Expression

lemma run_boolXor {n : ℕ} (O : IndependenceOracle n) (a b : Bool) :
    run O boolXor (a,b)=some (xor a b) := by cases a <;> cases b <;> rfl

lemma run_singleAt {n : ℕ} (O : IndependenceOracle n) (i : ℕ) (S : Word×Word) :
    run O singleAt (i,S)=some (singleValue i S) := by
  simp only [singleAt,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_wordGet,run_wordGet]
  exact run_boolXor O _ _
lemma run_fullAt {n : ℕ} (O : IndependenceOracle n) (i : ℕ) (S : Word×Word) :
    run O fullAt (i,S)=some (fullValue i S) := by
  simp only [fullAt,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_wordGet,run_wordGet]
  exact run_boolAnd O _ _
lemma run_emptyAt {n : ℕ} (O : IndependenceOracle n) (i : ℕ) (S : Word×Word) :
    run O emptyAt (i,S)=some (emptyValue i S) := by
  simp only [emptyAt,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_wordGet,run_wordGet]
  change ((run O boolOr _).bind (run O boolNot))=_
  rw [run_boolOr]; exact run_boolNot O _

lemma run_plainCode {n : ℕ} (O : IndependenceOracle n) (S : Word×Word) :
    run O plainCode S=some (plainValue S) := by
  simp only [plainCode,run_compose,run_both,run_fst,run_ident,Option.bind_some,Option.map_some]
  rw [run_wordLength,Option.bind_some,run_rangeCode]
  change ((run O (mapWith singleAt) (List.range S.1.length,S)).bind (run O listAll))=_
  rw [run_mapWith O singleAt singleValue (run_singleAt O)]
  exact run_listAll O _
end Expression

lemma singleValue_source {n : ℕ} (S : Set (Fin n⊕Fin n)) (i : Fin n) :
    Expression.singleValue i.val (stateEncode S)=decide (PairSingle (slotPair i) S) := by
  rw [Expression.singleValue,stateEncode_get_left,stateEncode_get_right]
  unfold PairSingle slotPair
  by_cases ha : Sum.inl i∈S <;> by_cases hb : Sum.inr i∈S <;> simp [ha,hb]
lemma fullValue_source {n : ℕ} (S : Set (Fin n⊕Fin n)) (i : Fin n) :
    Expression.fullValue i.val (stateEncode S)=decide (PairFull (slotPair i) S) := by
  rw [Expression.fullValue,stateEncode_get_left,stateEncode_get_right]
  unfold PairFull slotPair
  by_cases ha : Sum.inl i∈S <;> by_cases hb : Sum.inr i∈S <;> simp [ha,hb]
lemma emptyValue_source {n : ℕ} (S : Set (Fin n⊕Fin n)) (i : Fin n) :
    Expression.emptyValue i.val (stateEncode S)=decide (PairEmpty (slotPair i) S) := by
  rw [Expression.emptyValue,stateEncode_get_left,stateEncode_get_right]
  unfold PairEmpty slotPair
  by_cases ha : Sum.inl i∈S <;> by_cases hb : Sum.inr i∈S <;> simp [ha,hb]

lemma plainValue_source {n : ℕ} (S : Set (Fin n⊕Fin n)) :
    Expression.plainValue (stateEncode S)=decide (PlainState (pairedSlots n) S) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Expression.plainValue,List.all_map,List.all_eq_true,Function.comp_apply,id_eq,
    stateEncode_left_length,List.mem_range,decide_eq_true_eq]
  constructor
  · intro h p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    have hh := h i.val i.isLt
    rw [singleValue_source] at hh
    exact of_decide_eq_true hh
  · intro h i hi
    rw [singleValue_source S ⟨i,hi⟩]
    exact decide_eq_true (h _ (by simp [pairedSlots]))

lemma plainCode_source {n : ℕ} (O : IndependenceOracle n) (S : Set (Fin n⊕Fin n)) :
    run O Expression.plainCode (stateEncode S)=some (decide (PlainState (pairedSlots n) S)) := by
  rw [Expression.run_plainCode,plainValue_source]

namespace Expression

lemma run_defectAt {n : ℕ} (O : IndependenceOracle n) (i p r : ℕ) (S : Word×Word) :
    run O defectAt (i,((p,r),S))=some (defectAtValue i ((p,r),S)) := by
  simp only [defectAt,run_applyIf,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_natEqual]
  by_cases hi : i=p
  · subst i; simp only [decide_true,Option.bind_some,ite_true]; simpa only [defectAtValue,ite_true] using run_emptyAt O p S
  · simp only [hi,decide_false,Option.bind_some,Bool.false_eq_true,ite_false]
    rw [run_natEqual]
    by_cases hr : i=r
    · subst i; simp only [decide_true,Option.bind_some,ite_true]
      simpa only [defectAtValue,hi,ite_false,ite_true] using run_fullAt O r S
    · simp only [hr,decide_false,Option.bind_some,Bool.false_eq_true,ite_false]
      simpa only [defectAtValue,hi,hr,ite_false] using run_singleAt O i S

lemma run_defectCode {n : ℕ} (O : IndependenceOracle n) (p r : ℕ) (S : Word×Word) :
    run O defectCode ((p,r),S)=some (defectValue p r S) := by
  simp only [defectCode,run_compose,run_both,run_fst,run_snd,run_ident,Option.bind_some,Option.map_some]
  rw [run_natEqual,run_wordLength]
  simp only [Option.bind_some]
  rw [run_rangeCode]
  simp only [Option.bind_some,run_boolNot,run_compose]
  rw [run_mapWith O defectAt defectAtValue (by intro i v; rcases v with ⟨⟨p,r⟩,S⟩; exact run_defectAt O i p r S)]
  simp only [Option.bind_some,run_listAll,Option.map_some]
  rw [run_boolAnd]
  congr 1
  simp only [defectValue,decide_not]
end Expression

lemma slotPair_inj {α : Type*} (i j : α) : slotPair i=slotPair j ↔ i=j := by simp [slotPair]
lemma slotPair_mem {n : ℕ} (i : Fin n) : slotPair i∈pairedSlots n := by simp [pairedSlots]
lemma defect_paired_iff {n : ℕ} (p r : Fin n) (S : Set (Fin n⊕Fin n)) :
    DefectState (pairedSlots n) (slotPair p) (slotPair r) S ↔
      p≠r ∧ PairEmpty (slotPair p) S ∧ PairFull (slotPair r) S ∧
      ∀ i, i≠p → i≠r → PairSingle (slotPair i) S := by
  constructor
  · intro h
    refine ⟨fun hp => h.2.2.1 (congrArg slotPair hp),h.2.2.2.1,h.2.2.2.2.1,?_⟩
    intro i hip hir
    exact h.2.2.2.2.2 (slotPair i) (slotPair_mem i) (fun he => hip ((slotPair_inj i p).mp he)) (fun he => hir ((slotPair_inj i r).mp he))
  · rintro ⟨hpr,hp,hr,h⟩
    refine ⟨slotPair_mem p,slotPair_mem r,fun he => hpr ((slotPair_inj p r).mp he),hp,hr,?_⟩
    intro t ht htp htr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
    exact h i (fun he => htp (congrArg slotPair he)) (fun he => htr (congrArg slotPair he))

lemma defectValue_source {n : ℕ} (S : Set (Fin n⊕Fin n)) (p r : Fin n) :
    Expression.defectValue p.val r.val (stateEncode S)=
      decide (DefectState (pairedSlots n) (slotPair p) (slotPair r) S) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Expression.defectValue,Bool.and_eq_true,decide_eq_true_eq,List.all_map,List.all_eq_true,
    Function.comp_apply,id_eq,stateEncode_left_length,List.mem_range]
  rw [defect_paired_iff]
  constructor
  · rintro ⟨hne,h⟩
    have hpr : p≠r := fun he => hne (congrArg Fin.val he)
    refine ⟨hpr,?_,?_,?_⟩
    · have hh := h p.val p.isLt
      simpa only [Expression.defectAtValue,ite_true,emptyValue_source,decide_eq_true_eq] using hh
    · have hh := h r.val r.isLt
      have hrp : r.val≠p.val := Ne.symm hne
      simpa only [Expression.defectAtValue,hrp,ite_false,ite_true,fullValue_source,decide_eq_true_eq] using hh
    · intro i hip hir
      have hh := h i.val i.isLt
      have hip' : i.val≠p.val := fun he => hip (Fin.ext he)
      have hir' : i.val≠r.val := fun he => hir (Fin.ext he)
      simpa only [Expression.defectAtValue,hip',hir',ite_false,singleValue_source,decide_eq_true_eq] using hh
  · rintro ⟨hpr,hp,hr,h⟩
    refine ⟨fun he => hpr (Fin.ext he),?_⟩
    intro i hi
    let j : Fin n := ⟨i,hi⟩
    change Expression.defectAtValue j.val ((p.val,r.val),stateEncode S)=true
    by_cases hjp : j=p
    · subst p
      simpa only [Expression.defectAtValue,ite_true,emptyValue_source,decide_eq_true_eq] using hp
    · by_cases hjr : j=r
      · subst r
        have hne : j.val≠p.val := fun he => hjp (Fin.ext he)
        simpa only [Expression.defectAtValue,hne,ite_false,ite_true,fullValue_source,decide_eq_true_eq] using hr
      · have hip : j.val≠p.val := fun he => hjp (Fin.ext he)
        have hir : j.val≠r.val := fun he => hjr (Fin.ext he)
        simpa only [Expression.defectAtValue,hip,hir,ite_false,singleValue_source,decide_eq_true_eq] using h j hjp hjr

namespace Expression

lemma run_countWith {n : ℕ} (O : IndependenceOracle n) {a b} (p : Expression (.prod a b) .bool)
    (f : Value a → Value b → Bool) (hp : ∀ x z,run O p (x,z)=some (f x z))
    (xs : List (Value a)) (z : Value b) :
    run O (countWith p) (xs,z)=some (xs.countP (fun x => f x z)) := by
  rw [countWith,run_compose,run_filterWith O p f hp,Option.bind_some,run_listLength]
  simp only [List.countP_eq_length_filter]

lemma run_countPlainCode {n : ℕ} (O : IndependenceOracle n) (xs : List (Word×Word)) :
    run O countPlainCode xs=some (countPlainValue xs) := by
  change run O (countWith (fst (b:=.unit) >>> plainCode)) (xs,())=_
  exact run_countWith (a:=StateData) (b:=.unit) O _ (fun x (_ : Unit) => plainValue x) (fun x _ => run_plainCode O x) xs ()
lemma run_countDefectCode {n : ℕ} (O : IndependenceOracle n) (xs : List (Word×Word)) (p r : ℕ) :
    run O countDefectCode (xs,(p,r))=some (countDefectValue xs p r) := by
  exact run_countWith (a:=StateData) (b:=NN) O _ (fun S u => defectValue u.1 u.2 S)
    (fun S u => run_defectCode O u.1 u.2 S) xs (p,r)

lemma learningRatio_nonneg (xs : List (Word×Word)) (p r : ℕ) : 0≤learningRatio xs p r := by
  unfold learningRatio; positivity
lemma run_learningRatio {n : ℕ} (O : IndependenceOracle n) (xs : List (Word×Word)) (p r : ℕ) :
    run O learningRatioCode (xs,(p,r))=some (rationalPair (learningRatio xs p r)) := by
  simp only [learningRatioCode,run_compose,run_both,run_fst,Option.bind_some]
  rw [run_countPlainCode,run_countDefectCode]
  exact run_normalizeRat_pair O _ _

lemma weightUpdate_nonneg (p r : ℕ) (xs : List (Word×Word)) (q : ℚ) (hq : 0≤q) :
    0≤weightUpdate p r xs q := by
  unfold weightUpdate
  split_ifs
  · exact hq
  · exact mul_nonneg hq (learningRatio_nonneg xs p r)
lemma run_weightStep {n : ℕ} (O : IndependenceOracle n) (p r : ℕ) (xs : List (Word×Word)) (q : ℚ) (hq : 0≤q) :
    run O weightStep (xs,((p,r),rationalPair q))=some ((p,r),rationalPair (weightUpdate p r xs q)) := by
  simp only [weightStep,run_both,run_compose,run_fst,run_snd,Option.bind_some,run_applyIf]
  rw [run_natEqual]
  by_cases hpr : p=r
  · subst p; simp only [decide_true,Option.bind_some,ite_true,Option.map_some,weightUpdate]
  · simp only [hpr,decide_false,Option.bind_some,Option.map_some,Bool.false_eq_true,ite_false]
    rw [run_learningRatio]
    simp only [Option.bind_some,Option.map_some]
    rw [run_ratMul O q _ hq (learningRatio_nonneg xs p r)]
    simp only [Option.map_some,weightUpdate,hpr,ite_false]

lemma fold_weightStep {n : ℕ} (O : IndependenceOracle n) (p r : ℕ) (h : List (List (Word×Word)))
    (q : ℚ) (hq : 0≤q) :
    foldValue (run O weightStep) h ((p,r),rationalPair q)=some
      ((p,r),rationalPair (h.foldl (fun q xs => weightUpdate p r xs q) q)) := by
  induction h generalizing q with
  | nil => rfl
  | cons xs h ih =>
    rw [foldValue,run_weightStep O p r xs q hq,Option.bind_some]
    exact ih _ (weightUpdate_nonneg p r xs q hq)
lemma run_historyWeightCode {n : ℕ} (O : IndependenceOracle n) (p r : ℕ) (h : List (List (Word×Word))) :
    run O historyWeightCode (h,(p,r))=some (rationalPair (historyWeightValue p r h)) := by
  change ((foldValue (run O weightStep) h ((p,r),rationalPair 4)).bind fun z => some z.2)=_
  rw [fold_weightStep O p r h 4 (by norm_num)]
  rfl
end Expression

lemma countPlainValue_source {n : ℕ} (xs : List (Set (Fin n⊕Fin n))) :
    Expression.countPlainValue (sampleEncode xs)=xs.countP (fun S => decide (PlainState (pairedSlots n) S)) := by
  simp only [Expression.countPlainValue,sampleEncode,List.countP_map,plainValue_source,Function.comp_def]
lemma countDefectValue_source {n : ℕ} (xs : List (Set (Fin n⊕Fin n))) (p r : Fin n) :
    Expression.countDefectValue (sampleEncode xs) p.val r.val=
      xs.countP (fun S => decide (DefectState (pairedSlots n) (slotPair p) (slotPair r) S)) := by
  simp only [Expression.countDefectValue,sampleEncode,List.countP_map,defectValue_source,Function.comp_def]

lemma weightUpdate_source {n : ℕ} (xs : List (Set (Fin n⊕Fin n))) (p r : Fin n)
    (w : ((Fin n⊕Fin n)×(Fin n⊕Fin n)) → ((Fin n⊕Fin n)×(Fin n⊕Fin n)) → ℚ) :
    Expression.weightUpdate p.val r.val (sampleEncode xs) (w (slotPair p) (slotPair r))=
      rationalLearn (pairedSlots n) w xs (slotPair p) (slotPair r) := by
  unfold Expression.weightUpdate rationalLearn
  by_cases hpr : p=r
  · subst p; simp
  · have hv : p.val≠r.val := fun he => hpr (Fin.ext he)
    have hs : slotPair p≠slotPair r := fun he => hpr ((slotPair_inj p r).mp he)
    rw [ite_eq_right hv,ite_eq_left ⟨slotPair_mem p,slotPair_mem r,hs⟩,rationalTypeRatio]
    rw [Expression.learningRatio,countPlainValue_source,countDefectValue_source]

lemma historyWeight_source {n : ℕ} (h : List (List (Set (Fin n⊕Fin n)))) (p r : Fin n) :
    Expression.historyWeightValue p.val r.val (historyEncode h)=
      rationalHistory (pairedSlots n) id h (slotPair p) (slotPair r) := by
  have hf : ∀ (l : List (List (Set (Fin n⊕Fin n))))
      (w : ((Fin n⊕Fin n)×(Fin n⊕Fin n)) → ((Fin n⊕Fin n)×(Fin n⊕Fin n)) → ℚ),
      (historyEncode l).foldl (fun q xs => Expression.weightUpdate p.val r.val xs q) (w (slotPair p) (slotPair r))=
        (l.foldl (fun w xs => rationalLearn (pairedSlots n) w xs) w) (slotPair p) (slotPair r) := by
    intro l
    induction l with
    | nil => intro w; rfl
    | cons xs l ih =>
      intro w
      change (historyEncode l).foldl _ (Expression.weightUpdate p.val r.val (sampleEncode xs) (w (slotPair p) (slotPair r)))=_
      rw [weightUpdate_source]
      exact ih _
  exact hf h (fun _ _ => 4)

namespace Expression

lemma run_listAppend {n : ℕ} (O : IndependenceOracle n) {a} (xs ys : List (Value a)) :
    run O listAppend (xs,ys)=some (xs++ys) := by
  have hf : ∀ (us vs : List (Value a)),foldValue (run O cons) us vs=some (us.reverse++vs) := by
    intro us
    induction us with
    | nil => intro vs; rfl
    | cons u us ih => intro vs; simpa [foldValue,run,List.reverse_cons,List.append_assoc] using ih (u::vs)
  simp only [listAppend,onLeft,run_compose,run_both,run_fst,run_snd,Option.bind_some]
  rw [run_listReverse]
  simp only [Option.bind_some,Option.map_some]
  change foldValue (run O cons) xs.reverse ys=_
  rw [hf,List.reverse_reverse]

lemma run_productStep {n : ℕ} (O : IndependenceOracle n) {a b}
    (x : Value a) (zs : List (Value a × Value b)) (ys : List (Value b)) :
    run O productStep (x,(zs,ys))=some (zs++ys.map (fun y => (x,y)),ys) := by
  simp only [productStep,run_both,run_compose,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_mapWith O swap (fun y x => (x,y)) (fun _ _ => rfl)]
  simp only [Option.map_some,Option.bind_some]
  rw [run_listAppend]
  rfl
lemma run_productCode {n : ℕ} (O : IndependenceOracle n) {a b}
    (xs : List (Value a)) (ys : List (Value b)) :
    run O productCode (xs,ys)=some ((xs ×ˢ ys)) := by
  have hf : ∀ (us : List (Value a)) (acc : List (Value a × Value b)),
      foldValue (run O productStep) us (acc,ys)=some (acc++(us ×ˢ ys),ys) := by
    intro us
    induction us with
    | nil => intro acc; simp [foldValue]
    | cons u us ih =>
      intro acc
      rw [foldValue,run_productStep,Option.bind_some,ih]
      simp [List.product_cons,List.append_assoc]
  change ((foldValue (run O productStep) xs ([],ys)).bind fun z => some z.1)=_
  rw [hf]
  rfl

lemma run_indexPairs {n : ℕ} (O : IndependenceOracle n) (k : ℕ) :
    run O indexPairs k=some ((List.range k) ×ˢ (List.range k)) := by
  simp only [indexPairs,run_compose,run_both]
  rw [run_rangeCode]
  simp only [Option.bind_some,Option.map_some]
  exact run_productCode O _ _
end Expression

open Expression
lemma controlled_listAppend {a : DataType} : Controlled (listAppend (a:=a)) := by
  unfold listAppend
  apply controlled_compose
  · exact controlled_onLeft _ controlled_listReverse
  · apply controlled_fold (Expression.cons (a:=a)) (controlled_atomic _ trivial) (.mul (.constant 2) .input)
    intro n O xs z pre post he y hy
    have hh := foldValue_eq_foldl (run O (cons (a:=a))) (fun z x => x::z) (fun _ _ => rfl) pre z
    rw [hh] at hy
    cases hy
    rw [List.foldl_flip_cons_eq_append',width_list_append,width_list_reverse]
    have hp : width (a:=.list a) pre≤width (a:=.list a) xs := by rw [he,width_list_append]; omega
    rw [width_pair (a:=.list a) (b:=.list a)]
    dsimp [SizePolynomial.eval]
    omega
lemma width_list_map_pair {a b : DataType} (x : Value a) (ys : List (Value b)) :
    width (a:=.list (.prod a b)) (ys.map (fun y => (x,y)))≤
      4*(width x+1)*(width (a:=.list b) ys+1) := by
  have he : width (a:=.list (.prod a b)) (ys.map (fun y => (x,y)))=
      (4*width x+2)*ys.length+width (a:=.list b) ys := by
    induction ys with
    | nil => rfl
    | cons y ys ih =>
      simp only [List.map_cons,width_cons (a:=.prod a b),width_pair (a:=a) (b:=b),ih,
        List.length_cons,width_cons (a:=b)]
      ring
  rw [he]
  have hl := list_length_le_width ys
  nlinarith
lemma width_list_product {a b : DataType} (xs : List (Value a)) (ys : List (Value b)) :
    width (a:=.list (.prod a b)) (xs ×ˢ ys)≤
      8*(width (a:=.list a) xs+1)*(width (a:=.list b) ys+1) := by
  have hh : width (a:=.list (.prod a b)) (xs ×ˢ ys)≤
      4*width (a:=.list a) xs*(width (a:=.list b) ys+1) := by
    induction xs with
    | nil => simp only [List.nil_product,width_nil (a:=.prod a b)]; omega
    | cons x xs ih =>
      rw [List.product_cons,width_list_append (a:=.prod a b)]
      have hx := width_list_map_pair x ys
      rw [width_cons (a:=a)]
      nlinarith
  nlinarith
lemma controlled_productStep {a b : DataType} : Controlled (productStep (a:=a) (b:=b)) := by
  have hm := controlled_mapWith (Expression.swap (a:=b) (b:=a)) controlled_swap
  have ha := controlled_listAppend (a:=.prod a b)
  unfold productStep
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma fold_productStep {n : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (xs : List (Value a)) (zs : List (Value a×Value b)) (ys : List (Value b)) :
    foldValue (run O (productStep (a:=a) (b:=b))) xs (zs,ys)=some (zs++(xs ×ˢ ys),ys) := by
  induction xs generalizing zs with
  | nil => simp [foldValue]
  | cons x xs ih =>
    rw [foldValue,run_productStep,Option.bind_some,ih]
    simp [List.product_cons,List.append_assoc]
lemma controlled_productCode {a b : DataType} : Controlled (productCode (a:=a) (b:=b)) := by
  unfold productCode
  apply controlled_compose
  · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
  · apply controlled_compose
    · apply controlled_fold productStep controlled_productStep
        (.mul (.constant 32) (.mul (.add .input (.constant 1)) (.add .input (.constant 1))))
      intro n O xs z pre post he y hy
      rcases z with ⟨zs,ys⟩
      rw [fold_productStep] at hy
      cases hy
      have hp : width (a:=.list a) pre≤width (a:=.list a) xs := by rw [he,width_list_append]; omega
      have hb := width_list_product pre ys
      rw [width_pair (a:=.list (.prod a b)) (b:=.list b),width_list_append,
        width_pair (a:=.list a) (b:=.prod (.list (.prod a b)) (.list b)),
        width_pair (a:=.list (.prod a b)) (b:=.list b)]
      dsimp [SizePolynomial.eval]
      nlinarith
    · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma controlled_wordGet : Controlled wordGet := by
  have hg := controlled_getD (a:=.bool)
  unfold wordGet
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma controlled_wordNot : Controlled wordNot := by
  have hm := controlled_mapWith (c:=.unit) (fst >>> boolNot) (by
    apply controlled_compose; exact controlled_atomic _ trivial; exact controlled_boolNot)
  have hf := controlled_fromList
  unfold wordNot
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma controlled_wordCountStep : Controlled wordCountStep := by unfold wordCountStep; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma fold_wordCount_bound {n : ℕ} (O : IndependenceOracle n) (xs : List Bool) (z y : ℕ)
    (hy : foldValue (run O wordCountStep) xs z=some y) : y≤z+xs.length := by
  induction xs generalizing z with
  | nil => cases hy; simp
  | cons b xs ih =>
    cases b with
    | false => have hh := ih z hy; simp only [List.length_cons]; omega
    | true => have hh := ih (z+1) hy; simp only [List.length_cons]; omega
lemma controlled_wordCount : Controlled wordCount := by
  unfold wordCount
  apply controlled_compose
  · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
  · apply controlled_compose
    · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
    · apply controlled_fold wordCountStep controlled_wordCountStep (.mul (.constant 2) .input)
      intro n O xs z pre post he y hy
      have hh := bits_length_mono (fold_wordCount_bound O pre z y hy)
      have ha := bits_length_add z pre.length
      have hp : pre.length≤xs.length := by rw [he,List.length_append]; omega
      have hl := bits_length_le_value pre.length
      rw [width_nat,width_pair (a:=.list .bool) (b:=.nat),width_nat,width_list_bool]
      dsimp [SizePolynomial.eval]
      omega
lemma controlled_deficiency : Controlled deficiencyCode := by
  have hl := controlled_wordLength
  have hc := controlled_wordCount
  have hn := controlled_wordNot
  have hs := controlled_natSub
  unfold deficiencyCode
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)

open Expression
lemma controlled_normalizeRat : Controlled normalizeRat := by
  have hg := controlled_gcd
  unfold normalizeRat
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma controlled_ratAdd : Controlled ratAdd := by
  have hg := controlled_normalizeRat
  unfold ratAdd
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma controlled_ratMul : Controlled ratMul := by
  have hg := controlled_normalizeRat
  unfold ratMul
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma controlled_ratDiv : Controlled ratDiv := by
  have hg := controlled_normalizeRat
  unfold ratDiv
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma controlled_ratLess : Controlled ratLess := by unfold ratLess; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_ratMinOne : Controlled ratMinOne := by unfold ratMinOne; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))

lemma iterateM_succ_last {A : Type*} (f : A → Option A) (k : ℕ) (x : A) :
    iterateM f (k+1) x=(iterateM f k x).bind f := by
  induction k generalizing x with
  | zero => simp [iterateM]
  | succ k ih =>
    simp only [iterateM,Option.bind_assoc]
    congr 1
    funext y
    exact ih y
open Expression
open scoped Classical
namespace Effect
lemma realizes_repeat_succ_last {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a}
    (p : Effect a a) (ea : A → Value a) (eb : B → Value a) (k : ℕ) (x : Value a)
    (t : DrawTree A) (f : A → DrawTree B)
    (hp : Realizes O (repeatCode p) ea (k,x) t)
    (hq : ∀ y,Realizes O p eb (ea y) (f y)) :
    Realizes O (repeatCode p) eb (k+1,x) (t.bind f) := by
  intro bank
  rw [run_repeat,iterateM_succ_last,←run_repeat,hp,Option.bind_some,bankEval_bind]
  cases ht : bankEval t bank with
  | mk out rest =>
    cases out with
    | none => rfl
    | some y => exact hq y rest
lemma law_repeat_succ_last {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a}
    (p : Effect a a) (ea : A → Value a) (eb : B → Value a) (k : ℕ) (x : Value a)
    (t : DrawTree A) (f : A → DrawTree B)
    (hp : RealizesLaw O (repeatCode p) ea (k,x) t)
    (hq : ∀ y,RealizesLaw O p eb (ea y) (f y)) :
    RealizesLaw O (repeatCode p) eb (k+1,x) (t.bind f) := by
  classical
  rcases hp with ⟨u,hu,hp⟩
  choose g hg hq using hq
  exact ⟨u.bind g,hu.bind hg,realizes_repeat_succ_last O p ea eb k x u g hp hq⟩

lemma phaseRepeat_bind {A B : Type*} (f : ℕ → A → DrawTree (Option A)) (t : DrawTree B)
    (g : B → A) (k : ℕ) :
    (t.bind (fun x => phaseRepeat f (k+1) (g x)))=
      (t.bind (fun x => phaseRepeat f k (g x))).optionBind (f (k+1)) := by
  simp only [phaseRepeat,DrawTree.optionBind,DrawTree.bind_assoc]
lemma law_phaseRepeat {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a}
    (p : Effect a (Optional a)) (e : ℕ → A → Value a)
    (f : ℕ → A → DrawTree (Option A))
    (hp : ∀ j x,RealizesLaw O p (optionEncode (e (j+1))) (e j x) (f (j+1) x))
    (k : ℕ) (x : A) :
    RealizesLaw O (repeatCode (optionContinue p)) (optionEncode (e k))
      (k,optionEncode (e 0) (some x)) (phaseRepeat f k x) := by
  induction k with
  | zero => exact ⟨.leaf (some x),.leaf (some x),fun _ => rfl⟩
  | succ k ih =>
    apply law_repeat_succ_last O (optionContinue p) (optionEncode (e k)) _ k _ _ _ ih
    intro y
    exact law_optionContinue O p (e k) (e (k+1)) (f (k+1)) y (hp k)

lemma searchRepeat_done {X : Type*} (step : X → DrawTree X) (P : X → Prop) (k : ℕ) (y : FiniteChain.Inside P) :
    treeRepeat (searchStep step P) k (.inr y)=.leaf (.inr y) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih
lemma searchRepeat_finish {X : Type*} [Fintype X] (step : X → DrawTree X) (P : X → Prop) (k : ℕ) (x : X) :
    (treeRepeat (searchStep step P) k (.inl x)).map searchFinish=hittingTree step P k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [treeRepeat,searchStep,DrawTree.map_bind,DrawTree.bind_map,hittingTree]
    congr 1
    funext y
    by_cases hy : P y
    · rw [dite_eq_left hy,searchRepeat_done,dite_eq_left hy]; rfl
    · rw [dite_eq_right hy,ih,dite_eq_right hy]

lemma law_hitStep {n : ℕ} (O : IndependenceOracle n) {X : Type*} {a}
    (step : Effect a a) (test : Expression a .bool) (e : X → Value a)
    (f : X → DrawTree X) (P : X → Prop)
    (hs : ∀ x,RealizesLaw O step e (e x) (f x))
    (ht : ∀ x,run O test (e x)=some (decide (P x))) (u : SearchState X P) :
    RealizesLaw O (hitStepCode step test) (searchEncode e) (searchEncode e u) (searchStep f P u) := by
  unfold hitStepCode
  cases u with
  | inl x =>
    apply law_choose O _ _ _ _ _ _ false rfl
    change RealizesLaw O (map (precompose fst step) (both ident test)) _ _ _
    apply law_map O _ _ e _ _ _ _
    · exact law_precompose O fst step _ _ _ _ rfl (hs x)
    · intro y
      rw [run_both,run_ident,Option.bind_some,ht]
      by_cases hy : P y
      · simp only [hy,dite_eq_left,decide_true,Option.map_some]; rfl
      · simp only [hy,decide_false,Option.map_some]; rfl
  | inr y =>
    apply law_choose O _ _ _ _ _ _ true rfl
    change RealizesLaw O (pure ident) (searchEncode e) _ (.leaf (.inr y))
    exact (realizes_pure O ident (searchEncode e) _ (Sum.inr y) rfl).law

lemma law_hitting {n : ℕ} (O : IndependenceOracle n) {X : Type*} [Fintype X] {a}
    (step : Effect a a) (test : Expression a .bool) (e : X → Value a)
    (f : X → DrawTree X) (P : X → Prop)
    (hs : ∀ x,RealizesLaw O step e (e x) (f x))
    (ht : ∀ x,run O test (e x)=some (decide (P x))) (k : ℕ) (x : X) :
    RealizesLaw O (hittingCode step test) (optionEncode (fun y : FiniteChain.Inside P => e y.val))
      (k,e x) (hittingTree f P k x) := by
  unfold hittingCode
  apply law_precompose O _ _ _ _ (k,searchEncode e (.inl x : SearchState X P)) _ rfl
  rw [←searchRepeat_finish]
  apply law_map O _ _ (searchEncode e) _ _ _ searchFinish
  · exact law_repeat O _ _ _ (law_hitStep O step test e f P hs ht) k (.inl x)
  · intro u
    cases u <;> rfl
end Effect

open Expression
namespace Effect
lemma law_recode {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b c}
    (p : Effect a b) (q : Expression b c) (ea : A → Value b) (eb : A → Value c)
    (x : Value a) (t : DrawTree A) (hp : RealizesLaw O p ea x t)
    (hq : ∀ y,run O q (ea y)=some (eb y)) : RealizesLaw O (map p q) eb x t := by
  have hh := law_map O p q ea eb x t id hp hq
  simpa only [DrawTree.map,id_eq,DrawTree.bind_leaf] using hh

lemma law_withContext {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b c}
    (p : Effect (.prod c a) b) (e : A → Value b) (ctx : Value c) (x : Value a)
    (t : DrawTree A) (hp : RealizesLaw O p e (ctx,x) t) :
    RealizesLaw O (withContext p) (fun y => (ctx,e y)) (ctx,x) t := by
  unfold withContext
  rw [←DrawTree.bind_leaf t]
  apply law_letIn O p _ e _ _ t DrawTree.leaf hp
  intro y
  exact (realizes_pure O _ _ _ y rfl).law

lemma law_optionMap {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b c}
    (p : Effect a (Optional b)) (q : Expression b c) (ea : A → Value b) (eb : B → Value c)
    (x : Value a) (t : DrawTree (Option A)) (f : A → B)
    (hp : RealizesLaw O p (optionEncode ea) x t)
    (hq : ∀ y,run O q (ea y)=some (eb (f y))) :
    RealizesLaw O (map p (optionMapCode q)) (optionEncode eb) x (t.map (Option.map f)) := by
  apply law_map O p _ (optionEncode ea) (optionEncode eb) x t _ hp
  intro y
  cases y with
  | none => rfl
  | some y =>
    change ((run O q (ea y)).bind fun z => some (true,z))=_
    rw [hq]; rfl

lemma law_optionRecode {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b c}
    (p : Effect a (Optional b)) (q : Expression b c) (ea : A → Value b) (eb : A → Value c)
    (x : Value a) (t : DrawTree (Option A))
    (hp : RealizesLaw O p (optionEncode ea) x t)
    (hq : ∀ y,run O q (ea y)=some (eb y)) :
    RealizesLaw O (map p (optionMapCode q)) (optionEncode eb) x t := by
  apply law_recode O p _ (optionEncode ea) (optionEncode eb) x t hp
  intro y
  cases y with
  | none => rfl
  | some y =>
    change ((run O q (ea y)).bind fun z => some (true,z))=_
    rw [hq]; rfl
end Effect

open scoped Classical
namespace Expression

lemma run_defectPairsCode {n : ℕ} (O : IndependenceOracle n) (S : Word×Word) :
    run O defectPairsCode S=some (defectPairsValue S) := by
  simp only [defectPairsCode,run_compose,run_both,run_fst,run_ident,Option.bind_some]
  rw [run_wordLength,Option.bind_some,run_indexPairs]
  simp only [Option.bind_some,Option.map_some]
  exact run_filterWith (a:=NN) (b:=StateData) O defectCode (fun pr S => defectValue pr.1 pr.2 S)
    (fun pr S => run_defectCode O pr.1 pr.2 S) _ S

lemma run_chainCode {n : ℕ} (O : IndependenceOracle n) (S : Word×Word) :
    run O chainCode S=some (chainValue S) := by
  simp only [chainCode,run_compose,run_both]
  rw [run_plainCode,run_defectPairsCode]
  simp only [Option.bind_some,run_compose,run_listLength,run_natEqZero,run_boolNot,Option.map_some]
  rw [run_boolOr]
  simp only [chainValue,decide_not]

lemma run_multiplierCode {n : ℕ} (O : IndependenceOracle n) (h : List (List (Word×Word))) (S : Word×Word) :
    run O multiplierCode (h,S)=some (rationalPair (multiplierValue h S)) := by
  simp only [multiplierCode,run_letIn,run_compose,run_snd,Option.bind_some]
  rw [run_defectPairsCode]
  simp only [Option.bind_some,run_applyIf,run_compose,run_snd,run_listLength,run_natEqZero]
  by_cases he : (defectPairsValue S).length=0
  · simp only [he,decide_true,ite_true,multiplierValue,run_constant]
    rfl
  · simp only [he,decide_false,Option.bind_some,Bool.false_eq_true,ite_false,multiplierValue,
      run_compose,run_both,run_fst,run_snd,run_constant,Option.map_some]
    rw [run_headD]
    simp only [Option.map_some,Option.bind_some]
    exact run_historyWeightCode O _ _ h
end Expression

lemma mem_defectPairsValue {n : ℕ} (S : Set (Fin n⊕Fin n)) (p r : ℕ) :
    (p,r)∈Expression.defectPairsValue (stateEncode S) ↔
      ∃ (hp : p<n) (hr : r<n),DefectState (pairedSlots n) (slotPair ⟨p,hp⟩) (slotPair ⟨r,hr⟩) S := by
  simp only [Expression.defectPairsValue,List.mem_filter,List.mem_product,List.mem_range,stateEncode_left_length]
  constructor
  · rintro ⟨⟨hp,hr⟩,h⟩
    exact ⟨hp,hr,of_decide_eq_true (by simpa only [defectValue_source S ⟨p,hp⟩ ⟨r,hr⟩] using h)⟩
  · rintro ⟨hp,hr,h⟩
    exact ⟨⟨hp,hr⟩,by simpa only [defectValue_source S ⟨p,hp⟩ ⟨r,hr⟩] using decide_eq_true h⟩

lemma defectPairs_nonempty_source {n : ℕ} (S : Set (Fin n⊕Fin n)) :
    (Expression.defectPairsValue (stateEncode S)).length≠0 ↔
      ∃ p r,DefectState (pairedSlots n) p r S := by
  rw [Ne, List.length_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨⟨p,r⟩,hm⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨hp,hr,hd⟩ := (mem_defectPairsValue S p r).mp hm
    exact ⟨_,_,hd⟩
  · rintro ⟨p,r,h⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h.1
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h.2.1
    exact List.ne_nil_of_mem ((mem_defectPairsValue S i.val j.val).mpr ⟨i.isLt,j.isLt,h⟩)

lemma chainValue_source {n : ℕ} (S : Set (Fin n⊕Fin n)) :
    Expression.chainValue (stateEncode S)=decide (ChainState (pairedSlots n) S) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hh
    apply decide_eq_true
    have ho : Expression.plainValue (stateEncode S)=true ∨
        decide ((Expression.defectPairsValue (stateEncode S)).length≠0)=true := by
      simpa only [Expression.chainValue,Bool.or_eq_true] using hh
    rcases ho with hp|hd
    · exact Or.inl (of_decide_eq_true (by simpa only [plainValue_source] using hp))
    · exact Or.inr ((defectPairs_nonempty_source S).mp (of_decide_eq_true hd))
  · intro hh
    rw [Expression.chainValue,Bool.or_eq_true]
    rcases of_decide_eq_true hh with hp|hd
    · exact Or.inl (by rw [plainValue_source]; exact decide_eq_true hp)
    · exact Or.inr (decide_eq_true ((defectPairs_nonempty_source S).mpr hd))

lemma multiplierValue_source {n : ℕ} (h : List (List (Set (Fin n⊕Fin n)))) (S : Set (Fin n⊕Fin n)) :
    Expression.multiplierValue (historyEncode h) (stateEncode S)=
      rationalMultiplier (pairedSlots n) (rationalHistory (pairedSlots n) id h) S := by
  unfold Expression.multiplierValue rationalMultiplier
  by_cases he : (Expression.defectPairsValue (stateEncode S)).length=0
  · have hn : ¬∃ p r,DefectState (pairedSlots n) p r S := by
      intro hh
      exact ((defectPairs_nonempty_source S).mpr hh) he
    rw [ite_eq_left he,dite_eq_right hn]
  · let l := Expression.defectPairsValue (stateEncode S)
    have hl : l≠[] := by simpa only [List.length_eq_zero_iff] using he
    have hm : l.headD (0,0)∈l := by
      cases hh : l with
      | nil => exact False.elim (hl hh)
      | cons a l => simp
    obtain ⟨hp,hr,hd⟩ := (mem_defectPairsValue S (l.headD (0,0)).1 (l.headD (0,0)).2).mp hm
    have hex : ∃ p r,DefectState (pairedSlots n) p r S := ⟨_,_,hd⟩
    rw [ite_eq_right he,dite_eq_left hex,historyWeight_source h ⟨_,hp⟩ ⟨_,hr⟩]
    have hh := hex.choose_spec.choose_spec.unique hd
    exact congrArg₂ (rationalHistory (pairedSlots n) id h) hh.1.symm hh.2.symm

namespace Expression

lemma run_updateAt {n : ℕ} (O : IndependenceOracle n) (i : ℕ) (w : Word) (j : ℕ) (b : Bool) :
    run O updateAt (i,(w,(j,b)))=some (if i=j then b else w[i]?.getD false) := by
  simp only [updateAt,run_applyIf,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_natEqual,run_wordGet]
  by_cases h : i=j <;> simp [h]
lemma run_updateWord {n : ℕ} (O : IndependenceOracle n) (w : Word) (j : ℕ) (b : Bool) :
    run O updateWord (w,(j,b))=some (w.set j b) := by
  simp only [updateWord,run_compose,run_both,run_fst,run_ident,Option.bind_some]
  rw [run_wordLength,Option.bind_some,run_rangeCode]
  simp only [Option.bind_some,Option.map_some,run_compose]
  rw [run_mapWith (a:=.nat) (b:=.bool) (c:=.prod .word (.prod .nat .bool)) O updateAt
    (fun i z => if i=z.2.1 then z.2.2 else z.1[i]?.getD false)
    (fun i z => run_updateAt O i z.1 z.2.1 z.2.2)]
  simp only [Option.bind_some]
  rw [run_fromList]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_set]
    rw [List.getElem?_eq_getElem (by simpa using hi)]
    simp only [Option.getD_some]
    by_cases he : i=j
    · simp [he]
    · simp [he,Ne.symm he]

lemma run_splitWord {n : ℕ} (O : IndependenceOracle n) (w : Word) (k : ℕ) :
    run O splitWord (w,k)=some (w.take k,w.drop k) := by
  change ((run O (splitAtCode (a:=.bool)) (w,k)).bind (run O (both (fst >>> fromList) (snd >>> fromList))))=_
  rw [run_splitAtCode]
  simp only [Option.bind_some,run_both,run_compose,run_fst,run_snd]
  rw [run_fromList,run_fromList]
  rfl

lemma run_exchangeWord {n : ℕ} (O : IndependenceOracle n) (w : Word) (a b : ℕ) :
    run O exchangeWord (w,(a,b))=some ((w.set a false).set b true) := by
  simp only [exchangeWord,run_letIn,run_compose,run_both,run_fst,run_snd,run_constant,
    Option.bind_some,Option.map_some]
  rw [run_updateWord]
  simp only [Option.bind_some]
  exact run_updateWord O _ _ _

lemma run_exchangeSetCode {n : ℕ} (O : IndependenceOracle n) (S : Word×Word) (a b : ℕ) :
    run O exchangeSetCode (S,(a,b))=some
      ((((S.1++S.2).set a false).set b true).take S.1.length,
       (((S.1++S.2).set a false).set b true).drop S.1.length) := by
  simp only [exchangeSetCode,run_compose,run_both,run_fst,run_snd,run_append,Option.bind_some,Option.map_some]
  rw [run_exchangeWord,run_wordLength]
  simp only [Option.bind_some,Option.map_some]
  exact run_splitWord O _ _
end Expression

open scoped Classical
lemma position_inj {n : ℕ} (i j : Fin n⊕Fin n) : position i=position j ↔ i=j := by
  exact ⟨fun h => finSumFinEquiv.injective (Fin.ext h),fun h => congrArg position h⟩

lemma combinedEncode_update {n : ℕ} (S : Set (Fin n⊕Fin n)) (i : Fin n⊕Fin n) (b : Bool) :
    (combinedEncode S).set (position i) b=combinedEncode (if b then insert i S else S\{i}) := by
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    let j : Fin n⊕Fin n := finSumFinEquiv.symm ⟨k,by simpa using hk'⟩
    have hj : position j=k := by simp [position,j]
    have ha := combinedEncode_get S j
    have hb := combinedEncode_get (if b then insert i S else S\{i}) j
    rw [hj,List.getElem?_eq_getElem (by simpa using hk),Option.getD_some] at ha
    rw [hj,List.getElem?_eq_getElem hk',Option.getD_some] at hb
    rw [List.getElem_set,ha,hb]
    have he : position i=k ↔ i=j := by rw [←hj,position_inj]
    simp only [he]
    cases b <;> by_cases hij : i=j <;> simp [hij,eq_comm]

lemma exchangeSetCode_source {n : ℕ} (O : IndependenceOracle n) (S : Set (Fin n⊕Fin n)) (a : ExchangeChoice S) :
    run O Expression.exchangeSetCode (stateEncode S,(position a.1.val,position a.2.val))=
      some (stateEncode (exchangedSet S a)) := by
  rw [Expression.run_exchangeSetCode,stateEncode_left_length]
  change some (((combinedEncode S).set (position a.1.val) false |>.set (position a.2.val) true).take n,
    ((combinedEncode S).set (position a.1.val) false |>.set (position a.2.val) true).drop n)=_
  rw [combinedEncode_update]
  simp only [Bool.false_eq_true,ite_false]
  rw [combinedEncode_update]
  simp only [ite_true]
  change some ((combinedEncode (exchangedSet S a)).take n,(combinedEncode (exchangedSet S a)).drop n)=_
  have hh (x y : Word) : some ((x++y).take x.length,(x++y).drop x.length)=some (x,y) := by simp
  simpa only [combinedEncode, stateEncode_left_length, Prod.eta] using hh (stateEncode (exchangedSet S a)).1 (stateEncode (exchangedSet S a)).2

open scoped Classical
namespace Expression
lemma historyWeightValue_nonneg (p r : ℕ) (h : List (List (Word×Word))) :
    0≤historyWeightValue p r h := by
  have hf : ∀ (l : List (List (Word×Word))) (q : ℚ),0≤q →
      0≤l.foldl (fun q xs => weightUpdate p r xs q) q := by
    intro l
    induction l with
    | nil => intro q hq; exact hq
    | cons xs l ih => intro q hq; exact ih _ (weightUpdate_nonneg p r xs q hq)
  exact hf h 4 (by norm_num)
lemma multiplierValue_nonneg (h : List (List (Word×Word))) (S : Word×Word) :
    0 ≤ multiplierValue h S := by
  unfold multiplierValue
  split_ifs
  · norm_num
  · exact historyWeightValue_nonneg _ _ h

lemma rationalRho_nonneg (n : ℕ) : 0≤rationalRho n := by
  cases n with
  | zero => norm_num [rationalRho]
  | succ n =>
    unfold rationalRho
    have hh : (1:ℚ) ≤ 2*((n+1:ℕ):ℚ) := by push_cast; linarith [Nat.cast_nonneg (α:=ℚ) n]
    exact sub_nonneg.mpr ((div_le_one (by positivity : (0:ℚ)<2*((n+1:ℕ):ℚ))).mpr hh)
lemma run_rhoCode {n : ℕ} (O : IndependenceOracle n) (m : ℕ) :
    run O rhoCode m=some (rationalPair (rationalRho m)) := by
  simp only [rhoCode,run_applyIf,run_natEqZero]
  by_cases hm : m=0
  · subst m; simp only [decide_true,Option.bind_some,ite_true,run_constant]
    norm_num [rationalPair,rationalRho]
  · simp only [hm,decide_false,Option.bind_some,Bool.false_eq_true,ite_false]
    change run O (both (both (snd (a:=.nat) (b:=.nat)) (constant 1) >>> natSub) snd >>> normalizeRat) (m,m*2)=_
    simp only [run_compose,run_both,run_snd,run_constant,Option.bind_some,Option.map_some]
    rw [run_natSub]
    simp only [Option.bind_some]
    rw [run_normalizeRat_pair]
    congr 2
    have hp : 1 ≤ m*2 := by omega
    have hz : (m:ℚ)≠0 := by exact_mod_cast hm
    rw [Nat.cast_sub hp,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    unfold rationalRho
    field_simp

end Expression

lemma annealCode_source {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r j : ℕ) (h : List (List (Set (Fin n⊕Fin n)))) (S : Set (Fin n⊕Fin n)) :
    run O Expression.annealCode (((r,j),historyEncode h),stateEncode S)=
      some (rationalPair ((rationalRho n^j)^(oracleDeficiency n r O S))) := by
  simp only [Expression.annealCode,Expression.run_compose,Expression.run_both,
    Expression.run_fst,Expression.run_snd,Option.bind_some,Option.map_some]
  rw [Expression.run_wordLength,stateEncode_left_length]
  simp only [Option.bind_some]
  rw [Expression.run_rhoCode]
  simp only [Option.bind_some]
  rw [Expression.run_ratPowCode O _ (Expression.rationalRho_nonneg n)]
  simp only [Option.bind_some]
  rw [deficiencyCode_source M₁ M₂ O hO hE₁ hE₂ r _ _ (stateEncode_left_length S) (stateEncode_right_length S),stateEncode_repr]
  simp only [Option.bind_some,Option.map_some]
  exact Expression.run_ratPowCode O _ (pow_nonneg (Expression.rationalRho_nonneg n) _) _

lemma weightCode_source {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r j : ℕ) (h : List (List (Set (Fin n⊕Fin n)))) (S : Set (Fin n⊕Fin n)) :
    run O Expression.weightCode (((r,j),historyEncode h),stateEncode S)=some
      (rationalPair (rationalMultiplier (pairedSlots n) (rationalHistory (pairedSlots n) id h) S*
        (rationalRho n^j)^(oracleDeficiency n r O S))) := by
  simp only [Expression.weightCode,Expression.run_compose,Expression.run_both,
    Expression.run_fst,Expression.run_snd,Option.bind_some,Option.map_some]
  rw [Expression.run_multiplierCode,multiplierValue_source,annealCode_source M₁ M₂ O hO hE₁ hE₂]
  simp only [Option.bind_some,Option.map_some]
  apply Expression.run_ratMul
  · rw [←multiplierValue_source]
    exact Expression.multiplierValue_nonneg _ _
  · exact pow_nonneg (pow_nonneg (Expression.rationalRho_nonneg n) j) _

open Expression
namespace Effect

lemma bernoulliCode_source {n : ℕ} (O : IndependenceOracle n) (q : ℚ) :
    Realizes O bernoulliCode id (rationalPair q) (DrawTree.bernoulli q) := by
  have hd : q.den-1+1=q.den := by have hh := q.den_pos; omega
  have hh : Realizes O draw Fin.val q.den (.draw (q.den-1) DrawTree.leaf) := by
    simpa only [hd] using realizes_draw O (q.den-1)
  have hp : Realizes O (precompose (snd (a:=.nat)) draw) Fin.val (rationalPair q)
      (.draw (q.den-1) DrawTree.leaf) :=
    realizes_precompose (a:=NN) (b:=.nat) (c:=.nat) O snd draw Fin.val (rationalPair q) q.den _ rfl hh
  change Realizes O (letIn (precompose snd draw) (pure (both snd (fst >>> fst) >>> less))) id
    (rationalPair q) _
  have hr := realizes_letIn O (precompose (snd (a:=.nat)) draw)
    (pure (both snd (fst >>> fst) >>> less)) Fin.val id (rationalPair q)
    (.draw (q.den-1) DrawTree.leaf) (fun (i : Fin (q.den-1+1)) => .leaf (decide (i.val<q.num.natAbs))) hp
    (fun i => realizes_pure O _ id _ _ rfl)
  exact hr
end Effect

open Expression
open scoped Classical

lemma acceptanceCode_source {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r j : ℕ) (h : List (List (Set (Fin n⊕Fin n)))) (S T : ChainIndex (pairedSlots n)) :
    run O acceptanceCode (((r,j),historyEncode h),(stateEncode S.val,stateEncode T.val))=some
      (rationalPair (rationalAcceptance (pairedSlots n) (rationalHistory (pairedSlots n) id h)
        (oracleAnneal n r O j) S T)) := by
  have hn (U : Set (Fin n⊕Fin n)) : 0 ≤ rationalWeight (pairedSlots n)
      (rationalHistory (pairedSlots n) id h) (oracleAnneal n r O j) U := by
    unfold rationalWeight
    apply mul_nonneg
    · rw [←multiplierValue_source]; exact multiplierValue_nonneg _ _
    · exact pow_nonneg (pow_nonneg (rationalRho_nonneg n) j) _
  simp only [acceptanceCode,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [weightCode_source M₁ M₂ O hO hE₁ hE₂,weightCode_source M₁ M₂ O hO hE₁ hE₂]
  simp only [Option.bind_some,Option.map_some]
  change ((run O ratDiv (rationalPair (rationalWeight (pairedSlots n) (rationalHistory (pairedSlots n) id h)
    (oracleAnneal n r O j) T.val),rationalPair (rationalWeight (pairedSlots n) (rationalHistory (pairedSlots n) id h)
    (oracleAnneal n r O j) S.val))).bind (run O ratMinOne))=_
  rw [run_ratDiv O _ _ (hn _) (hn _),Option.bind_some]
  exact run_ratMinOne O _ (div_nonneg (hn _) (hn _))

open scoped Classical
namespace Expression

lemma run_membersCode {n : ℕ} (O : IndependenceOracle n) (w : Word) :
    run O membersCode w=some (memberPositions w) := by
  simp only [membersCode,run_compose,run_both,run_ident,run_wordLength,Option.bind_some,Option.map_some]
  rw [run_rangeCode]
  simp only [Option.bind_some]
  apply run_filterWith
  intro i w
  exact run_wordGet O w i
end Expression

open Expression
namespace Effect

lemma uniformVia_size {A : Type*} [Fintype A] [Nonempty A] (m : ℕ) (e : Fin m ≃ A)
    (h : m=Fintype.card A) (hc : m-1+1=m) :
    (DrawTree.draw (m-1) (fun i => .leaf (e (Fin.cast hc i))))=
      DrawTree.uniformVia A ((finCongr h.symm).trans e) := by
  subst m
  rfl

lemma realizes_uniformList {n : ℕ} (O : IndependenceOracle n) {A : Type*} [Fintype A] [Nonempty A]
    {a} (encode : A → Value a) (l : List (Value a)) (e : Fin l.length ≃ A)
    (he : ∀ i,l.get i=encode (e i)) :
    RealizesLaw O uniformList encode l (DrawTree.uniformChoice A) := by
  have hlen : l.length=Fintype.card A := by simpa using Fintype.card_congr e
  have hp : 0<l.length := by rw [hlen]; exact Fintype.card_pos
  let hc : l.length-1+1=l.length := by omega
  let ee : Fin (Fintype.card A) ≃ A := (finCongr hlen.symm).trans e
  let t : DrawTree A := .draw (l.length-1) (fun i => .leaf (e (Fin.cast hc i)))
  have ht : t=DrawTree.uniformVia A ee := uniformVia_size l.length e hlen hc
  apply RealizesLaw.reindex (u:=t)
  · apply Realizes.law
    change Realizes O (letIn (precompose listLength draw) (pure _)) encode l
      ((DrawTree.draw (l.length-1) DrawTree.leaf).bind (fun i => .leaf (e (Fin.cast hc i))))
    apply realizes_letIn O (a:=.list a) (b:=.nat) (c:=a) _ _
      (fun i : Fin (l.length-1+1) => i.val) encode l _ _
    · apply realizes_precompose O (a:=.list a) (b:=.nat) (c:=.nat) listLength draw
        (fun i : Fin (l.length-1+1) => i.val) l l.length _ (run_listLength O l)
      simpa only [hc] using realizes_draw O (l.length-1)
    · intro i
      apply realizes_pure
      simp only [run_compose,run_both,run_fst,run_snd,run_constant,Option.bind_some,Option.map_some]
      rw [run_getDCode]
      rw [List.getD_eq_getElem (l:=l) (d:=zeroValue a) (n:=i.val) (by omega)]
      exact congrArg some (he (Fin.cast hc i))
  · rw [ht]
    exact (DrawTree.uniformVia_reindexed A ee).symm
end Effect

open scoped Classical
open Expression
lemma run_exchangePositionsCode {n : ℕ} (O : IndependenceOracle n) (S : Word×Word) :
    run O exchangePositionsCode S=some (exchangePositions S) := by
  simp only [exchangePositionsCode,run_compose,run_both,run_append,Option.bind_some,run_membersCode,
    run_wordNot,Option.map_some]
  exact run_productCode O (a:=.nat) (b:=.nat) _ _
lemma exchangeListEquiv_val {n : ℕ} (S : Set (Fin n⊕Fin n))
    (i : Fin (exchangePositions (stateEncode S)).length) :
    (position (exchangeListEquiv S i).1.val,position (exchangeListEquiv S i).2.val)=
      (exchangePositions (stateEncode S)).get i := by
  simp [exchangeListEquiv,exchangePositionEquiv,memberPositionEquiv_val,List.Nodup.getEquiv]

namespace Effect

lemma proposal_source {n : ℕ} (O : IndependenceOracle n) (S : Set (Fin n⊕Fin n))
    [Nonempty (ExchangeChoice S)] :
    RealizesLaw O proposal (fun a : ExchangeChoice S => (position a.1.val,position a.2.val))
      (stateEncode S) (DrawTree.uniformChoice (ExchangeChoice S)) := by
  apply law_precompose O _ _ _ _ _ _ (run_exchangePositionsCode O _)
  exact realizes_uniformList O _ _ (exchangeListEquiv S) (fun i => (exchangeListEquiv_val S i).symm)
end Effect

section
open Expression
open scoped Classical

variable {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r j : ℕ) (h : List (List (Set (Fin n⊕Fin n))))
local notation "GS" => pairedSlots n
local notation "ctx" => (((r,j),historyEncode h) : Value WeightContext)
local notation "W" => rationalHistory GS id h
local notation "F" => oracleAnneal n r O j
open Effect
include M₁ M₂ hO hE₁ hE₂

lemma offerCore_source (S : ChainIndex GS) (U : Set (Fin n⊕Fin n)) :
    RealizesLaw O offerCore (fun T : ChainIndex GS => stateEncode T.val)
      ((ctx,stateEncode S.val),stateEncode U)
      (if hu : ChainState GS U then
        (DrawTree.bernoulli (rationalAcceptance GS W F S ⟨U,hu⟩)).map
          (fun b => if b then ⟨U,hu⟩ else S)
      else .leaf S) := by
  have ht : run O ((snd (a:=WeightInput) (b:=StateData)) >>> chainCode) ((ctx,stateEncode S.val),stateEncode U)=some (decide (ChainState GS U)) := by
    change run O chainCode (stateEncode U)=_
    rw [run_chainCode,chainValue_source]
  unfold offerCore
  apply law_choose O _ _ _ _ _ _ _ ht
  by_cases hu : ChainState GS U
  · simp only [hu,decide_true,ite_true,dite_eq_left]
    change RealizesLaw O (letIn (precompose _ bernoulliCode) (pure _)) _ _
      ((DrawTree.bernoulli (rationalAcceptance GS W F S ⟨U,hu⟩)).bind (fun b => .leaf (if b then ⟨U,hu⟩ else S)))
    apply law_letIn O (a:=OfferInput) (b:=.bool) (c:=StateData) _ _ id _ _ _ _
    · apply Realizes.law
      apply realizes_precompose O _ _ _ _ (rationalPair (rationalAcceptance GS W F S ⟨U,hu⟩))
      · exact acceptanceCode_source M₁ M₂ O hO hE₁ hE₂ r j h S ⟨U,hu⟩
      · exact bernoulliCode_source O _
    · intro b
      apply Realizes.law
      apply realizes_pure
      cases b <;> rfl
  · simp only [hu,decide_false,Bool.false_eq_true,ite_false]
    exact (realizes_pure O _ _ _ S rfl).law

lemma offerCode_source (S : ChainIndex GS) (a : ExchangeChoice S.val) :
    RealizesLaw O offerCode (fun T : ChainIndex GS => stateEncode T.val)
      ((ctx,stateEncode S.val),(position a.1.val,position a.2.val))
      (rationalExchange GS W F S a) := by
  unfold offerCode
  apply law_precompose O _ _ _ _ ((ctx,stateEncode S.val),stateEncode (exchangedSet S.val a))
  · simp only [run_both,run_compose,run_fst,run_snd,Option.bind_some,Option.map_some]
    rw [exchangeSetCode_source]
    rfl
  · exact offerCore_source M₁ M₂ O hO hE₁ hE₂ r j h S _

lemma activeStepCode_source (S : ChainIndex GS) [Nonempty (ExchangeChoice S.val)] :
    RealizesLaw O activeStepCode (fun T : ChainIndex GS => stateEncode T.val) (ctx,stateEncode S.val)
      ((DrawTree.uniformChoice (ExchangeChoice S.val)).bind (rationalExchange GS W F S)) := by
  unfold activeStepCode
  apply law_letIn O (a:=WeightInput) (b:=NN) (c:=StateData) _ _
    (fun a : ExchangeChoice S.val => (position a.1.val,position a.2.val)) _ _ _ _
  · exact law_precompose O snd proposal _ _ _ _ rfl (proposal_source O S.val)
  · exact offerCode_source M₁ M₂ O hO hE₁ hE₂ r j h S

lemma stepCode_source (hn : 0<n) (S : ChainIndex GS) :
    RealizesLaw O stepCode (fun T : ChainIndex GS => stateEncode T.val) (ctx,stateEncode S.val)
      (rationalMetropolis GS (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n) W F S) := by
  let : Nonempty (ExchangeChoice S.val) := Fintype.card_pos_iff.mp (by
    rw [exchangeChoice_card GS (pairedSlots_fresh n) (pairedSlots_cover n),pairedSlots_length]; positivity)
  unfold stepCode rationalMetropolis
  apply law_letIn O (a:=WeightInput) (b:=.bool) (c:=StateData) _ _ id _ _ _ _
  · apply Realizes.law
    exact realizes_precompose O _ bernoulliCode id _ (rationalPair (1/2)) _ (by norm_num [run_constant,rationalPair]) (bernoulliCode_source O _)
  · intro b
    apply law_choose O _ _ _ _ _ _ b rfl
    cases b with
    | false =>
      exact law_precompose O fst activeStepCode _ _ _ _ rfl (activeStepCode_source M₁ M₂ O hO hE₁ hE₂ r j h S)
    | true => exact (realizes_pure O _ _ _ S rfl).law
end

section
open Expression
open scoped Classical

lemma binaryValue_injective_length (x y : Word) (hlen : x.length=y.length)
    (hv : binaryValue x=binaryValue y) : x=y := by
  induction x generalizing y with
  | nil => cases y <;> simp_all
  | cons b x ih =>
    cases y with
    | nil => simp at hlen
    | cons c y =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hlen
      have hbc : b=c := by cases b <;> cases c <;> simp_all [binaryValue] <;> omega
      subst c
      have hxy : binaryValue x=binaryValue y := by cases b <;> simp_all [binaryValue]
      rw [ih y hlen hxy]

lemma binaryValue_replicate_false (k : ℕ) : binaryValue (List.replicate k false)=0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,binaryValue,ih]

lemma padded_range (w : Word) (k : ℕ) (hk : w.length≤k) :
    (List.range k).map (fun i => w[i]?.getD false)=w++List.replicate (k-w.length) false := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    by_cases h : i<w.length
    · rw [List.getElem?_eq_getElem h,List.getElem_append_left h]; rfl
    · rw [List.getElem?_eq_none (by omega),List.getElem_append_right (by omega)]
      simp
namespace Expression

lemma run_paddedBitsCode {n : ℕ} (O : IndependenceOracle n) (k v : ℕ) (hv : v<2^k) :
    run O paddedBitsCode (k,v)=some (List.ofFn ((wordEquiv k).symm ⟨v,hv⟩)) := by
  have hk : v.bits.length≤k := by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr hv
  have hr : (List.range k).map (fun i => v.bits[i]?.getD false)=v.bits++List.replicate (k-v.bits.length) false := padded_range _ _ hk
  have he : ((List.range k).map (fun i => v.bits[i]?.getD false)).reverse=
      List.ofFn ((wordEquiv k).symm ⟨v,hv⟩) := by
    apply List.reverse_inj.mp
    simp only [List.reverse_reverse]
    apply binaryValue_injective_length
    · simp
    · rw [hr,binaryValue_append,binaryValue_replicate_false,binaryValue_bits,binaryValue_ofFn_reverse]
      simp
  simp only [paddedBitsCode,run_compose,run_both,run_fst,run_snd,Option.bind_some]
  rw [run_rangeCode]
  change ((run O (mapWith (c:=.word) (Expression.swap >>> wordGet)) (List.range k,v.bits)).bind fun l =>
    (run O fromList l).bind (run O reverse))=_
  rw [run_mapWith O (c:=.word) (Expression.swap >>> wordGet) (fun i w => w[i]?.getD false) (fun i w => run_wordGet O w i)]
  simp only [Option.bind_some]
  rw [run_fromList]
  exact congrArg some he

lemma plainDecodeCode_source {n : ℕ} (O : IndependenceOracle n) (v : Fin (2^n)) :
    run O plainDecodeCode (n,v.val)=some (stateEncode (wordPlainEquiv n ((wordEquiv n).symm v)).val.val) := by
  rw [plainDecodeCode,run_compose,run_paddedBitsCode O n v.val v.isLt,Option.bind_some,run_both,run_ident,Option.bind_some,run_wordNot]
  simp only [Option.map_some]
  congr 1
  change (List.ofFn _,(List.ofFn _).map Bool.not)=_
  unfold stateEncode wordPlainEquiv
  simp only []
  apply Prod.ext
  · apply List.ext_getElem <;> simp [transversal]
  · apply List.ext_getElem <;> simp [transversal]
end Expression
namespace Effect
attribute [local instance] OAI.CommonBasesFPRAS.MachineCode.Effect.instNonemptyPlainIndexSumFinPairedSlots
lemma plainCode_source {n : ℕ} (O : IndependenceOracle n) :
    RealizesLaw O plainCode (fun S : PlainIndex (pairedSlots n) => stateEncode S.val.val) n
      (DrawTree.uniformVia _ (canonicalPlainEnumeration n)) := by
  have hp : 0<2^n := by positivity
  let hc : 2^n-1+1=2^n := by omega
  let e : Fin (2^n) ≃ PlainIndex (pairedSlots n) := (wordEquiv n).symm.trans (wordPlainEquiv n)
  let t : DrawTree (PlainIndex (pairedSlots n)) := .draw (2^n-1) (fun i => .leaf (e (Fin.cast hc i)))
  have ht : t=DrawTree.uniformVia _ (canonicalPlainEnumeration n) := by
    exact uniformVia_size (2^n) e (plainIndex_card n).symm hc
  rw [←ht]
  apply Realizes.law
  change Realizes O (letIn (a:=.nat) (b:=.nat) (c:=StateData) _ _) _ n
    ((DrawTree.draw (2^n-1) DrawTree.leaf).bind (fun i => .leaf (e (Fin.cast hc i))))
  apply realizes_letIn O (a:=.nat) (b:=.nat) (c:=StateData) _ _
    (fun i : Fin (2^n-1+1) => i.val) _ n _ _
  · apply realizes_precompose O _ draw _ _ (2^n)
    · change run O powCode (2,n)=_; exact run_powCode O 2 n
    · simpa only [hc] using realizes_draw O (2^n-1)
  · intro i
    apply realizes_pure
    exact plainDecodeCode_source O (Fin.cast hc i)

end Effect

lemma rationalHistory_map {X : Type*} {n : ℕ} (f : X → List (Set (Fin n⊕Fin n))) (h : List X) :
    rationalHistory (pairedSlots n) id (h.map f)=rationalHistory (pairedSlots n) f h := by
  simp only [rationalHistory,List.foldl_map,id_eq]
lemma historyEncode_take {n : ℕ} (h : List (List (Set (Fin n⊕Fin n)))) (j : ℕ) :
    (historyEncode h).take j=historyEncode (h.take j) := by simp only [historyEncode,List.map_take]

variable {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r N : ℕ) (h : List (PhaseSample n N)) (j : ℕ) (hn : 0<n)
local notation "GS" => pairedSlots n
local notation "ctx" => (((r,j),historyEncode (h.map (observedSets n N))) : Value WeightContext)
open Effect
include M₁ M₂ hO hE₁ hE₂

lemma storedStepCode_source (S : ChainIndex GS) :
    RealizesLaw O storedStepCode (fun T : ChainIndex GS => stateEncode T.val) (ctx,stateEncode S.val)
      (canonicalStepTree n hn r O N h j S) := by
  unfold storedStepCode
  apply law_precompose O storedStepPrep stepCode _ _
    (((r,j),historyEncode ((h.map (observedSets n N)).take j)),stateEncode S.val)
  · simp only [storedStepPrep,run_both,run_compose,run_fst,run_snd,Option.bind_some,Option.map_some]
    rw [run_takeCode,historyEncode_take]; rfl
  · have hp := stepCode_source M₁ M₂ O hO hE₁ hE₂ r j
      ((h.map (observedSets n N)).take j) hn S
    have he : rationalHistory GS id ((h.map (observedSets n N)).take j)=rationalStored n N h j := by
      rw [←List.map_take,rationalHistory_map]; rfl
    rw [he] at hp
    exact hp.reindex (canonicalMetropolis_reindexed n hn _ _ S)

lemma traceCode_source (cap : ℕ) (S : PlainIndex GS) :
    RealizesLaw O traceCode (optionEncode (fun T : PlainIndex GS => stateEncode T.val.val))
      (cap+1,(ctx,stateEncode S.val.val)) (canonicalTraceTree n hn r O N h j cap S) := by
  unfold traceCode canonicalTraceTree
  apply law_optionRecode O _ snd
    (fun y : PlainIndex GS => (ctx,stateEncode y.val.val)) _ _ _
  · exact law_hitting O (withContext storedStepCode) (snd >>> Expression.plainCode)
      (fun T : ChainIndex GS => (ctx,stateEncode T.val)) (canonicalStepTree n hn r O N h j)
      (plainPredicate GS)
      (fun T => law_withContext O storedStepCode _ ctx _ _
        (storedStepCode_source M₁ M₂ O hO hE₁ hE₂ r N h j hn T))
      (fun T => plainCode_source O T.val) (cap+1) S.val
  · intro T; rfl
end

section
open Expression
namespace Effect

lemma law_withOptionContext {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b c}
    (p : Effect (.prod c a) (Optional b)) (e : A → Value b) (ctx : Value c) (x : Value a)
    (t : DrawTree (Option A)) (hp : RealizesLaw O p (optionEncode e) (ctx,x) t) :
    RealizesLaw O (withOptionContext p) (optionEncode (fun y => (ctx,e y))) (ctx,x) t := by
  unfold withOptionContext
  rw [←DrawTree.bind_leaf t]
  apply law_letIn O p _ (optionEncode e) _ _ t DrawTree.leaf hp
  intro y
  apply Realizes.law
  apply realizes_pure
  cases y <;> rfl
end Effect

open Expression
open scoped Classical
section Correct
variable {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r N L : ℕ) (h : List (PhaseSample n N)) (hn : 0<n) (cap : ℕ)
local notation "GS" => pairedSlots n
local notation "tau" => 20*n^4*(n*(L+1)+2)
local notation "ctx" => (((r,historyEncode (h.map (observedSets n N))),(cap,tau)) : Value RestartContext)
local notation "enc" => (fun j (x : PlainIndex GS) => ((ctx,j),stateEncode (Subtype.val (Subtype.val x))))
open Effect
include M₁ M₂ hO hE₁ hE₂
lemma traceAtCode_source (j : ℕ) (x : PlainIndex GS) :
    RealizesLaw O traceAtCode (optionEncode (fun y : PlainIndex GS => stateEncode y.val.val))
      (enc j x) (canonicalTraceTree n hn r O N h j cap x) := by
  apply law_precompose O traceAtPrep traceCode _ _ _ _
  · rfl
  · exact traceCode_source M₁ M₂ O hO hE₁ hE₂ r N h j hn cap x
lemma restartTick_source (j : ℕ) (x : PlainIndex GS) :
    RealizesLaw O restartTick (optionEncode (enc (j+1))) (enc j x)
      (DrawTree.iterate (canonicalTraceTree n hn r O N h (j+1) cap) tau x) := by
  apply law_precompose O restartTickPrep _ _ _ _ _
  · rfl
  · apply law_iterate O (withOptionContext traceAtCode) (enc (j+1)) _ _ tau x
    intro y
    apply law_withOptionContext
    exact traceAtCode_source M₁ M₂ O hO hE₁ hE₂ r N L h hn cap (j+1) y
end Correct

open Effect
lemma canonicalRestart_phaseRepeat {n : ℕ} (hn : 0<n) (r : ℕ) (O : IndependenceOracle n)
    (N L : ℕ) (h : List (PhaseSample n N)) (cap k : ℕ) :
    canonicalRestartTree n hn r O N L h cap k =
      ((@DrawTree.uniformVia (PlainIndex (pairedSlots n)) _ (plainIndex_nonempty (pairedSlots n) (pairedSlots_fresh n) (pairedSlots_cover n)) (canonicalPlainEnumeration n)).bind
        (fun x => phaseRepeat (fun j => DrawTree.iterate (canonicalTraceTree n hn r O N h j cap)
          (20*n^4*(n*(L+1)+2))) k x)) := by
  let := plainIndex_nonempty (pairedSlots n) (pairedSlots_fresh n) (pairedSlots_cover n)
  induction k with
  | zero => rfl
  | succ k ih => rw [canonicalRestartTree,ih,Effect.phaseRepeat_bind]

variable {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r N L : ℕ) (h : List (PhaseSample n N)) (hn : 0<n) (cap k : ℕ)
local notation "GS" => pairedSlots n
local notation "tau" => 20*n^4*(n*(L+1)+2)
local notation "ctx" => (((r,historyEncode (h.map (observedSets n N))),(cap,tau)) : Value RestartContext)
local notation "enc" => (fun j (x : PlainIndex GS) => ((ctx,j),stateEncode (Subtype.val (Subtype.val x))))
open Effect
include M₁ M₂ hO hE₁ hE₂
lemma restartCode_source :
    RealizesLaw O restartCode (optionEncode (fun x : PlainIndex GS => stateEncode x.val.val))
      (n,(k,ctx)) (canonicalRestartTree n hn r O N L h cap k) := by
  rw [canonicalRestart_phaseRepeat]
  unfold restartCode
  apply law_optionRecode O _ snd (enc k) _ _ _
  · apply law_letIn O _ _ (fun x : PlainIndex GS => stateEncode x.val.val) _ _ _ _
    · exact law_precompose O fst plainCode _ _ n _ rfl (Effect.plainCode_source O)
    · intro x
      apply law_precompose O restartPrep _ _ _ _ _
      · rfl
      · exact law_phaseRepeat O restartTick enc _
          (restartTick_source M₁ M₂ O hO hE₁ hE₂ r N L h hn cap) k x
  · intro x; rfl
end

open Expression
open scoped Classical
namespace Expression

lemma run_allRange {n : ℕ} (O : IndependenceOracle n) {a} (p : Expression (.prod .nat a) .bool)
    (f : ℕ → Value a → Bool) (hp : ∀ i x,run O p (i,x)=some (f i x)) (m : ℕ) (x : Value a) :
    run O (allRange p) (m,x)=some (decide (∀ i < m,f i x=true)) := by
  simp only [allRange,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_rangeCode]
  simp only [Option.bind_some,run_compose]
  rw [run_mapWith O p f hp,Option.bind_some,run_listAll]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp
end Expression
lemma rationalPair_pos {q : ℚ} (hq : 0 ≤ q) : 0 < (rationalPair q).1 ↔ 0 < q := by
  have hd : (0:ℚ) < (rationalPair q).2 := by exact_mod_cast rationalPair_den q
  conv_rhs => rw [←rationalPair_value hq]
  rw [div_pos_iff_of_pos_right hd]
  exact_mod_cast (Iff.rfl : 0 < (rationalPair q).1 ↔ 0 < (rationalPair q).1)
namespace Expression

lemma run_pairPositiveCode {n : ℕ} (O : IndependenceOracle n) (h : List (List (Word×Word))) (p q : ℕ) :
    run O pairPositiveCode (h,(p,q))=some (decide (0 < historyWeightValue p q h)) := by
  simp only [pairPositiveCode,run_compose]
  rw [run_historyWeightCode]
  simp only [Option.bind_some,run_compose,run_fst]
  rw [run_natEqZero]
  simp only [Option.bind_some,run_boolNot]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq]
  exact (Nat.pos_iff_ne_zero.symm).trans (rationalPair_pos (historyWeightValue_nonneg p q h))

lemma run_slotRowCode {n : ℕ} (O : IndependenceOracle n) (p m : ℕ) (h : List (List (Word×Word))) :
    run O slotRowCode (p,(m,h))=some (decide (∀ q < m,0 < historyWeightValue p q h)) := by
  change run O (allRange (a:=.prod .nat HistoryData) _) (m,(p,h))=_
  rw [run_allRange (a:=.prod .nat HistoryData) O _ (fun q u => decide (0 < historyWeightValue u.1 q u.2))]
  · simp
  · intro q u; exact run_pairPositiveCode O u.2 u.1 q
lemma run_slotsPositiveCode {n : ℕ} (O : IndependenceOracle n) (m : ℕ) (h : List (List (Word×Word))) :
    run O slotsPositiveCode (m,h)=some (decide (∀ p < m,∀ q < m,0 < historyWeightValue p q h)) := by
  change run O (allRange slotRowCode) (m,(m,h))=_
  rw [run_allRange (a:=.prod .nat HistoryData) O _ (fun p u => decide (∀ q < u.1,0 < historyWeightValue p q u.2))
    (fun p u => run_slotRowCode O p u.1 u.2)]
  simp
lemma run_prefixPositiveCode {n : ℕ} (O : IndependenceOracle n) (j m : ℕ) (h : List (List (Word×Word))) :
    run O prefixPositiveCode (j,(m,h))=some (decide (∀ p < m,∀ q < m,0 < historyWeightValue p q (h.take j))) := by
  simp only [prefixPositiveCode,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_takeCode]
  exact run_slotsPositiveCode O m (h.take j)
lemma run_historyPositiveCode {n : ℕ} (O : IndependenceOracle n) (m : ℕ) (h : List (List (Word×Word))) :
    run O historyPositiveCode (m,h)=some (decide (∀ j ≤ h.length,∀ p < m,∀ q < m,0 < historyWeightValue p q (h.take j))) := by
  simp only [historyPositiveCode,run_compose,run_both,run_snd,run_ident,run_constant,Option.bind_some,Option.map_some]
  rw [run_listLength]
  change run O (allRange prefixPositiveCode) (h.length+1,(m,h))=_
  rw [run_allRange (a:=.prod .nat HistoryData) O _ (fun j u => decide (∀ p < u.1,∀ q < u.1,0 < historyWeightValue p q (u.2.take j)))
    (fun j u => run_prefixPositiveCode O j u.1 u.2)]
  simp only [decide_eq_true_eq,Nat.lt_add_one_iff]
end Expression

lemma rationalHistory_inactive {Γ X : Type*} [DecidableEq Γ] (gs : List (Γ×Γ)) (s : X → List (Set Γ))
    (h : List X) (p q : Γ×Γ) (hp : ¬(p∈gs ∧ q∈gs ∧ p≠q)) : rationalHistory gs s h p q=4 := by
  have hh : ∀ (l : List X) (w : (Γ×Γ) → (Γ×Γ) → ℚ),
      (l.foldl (fun w x => rationalLearn gs w (s x)) w) p q=w p q := by
    intro l
    induction l with
    | nil => intro w; rfl
    | cons x l ih => intro w; rw [List.foldl_cons,ih]; simp [rationalLearn,hp]
  exact hh h _
lemma rationalHistoryPositive_slots {n N : ℕ} (h : List (PhaseSample n N)) :
    rationalHistoryPositive n N h ↔ ∀ j ≤ h.length,∀ p q : Fin n,0 < rationalStored n N h j (slotPair p) (slotPair q) := by
  constructor
  · intro hh j hj p q; exact hh j hj _ _
  · intro hh j hj p q
    by_cases hpq : p∈pairedSlots n ∧ q∈pairedSlots n ∧ p≠q
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hpq.1
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hpq.2.1
      exact hh j hj a b
    · change 0 < rationalHistory _ _ _ p q
      have hz := rationalHistory_inactive (pairedSlots n) (observedSets n N) (h.take j) p q hpq
      rw [hz]; norm_num
lemma historyPositiveCode_source {n N : ℕ} (O : IndependenceOracle n) (h : List (PhaseSample n N)) :
    run O Expression.historyPositiveCode (n,historyEncode (h.map (observedSets n N)))=
      some (decide (rationalHistoryPositive n N h)) := by
  rw [Expression.run_historyPositiveCode]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [rationalHistoryPositive_slots]
  have hlen : (historyEncode (h.map (observedSets n N))).length=h.length := by simp [historyEncode]
  rw [hlen]
  constructor
  · intro hp j hj p q
    have hh := hp j hj p.val p.isLt q.val q.isLt
    rw [historyEncode_take,historyWeight_source,←List.map_take,rationalHistory_map] at hh
    exact hh
  · intro hp j hj p hp' q hq'
    rw [historyEncode_take,historyWeight_source (p:=⟨p,hp'⟩) (r:=⟨q,hq'⟩),←List.map_take,rationalHistory_map]
    exact hp j hj ⟨p,hp'⟩ ⟨q,hq'⟩
end MachineCode

namespace DrawTree
lemma Reindexed.lift_map {A B : Type*} (f : A → B) (t : DrawTree A) (u : DrawTree B)
    (h : Reindexed (t.map f) u) : ∃ v, Reindexed t v ∧ v.map f=u := by
  classical
  induction t generalizing u with
  | leaf a =>
    cases h
    exact ⟨.leaf a,.leaf a,rfl⟩
  | draw w k ih =>
    cases h with
    | draw _ _ l e hh =>
      choose v hv he using fun i => ih i (l (e i)) (hh i)
      refine ⟨.draw w (fun i => v (e.symm i)),.draw w k _ e (by intro i; simpa using hv i),?_⟩
      simp only [DrawTree.map,DrawTree.bind] at he ⊢
      congr 1
      funext i
      simpa using he (e.symm i)
end DrawTree
namespace MachineCode

open Expression
namespace Effect
lemma law_unmap {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b}
    (p : Effect a b) (e : B → Value b) (x : Value a) (t : DrawTree A) (f : A → B)
    (h : RealizesLaw O p e x (t.map f)) : RealizesLaw O p (e ∘ f) x t := by
  rcases h with ⟨u,hu,hp⟩
  obtain ⟨v,hv,rfl⟩ := hu.lift_map f t u
  refine ⟨v,hv,fun bank => ?_⟩
  simpa only [bankEval_map,Option.map_map,Function.comp_def] using hp bank

lemma sampleRepeat_finish {X : Type*} (f : X → DrawTree X) (k : ℕ) (acc : List X) (x : X) :
    (treeRepeat (sampleTickTree f) k (acc,x)).map (fun s => s.1.reverse++[s.2])=
      (DrawTree.sample f k x).map (fun v => acc.reverse++v.toList) := by
  induction k generalizing acc x with
  | zero => rfl
  | succ k ih =>
    simp only [treeRepeat,sampleTickTree,DrawTree.map_bind,DrawTree.bind_map,DrawTree.sample]
    congr 1
    funext y
    rw [ih]
    change (DrawTree.sample f k y).map (fun v => (x::acc).reverse++v.toList)=
      ((DrawTree.sample f k y).map (fun v => (x,v))).map (fun v : X × FiniteChain.Sample X k => acc.reverse++v.1::v.2.toList)
    rw [DrawTree.map_map]
    congr 1
    funext v
    simp [List.reverse_cons,List.append_assoc]

lemma law_sampleTick {n : ℕ} (O : IndependenceOracle n) {X : Type*} {a}
    (p : Effect a a) (e : X → Value a) (f : X → DrawTree X)
    (hp : ∀ x,RealizesLaw O p e (e x) (f x)) (s : List X × X) :
    RealizesLaw O (sampleTick p) (fun u => (u.1.map e,e u.2)) (s.1.map e,e s.2) (sampleTickTree f s) := by
  unfold sampleTick sampleTickTree DrawTree.map
  apply law_letIn O (a:=.prod (.list a) a) (b:=a) (c:=.prod (.list a) a) _ _ e _ _ _ _
  · exact law_precompose O snd p _ _ _ _ rfl (hp s.2)
  · intro y
    exact (realizes_pure O _ _ _ (s.2::s.1,y) rfl).law

lemma law_sample {n : ℕ} (O : IndependenceOracle n) {X : Type*} {a}
    (p : Effect a a) (e : X → Value a) (f : X → DrawTree X)
    (hp : ∀ x,RealizesLaw O p e (e x) (f x)) (k : ℕ) (x : X) :
    RealizesLaw O (sampleCode p) (fun v => v.toList.map e) (k,e x) (DrawTree.sample f k x) := by
  apply law_unmap O (a:=.prod .nat a) (b:=.list a) (sampleCode p)
    (fun l : List X => l.map e) (k,e x) (DrawTree.sample f k x) (fun v => v.toList)
  unfold sampleCode
  apply law_precompose O _ _ _ _ (k,(([] : List (Value a)),e x)) _ rfl
  have he := sampleRepeat_finish f k [] x
  simp only [List.reverse_nil,List.nil_append] at he
  rw [←he]
  apply law_map O _ _ (fun u : List X × X => (u.1.map e,e u.2)) _ _ _ _
  · exact law_repeat O (sampleTick p) _ _ (law_sampleTick O p e f hp) k ([],x)
  · intro u
    simp only [sampleFinish,run_compose,run_both,run_fst,run_snd,run_constant,Option.bind_some,Option.map_some]
    rw [run_listReverse]
    change run O listAppend ((u.1.map e).reverse,[e u.2])=_
    rw [run_listAppend]
    simp
end Effect

section
open Expression
open scoped Classical
namespace Expression
lemma run_mapEach {n : ℕ} (O : IndependenceOracle n) {a b} (p : Expression a b)
    (f : Value a → Value b) (hp : ∀ x,run O p x=some (f x)) (xs : List (Value a)) :
    run O (mapEach p) xs=some (xs.map f) := by
  change run O (mapWith (c:=.unit) (fst >>> p)) (xs,())=_
  exact run_mapWith (c:=.unit) O _ (fun x _ => f x) (fun x _ => hp x) xs ()
end Expression
namespace Effect
lemma law_retainOption {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b}
    (p : Effect a (Optional b)) (e : A → Value b) (x : Value a)
    (t : DrawTree (Option A)) (hp : RealizesLaw O p (optionEncode e) x t) :
    RealizesLaw O (retainOption p) (optionEncode (fun y => (x,e y))) x t := by
  unfold retainOption
  rw [←DrawTree.bind_leaf t]
  apply law_letIn O p _ (optionEncode e) _ _ t DrawTree.leaf hp
  intro y
  apply Realizes.law
  apply realizes_pure
  cases y <;> rfl

end Effect
variable {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r N L : ℕ) (h : List (PhaseSample n N)) (hn : 0<n)
local notation "GS" => pairedSlots n
local notation "ctx" => ((params n r N L,historyEncode (h.map (observedSets n N))) : Value PhaseInput)
open Effect
include M₁ M₂ hO hE₁ hE₂
lemma phaseRestartCode_source :
    RealizesLaw O phaseRestartCode (optionEncode (fun x : PlainIndex GS => stateEncode x.val.val)) ctx
      (canonicalRestartTree n hn r O N L h (restartCap n L) h.length) := by
  apply law_precompose O phaseRestartPrep restartCode _ ctx _ _
  · simp only [phaseRestartPrep,params,run_both,run_compose,run_fst,run_snd,Option.bind_some,Option.map_some]
    rw [run_listLength]
    simp only [historyEncode,List.length_map]
    rfl
  · exact restartCode_source M₁ M₂ O hO hE₁ hE₂ r N L h hn _ _
lemma startCode_source :
    RealizesLaw O startCode (optionEncode (fun x : ChainIndex GS => stateEncode x.val)) ctx
      (canonicalStartTree n hn r O N L h) := by
  apply law_optionMap O phaseRestartCode ident (fun x : PlainIndex GS => stateEncode x.val.val) _ ctx _ Subtype.val
  · exact phaseRestartCode_source M₁ M₂ O hO hE₁ hE₂ r N L h hn
  · intro x; rfl
lemma phaseStepCode_source (x : ChainIndex GS) :
    RealizesLaw O phaseStepCode (fun y : ChainIndex GS => stateEncode y.val) (ctx,stateEncode x.val)
      (canonicalStepTree n hn r O N h h.length x) := by
  apply law_precompose O phaseStepPrep storedStepCode _ _ _ _
  · simp only [phaseStepPrep,params,run_both,run_compose,run_fst,run_snd,Option.bind_some,Option.map_some]
    rw [run_listLength]
    simp only [historyEncode,List.length_map]
    rfl
  · exact storedStepCode_source M₁ M₂ O hO hE₁ hE₂ r N h h.length hn x
lemma phaseSampleCode_source (x : ChainIndex GS) :
    RealizesLaw O phaseSampleCode (fun v : PhaseSample n N => sampleEncode (observedSets n N v))
      (ctx,stateEncode x.val) (DrawTree.sample (canonicalStepTree n hn r O N h h.length) (N-1) x) := by
  apply law_precompose O phaseSamplePrep _ _ _ _ _
  · simp only [phaseSamplePrep,params,run_both,run_compose,run_fst,run_snd,run_ident,run_constant,Option.bind_some,Option.map_some]
    rw [run_natSub]
    rfl
  · apply law_recode O _ (mapEach snd) (fun v : PhaseSample n N => v.toList.map (fun y => (ctx,stateEncode y.val))) _ _ _
    · exact law_sample O (withContext phaseStepCode) (fun y : ChainIndex GS => (ctx,stateEncode y.val)) _
        (fun y => law_withContext O phaseStepCode _ ctx _ _
          (phaseStepCode_source M₁ M₂ O hO hE₁ hE₂ r N L h hn y)) (N-1) x
    · intro v
      rw [run_mapEach O snd Prod.snd (fun _ => rfl)]
      simp only [sampleEncode,observedSets,List.map_map]
      rfl
omit M₁ M₂ hO hE₁ hE₂ in
lemma positiveTest_source : run O positiveTest ctx=some (decide (rationalHistoryPositive n N h)) :=
  historyPositiveCode_source O h
lemma phaseCode_source :
    RealizesLaw O phaseCode (optionEncode (fun v : PhaseSample n N => sampleEncode (observedSets n N v))) ctx
      (canonicalPhaseTree n hn r O N L h) := by
  unfold phaseCode canonicalPhaseTree
  apply law_choose O positiveTest _ _ _ ctx _ (decide (rationalHistoryPositive n N h)) (positiveTest_source O r N L h)
  by_cases hh : rationalHistoryPositive n N h
  · simp only [hh,decide_true,ite_true]
    apply law_optionBind O (retainOption startCode) (someCode phaseSampleCode)
      (fun x : ChainIndex GS => (ctx,stateEncode x.val)) _ ctx _ _
    · exact law_retainOption O startCode _ ctx _ (startCode_source M₁ M₂ O hO hE₁ hE₂ r N L h hn)
    · intro x
      exact law_some O phaseSampleCode _ _ _ (phaseSampleCode_source M₁ M₂ O hO hE₁ hE₂ r N L h hn x)
  · simp only [hh,decide_false,Bool.false_eq_true,ite_false]
    exact law_none (a:=PhaseInput) O _ ctx
end

open Expression

lemma bits_length_add_max (a b : ℕ) : (a+b).bits.length≤ max a.bits.length b.bits.length+1 := by
  simp only [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have ha := (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (Nat.le_max_left a.size b.size))
  have hb := (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (Nat.le_max_right a.size b.size))
  rw [pow_succ]
  omega

lemma pairHeight_pos (p : ℕ × ℕ) : 1≤pairHeight p := Nat.le_max_left _ _
lemma pairHeight_fst (p : ℕ × ℕ) : p.1.bits.length≤pairHeight p := (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
lemma pairHeight_snd (p : ℕ × ℕ) : p.2.bits.length≤pairHeight p := (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
lemma width_le_pairHeight (p : ℕ × ℕ) : width (a:=NN) p≤4*pairHeight p := by
  obtain ⟨a,b⟩ := p
  have h₀ := pairHeight_pos (a,b)
  have h₁ := pairHeight_fst (a,b)
  have h₂ := pairHeight_snd (a,b)
  dsimp only [Prod.fst,Prod.snd] at h₁ h₂
  rw [width_pair (a:=.nat) (b:=.nat),width_nat,width_nat]
  omega
lemma pairHeight_le_width (p : ℕ × ℕ) : pairHeight p≤width (a:=NN) p := by
  obtain ⟨a,b⟩ := p
  simp only [pairHeight,width_pair (a:=.nat) (b:=.nat),width_nat]
  omega
lemma pairHeight_normalize (a b : ℕ) : pairHeight (normalizePair a b)≤pairHeight (a,b) := by
  by_cases hb : b=0
  · subst b
    simp [normalizePair,pairHeight]
  · rw [normalizePair,ite_eq_right hb]
    have h₁ := bits_length_mono (Nat.div_le_self a (Nat.gcd a b))
    have h₂ := bits_length_mono (Nat.div_le_self b (Nat.gcd a b))
    dsimp [pairHeight]
    omega
lemma pairHeight_ratAdd_raw (a b c d : ℕ) :
    pairHeight (normalizePair (a*d+c*b) (b*d))≤pairHeight (a,b)+pairHeight (c,d)+1 := by
  apply (pairHeight_normalize _ _).trans
  have h₁ := bits_length_mul a d
  have h₂ := bits_length_mul c b
  have h₃ := bits_length_mul b d
  have h₄ := bits_length_add_max (a*d) (c*b)
  have ha := pairHeight_fst (a,b)
  have hb := pairHeight_snd (a,b)
  have hc := pairHeight_fst (c,d)
  have hd := pairHeight_snd (c,d)
  dsimp only [pairHeight] at *
  omega
lemma pairHeight_ratMul_raw (a b c d : ℕ) :
    pairHeight (normalizePair (a*c) (b*d))≤pairHeight (a,b)+pairHeight (c,d) := by
  apply (pairHeight_normalize _ _).trans
  have h₁ := bits_length_mul a c
  have h₂ := bits_length_mul b d
  have ha := pairHeight_fst (a,b)
  have hb := pairHeight_snd (a,b)
  have hc := pairHeight_fst (c,d)
  have hd := pairHeight_snd (c,d)
  have hp := pairHeight_pos (a,b)
  dsimp only [pairHeight] at *
  omega
lemma run_ratAdd_height {n : ℕ} (O : IndependenceOracle n) (p q y : ℕ×ℕ)
    (hy : run O ratAdd (p,q)=some y) : pairHeight y≤ pairHeight p+pairHeight q+1 := by
  obtain ⟨a,b⟩ := p
  obtain ⟨c,d⟩ := q
  rw [run_ratAdd_raw] at hy
  cases hy
  exact pairHeight_ratAdd_raw _ _ _ _
lemma run_ratMul_height {n : ℕ} (O : IndependenceOracle n) (p q y : ℕ×ℕ)
    (hy : run O ratMul (p,q)=some y) : pairHeight y≤ pairHeight p+pairHeight q+1 := by
  obtain ⟨a,b⟩ := p
  obtain ⟨c,d⟩ := q
  rw [run_ratMul_raw] at hy
  cases hy
  have hh := pairHeight_ratMul_raw a b c d
  omega
lemma fold_pairHeight {n : ℕ} (O : IndependenceOracle n) (p : Expression (.prod NN NN) NN)
    (hp : ∀ x z y,run O p (x,z)=some y → pairHeight y≤pairHeight x+pairHeight z+1)
    (xs : List (ℕ×ℕ)) (z y : ℕ×ℕ) (hy : foldValue (run O p) xs z=some y) :
    pairHeight y≤pairHeight z+width (a:=.list NN) xs := by
  induction xs generalizing z with
  | nil => cases hy; simp
  | cons x xs ih =>
    rw [foldValue] at hy
    cases he : run O p (x,z) with
    | none => simp [he] at hy
    | some w =>
      simp only [he,Option.bind_some] at hy
      have hw := hp x z w he
      have hh := ih w hy
      have hx := pairHeight_le_width x
      rw [width_cons (a:=NN)]
      omega
lemma controlled_pairFold (p : Expression (.prod NN NN) NN) (hp : Controlled p)
    (hg : ∀ {n : ℕ} (O : IndependenceOracle n) (x z y : ℕ×ℕ),
      run O p (x,z)=some y → pairHeight y≤pairHeight x+pairHeight z+1) : Controlled (.fold p) := by
  apply controlled_fold p hp (.mul (.constant 4) .input)
  intro n O xs z pre post he y hy
  have hh := fold_pairHeight O p (hg O) pre z y hy
  have hb := width_le_pairHeight y
  have hz := pairHeight_le_width z
  have hpre : width (a:=.list NN) pre≤width (a:=.list NN) xs := by rw [he,width_list_append]; omega
  simp only [SizePolynomial.eval,width_pair (a:=.list NN) (b:=NN)]
  omega
lemma controlled_ratSum : Controlled ratSumCode := by
  unfold ratSumCode
  apply controlled_compose
  · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
  · exact controlled_pairFold ratAdd controlled_ratAdd run_ratAdd_height
lemma controlled_ratProduct : Controlled ratProductCode := by
  unfold ratProductCode
  apply controlled_compose
  · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
  · exact controlled_pairFold ratMul controlled_ratMul run_ratMul_height


lemma controlled_wordTake : Controlled wordTake := by unfold wordTake; (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_clog : Controlled clogCode := by unfold clogCode; (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_rejectStep : Controlled rejectStep := by
  have h := controlled_wordTake
  unfold rejectStep
  repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma fold_reject_width {n : ℕ} (O : IndependenceOracle n) (xs : List Word)
    (v k : ℕ) (z : Bool×ℕ) (y : Value RejectState)
    (hy : foldValue (run O rejectStep) xs ((v,k),z)=some y) :
    y.1=(v,k) ∧ y.2.2.bits.length ≤ max z.2.bits.length v.bits.length := by
  induction xs generalizing z with
  | nil => cases hy; exact ⟨rfl,Nat.le_max_left _ _⟩
  | cons x xs ih =>
    rw [foldValue,run_rejectStep] at hy
    simp only [Option.bind_some] at hy
    split_ifs at hy with hh
    · have hi := ih _ hy
      refine ⟨hi.1,hi.2.trans ?_⟩
      have hb := bits_length_mono hh.le
      dsimp only [Prod.snd]
      exact max_le (hb.trans (Nat.le_max_right _ _)) (Nat.le_max_right _ _)
    · exact ih z hy
lemma controlled_rejectFold : Controlled (.fold rejectStep) := by
  apply controlled_fold rejectStep controlled_rejectStep (.mul (.constant 3) .input)
  intro n O xs z pre post he y hy
  obtain ⟨⟨v,k⟩,⟨b,u⟩⟩ := z
  change ℕ at v k u
  obtain ⟨⟨v',k'⟩,⟨b',u'⟩⟩ := y
  change ℕ at v' k' u'
  have hh := fold_reject_width O pre v k (b,u) ((v',k'),(b',u')) hy
  dsimp only [Prod.fst,Prod.snd] at hh
  rw [width_pair (a:=NN) (b:=Optional .nat),hh.1,width_pair (a:=.bool) (b:=.nat),width_bool,width_nat]
  simp only [SizePolynomial.eval,width_pair (a:=.list .word) (b:=RejectState),
    width_pair (a:=NN) (b:=Optional .nat),width_pair (a:=.bool) (b:=.nat),
    width_pair (a:=.nat) (b:=.nat),width_nat,width_bool] at *
  omega
lemma controlled_reject : Controlled rejectCode := by
  have h := controlled_rejectFold
  unfold rejectCode
  repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
namespace Effect
lemma controlled_pure {a b : DataType} (p : Expression a b) (hp : Controlled p) : Controlled (pure p) := by
  unfold pure; (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply _root_.OAI.CommonBasesFPRAS.MachineCode.controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_bind {a b c : DataType} (p : Effect a b) (q : Effect b c)
    (hp : Controlled p) (hq : Controlled q) : Controlled (bind p q) := by unfold bind; (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply _root_.OAI.CommonBasesFPRAS.MachineCode.controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_keep {a b : DataType} (p : Effect a b) (hp : Controlled p) : Controlled (keep p) := by
  unfold keep; (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply _root_.OAI.CommonBasesFPRAS.MachineCode.controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_letIn {a b c : DataType} (p : Effect a b) (q : Effect (.prod a b) c)
    (hp : Controlled p) (hq : Controlled q) : Controlled (letIn p q) :=
  controlled_bind _ _ (controlled_keep _ hp) hq
lemma controlled_draw : Controlled draw := by
  have h₁ := controlled_reject
  have h₂ := controlled_clog
  unfold draw
  repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
end Effect

lemma controlled_optionMap {a b : DataType} (p : Expression a b) (hp : Controlled p) : Controlled (optionMapCode p) := by
  unfold optionMapCode; (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_mapEach {a b : DataType} (p : Expression a b) (hp : Controlled p) : Controlled (mapEach p) := by
  unfold mapEach; (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
namespace Effect
lemma controlled_precompose {a b c : DataType} (p : Expression a b) (q : Effect b c)
    (hp : Controlled p) (hq : Controlled q) : Controlled (precompose p q) := by
  unfold precompose; (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_map {a b c : DataType} (p : Effect a b) (q : Expression b c)
    (hp : Controlled p) (hq : Controlled q) : Controlled (map p q) :=
  controlled_bind p (pure q) hp (controlled_pure q hq)
lemma controlled_choose {a b : DataType} (test : Expression a .bool) (p q : Effect a b)
    (ht : Controlled test) (hp : Controlled p) (hq : Controlled q) : Controlled (choose test p q) := by
  unfold choose; (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_withContext {a b c : DataType} (p : Effect (.prod c a) b) (hp : Controlled p) :
    Controlled (withContext p) := by
  unfold withContext
  apply controlled_letIn _ _ hp
  apply controlled_pure; (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_retainOption {a b : DataType} (p : Effect a (Optional b)) (hp : Controlled p) :
    Controlled (retainOption p) := by
  unfold retainOption
  apply controlled_letIn _ _ hp
  apply controlled_pure; (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
end Effect

lemma run_both_parts {n : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression a b) (q : Expression a c) (x : Value a) (z : Value (.prod b c))
    (hz : run O (both p q) x=some z) : run O p x=some z.1 ∧ run O q x=some z.2 := by
  rw [run_both] at hz
  cases hp : run O p x with
  | none => simp [hp] at hz
  | some y =>
    simp only [hp,Option.bind_some] at hz
    cases hq : run O q x with
    | none => simp [hq] at hz
    | some w =>
      simp only [hq,Option.map_some,Option.some.injEq] at hz
      subst z
      exact ⟨rfl,rfl⟩
lemma width_fst {a b : DataType} (x : Value (.prod a b)) : width x.1≤width x := by
  obtain ⟨p,q⟩ := x; simp only [width_pair]; omega

lemma bankEval_rest_suffix {A : Type*} (t : DrawTree A) (bank : Bank) :
    ∃ pre,bank=pre++(bankEval t bank).2 := by
  induction t generalizing bank with
  | leaf a => exact ⟨[],rfl⟩
  | draw v k ih =>
    cases bank with
    | nil => exact ⟨[],rfl⟩
    | cons row bank =>
      simp only [bankEval]
      split
      · exact ⟨[row],rfl⟩
      · rename_i i hi
        obtain ⟨pre,hpre⟩ := ih ⟨i,rejectValue_lt _ _ _ hi⟩ bank
        exact ⟨row::pre,congrArg (List.cons row) hpre⟩
lemma bankEval_rest_width {A : Type*} (t : DrawTree A) (bank : Bank) :
    width (a:=BankData) (bankEval t bank).2≤width (a:=BankData) bank := by
  obtain ⟨pre,hpre⟩ := bankEval_rest_suffix t bank
  calc
    width (a:=BankData) (bankEval t bank).2 ≤ width (a:=BankData) (pre ++ (bankEval t bank).2) := by
      rw [width_list_append (a:=RandomRows)]; exact Nat.le_add_left _ _
    _ = width (a:=BankData) bank := congrArg (width (a:=BankData)) hpre.symm
namespace Effect
lemma RealizesLaw.outputs {n : ℕ} {O : IndependenceOracle n} {A : Type*} {a b : DataType}
    {p : Effect a b} {e : A → Value b} {x : Value a} {t : DrawTree A}
    (h : RealizesLaw O p e x t) (bank : Bank) :
    ∃ y : Option A,∃ rest : Bank,
      run O p (x,bank)=some (optionalValue b (y.map e),rest) ∧ width (a:=BankData) rest≤width (a:=BankData) bank := by
  obtain ⟨u,hu,hp⟩ := h
  exact ⟨(bankEval u bank).1,(bankEval u bank).2,hp bank,bankEval_rest_width u bank⟩
end Effect
lemma width_optionalValue {a : DataType} (x : Option (Value a)) (W : ℕ)
    (h : ∀ y,x=some y → width y≤W) : width (a:=Optional a) (optionalValue a x)≤width (zeroValue a)+W+3 := by
  cases x with
  | none => simp only [optionalValue,optionData,width_pair (a:=.bool) (b:=a),width_bool]; omega
  | some y =>
    have hh := h y rfl
    simp only [optionalValue,optionData,width_pair (a:=.bool) (b:=a),width_bool]
    omega

open Expression

open Expression
lemma oracleSafe_lift {a b : DataType} (p : Expression a b) (R : ℕ → Value a → Prop)
    (h : PolySafe p R) : OracleSafe p (fun _ _ => R) := h
lemma oracleSafe_controlled {a b : DataType} (p : Expression a b) (hp : Controlled p)
    (R : OraclePredicate a) (g : SizePolynomial)
    (hg : ∀ n O S x,R n O S x → width x≤g.eval S) : OracleSafe p R := by
  obtain ⟨f,hf⟩ := hp
  refine ⟨f.subst g,fun O S x hx => ?_⟩
  apply safe_mono p x (hf O x)
  rw [SizePolynomial.eval_subst]
  exact f.monotone (hg _ O S x hx)
lemma oracleSafe_reparam {a b : DataType} (p : Expression a b) (R : OraclePredicate a)
    (hp : OracleSafe p R) (g : SizePolynomial) : OracleSafe p (fun n O S x => R n O (g.eval S) x) := by
  obtain ⟨f,hf⟩ := hp
  exact ⟨f.subst g,fun O S x hx => by rw [SizePolynomial.eval_subst]; exact hf O _ x hx⟩
lemma oracleSafe_compose {a b c : DataType} (p : Expression a b) (q : Expression b c)
    (R : OraclePredicate a) (Q : OraclePredicate b) (hp : OracleSafe p R) (hq : OracleSafe q Q)
    (h : ∀ n O S x,R n O S x → ∀ y,run O p x=some y → Q n O S y) : OracleSafe (p >>> q) R := by
  obtain ⟨f,hf⟩ := hp
  obtain ⟨g,hg⟩ := hq
  refine ⟨.add f g,fun O S x hx => ?_⟩
  apply safe_compose O p q x
  · exact safe_mono p x (hf O S x hx) (Nat.le_add_right _ _)
  · intro y hy
    exact safe_mono q y (hg O S y (h _ O S x hx y hy)) (Nat.le_add_left _ _)
lemma oracleSafe_both {a b c : DataType} (p : Expression a b) (q : Expression a c)
    (R : OraclePredicate a) (hp : OracleSafe p R) (hq : OracleSafe q R) : OracleSafe (both p q) R := by
  obtain ⟨f,hf⟩ := hp
  obtain ⟨g,hg⟩ := hq
  refine ⟨.add (.mul (.constant 3) (.add f g)) (.constant 1),fun O S x hx => ?_⟩
  apply safe_both O p q x
  · exact safe_mono p x (hf O S x hx) (Nat.le_add_right _ _)
  · exact safe_mono q x (hg O S x hx) (Nat.le_add_left _ _)
lemma oracleSafe_pull {a b c : DataType} (p : Expression a b) (q : Expression b c)
    (R : OraclePredicate a) (Q : OraclePredicate b) (hp : Controlled p)
    (g : SizePolynomial) (hw : ∀ n O S x,R n O S x → width x≤g.eval S)
    (hq : OracleSafe q Q)
    (hh : ∀ n O S x,R n O S x → ∀ y,run O p x=some y → Q n O S y) : OracleSafe (p >>> q) R :=
  oracleSafe_compose p q R Q (oracleSafe_controlled p hp R g hw) hq hh
lemma oracleSafe_input_bound {a b : DataType} (p : Expression a b) (R : OraclePredicate a)
    (hp : OracleSafe p R) : ∃ f : SizePolynomial,∀ n O S x,R n O S x → width x≤f.eval S := by
  obtain ⟨f,hf⟩ := hp
  exact ⟨f,fun _ O S x hx => safe_input (hf O S x hx)⟩
lemma oracleSafe_applyIf {a b : DataType} (t : Expression a .bool) (p q : Expression a b)
    (R : OraclePredicate a) (ht : OracleSafe t R)
    (hp : OracleSafe p (fun n O S x => R n O S x ∧ run O t x=some false))
    (hq : OracleSafe q (fun n O S x => R n O S x ∧ run O t x=some true)) :
    OracleSafe (applyIf t p q) R := by
  have hid : OracleSafe (ident (a:=a)) R := by
    obtain ⟨f,hf⟩ := oracleSafe_input_bound t R ht
    exact oracleSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) R f hf
  have hboth := oracleSafe_both t ident R ht hid
  obtain ⟨f,hf⟩ := hboth
  obtain ⟨g,hg⟩ := hp
  obtain ⟨k,hk⟩ := hq
  unfold applyIf
  apply oracleSafe_compose (both t ident) (branch p q) R
    (fun n O S z => width z≤f.eval S ∧ R n O S z.2 ∧ run O t z.2=some z.1) ⟨f,hf⟩
  · refine ⟨.add f (.add g k),fun O S z hz => ?_⟩
    obtain ⟨v,x⟩ := z
    refine ⟨hz.1.trans (Nat.le_add_right _ _),?_,?_⟩
    · intro y hy
      cases v
      · exact (safe_output (hg O S x ⟨hz.2.1,hz.2.2⟩) hy).trans (by dsimp [SizePolynomial.eval]; omega)
      · exact (safe_output (hk O S x ⟨hz.2.1,hz.2.2⟩) hy).trans (by dsimp [SizePolynomial.eval]; omega)
    · cases v
      · exact safe_mono p x (hg O S x ⟨hz.2.1,hz.2.2⟩) (by dsimp [SizePolynomial.eval]; omega)
      · exact safe_mono q x (hk O S x ⟨hz.2.1,hz.2.2⟩) (by dsimp [SizePolynomial.eval]; omega)
  · intro n O S x hx z hz
    have hh := run_both_parts O t ident x z hz
    have he : x=z.2 := Option.some.inj hh.2
    exact ⟨safe_output (hf O S x hx) hz,he ▸ hx,he ▸ hh.1⟩

lemma oracleSafe_fold {a b : DataType} (p : Expression (.prod a b) b)
    (R : OraclePredicate (.prod (.list a) b)) (Q : OraclePredicate (.prod a b))
    (hp : OracleSafe p Q) (g : SizePolynomial)
    (hinput : ∀ {n : ℕ} (O : IndependenceOracle n) S x,R n O S x → width x≤g.eval S)
    (hacc : ∀ {n : ℕ} (O : IndependenceOracle n) S xs z,R n O S (xs,z) →
      ∀ pre post,xs=pre++post → ∀ y,foldValue (run O p) pre z=some y → width y≤g.eval S)
    (hstep : ∀ {n : ℕ} (O : IndependenceOracle n) S xs z,R n O S (xs,z) →
      ∀ pre x post,xs=pre++x::post → ∀ y,foldValue (run O p) pre z=some y → Q n O S (x,y)) :
    OracleSafe (.fold p) R := by
  obtain ⟨f,hf⟩ := hp
  refine ⟨.add f g,fun O S x hx => ?_⟩
  obtain ⟨xs,z⟩ := x
  refine ⟨(hinput O S (xs,z) hx).trans (Nat.le_add_left _ _),?_,?_⟩
  · intro y hy
    exact (hacc O S xs z hx xs [] (by simp) y hy).trans (Nat.le_add_left _ _)
  · apply foldSafe_prefix
    intro pre x post he y hy
    exact safe_mono p (x,y) (hf O S (x,y) (hstep O S xs z hx pre x post he y hy))
      (Nat.le_add_right _ _)

lemma oracleSafe_iterateNat {a : DataType} (p : Expression a a)
    (R : OraclePredicate (.prod .nat a)) (Q : OraclePredicate a)
    (hp : OracleSafe p Q) (g : SizePolynomial)
    (hinput : ∀ {n : ℕ} (O : IndependenceOracle n) S k z,R n O S (k,z) → k+width (a:=a) z≤g.eval S)
    (hacc : ∀ {n : ℕ} (O : IndependenceOracle n) S k z,R n O S (k,z) →
      ∀ j,j≤k → ∀ y,iterateM (run O p) j z=some y → width (a:=a) y≤g.eval S)
    (hbody : ∀ {n : ℕ} (O : IndependenceOracle n) S k z,R n O S (k,z) →
      ∀ j,j<k → ∀ y,iterateM (run O p) j z=some y → Q n O S y) :
    OracleSafe (iterateNat p) R := by
  let T : SizePolynomial := .add (.mul (.constant 12) g) (.constant 4)
  have hnatwidth : ∀ {n : ℕ} (O : IndependenceOracle n) S x,R n O S x → width x≤T.eval S := by
    intro n O S x hx
    obtain ⟨k,z⟩ := x
    have hh : k+width (a:=a) z≤g.eval S := hinput O S k z hx
    have hb := bits_length_le_value k
    rw [width_pair (a:=.nat) (b:=a),width_nat]
    dsimp [T,SizePolynomial.eval]
    have h₁ := Nat.mul_le_mul_left 2 hh
    omega
  have hu : OracleSafe (onLeft (c:=a) unary) R := by
    unfold onLeft
    apply oracleSafe_both
    · apply oracleSafe_compose _ _ R (fun _ _ S k => k≤g.eval S)
        (oracleSafe_controlled Expression.fst (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) R T (fun n O => hnatwidth O))
        (oracleSafe_reparam unary (fun _ _ S k => k≤S) (oracleSafe_lift _ _ polySafe_unary) g)
      intro n O S x hx y hy
      obtain ⟨k,z⟩ := x
      simp only [run_fst, Option.some.injEq] at hy
      subst y
      have hh : k+width (a:=a) z≤g.eval S := hinput O S k z hx
      exact (Nat.le_add_right k (width (a:=a) z)).trans hh
    · exact oracleSafe_controlled Expression.snd (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) R T (fun n O => hnatwidth O)
  let Rw : OraclePredicate (.prod .word a) := fun n O S x => R n O S (x.1.length,x.2)
  let Rl : OraclePredicate (.prod (.list .bool) a) := fun n O S x => R n O S (x.1.length,x.2)
  have hw : ∀ {n : ℕ} (O : IndependenceOracle n) S x,Rw n O S x → width x≤T.eval S := by
    intro n O S x hx
    obtain ⟨w,z⟩ := x
    have hh : w.length+width (a:=a) z≤g.eval S := hinput O S w.length z hx
    rw [width_pair (a:=.word) (b:=a),width_word]
    dsimp [T,SizePolynomial.eval]
    omega
  have hfold : OracleSafe (.fold (snd >>> p)) Rl := by
    refine oracleSafe_fold (Expression.snd (a:=.bool) >>> p) Rl
      (fun n O S x => width x≤T.eval S ∧ Q n O S x.2) ?_ T ?_ ?_ ?_
    · apply oracleSafe_compose _ _ _ Q
        (oracleSafe_controlled Expression.snd (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ T (by intro n O S x hx; exact hx.1)) hp
      intro n O S x hx y hy
      cases hy
      exact hx.2
    · intro n O S x hx
      obtain ⟨xs,z⟩ := x
      have hh : xs.length+width (a:=a) z≤g.eval S := hinput O S xs.length z hx
      rw [width_pair (a:=.list .bool) (b:=a),width_list_bool]
      dsimp [T,SizePolynomial.eval]
      omega
    · intro n O S xs z hx pre post he y hy
      rw [foldValue_iterateM] at hy
      have hj : pre.length≤xs.length := by rw [he,List.length_append]; omega
      have hh := hacc O S xs.length z hx pre.length hj y hy
      dsimp [T,SizePolynomial.eval]
      omega
    · intro n O S xs z hx pre b post he y hy
      rw [foldValue_iterateM] at hy
      have hj : pre.length<xs.length := by rw [he,List.length_append,List.length_cons]; omega
      have hh := hacc O S xs.length z hx pre.length hj.le y hy
      refine ⟨?_,hbody O S xs.length z hx pre.length hj y hy⟩
      rw [width_pair (a:=.bool) (b:=a),width_bool]
      dsimp [T,SizePolynomial.eval]
      omega
  unfold iterateNat iterateWord
  apply oracleSafe_compose _ _ R Rw hu
  · apply oracleSafe_compose _ _ Rw Rl
      (oracleSafe_controlled _ (by unfold onLeft; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) Rw T (fun n O => hw O)) hfold
    intro n O S x hx y hy
    cases hy
    exact hx
  · intro n O S x hx y hy
    obtain ⟨k,z⟩ := x
    obtain ⟨w,hw,hk⟩ := run_unary O k
    simp only [onLeft,run_both,run_compose,run_fst,run_snd,Option.bind_some,hw,Option.map_some] at hy
    cases hy
    change R n O S (w.length,z)
    rwa [hk]

namespace Effect
lemma scope_width {a b : DataType} (p : Expression a b) (R : OraclePredicate a)
    (hp : OracleSafe p R) : ∃ f : SizePolynomial,∀ n O S x,bankScope R n O S x → width x≤f.eval S := by
  obtain ⟨f,hf⟩ := oracleSafe_input_bound p R hp
  refine ⟨.add (.mul (.constant 2) f) (.add .input (.constant 1)),?_⟩
  intro n O S x hx
  have hh := hf n O S x.1 hx.1
  have hb : width (a:=BankData) x.2≤S := hx.2
  rw [width_pair (a:=a) (b:=BankData)]
  dsimp only [SizePolynomial.eval]
  omega
lemma safe_scope_fst {a b : DataType} (p : Expression a b) (R : OraclePredicate a)
    (hp : OracleSafe p R) : OracleSafe (fst (b:=BankData) >>> p) (bankScope R) := by
  obtain ⟨f,hf⟩ := scope_width p R hp
  apply oracleSafe_pull _ _ _ R (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) f hf hp
  intro n O S x hx y hy
  cases hy
  exact hx.1
lemma safe_scope_controlled {a b c : DataType} (p : Expression a b) (q : Expression (.prod a BankData) c)
    (R : OraclePredicate a) (hp : OracleSafe p R) (hq : Controlled q) : OracleSafe q (bankScope R) := by
  obtain ⟨f,hf⟩ := scope_width p R hp
  exact oracleSafe_controlled q hq _ f hf
lemma oracleSafe_precompose {a b c : DataType} (p : Expression a b) (q : Effect b c)
    (R : OraclePredicate a) (Q : OraclePredicate b) (hp : OracleSafe p R)
    (hq : OracleSafe q (bankScope Q))
    (h : ∀ n O S x,R n O S x → ∀ y,run O p x=some y → Q n O S y) :
    OracleSafe (precompose p q) (bankScope R) := by
  unfold precompose onLeft
  apply oracleSafe_compose _ _ _ (bankScope Q)
    (oracleSafe_both _ _ _ (safe_scope_fst p R hp) (safe_scope_controlled p _ R hp (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))))) hq
  intro n O S x hx y hy
  have hh := run_both_parts O (fst >>> p) snd x y hy
  have hp' : run O p x.1=some y.1 := hh.1

  have hb : x.2=y.2 := Option.some.inj hh.2
  exact ⟨h n O S x.1 hx.1 y.1 hp',hb ▸ hx.2⟩
end Effect
end MachineCode

namespace DrawTree
lemma All.mono {A : Type*} {t : DrawTree A} {P Q : A → Prop}
    (h : All P t) (hq : ∀ x,P x → Q x) : All Q t := by
  induction t with
  | leaf x => exact hq x h
  | draw v k ih => exact fun i => ih i (h i)
lemma all_bind_of_all {A B : Type*} (t : DrawTree A) (f : A → DrawTree B)
    (P : A → Prop) (Q : B → Prop) (ht : All P t)
    (hf : ∀ x,P x → All Q (f x)) : All Q (t.bind f) := by
  induction t with
  | leaf x => exact hf x ht
  | draw v k ih => exact fun i => ih i (ht i)
end DrawTree
namespace MachineCode

lemma bankEval_all {A : Type*} (t : DrawTree A) (P : A → Prop)
    (ht : DrawTree.All P t) (bank : Bank) (x : A)
    (hx : (bankEval t bank).1=some x) : P x := by
  induction t generalizing bank with
  | leaf a =>
    have he : a=x := Option.some.inj hx
    exact he ▸ ht
  | draw v k ih =>
    cases bank with
    | nil => cases hx
    | cons row bank =>
      simp only [bankEval] at hx
      split at hx
      · cases hx
      · exact ih _ (ht _) bank hx
open Expression
namespace Effect
lemma RealizesLaw.outputs_all {n : ℕ} {O : IndependenceOracle n}
    {A : Type*} {a b : DataType} {p : Effect a b} {e : A → Value b}
    {x : Value a} {t : DrawTree A} (h : RealizesLaw O p e x t)
    (P : A → Prop) (ht : DrawTree.All P t) (bank : Bank) :
    ∃ y : Option A,∃ rest : Bank,
      run O p (x,bank)=some (optionalValue b (y.map e),rest) ∧
      width (a:=BankData) rest≤width (a:=BankData) bank ∧
      ∀ v,y=some v → P v := by
  obtain ⟨u,hu,hp⟩ := h
  refine ⟨(bankEval u bank).1,(bankEval u bank).2,hp bank,bankEval_rest_width u bank,?_⟩
  intro v hv
  exact bankEval_all u P (hu.all P ht) bank v hv
lemma RealizesLaw.run_bound {n : ℕ} {O : IndependenceOracle n}
    {A : Type*} {a b : DataType} {p : Effect a b} {e : A → Value b}
    {x : Value a} {t : DrawTree A} (h : RealizesLaw O p e x t)
    (W : ℕ) (R : Value b → Prop)
    (ht : DrawTree.All (fun v => width (e v)≤W ∧ R (e v)) t)
    (bank : Bank) (y : Value (.prod (Optional b) BankData))
    (hy : run O p (x,bank)=some y) :
    width y≤2*(width (zeroValue b)+W+3)+1+width (a:=BankData) bank ∧
    (y.1.1=true → R y.1.2) := by
  obtain ⟨v,rest,he,hrest,hv⟩ := h.outputs_all _ ht bank
  have he' : y=(optionalValue b (v.map e),rest) := Option.some.inj (hy.symm.trans he)
  subst y
  constructor
  · have hw : width (optionalValue b (v.map e))≤width (zeroValue b)+W+3 := by
      apply width_optionalValue
      intro z hz
      obtain ⟨u,hu,hz⟩ := Option.map_eq_some_iff.mp hz
      subst z
      exact (hv u hu).1
    rw [width_pair (a:=Optional b) (b:=BankData)]
    omega
  · cases v with
    | none => intro h; cases h
    | some z => intro _; exact (hv z rfl).2
lemma RealizesLaw.rest_width {n : ℕ} {O : IndependenceOracle n}
    {A : Type*} {a b : DataType} {p : Effect a b} {e : A → Value b}
    {x : Value a} {t : DrawTree A} (h : RealizesLaw O p e x t)
    (bank : Bank) (y : Value (.prod (Optional b) BankData))
    (hy : run O p (x,bank)=some y) : width (a:=BankData) y.2≤width (a:=BankData) bank := by
  obtain ⟨v,rest,he,hrest⟩ := h.outputs bank
  have he' : y=(optionalValue b (v.map e),rest) := Option.some.inj (hy.symm.trans he)
  exact he' ▸ hrest

end Effect

open Expression
namespace Effect

lemma oracleSafe_loopStep {a : DataType} (p : Effect a a)
    (R : OraclePredicate a) (hp : OracleSafe p (bankScope R))
    (g : SizePolynomial) :
    OracleSafe (loopStep p) (fun n O S x => width x≤g.eval S ∧
      (x.1.1=true → R n O S x.1.2 ∧ width (a:=BankData) x.2≤S)) := by
  unfold loopStep
  apply oracleSafe_applyIf
  · exact oracleSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ g (by intro n O S x hx; exact hx.1)
  · exact oracleSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ g (by intro n O S x hx; exact hx.1.1)
  · apply oracleSafe_pull _ p _ (bankScope R) (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) g
      (by intro n O S x hx; exact hx.1.1) hp
    intro n O S x hx y hy
    have hv : x.1.1=true := Option.some.inj hx.2
    cases hy
    exact hx.1.2 hv

lemma oracleSafe_repeat_scoped {a : DataType} (p : Effect a a)
    (R : OraclePredicate (.prod .nat a)) (Q : OraclePredicate a)
    (hp : OracleSafe p (bankScope Q)) (g : SizePolynomial)
    (hinput : ∀ n O S k x,R n O S (k,x) → k+width (a:=a) x≤g.eval S)
    (hprefix : ∀ n O S k x bank,R n O S (k,x) → width (a:=BankData) bank≤S →
      ∀ j,j≤k → ∀ y,iterateM (run O (loopStep p)) j (optionalValue a (some x),bank)=some y →
       width (a:=.prod (Optional a) BankData) y≤g.eval S ∧
       (y.1.1=true → Q n O S y.1.2 ∧ width (a:=BankData) y.2≤S)) :
    OracleSafe (repeatCode p) (bankScope R) := by
  let T : OraclePredicate (.prod .nat (.prod (Optional a) BankData)) := fun n O S z =>
    ∃ k x bank,R n O S (k,x) ∧ width (a:=BankData) bank≤S ∧ z=(k,(optionalValue a (some x),bank))
  let W : SizePolynomial := .add (.mul (.constant 20) g) (.add (.mul (.constant 2) .input) (.constant 20))
  have htwidth : ∀ n O S x,bankScope R n O S x → width x≤W.eval S := by
    intro n O S x hx
    obtain ⟨⟨k,z⟩,bank⟩ := x
    have hi : k+width (a:=a) z≤g.eval S := hinput n O S k z hx.1
    have h₁ := Nat.mul_le_mul_left 4 hi
    have hb : width (a:=BankData) bank≤S := hx.2
    have hk := bits_length_le_value k
    rw [width_pair (a:=.prod .nat a) (b:=BankData),width_pair (a:=.nat) (b:=a),width_nat]
    dsimp [W,SizePolynomial.eval]
    omega
  unfold repeatCode
  apply oracleSafe_pull _ _ (bankScope R) T (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) W htwidth
  · apply oracleSafe_iterateNat _ T _ (oracleSafe_loopStep p Q hp g) W
    · intro n O S k z hz
      obtain ⟨k',x,bank,hx,hb,he⟩ := hz
      cases he
      have hi : k+width (a:=a) x≤g.eval S := hinput n O S k x hx
      have h₁ := Nat.mul_le_mul_left 2 hi
      rw [width_pair (a:=Optional a) (b:=BankData),width_pair (a:=.bool) (b:=a),width_bool]
      change k+(2*(2*1+1+width (a:=a) x)+1+width (a:=BankData) bank)≤_
      have harith : ∀ (k v b G S : ℕ),k+v≤G → b≤S →
          k+(2*(2*1+1+v)+1+b)≤20*G+(2*S+20) := by
        intros; omega
      exact harith k (width (a:=a) x) (width (a:=BankData) bank) (g.eval S) S hi hb
    · intro n O S k z hz j hj y hy
      obtain ⟨k',x,bank,hx,hb,he⟩ := hz
      cases he
      have hh := (hprefix n O S k x bank hx hb j hj y hy).1
      dsimp [W,SizePolynomial.eval]
      omega
    · intro n O S k z hz j hj y hy
      obtain ⟨k',x,bank,hx,hb,he⟩ := hz
      cases he
      exact hprefix n O S k x bank hx hb j hj.le y hy
  · intro n O S x hx y hy
    cases hy
    exact ⟨x.1.1,x.1.2,x.2,hx.1,hx.2,rfl⟩

lemma oracleSafe_repeat_law {a : DataType} (p : Effect a a)
    (R : OraclePredicate (.prod .nat a)) (Q : OraclePredicate a)
    (hp : OracleSafe p (bankScope Q)) (g : SizePolynomial)
    (hinput : ∀ n O S k x,R n O S (k,x) → k+width (a:=a) x≤g.eval S)
    (hlaw : ∀ n O S k x,R n O S (k,x) → ∀ j,j≤k →
      ∃ (A : Type) (e : A → Value a) (t : DrawTree A),
        RealizesLaw O (repeatCode p) e (j,x) t ∧
        DrawTree.All (fun v => width (e v)≤g.eval S ∧ Q n O S (e v)) t) :
    OracleSafe (repeatCode p) (bankScope R) := by
  let W : SizePolynomial := .add (.mul (.constant 2) g)
    (.add .input (.constant (2*(width (zeroValue a)+3)+1)))
  apply oracleSafe_repeat_scoped p R Q hp W
  · intro n O S k x hx
    have hh : k+width (a:=a) x≤g.eval S := hinput n O S k x hx
    exact hh.trans (by omega :
      g.eval S≤2*g.eval S+(S+(2*(width (zeroValue a)+3)+1)))
  · intro n O S k x bank hx hb j hj y hy
    obtain ⟨A,e,t,ht,he⟩ := hlaw n O S k x hx j hj
    have hyr : run O (repeatCode p) ((j,x),bank)=some y := by rw [run_repeat]; exact hy
    have hh := ht.run_bound (g.eval S) (Q n O S) he bank y hyr
    have hr := ht.rest_width bank y hyr
    refine ⟨?_,fun hv => ⟨hh.2 hv,hr.trans hb⟩⟩
    dsimp [W,SizePolynomial.eval]
    omega

end Effect

namespace Effect
lemma optionScope_width {a : DataType} (R : OraclePredicate a) (g : SizePolynomial)
    (hw : ∀ n O S x,R n O S x → width x≤g.eval S) :
    ∀ n O S x,optionScope R n O S x → width x≤
      (.add g (.constant (width (zeroValue a)+3)) : SizePolynomial).eval S := by
  intro n O S x hx
  rcases hx with rfl | ⟨hflag,hx⟩
  · rw [width_pair (a:=.bool) (b:=a),width_bool]
    change 2*1+1+width (zeroValue a)≤_
    dsimp [SizePolynomial.eval]
    omega
  · have hh := hw n O S x.2 hx
    rw [width_pair (a:=.bool) (b:=a),width_bool]
    dsimp [SizePolynomial.eval]
    omega
lemma oracleSafe_optionContinue {a b : DataType} (p : Effect a (Optional b))
    (R : OraclePredicate a) (hp : OracleSafe p (bankScope R)) :
    OracleSafe (optionContinue p) (bankScope (optionScope R)) := by
  obtain ⟨f,hf⟩ := oracleSafe_input_bound p (bankScope R) hp
  have hu : ∀ n O S x,R n O S x → width (a:=a) x≤f.eval S := by
    intro n O S x hx
    exact (width_fst (a:=a) (b:=BankData) (x,([] : Bank))).trans (hf n O S (x,[]) ⟨hx,by exact Nat.zero_le S⟩)
  let W : SizePolynomial := .add (.mul (.constant 2)
    (.add f (.constant (width (zeroValue a)+3)))) (.add .input (.constant 1))
  have hw : ∀ n O S x,bankScope (optionScope R) n O S x → width x≤W.eval S := by
    intro n O S x hx
    have hh := optionScope_width R f hu n O S x.1 hx.1
    have hb := hx.2
    rw [width_pair (a:=Optional a) (b:=BankData)]
    dsimp [W,SizePolynomial.eval] at *
    omega
  unfold optionContinue choose
  apply oracleSafe_applyIf _ _ _ _
  · exact oracleSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ W hw
  · exact oracleSafe_controlled _ (by (repeat' (first | assumption | exact Effect.controlled_draw | apply Effect.controlled_precompose | apply Effect.controlled_map | apply Effect.controlled_bind | apply Effect.controlled_letIn | apply Effect.controlled_pure <;> (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)) | apply Effect.controlled_keep | apply Effect.controlled_choose | apply Effect.controlled_withContext | apply Effect.controlled_retainOption | apply controlled_optionMap <;> (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)) | apply controlled_mapEach <;> (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)) | repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)))) _ W (by intro n O S x hx; exact hw n O S x hx.1)
  · unfold precompose onLeft
    apply oracleSafe_pull _ p _ (bankScope R) (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) W
      (by intro n O S x hx; exact hw n O S x hx.1) hp
    intro n O S x hx y hy
    have hv : x.1.1=true := Option.some.inj hx.2
    have he : (x.1.2,x.2)=y := Option.some.inj hy
    subst y
    refine ⟨?_,hx.1.2⟩
    rcases hx.1.1 with hnone | ⟨_,hh⟩
    · rw [hnone] at hv; cases hv
    · exact hh
end Effect

open scoped Classical
lemma width_stateEncode {n : ℕ} (T : Set (Fin n⊕Fin n)) : width (a:=StateData) (stateEncode T)=3*n+1 := by
  rw [width_pair (a:=.word) (b:=.word),width_word,width_word,stateEncode_left_length,stateEncode_right_length]
  omega
lemma width_sampleEncode {n : ℕ} (xs : List (Set (Fin n⊕Fin n))) :
    width (a:=SampleData) (sampleEncode xs)=xs.length*(6*n+4) := by
  induction xs with
  | nil => change width (a:=.list StateData) []=0*(6*n+4); rw [width_nil,Nat.zero_mul]
  | cons x xs ih =>
    change width (a:=.list StateData) (stateEncode x::sampleEncode xs)=_
    rw [width_cons (a:=StateData),width_stateEncode,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
lemma width_observation {n N : ℕ} (v : PhaseSample n N) :
    width (a:=SampleData) (sampleEncode (observedSets n N v))≤(N+1)*(6*n+4) := by
  rw [width_sampleEncode]
  have hl : (observedSets n N v).length=N-1+1 := by
    simp only [observedSets,List.length_map]
    exact FiniteChain.Sample.toList_length v
  rw [hl]
  exact Nat.mul_le_mul_right _ (by omega)
lemma width_history_observed {n N : ℕ} (h : List (PhaseSample n N)) :
    width (a:=HistoryData) (historyEncode (h.map (observedSets n N)))≤h.length*(2*((N+1)*(6*n+4))+2) := by
  unfold historyEncode
  apply (width_list_le _ _ ?_).trans
  · simp only [List.length_map]; rfl
  · intro x hx
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    exact width_observation u

open Expression
open Effect
open scoped Classical

namespace SamplerModel
variable {n : ℕ} {O : IndependenceOracle n}
lemma width_histValue (m : SamplerModel n O) (S : ℕ) (hm : m.Bounded S)
    (h : m.Hist) (hh : h.length≤S) : width (m.histValue h)≤20*(S+1)^3 := by
  have he := width_history_observed h
  have hb : h.length*(2*((m.samples+1)*(6*n+4))+2)≤S*(2*((S+1)*(6*S+4))+2) := by
    gcongr
    · exact hm.2.2.1
    · exact hm.1
  exact he.trans (hb.trans (by nlinarith))
lemma width_phaseValue (m : SamplerModel n O) (S : ℕ) (hm : m.Bounded S)
    (h : m.Hist) (hh : h.length≤S) : width (m.phaseValue h)≤100*(S+1)^3 := by
  have hn := (bits_length_le_value n).trans hm.1
  have hr := (bits_length_le_value m.rank).trans hm.2.1
  have hs := (bits_length_le_value m.samples).trans hm.2.2.1
  have hl := (bits_length_le_value m.phases).trans hm.2.2.2.1
  have hc := (bits_length_le_value m.cap).trans hm.2.2.2.2.1
  have ht := (bits_length_le_value m.tau).trans hm.2.2.2.2.2
  have hh := m.width_histValue S hm h hh
  rw [phaseValue,width_pair (a:=AlgorithmParams) (b:=HistoryData)]
  rw [params,width_pair (a:=NN) (b:=.prod NN NN),width_pair (a:=NN) (b:=NN),
    width_pair (a:=.nat) (b:=.nat),width_pair (a:=.nat) (b:=.nat),width_pair (a:=.nat) (b:=.nat)]
  simp only [width_nat]
  dsimp only [cap,tau] at hc ht
  have hp : S+1≤(S+1)^3 := Nat.le_self_pow (by decide) _
  omega
end SamplerModel

lemma eval_sourceWidthPoly (c S : ℕ) : (sourceWidthPoly c).eval S=c*(S+1)^3 := by
  simp only [sourceWidthPoly,SizePolynomial.eval]; ring

end MachineCode

namespace DrawTree
lemma all_of_forall {A : Type*} (t : DrawTree A) (P : A → Prop) (h : ∀ x,P x) : All P t := by
  induction t with
  | leaf x => exact h x
  | draw n k ih => exact ih
end DrawTree
namespace MachineCode

open Expression
open scoped Classical

open Expression

open Expression
open scoped Classical

open Expression
open scoped Classical

open Expression

open Expression
open scoped Classical

section
open Expression
namespace Effect

lemma optionRepeat_none {X : Type*} (f : X → DrawTree (Option X)) (k : ℕ) :
    treeRepeat (fun x => match x with | none => .leaf none | some y => f y) k none=.leaf none := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih
lemma iterate_history {X : Type*} (K : List X → DrawTree (Option X)) (k : ℕ) (h : List X) :
    DrawTree.iterate (historyTickTree K) k h=DrawTree.history K k h := by
  rw [←treeRepeat_option]
  induction k generalizing h with
  | zero => rfl
  | succ k ih =>
    simp only [treeRepeat,historyTickTree,DrawTree.map_bind,DrawTree.history,DrawTree.optionBind]
    congr 1
    funext u
    cases u with
    | none => exact optionRepeat_none _ k
    | some x => exact ih (h++[x])
lemma law_historyTickCode {n : ℕ} (O : IndependenceOracle n) {X : Type*} {a c}
    (p : Effect (.prod c (.list a)) (Optional a)) (e : X → Value a) (ctx : Value c)
    (K : List X → DrawTree (Option X)) (h : List X)
    (hp : RealizesLaw O p (optionEncode e) (ctx,h.map e) (K h)) :
    RealizesLaw O (historyTickCode p) (optionEncode (fun h => (ctx,h.map e))) (ctx,h.map e) (historyTickTree K h) := by
  apply law_optionMap O (retainOption p) _ (fun y => ((ctx,h.map e),e y)) _ _ _ (fun x => h++[x])
  · exact law_retainOption O p e (ctx,h.map e) (K h) hp
  · intro x
    simp only [run_both,run_compose,run_fst,run_snd,run_constant,Option.bind_some,Option.map_some]
    change ((run O listAppend (h.map e,[e x])).map fun l => (ctx,l))=_
    rw [run_listAppend]
    simp

end Effect

open Expression
open scoped BigOperators Classical
end

open Expression
open scoped Classical
namespace Effect
lemma history_length {X : Type*} (K : List X → DrawTree (Option X)) (k : ℕ) (h : List X) :
    DrawTree.All (fun v => ∀ h',v=some h' → h'.length=h.length+k) (DrawTree.history K k h) := by
  induction k generalizing h with
  | zero => intro h' he; cases he; simp
  | succ k ih =>
    unfold DrawTree.history DrawTree.optionBind
    apply DrawTree.all_bind_of_all (K h) _ (fun _ => True) _ (DrawTree.all_of_forall _ _ (by intros; trivial))
    intro u _
    cases u with
    | none => intro h' he; cases he
    | some x =>
      apply (ih (h++[x])).mono
      intro v hv h' he
      have hh := hv h' he
      simpa only [List.length_append,List.length_singleton,Nat.add_assoc,Nat.add_comm 1 k] using hh
lemma phaseOptWidth_bound {n : ℕ} {O : IndependenceOracle n} (m : SamplerModel n O)
    (S : ℕ) (hm : m.Bounded S) (v : Option m.Hist)
    (hv : ∀ h,v=some h → h.length≤S) :
    width (optionEncode m.phaseValue v)≤phaseOptWidth.eval S := by
  cases v with
  | none =>
    rw [optionEncode,optionalValue,width_pair (a:=.bool) (b:=PhaseInput),width_bool]
    change 2*1+1+width (zeroValue PhaseInput)≤(sourceWidthPoly 100).eval S+(width (zeroValue PhaseInput)+3)
    omega
  | some h =>
    have hw := m.width_phaseValue S hm h (hv h rfl)
    rw [optionEncode,optionalValue,width_pair (a:=.bool) (b:=PhaseInput),width_bool]
    change 2*1+1+width (m.phaseValue h)≤(sourceWidthPoly 100).eval S+(width (zeroValue PhaseInput)+3)
    rw [eval_sourceWidthPoly]
    omega
lemma historyTick_source {n : ℕ} {O : IndependenceOracle n} (m : SamplerModel n O) (h : m.Hist) :
    RealizesLaw O (historyTickCode phaseCode) (optionEncode m.phaseValue) (m.phaseValue h)
      (historyTickTree (canonicalPhaseTree n m.positive m.rank O m.samples m.phases) h) := by
  have hl := law_historyTickCode O phaseCode
    (fun v : PhaseSample n m.samples => sampleEncode (observedSets n m.samples v))
    (params n m.rank m.samples m.phases)
    (canonicalPhaseTree n m.positive m.rank O m.samples m.phases) h (by
      simpa only [SamplerModel.phaseValue,SamplerModel.histValue,historyEncode,List.map_map,Function.comp_def] using
        phaseCode_source m.M₁ m.M₂ O m.exact m.ground₁ m.ground₂ m.rank m.samples m.phases h m.positive)
  change RealizesLaw O _ (optionEncode (fun h => m.phaseValue h)) _ _
  simpa only [SamplerModel.phaseValue,SamplerModel.histValue,historyEncode,List.map_map,Function.comp_def] using hl

lemma safe_historyRepeat : OracleSafe (repeatCode (optionContinue (historyTickCode phaseCode)))
    (bankScope historyRepeatScope) := by
  apply oracleSafe_repeat_law _ historyRepeatScope (optionScope phaseScope)
    (oracleSafe_optionContinue _ _ safe_historyTick) (.add .input phaseOptWidth)
  · intro n O S k z hz
    obtain ⟨hk,m,hm,rfl⟩ := hz
    exact Nat.add_le_add hk (phaseOptWidth_bound m S hm (some []) (by intro h he; cases he; exact Nat.zero_le S))
  · intro n O S k z hz j hj
    obtain ⟨hk,m,hm,rfl⟩ := hz
    let K := canonicalPhaseTree n m.positive m.rank O m.samples m.phases
    let f := historyTickTree K
    let F : Option m.Hist → DrawTree (Option m.Hist) := fun u => match u with
      | none => .leaf none | some h => f h
    refine ⟨Option m.Hist,optionEncode m.phaseValue,treeRepeat F j (some []),?_,?_⟩
    · apply law_repeat O _ _ F _ j (some [])
      intro u
      change RealizesLaw O (optionContinue (historyTickCode phaseCode)) (optionEncode m.phaseValue)
        (optionEncode m.phaseValue u) (match u with | none => .leaf none | some h => f h)
      cases u <;> exact law_optionContinue O (historyTickCode phaseCode) m.phaseValue m.phaseValue f _
        (fun h => historyTick_source m h)
    · have he : treeRepeat F j (some [])=DrawTree.iterate f j [] := by
        convert treeRepeat_option f j ([] : m.Hist) using 2
        funext u; cases u <;> rfl
      rw [he]
      change DrawTree.All _ (DrawTree.iterate (historyTickTree K) j [])
      rw [iterate_history]
      apply (history_length K j []).mono
      intro v hv
      have hb : ∀ h,v=some h → h.length≤S := by
        intro h he
        have hh := hv h he
        simp only [List.length_nil,Nat.zero_add] at hh
        exact hh.le.trans (hj.trans hk)
      refine ⟨(phaseOptWidth_bound m S hm v hb).trans (Nat.le_add_left _ _),?_⟩
      cases v with
      | none => exact Or.inl rfl
      | some h => exact Or.inr ⟨rfl,m,hm,h,hb h rfl,rfl⟩
lemma historyInputScope_width : ∀ n O S z,historyInputScope n O S z →
    width z≤(SizePolynomial.add (.mul (.constant 2) .input) (.add (.constant 1) (sourceWidthPoly 100))).eval S := by
  intro n O S z hz
  obtain ⟨hk,m,hm,he⟩ := hz
  have hb := (bits_length_le_value z.1).trans hk
  have hw := m.width_phaseValue S hm [] (Nat.zero_le S)
  rw [width_pair (a:=.nat) (b:=PhaseInput),width_nat,he]
  change _≤2*S+(1+(sourceWidthPoly 100).eval S)
  rw [eval_sourceWidthPoly]
  omega
lemma safe_historyCode : OracleSafe (historyCode phaseCode) (bankScope historyInputScope) := by
  unfold historyCode iterateCode
  apply oracleSafe_precompose _ _ historyInputScope historyRepeatScope
    (oracleSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ _ historyInputScope_width) safe_historyRepeat
  intro n O S z hz y hy
  cases hy
  obtain ⟨hk,m,hm,he⟩ := hz
  exact ⟨hk,m,hm,by rw [he]; rfl⟩
lemma algorithmScope_width : ∀ n O S z,algorithmScope n O S z → width z≤(sourceWidthPoly 100).eval S := by
  intro n O S z hz
  obtain ⟨m,hm,rfl⟩ := hz
  rw [eval_sourceWidthPoly]
  exact (width_fst (a:=AlgorithmParams) (b:=HistoryData) (m.phaseValue [])).trans
    (m.width_phaseValue S hm [] (Nat.zero_le S))
lemma safe_algorithmHistory_oai : OracleSafe algorithmHistoryCode (bankScope algorithmScope) := by
  unfold algorithmHistoryCode
  apply oracleSafe_precompose _ _ algorithmScope historyInputScope
    (oracleSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ _ algorithmScope_width) safe_historyCode
  intro n O S z hz y hy
  obtain ⟨m,hm,rfl⟩ := hz
  cases hy
  exact ⟨hm.2.2.2.1,m,hm,rfl⟩
end Effect

open Expression

open Expression Effect

open Expression
open scoped Classical

open Expression

open Expression Effect

open Expression
open Expression Effect

open Expression

open Expression

open Expression Effect

open Expression

open Expression

open Expression Effect
open scoped Classical

open Expression

open Expression
open scoped Classical

open Expression

open scoped Classical

end MachineCode
end CommonBasesFPRAS

open CommonBasesFPRAS CommonBasesFPRAS.MachineCode

end OAI
end

theorem solution : type_of% @OAI.CommonBasesFPRAS.MachineCode.Effect.safe_algorithmHistory_oai := @OAI.CommonBasesFPRAS.MachineCode.Effect.safe_algorithmHistory_oai
