-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.pack_length_bound_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:49:29.316213+00:00
-- url     : https://prove2.me/submissions/e89b8198-7616-44b1-9e62-dd96d0e0f0a1

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K031

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Height
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalHeight
open scoped BigOperators

lemma zero (b : ℕ) : Height 0 b := by
  constructor
  · simp
  · simpa using (one_le_pow₀ (by norm_num : (1:ℕ)≤2) : 1≤2^b)

end MetricKMedianRecovery.RationalHeight

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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MergeResources
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
open RationalHeight
variable {V : Type*} [DecidableEq V]

lemma parent_shorten (key : ℕ) (i : V) (l u : ℚ) (x : Label V) :
    parent (shorten key i l u x)=parent x := by
  simp only [shorten,Equiv.swap_apply_def]
  split_ifs with hu hl
  · subst x; rfl
  · subst x; rfl
  · rfl

lemma height_shorten (key : ℕ) (i : V) (l u : ℚ) (h : ℕ)
    (hl : Height l h) (hu : Height u h) (x : Label V) (hx : HeightBound h x) :
    HeightBound h (shorten key i l u x) := by
  simp only [shorten,Equiv.swap_apply_def]
  split_ifs
  · exact hl
  · exact hu
  · exact hx

end MetricKMedianRecovery.RationalLeaves

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [DecidableEq V]

lemma Correction.parent (r : Correction V) (x : Label V) : parent (r.apply x)=parent x := by
  cases r with
  | identity=>rfl
  | shorten key i l u=>exact parent_shorten key i l u x

lemma Correction.height {h : ℕ} (r : Correction V) (hr : r.Bounded h)
    (x : Label V) (hx : HeightBound h x) : HeightBound h (r.apply x) := by
  cases r with
  | identity=>exact hx
  | shorten key i l u=>exact height_shorten key i l u h hr.1 hr.2 x hx

lemma State.Resources.map_bank {F : Finset V} {q h p : ℕ} {s : State V}
    (hs : s.Resources F q h p) (hb : Before (3*q) s.mapFree) :
    BankBound F h (3*q) (q*(2*F.card+1)) s.mapFree := by
  refine ⟨?_,?_,hb,?_⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    rw [Correction.parent]
    exact hs.bank.rooted y hy
  · intro x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    exact s.correction.height hs.correction y (hs.bank.height y hy)
  · exact (Finset.card_image_le).trans hs.bank.card

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyAge
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
lemma Before.level {key : ℕ} {B : Finset (Label V)} (hb : Before key B)
    (x : Label V) (hx : x∈B) : level x ≤ key := by
  cases x with
  | inl i=>exact Nat.zero_le _
  | inr c=>exact hb c hx

lemma level_shorten (key : ℕ) (i : V) (l u : ℚ) (x : Label V) :
    level (shorten key i l u x)=level x := by
  simp only [shorten,Equiv.swap_apply_def]
  split_ifs with hu hl
  · subst x; rfl
  · subst x; rfl
  · rfl

end MetricKMedianRecovery.RationalLeaves

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [DecidableEq V]

lemma Correction.level (r : Correction V) (x : Label V) : level (r.apply x)=level x := by
  cases r with
  | identity=>rfl
  | shorten key i l u=>exact level_shorten key i l u x

lemma Correction.before (r : Correction V) {key : ℕ} {B : Finset (Label V)}
    (hb : Before key B) : Before key (B.image r.apply) := by
  intro c hc
  obtain ⟨x,hx,he⟩:=Finset.mem_image.mp hc
  have h:=hb.level x hx
  rw [←r.level x,he] at h
  exact h

lemma State.Resources.map_bound {F : Finset V} {q h p : ℕ} {s : State V}
    (hs : s.Resources F q h p) : BankBound F h (3*q) (q*(2*F.card+1)) s.mapFree :=
  hs.map_bank (s.correction.before hs.bank.before)

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace Signed
lemma encode_length (z : ℤ) : (encode z).length=z.natAbs.size+1 := by
  simp only [encode,List.length_cons,Nat.size_eq_bits_len]
end Signed
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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRational
lemma encode_length (q : ℚ) : (encode q).length=2*(q.num.natAbs.size+1)+1+q.den.size := by
  simp only [encode,pairBits_length,Signed.encode_length,←Nat.size_eq_bits_len]
lemma encode_height {q : ℚ} {b : ℕ} (hq : RationalHeight.Height q b) :
    (encode q).length≤3*b+6 := by
  have hn := Nat.size_le_size hq.1
  have hd := Nat.size_le_size hq.2
  rw [Nat.size_pow] at hn hd
  rw [encode_length]
  omega
end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SensitiveMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseHistoryTransfer
open PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma History.phase_bound {loc : D → X} {F B Q : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : History loc F B v lam eta q Q P) :
    ∀ H∈P,H.length≤F.card+B.card ∧ ∀ x∈H,x∈F∪B := by
  induction h with
  | nil=>simp
  | @cons q Q H T hh ht ih=>
    intro G hG
    rcases List.mem_cons.mp hG with rfl|hG
    · refine ⟨?_,fun x hx=>hh.1.opened_subset (List.mem_toFinset.mpr hx)⟩
      have hs:=Finset.card_le_card hh.1.opened_subset
      rw [List.toFinset_card_of_nodup hh.1.nodup] at hs
      exact hs.trans (Finset.card_union_le F B)
    · exact ih G hG

end MetricKMedianRecovery.PhaseHistoryTransfer

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_StateBits2
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open RationalLeaves RationalHeight
lemma heightBound_height {m h : ℕ} {x : Label (Fin m)} (hx : HeightBound h x) :
    Height (rationalHeight x) h := by
  cases x with
  | inl i=>exact zero h
  | inr c=>exact hx
lemma encode_length_bound {m key h : ℕ} (x : Label (Fin m))
    (hk : level x≤key) (hh : HeightBound h x) : (encode x).length≤2*key+2*m+3*h+8 := by
  have hp : (parent x).val≤ m := (parent x).isLt.le
  have hl : (level x).size≤key := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hk
  have hi : (parent x).val.size≤ m := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hp
  have hr := BinaryRational.encode_height (heightBound_height hh)
  simp only [encode,pairBits_length,Nat.size_eq_bits_len]
  omega
end MetricKMedianRecovery.BitMachine.BinaryLabel

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

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledState
open WordOperations WordList RationalLeaves RationalHeight CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

lemma bank_labels {m q h p t : ℕ} {F : Finset (Fin m)} {s : State (Fin m)}
    (hs : s.Resources F q h p) (hq : q≤t) :
    ∀ x∈F.image original∪s.B,(BinaryLabel.encode x).length≤labelBound m t h := by
  intro x hx
  suffices hh : (BinaryLabel.encode x).length≤2*(3*t)+2*m+3*h+8 by
    exact hh.trans (by simp only [labelBound]; omega)
  apply BinaryLabel.encode_length_bound x
  · rcases Finset.mem_union.mp hx with hx|hx
    · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
      exact Nat.zero_le _
    · exact (hs.bank.before.level x hx).trans (Nat.mul_le_mul_left _ hq)
  · rcases Finset.mem_union.mp hx with hx|hx
    · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
      trivial
    · exact hs.bank.height x hx
lemma mapped_labels {m q h p t : ℕ} {F : Finset (Fin m)} {s : State (Fin m)}
    (hs : s.Resources F q h p) (hq : q≤t) :
    ∀ x∈F.image original∪s.mapFree,(BinaryLabel.encode x).length≤labelBound m t h := by
  intro x hx
  suffices hh : (BinaryLabel.encode x).length≤2*(3*t)+2*m+3*h+8 by
    exact hh.trans (by simp only [labelBound]; omega)
  apply BinaryLabel.encode_length_bound x
  · rcases Finset.mem_union.mp hx with hx|hx
    · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
      exact Nat.zero_le _
    · exact (hs.map_bound.before.level x hx).trans (Nat.mul_le_mul_left _ hq)
  · rcases Finset.mem_union.mp hx with hx|hx
    · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
      trivial
    · exact hs.map_bound.height x hx

lemma history_length {m d r t h : ℕ} [PseudoMetricSpace (Label (Fin m))]
    {loc : Fin d → Label (Fin m)} {F B Q : Finset (Label (Fin m))} {v lam eta : ℝ}
    {hs : List (List (Label (Fin m)))} (hh : History loc F B v lam eta r Q hs)
    (hn : hs.length≤t) (hF : F.card+B.card≤ m+bankBound m t)
    (hl : ∀ x∈F∪B,(BinaryLabel.encode x).length≤labelBound m t h) :
    (historyBits hs).length≤historyBound m t h := by
  have hb:=hh.phase_bound
  have he:=encode_le_bound (hs.map labels) ((m+bankBound m t)*(2*labelBound m t h+2)) (by
    intro w hw
    obtain ⟨H,hH,rfl⟩:=List.mem_map.mp hw
    exact BinaryFiniteContext.labels_length H ((hb H hH).1.trans hF) (fun x hx=>hl x ((hb H hH).2 x hx)))
  simp only [List.length_map] at he
  simpa only [historyBits,historyBound,Nat.mul_assoc] using he.trans (Nat.mul_le_mul_right _ hn)

section
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
lemma length_bound {loc : Fin d → Fin m} {F : Finset (Fin m)} {v eta lo hi : ℝ}
    {q n k h p t : ℕ} {s : State (Fin m)}
    (hc : Certified loc F v eta lo hi q n k s) (hs : s.Resources F q h p) (ht : q+n≤t) :
    (encode s).length≤bound m t h p := by
  have hq : q≤t := by omega
  have hn : n≤t := by omega
  have hF : F.card≤ m := (Finset.card_le_univ F).trans_eq (Fintype.card_fin m)
  have hFi : (F.image original).card≤ m := (Finset.card_image_le).trans hF
  have hB : s.B.card≤bankBound m t := hs.bank.card.trans (Nat.mul_le_mul hq (by omega))
  have hB' : s.mapFree.card≤bankBound m t := hs.map_bound.card.trans (Nat.mul_le_mul hq (by omega))
  have hb := BinaryFiniteContext.setBits_length s.B hB (fun x hx=>bank_labels hs hq x (Finset.mem_union_right _ hx))
  have hb' := BinaryFiniteContext.setBits_length s.mapFree hB' (fun x hx=>mapped_labels hs hq x (Finset.mem_union_right _ hx))
  have hP := history_length hc.old_prefix.history (hc.old_prefix.length_eq.le.trans hq) (Nat.add_le_add hFi hB) (bank_labels hs hq)
  have hP' := history_length hc.new_prefix.history (hc.new_prefix.length_eq.le.trans hq) (Nat.add_le_add hFi hB') (mapped_labels hs hq)
  have hT := history_length hc.new_tail.2.1 (hc.new_tail.1.le.trans hn) (Nat.add_le_add hFi hB') (mapped_labels hs hq)
  have hU := history_length hc.old_tail.2.1 (hc.old_tail.1.le.trans hn) (Nat.add_le_add hFi hB) (bank_labels hs hq)
  have hlam:=BinaryRational.encode_height hs.oldPrice
  have hlam':=BinaryRational.encode_height hs.newPrice
  simp only [encode,WordList.length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,bound]
  simp only [Nat.mul_assoc] at *
  omega
end
end MetricKMedianRecovery.BitMachine.BinaryCoupledState

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CorrectionSize
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves
variable {V : Type*} [LinearOrder V] {d : ℕ}
omit [LinearOrder V] in
lemma Correction.Keys.mono {r : Correction V} {q t : ℕ} (h : r.Keys q) (hqt : q≤t) : r.Keys t := by
  cases r with
  | identity=>trivial
  | shorten key i l u=>exact h.trans_le (Nat.mul_le_mul_left 3 hqt)
end MetricKMedianRecovery.CanonicalCoupledMerge

namespace MetricKMedianRecovery.BitMachine.BinaryCorrection
open WordOperations RationalLeaves CanonicalCoupledMerge
lemma length_bound {m q h : ℕ} (r : Correction (Fin m)) (hb : r.Bounded h) (hk : r.Keys q) :
    (encode r).length≤3*BinaryCoupledState.labelBound m q h+1 := by
  cases r with
  | identity=>simp only [encode,List.length_nil]; omega
  | shorten key i l u=>
    have hl:=BinaryLabel.encode_length_bound (leaf key i l) (show level (leaf key i l)≤3*q by exact hk)
      (show HeightBound h (leaf key i l) from hb.1)
    have hu:=BinaryLabel.encode_length_bound (leaf key i u) (show level (leaf key i u)≤3*q by exact hk)
      (show HeightBound h (leaf key i u) from hb.2)
    simp only [encode,pairBits_length,BinaryCoupledState.labelBound]
    omega
end MetricKMedianRecovery.BitMachine.BinaryCorrection

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList RationalLeaves CanonicalCoupledMerge
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
lemma length_bound {loc : Fin d→Fin m} {F : Finset (Fin m)} {v eta lo hi : ℝ}
    {q n k h p t : ℕ} {s : State (Fin m)}
    (hc : Certified loc F v eta lo hi q n k s) (hs : s.Resources F q h p)
    (hk : s.correction.Keys q) (ht : q+n≤t) :
    (stateBits s).length≤bound m t h p := by
  have ho:=BinaryCoupledState.length_bound hc hs ht
  have hr:=BinaryCorrection.length_bound s.correction hs.correction (hk.mono (show q≤t by omega))
  have he : (stateBits s).length≤(BinaryCoupledState.encode s).length+2*(BinaryCorrection.encode s.correction).length := by
    simp only [stateBits,BinaryCoupledState.encode,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  dsimp only [bound]
  omega
end MetricKMedianRecovery.BitMachine.BinaryCoupled

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList RationalLeaves RationalHeight CanonicalCoupledMerge
open BinaryCoupledState (labelBound bankBound historyBound)
open BinaryFiniteContext (setBits)
open BinaryFiniteMachine (historyBits)
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
lemma output_length_bound {loc : Fin d→Fin m} {F : Finset (Fin m)} {v eta lo hi : ℝ}
    {t total q k h p : ℕ} {o : Output (Fin m)} (hc : o.Correct loc F v eta lo hi total k)
    (hs : o.Resources F q h p) (hq : q≤t) (ht : total≤t) :
    (outputBits o).length≤bound m t h p := by
  have hF : F.card≤ m := (Finset.card_le_univ F).trans_eq (Fintype.card_fin m)
  have hFi : (F.image original).card≤ m := Finset.card_image_le.trans hF
  have hB : o.B.card≤bankBound m t := hs.bank.card.trans (Nat.mul_le_mul hq (by omega))
  have hl : ∀ x∈F.image original∪o.B,(BinaryLabel.encode x).length≤labelBound m t h := by
    intro x hx
    apply (BinaryLabel.encode_length_bound x ?_ ?_).trans (show 2*(3*t)+2*m+3*h+8≤labelBound m t h by unfold labelBound; omega)
    · rcases Finset.mem_union.mp hx with hx|hx
      · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
        exact Nat.zero_le _
      · exact (hs.bank.before.level x hx).trans (Nat.mul_le_mul_left _ hq)
    · rcases Finset.mem_union.mp hx with hx|hx
      · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
        trivial
      · exact hs.bank.height x hx
  have hb:=BinaryFiniteContext.setBits_length o.B hB (fun x hx=>hl x (Finset.mem_union_right _ hx))
  have hp:=BinaryCoupledState.history_length hc.2.2.2.1.history (hc.2.2.2.1.length_eq.le.trans ht) (Nat.add_le_add hFi hB) hl
  have hprice:=BinaryRational.encode_height hs.price
  simp only [outputBits,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,
    bound,BinaryCoupledState.bound]
  simp only [Nat.mul_assoc] at *
  omega
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open BinaryCoupledState
lemma bound_mono {m t h p m' t' h' p' : ℕ} (hm : m ≤ m') (ht : t ≤ t') (hh : h ≤ h') (hp : p ≤ p') :
    bound m t h p ≤ bound m' t' h' p' := by
  unfold bound BinaryCoupledState.bound historyBound bankBound labelBound
  gcongr
lemma boundPoly_eval (L : ℕ) : boundPoly.eval L=bound L L (8*L+3) L := by
  simp only [boundPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
    Polynomial.eval_one,bound,BinaryCoupledState.bound,historyBound,bankBound,labelBound]
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopSize
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordOperations WordList BinaryArithmetic RationalLeaves RationalHeight CanonicalCoupledMerge
open BinaryOpeningPayment (field field_encode)
open BinaryCoupled (stateBits outcomeBits outputBits)
lemma capPoly_eval (L : ℕ) : capPoly.eval L=20*L+4*BinaryCoupled.bound L L (8*L+3) L+100 := by
  simp only [capPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
    BinaryCoupled.boundPoly_eval]
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
lemma outcome_length_bound {loc : Fin d→Fin m} {F : Finset (Fin m)} {v eta lo hi : ℝ}
    {total k h L : ℕ} {f : Frame (Fin m)}
    (hf : f.Valid loc F v eta lo hi total k h L) (ht : total ≤ L) (hm : m ≤ L) (hh : h ≤ 8*L+3) :
    (outcomeBits f.out).length ≤ BinaryCoupled.bound L L (8*L+3) L+3 := by
  obtain ⟨he,hf⟩:=hf
  have hq : f.q ≤ L := by omega
  cases ho : f.out with
  | inl o=>
    rw [ho] at hf
    have hl:=BinaryCoupled.output_length_bound hf.1 hf.2 hq ht
    have hb:=BinaryCoupled.bound_mono hm (le_refl L) hh (le_refl L)
    simp only [outcomeBits,pairBits_length,List.length_nil]
    omega
  | inr s=>
    rw [ho] at hf
    have hl:=BinaryCoupled.length_bound hf.1 hf.2.1 hf.2.2 (show f.q+f.n ≤ L by omega)
    have hb:=BinaryCoupled.bound_mono hm (le_refl L) hh (le_refl L)
    simp only [outcomeBits,pairBits_length,List.length_cons,List.length_nil]
    omega
lemma pack_length_bound_s238_oai {loc : Fin d→Fin m} {F : Finset (Fin m)} {v eta lo hi : ℝ}
    {total k h L precision : ℕ} {f : Frame (Fin m)} {base : List Bool} {b : ℚ}
    (hf : f.Valid loc F v eta lo hi total k h L) (ht : total ≤ L) (hm : m ≤ L) (hh : h ≤ 8*L+3)
    (hbase : base.length ≤ L) (hb : (BinaryRational.encode b).length ≤ L)
    (hp : precision ≤ L) (hk : k.bits.length ≤ L) :
    (pack base b precision k f).length ≤ capPoly.eval L := by
  have ho:=outcome_length_bound hf ht hm hh
  have hn : f.q+f.n ≤ L := hf.1.trans_le ht
  simp only [pack,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil,List.length_replicate,capPoly_eval]
  omega
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.pack_length_bound_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.pack_length_bound_s238_oai
