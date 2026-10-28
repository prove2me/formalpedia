-- Prove2me | solution 1 for OAI.MatchingFPRAS.NumericMarking.sample_source
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T18:30:08.644773+00:00
-- url     : https://prove2.me/submissions/5d688492-db7b-47c1-97dd-f03d5d42492b

import Mathlib
import Definitions.Def_OAIQ051M004

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreePairProposal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Replica.Ladder

open Finset

lemma mem_base {T q : ℕ} (x : Slot T q) : x ∈ base T q ↔ rank x = T := by
  constructor
  · rintro hx
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hx
    rw [← hj]; rfl
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨(ofLex x).2,Finset.mem_univ _,?_⟩
    apply ofLex.injective
    apply Prod.ext
    · apply Fin.ext; exact hx.symm
    · rfl

end MatchingFPRAS.Replica.Ladder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_RunBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteChoice

open Finset

lemma tapeIndex_value (k : ℕ) (bits : Fin k → Bool) :
    (tapeIndex k bits).val = ∑ i, (if bits i then 1 else 0)*2^i.val := by
  change (finFunctionFinEquiv (fun i => finTwoEquiv.symm (bits i))).val = _
  rw [finFunctionFinEquiv_apply]
  apply sum_congr rfl; intro i _
  cases bits i <;> simp [finTwoEquiv]

end MatchingFPRAS.FiniteChoice

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RemainingBags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh.Materialized

open Finset MatchingFPRAS.FiniteChoice MatchingFPRAS.Variation
open scoped Classical

variable {n m : ℕ}

lemma sampleUnit_step (k : ℕ) (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (hz : 0 < count bags parent (plan rank)) (bits : Fin (n+2) → Fin k → Bool) :
    sampleUnit k (n+2) bags rank parent hb hne hp hz bits=
      residualSampler k bags rank parent hb hne hp (Fin.last (n+1))
        (drawEdge bags rank parent hb hne hp (Fin.last (n+1)) hz k (bits (Fin.last (n+1))))
        (fun i=>bits i.castSucc.castSucc) := rfl

open Finset MatchingFPRAS.Variation
open scoped Classical

end MatchingFPRAS.UnitRefresh.Materialized

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_AdaptiveLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh

lemma pairingCount_le_half_power (n : ℕ) : pairingCount n ≤ n^(n/2) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih' =>
    rw [pairingCount_add_two,show (n+2)/2=n/2+1 by omega,pow_succ]
    calc
      (n+1)*pairingCount n ≤ (n+2)*((n+2)^(n/2)) :=
        Nat.mul_le_mul (by omega) (ih.trans (Nat.pow_le_pow_left (by omega) (n/2)))
      _ = (n+2)^(n/2)*(n+2) := Nat.mul_comm _ _

end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.Trial

open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder MatchingFPRAS.Adaptive
open scoped Classical

attribute [instance] Layer.finite

end MatchingFPRAS.Trial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeFraction
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma normalize_repr (x : Fraction) : normalize x=repr (val x) := by
  by_cases hd : x.2=0
  · simp [normalize,repr,val,hd]
  · have he : val x=mkRat (x.1:Int) x.2 := by simp [val,Rat.mkRat_eq_div]
    simp only [normalize,hd,↓reduceIte,he,repr,Rat.num_mkRat,Rat.den_mkRat]
    simp [Nat.gcd_comm,←Int.natCast_ediv]

lemma val_nonneg (x : Fraction) : 0≤val x := by unfold val; positivity
lemma val_repr {q : ℚ} (h : 0≤q) : val (repr q)=q := by
  have hn : 0≤q.num := by exact Rat.num_nonneg.mpr h
  have he : (q.num.natAbs : ℤ)=q.num := Int.natAbs_of_nonneg hn
  change (q.num.natAbs:ℚ)/(q.den:ℚ)=q
  rw [←Int.cast_natCast q.num.natAbs,he]
  exact Rat.num_div_den q

lemma normalize_val (x : Fraction) : val (normalize x)=val x := by
  rw [normalize_repr]
  exact val_repr (val_nonneg x)

lemma normalize_den_pos (x : Fraction) : 0<(normalize x).2 := by
  rw [normalize_repr]; exact (val x).pos

lemma mul_val (x y : Fraction) : val (mul (x,y))=val x*val y := by
  rw [mul,normalize_val]
  simp only [val,Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

lemma add_val (x y : Fraction) (hx : x.2≠0) (hy : y.2≠0) :
    val (add (x,y))=val x+val y := by
  rw [add,normalize_val]
  simp only [val,Nat.cast_add,Nat.cast_mul]
  rw [div_add_div (x.1:ℚ) (y.1:ℚ) (b:=(x.2:ℚ)) (d:=(y.2:ℚ))
    (by exact_mod_cast hx) (by exact_mod_cast hy)]
  ring

lemma div_val (x y : Fraction) : val (div (x,y))=val x/val y := by
  rw [div,normalize_val]
  simp only [val,Nat.cast_mul]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

lemma less_val (x y : Fraction) (hx : 0<x.2) (hy : 0<y.2) :
    less (x,y)=decide (val x<val y) := by
  unfold less
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [val,val,div_lt_div_iff₀ (by exact_mod_cast hx) (by exact_mod_cast hy)]
  norm_cast

end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeDPCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped

variable {V : Type} [Fintype V] [DecidableEq V] {m : ℕ}

omit [Fintype V] in
lemma trim_activeRep (bags : V → Finset (Fin m)) (R : Finset V) (l : Fin m) :
    (trim (activeRep bags R) l.val).Perm (activeRep bags (UnitRefresh.trim bags R l)) := by
  unfold trim activeRep UnitRefresh.trim
  rw [List.filter_map]
  apply List.Perm.map
  apply List.perm_of_nodup_nodup_toFinset_eq ((Finset.nodup_toList R).filter _) (Finset.nodup_toList _)
  ext x
  simp
end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreePolynomialGrid
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B : Type} [Codec A] [Codec B]

variable {m n : A → ℕ} {f : A×(ℕ×ℕ) → B}
omit [Codec A] [Codec B] in
lemma clip_eq (K n : ℕ) (h : n.size≤K) : clip (K,n)=n := by simp [clip,h]
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeListMore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B X : Type} [Codec A] [Codec B] [Codec X]

lemma listMin_le_default (as : List ℕ) (d : ℕ) : listMin (as,d)≤d := by
  induction as generalizing d with
  | nil => rfl
  | cons a as ih => exact (ih (min d a)).trans (min_le_left _ _)

lemma listMin_le {as : List ℕ} {d a : ℕ} (ha : a∈as) : listMin (as,d)≤a := by
  induction as generalizing d with
  | nil => simp at ha
  | cons b bs ih =>
    simp only [List.mem_cons] at ha
    rcases ha with rfl|ha
    · exact (listMin_le_default bs (min d a)).trans (min_le_right _ _)
    · exact ih ha

lemma le_listMin {as : List ℕ} {d a : ℕ} (hd : a≤d) (ha : ∀ b∈as,a≤b) :
    a≤listMin (as,d) := by
  induction as generalizing d with
  | nil => exact hd
  | cons b bs ih =>
    apply ih (le_min hd (ha b (by simp)))
    intro c hc; exact ha c (by simp [hc])
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeCategorical
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma fold_den (xs : List Fraction) (a : Fraction) (ha : 0<a.2) :
    0<(xs.foldl (fun a b=>add (b,a)) a).2 := by
  induction xs generalizing a with
  | nil => exact ha
  | cons _ _ ih => exact ih _ (normalize_den_pos _)
lemma fold_val (xs : List Fraction) (a : Fraction) (ha : 0<a.2)
    (hx : ∀ b∈xs,0<b.2) :
    val (xs.foldl (fun a b=>add (b,a)) a)=val a+(xs.map val).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons b bs ih =>
    have hab : 0<(add (b,a)).2 := normalize_den_pos _
    rw [List.foldl_cons,ih _ hab (fun c hc=>hx c (by simp [hc])),
      add_val b a (Nat.ne_of_gt (hx b (by simp))) (Nat.ne_of_gt ha)]
    simp only [List.map_cons,List.sum_cons]
    ring
lemma sum_den (xs : List Fraction) : 0<(sum xs).2 := fold_den xs (0,1) (by decide)
lemma sum_val (xs : List Fraction) (hx : ∀ b∈xs,0<b.2) :
    val (sum xs)=(xs.map val).sum := by
  rw [sum,fold_val xs (0,1) (by decide) hx]
  simp [val]

lemma cumulativeFraction_val {r : ℕ} (p : Fin r → ℚ) (hp : ∀ i,0≤p i) (n : ℕ) :
    val (cumulativeFraction (List.ofFn (fun i=>repr (p i)),n))=FiniteChoice.cumulative p n := by
  rw [cumulativeFraction,sum_val]
  · simp only [List.map_take,List.map_ofFn,Function.comp_apply,val_repr (hp _),List.sum_take_ofFn,
      FiniteChoice.cumulative,Finset.sum_filter]
  · intro b hb
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hb)
    subst b
    exact (p i).pos

end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.TreeTyped

lemma bitDenominator_eq (bs : List Bool) : bitDenominator bs=2^bs.length := by
  have h : ∀ a,bs.foldl (fun a _=>2*a) a=a*2^bs.length := by
    induction bs with
    | nil => intro a; simp
    | cons _ _ ih => intro a; simp only [List.foldl_cons,ih,List.length_cons,pow_succ]; ring
  simpa [bitDenominator] using h 1

end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.ExecutableChoice
open TreeTyped TreeFraction

lemma choose_eq {r K : ℕ} (p : Fin r → ℚ) (hp : ∀ i,0≤p i)
    (hs : ∑ i,p i=1) (hK : 0<K) (J : Fin K) :
    choose (List.ofFn (fun i=>repr (p i)),(J.val,K))=(FiniteChoice.choose p hs hK J).val := by
  let j := FiniteChoice.choose p hs hK J
  have hpred (i : ℕ) : predicate ((List.ofFn (fun i=>repr (p i)),(J.val,K)),i)=
      decide ((J.val:ℚ)/K<FiniteChoice.cumulative p (i+1)) := by
    rw [predicate,less_val (J.val,K) (cumulativeFraction (List.ofFn (fun i=>repr (p i)),i+1)) hK (sum_den _),cumulativeFraction_val p hp]
    rfl
  unfold choose
  simp only [List.length_ofFn]
  apply le_antisymm
  · apply listMin_le
    simp only [List.mem_filter,List.mem_range,hpred,decide_eq_true_eq]
    exact ⟨j.isLt,FiniteChoice.choose_upper p hs hK J⟩
  · apply le_listMin j.isLt.le
    intro i hi
    simp only [List.mem_filter,List.mem_range,hpred,decide_eq_true_eq] at hi
    exact FiniteChoice.choose_le p hs hK J ⟨i,hi.1⟩ hi.2

lemma chooseBits_eq {r k : ℕ} (p : Fin r → ℚ) (hp : ∀ i,0≤p i)
    (hs : ∑ i,p i=1) (bits : Fin k → Bool) :
    chooseBits (List.ofFn (fun i=>repr (p i)),List.ofFn bits)=
      (FiniteChoice.chooseBits p hs k bits).val := by
  have hv' (k : ℕ) (bits : Fin k → Bool) :
      StackAddition.value (List.ofFn bits)=∑ i, (if bits i then 1 else 0)*2^i.val := by
    induction k with
    | zero => simp [StackAddition.value]
    | succ k ih =>
      rw [List.ofFn_succ,StackAddition.value,ih,Fin.sum_univ_succ]
      simp only [Fin.val_zero,pow_zero,Nat.mul_one,Fin.val_succ,pow_succ]
      rw [Finset.mul_sum]
      have hn : (bits 0).toNat=(if bits 0 then 1 else 0) := by cases bits 0 <;> rfl
      rw [hn]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
  have hv : StackAddition.value (List.ofFn bits)=(FiniteChoice.tapeIndex k bits).val := by
    rw [FiniteChoice.tapeIndex_value,hv']
  rw [chooseBits,bitDenominator_eq,List.length_ofFn,hv]
  exact choose_eq p hp hs (by positivity) (FiniteChoice.tapeIndex k bits)
end MatchingFPRAS.ExecutableChoice

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeFractionExtra
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped Polynomial

lemma sub_val (x y : Fraction) (hx : 0<x.2) (hy : 0<y.2) (h : val y≤val x) :
    val (sub (x,y))=val x-val y := by
  have hxy : y.1*x.2≤x.1*y.2 := by
    rw [val,val,div_le_div_iff₀ (by exact_mod_cast hy) (by exact_mod_cast hx)] at h
    exact_mod_cast h
  rw [sub,normalize_val]
  simp only [val,Nat.cast_sub hxy,Nat.cast_mul]
  rw [div_sub_div (x.1:ℚ) (y.1:ℚ) (by exact_mod_cast hx.ne') (by exact_mod_cast hy.ne')]
  ring
lemma mul_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    mul (repr x,repr y)=repr (x*y) := by
  have h:=mul_val (repr x) (repr y)
  rw [val_repr hx,val_repr hy] at h
  unfold mul at h ⊢
  rw [normalize_val] at h
  rw [normalize_repr,h]
lemma div_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    div (repr x,repr y)=repr (x/y) := by
  have h:=div_val (repr x) (repr y)
  rw [val_repr hx,val_repr hy] at h
  unfold div at h ⊢
  rw [normalize_val] at h
  rw [normalize_repr,h]
lemma sub_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) (hxy : y≤x) :
    sub (repr x,repr y)=repr (x-y) := by
  have h:=sub_val (repr x) (repr y) x.pos y.pos (by simpa only [val_repr hx,val_repr hy] using hxy)
  rw [val_repr hx,val_repr hy] at h
  unfold sub at h ⊢
  rw [normalize_val] at h
  rw [normalize_repr,h]
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeQuad
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B : Type} [Codec A] [Codec B]

omit [Codec A] [Codec B] in
lemma mem_listProduct (a : A) (b : B) (s : List A) (t : List B) :
    (a,b)∈s.product t ↔ a∈s ∧ b∈t := List.mem_product

omit [Codec A] [Codec B] in
lemma quadFn_ofFn (f : Fin 4→A) : quadFn (quadOfFn f)=f := by
  funext i
  fin_cases i <;> rfl
omit [Codec A] [Codec B] in
lemma mem_quads (q : Quad A) (s : List A) : q∈quads s ↔ ∀ i,quadFn q i∈s := by
  rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp only [quads,mem_listProduct]
  constructor
  · rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨⟨h 0,h 1⟩,⟨h 2,h 3⟩⟩
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBottleneck
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma maximum_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    maximum (repr x,repr y)=repr (max x y) := by
  unfold maximum
  rw [less_val _ _ x.pos y.pos,val_repr hx,val_repr hy]
  simp only [decide_eq_true_eq]
  split_ifs with h
  · rw [max_eq_right (le_of_lt h)]
  · rw [max_eq_left (le_of_not_gt h)]
lemma minimum_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    minimum (repr x,repr y)=repr (min x y) := by
  unfold minimum
  rw [less_val _ _ x.pos y.pos,val_repr hx,val_repr hy]
  simp only [decide_eq_true_eq]
  split_ifs with h
  · rw [min_eq_left (le_of_lt h)]
  · rw [min_eq_right (le_of_not_gt h)]
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeStateTable
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped

variable {I A : Type} [Codec I] [Codec A] [DecidableEq I] [Inhabited I]
omit [Codec I] [Codec A] [Inhabited I] in
lemma lookup_stateRep (d : A) (keys : List I) (s : I→A) (i : I) (hi : i∈keys) :
    lookup d (stateRep keys s,i)=s i := by
  induction keys with
  | nil=>simp at hi
  | cons j keys ih=>
    simp only [List.mem_cons] at hi
    by_cases hji : j=i
    · subst j
      simp [lookup,stateRep]
    · have hn : i∈keys:=hi.resolve_left (Ne.symm hji)
      simpa [lookup,stateRep,hji] using ih hn

omit [Codec I] [Codec A] [Inhabited I] in
lemma setState_rep (keys : List I) (s : I→A) (i : I) (a : A) :
    setState (stateRep keys s,(i,a))=stateRep keys (Function.update s i a) := by
  unfold setState stateRep
  simp only [List.map_map]
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_apply,Function.update_apply]

omit [Codec I] [Codec A] [Inhabited I] in
lemma setPair_rep (keys : List I) (s : I→A) (i j : I) (a : A×A) :
    setPair (stateRep keys s,((i,j),a))=stateRep keys (Replica.replacePair i j s a) := by
  simp only [setPair,setState_rep,Replica.replacePair]
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeReweight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
lemma lookup_image {I E A : Type} [DecidableEq E] (d : A) (keys : List I)
    (f : I→E) (g : I→A) (hf : Function.Injective f) (i : I) (hi : i∈keys) :
    lookup d (keys.map (fun j=>(f j,g j)),f i)=g i := by
  induction keys with
  | nil=>simp at hi
  | cons j keys ih=>
    by_cases hji : j=i
    · subst j; simp [lookup]
    · have hne : f j≠f i:=fun h=>hji (hf h)
      have hi' : i∈keys:=(List.mem_cons.mp hi).resolve_left (Ne.symm hji)
      simpa [lookup,hne] using ih hi'
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeNumberedCodec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {A : Type} [Fintype A] [LinearOrder A]

lemma index_orderedEnum (i : Fin (Fintype.card A)) :
    index (UnitRefresh.orderedEnum A i)=i.val := by simp [index]
end MatchingFPRAS.TreeTyped.Numbered

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeSlotIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeTyped.Numbered Replica.Ladder

lemma slot_index {T q : ℕ} (x : Slot T q) : index x=q*rank x+(ofLex x).2.val := by
  have he : numberOrderIso T q=coordinateOrderIso T q := Subsingleton.elim _ _
  have h:=congrArg (fun e : Slot T q≃o Fin ((T+1)*q)=>(e x).val) he
  change index x=(ofLex x).2.val+q*(ofLex x).1.val at h
  simpa only [rank,Nat.add_comm] using h
lemma slot_default_zero (T q : ℕ) (hq : 0<q) :
    index (toLex ((0 : Fin (T+1)),(⟨0,hq⟩ : Fin q)))=0 := by
  rw [slot_index]
  rfl
lemma slot_index_div {T q : ℕ} (x : Slot T q) : index x/q=rank x := by
  rw [slot_index,Nat.add_comm,Nat.add_mul_div_left]
  · simp [Nat.div_eq_of_lt (ofLex x).2.isLt]
  · exact Nat.zero_lt_of_lt (ofLex x).2.isLt
end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeOptions
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableOptions
open TreeTyped TreeFraction

variable {A B C Ω : Type} [Codec A] [Codec B] [Codec C]

omit [Codec A] [Codec B] [Codec C] in
lemma pure_repr (e : Ω→A) (a : Ω) : pure (e a)=repr e (.pure a) := by
  simp [pure,repr,WeightedOptions.pure,TreeFraction.repr,List.ofFn_succ]

omit [Codec A] [Codec B] [Codec C] in
lemma mix_repr (e : Ω→A) (p : ℚ) (hp : 0≤p) (hp1 : p≤1) (a b : WeightedOptions Ω) :
    mix (TreeFraction.repr p,(repr e a,repr e b))=repr e (.mix p hp hp1 a b) := by
  have h1 : (1,1)=TreeFraction.repr 1 := rfl
  simp only [mix,scale,repr,List.map_ofFn,h1,sub_repr (by decide) hp hp1]
  simp only [WeightedOptions.mix]
  rw [List.ofFn_add]
  apply congrArg₂ List.append <;> apply List.ofFn_inj.mpr <;> funext i
  · change (e (a.out i),mul (TreeFraction.repr p,TreeFraction.repr (a.mass i))) =
      (e (Fin.addCases a.out b.out (i.castAdd b.size)),TreeFraction.repr (Fin.addCases (fun i=>p*a.mass i) (fun i=>(1-p)*b.mass i) (i.castAdd b.size)))
    simp only [Fin.addCases_left,mul_repr hp (a.nonneg i)]
  · simp only [Function.comp_def,Fin.addCases_right]
    rw [mul_repr (sub_nonneg.mpr hp1) (b.nonneg i)]

omit [Codec A] [Codec B] [Codec C] in
lemma map_repr {Ψ : Type} (e : Ω→A) (d : Ψ→B) (f : Ω→Ψ) (g : C×A→B) (z : C)
    (h : ∀ a,g (z,e a)=d (f a)) (c : WeightedOptions Ω) :
    map g (z,repr e c)=repr d (c.map f) := by
  simp only [map,repr,List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext i
  simp only [WeightedOptions.map,Function.comp_apply,h]

omit [Codec A] [Codec B] [Codec C] in
lemma draw_repr [Fintype Ω] [DecidableEq Ω] (e : Ω→A) (c : WeightedOptions Ω) (d : A)
    {k : ℕ} (bits : Fin k→Bool) :
    draw d (repr e c,List.ofFn bits)=e (c.draw k bits) := by
  simp only [draw,repr,List.map_ofFn,Function.comp_def]
  rw [ExecutableChoice.chooseBits_eq c.mass c.nonneg c.total bits]
  simp only [List.getD,List.getElem?_ofFn,(FiniteChoice.chooseBits c.mass c.total k bits).isLt,
    ↓reduceDIte,Option.getD_some,WeightedOptions.draw]

end MatchingFPRAS.ExecutableOptions

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeOptionsFinite
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableOptions
open TreeTyped TreeFraction

variable {A : Type} [Codec A] [LinearOrder A]

omit [Codec A] in
lemma numbering_ofFn (s : Finset A) :
    List.ofFn (fun i=>(WeightedOptions.numbering s i).val)=s.sort (·≤·) := by
  apply List.ext_getElem
  · simp
  · intro i hi _
    simp only [List.getElem_ofFn]
    change s.orderEmbOfFin rfl ⟨i,by simpa using hi⟩ = (s.sort (·≤·))[i]
    rw [Finset.orderEmbOfFin_apply]
    rfl
omit [Codec A] in
lemma uniform_repr (s : Finset A) (hs : s.Nonempty) :
    uniform s=repr id (WeightedOptions.uniform s hs) := by
  unfold uniform repr
  rw [←numbering_ofFn,List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext i
  simp only [WeightedOptions.uniform,id_eq]
  simp only [Function.comp_def]
  rw [normalize_repr]
  congr 1
  simp only [val,Nat.cast_one,one_div]

omit [Codec A] in
lemma neighbors_repr (a : A) (s : Finset A) (d : ℕ) (hd : s.card≤d) :
    neighbors ((a,s),d)=repr id (WeightedOptions.neighbors a s d hd) := by
  have hsub : (s.card:ℚ)/d≤1 := by
    by_cases hz : d=0
    · simp [hz]
    · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hz)).mpr (by exact_mod_cast hd)
  have hn : TreeFraction.normalize (s.card,d)=TreeFraction.repr ((s.card:ℚ)/d) := normalize_repr _
  have hu : TreeFraction.normalize (1,d)=TreeFraction.repr ((d:ℚ)⁻¹) := by
    simpa only [val,Nat.cast_one,one_div] using normalize_repr (1,d)
  have h1 : (1,1)=TreeFraction.repr 1 := rfl
  simp only [neighbors,repr,hn,hu,h1,sub_repr (by decide) (by positivity) hsub]
  simp only [WeightedOptions.neighbors]
  rw [List.ofFn_succ_last,←numbering_ofFn,List.map_ofFn]
  simp only [Fin.lastCases_castSucc,Fin.lastCases_last,id_eq,Function.comp_def]
end MatchingFPRAS.ExecutableOptions

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeReach
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A C : Type} [Codec A] [Codec C] [LinearOrder A]

namespace FiniteReach
variable (p : C×(A×A) → Bool)

variable {p}

omit [Codec A] [Codec C] in
lemma countDown_sweep (x : Input C A) (n : ℕ) :
    countDown (fun x=>sweep p x.2) n x=(x.1,(fun s=>grow p (x.1,s))^[n] x.2) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [countDown,ih]
    simp only [sweep,Function.iterate_succ_apply]

omit [Codec A] [Codec C] in
lemma reach_eq (x : Input C A) : reach p x=(fun s=>grow p (x.1,s))^[x.1.2.card] x.2 := by
  rw [reach,countDown_sweep]
end FiniteReach
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeReachCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.FiniteReach
variable {A C : Type} [Codec A] [Codec C] [LinearOrder A] [Fintype A]
variable {p : C×(A×A) → Bool}
omit [Codec A] [Codec C]
lemma grow_source (G : SimpleGraph A) [DecidableRel G.Adj] (c : C)
    (hp : ∀ a b,p (c,(a,b))=decide (G.Adj a b)) (s : Finset A) :
    grow p ((c,Finset.univ),s)=ComputableReach.grow G s := by
  ext a
  simp only [grow,ComputableReach.grow,Finset.mem_union,Finset.mem_filter,hp,decide_eq_true_eq]
lemma reach_source (G : SimpleGraph A) [DecidableRel G.Adj] (c : C)
    (hp : ∀ a b,p (c,(a,b))=decide (G.Adj a b)) (s : Finset A) :
    reach p ((c,Finset.univ),s)=ComputableReach.reached G s (Fintype.card A) := by
  rw [reach_eq,Finset.card_univ]
  have he : (fun s=>grow p ((c,Finset.univ),s))=ComputableReach.grow G := funext (grow_source G c hp)
  rw [he]
  rfl
lemma reach_closure (G : SimpleGraph A) [DecidableRel G.Adj] (c : C)
    (hp : ∀ a b,p (c,(a,b))=decide (G.Adj a b)) (a : A) :
    reach p ((c,Finset.univ),{a})=ComputableReach.closure G a := reach_source G c hp {a}
end MatchingFPRAS.TreeTyped.FiniteReach

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeSparseComponents
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {A C : Type} [Codec A] [Codec C] [LinearOrder A]
attribute [local instance] Transport.Sparse.finsetOrder

variable (p : C×(A×A) → Bool)
variable {p}

omit [Codec A] [Codec C]
variable [Fintype A] {V : Type} [Fintype V] [DecidableEq V]
variable (ends : A → Sym2 V) (c : C)
variable (hp : ∀ a b,p (c,(a,b))=decide (∃ v,v∈ends a ∧ v∈ends b))
include hp
omit [Fintype A] in
lemma adjacent_eq (U : Finset A) (a b : A) :
    adjacent p ((c,U),(a,b))=decide ((Transport.overlayLineGraph (fun e v=>v∈ends e) U).Adj a b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [adjacent,Bool.and_eq_true,decide_eq_true_eq,hp]
  rfl
lemma component_eq (U : Finset A) (a : A) :
    component (p:=p) (((c,Finset.univ),U),a)=Transport.Sparse.component ends U a := by
  unfold component Transport.Sparse.component
  rw [FiniteReach.reach_closure _ (c,U) (adjacent_eq ends c hp U)]
lemma allComponents_eq (U : Finset A) :
    allComponents (p:=p) ((c,Finset.univ),U)=Transport.Sparse.allComponents ends U := by
  unfold allComponents Transport.Sparse.allComponents
  exact Finset.image_congr (fun a _=>component_eq ends c hp U a)
lemma discrepancies_eq (a b : Transport.PM (fun e v=>v∈ends e)) :
    discrepancies (p:=p) ((c,Finset.univ),(a.val,b.val))=Transport.Sparse.discrepancies ends a b := by
  unfold discrepancies Transport.Sparse.discrepancies
  dsimp only
  rw [allComponents_eq ends c hp]
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeCycleTable
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped ExecutableOptions

variable {E C : Type} [Codec E] [Codec C] [LinearOrder E]
attribute [local instance] Transport.Sparse.finsetOrder

variable [Fintype E] {V : Type} [Fintype V] [DecidableEq V]
variable (ends : E→Sym2 V) (p : C×(E×E)→Bool) (c : C)
variable (hp : ∀ a b,p (c,(a,b))=decide (∃ v,v∈ends a ∧ v∈ends b))
omit [Codec E] [Codec C] in
include hp in
lemma cycle_eq (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e)) (s : Finset E) :
    cycle p (((c,Finset.univ),pairRepr ends a),s)=pairRepr ends (Transport.Sparse.cycle ends a s) := by
  unfold cycle pairRepr
  rw [allComponents_eq ends c hp]
  unfold Transport.Sparse.cycle
  split_ifs <;> rfl
omit [Codec E] [Codec C] in
include hp in
lemma cycleTable_eq (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e)) :
    cycleTable p ((c,Finset.univ),pairRepr ends a)=repr (pairRepr ends) (Transport.Sparse.cycleTable ends a) := by
  unfold cycleTable
  rw [show discrepancies (p:=p) ((c,Finset.univ),pairRepr ends a)=Transport.Sparse.discrepancies ends a.1 a.2 from
    discrepancies_eq ends c hp a.1 a.2]
  unfold Transport.Sparse.cycleTable
  split_ifs with h hn hn
  · exact False.elim (Finset.card_pos.mpr hn |>.ne' h)
  · exact pure_repr _ _
  · rw [uniform_repr _ hn]
    exact map_repr id (pairRepr ends) _ _ ((c,Finset.univ),pairRepr ends a) (cycle_eq ends p c hp a) _
  · exfalso
    exact h (Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn))
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRationalWeight
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
lemma fold_product_repr (xs : List ℚ) (hx : ∀ x∈xs,0≤x) (a : ℚ) (ha : 0≤a) :
    ((xs.map repr).foldl (fun a b=>mul (b,a)) (repr a))=repr (xs.prod*a) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    have h : 0≤x:=hx x (by simp)
    simp only [List.map_cons,List.foldl_cons,mul_repr h ha]
    rw [ih (fun y hy=>hx y (by simp [hy])) (x*a) (mul_nonneg h ha)]
    congr 1
    simp only [List.prod_cons]
    ring
lemma product_repr (xs : List ℚ) (hx : ∀ x∈xs,0≤x) : product (xs.map repr)=repr xs.prod := by
  unfold product
  have h:=fold_product_repr xs hx 1 (by decide)
  simpa only [mul_one,show repr (1:ℚ)=(1,1) from rfl] using h
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped TreeFraction

variable {E C : Type} [Codec E] [Codec C] [LinearOrder E]
attribute [local instance] Transport.Sparse.finsetOrder

variable (w : C×E→Fraction) (c : C) (q : E→ℚ) (hq : ∀ e,0≤q e)
    (hw : ∀ e,w (c,e)=TreeFraction.repr (q e))
omit [Codec E] [Codec C] in
include hq hw in
lemma weight_repr (s : Finset E) : weight w (c,s)=TreeFraction.repr (∏ e∈s,q e) := by
  unfold weight
  dsimp only
  simp only [hw]
  change product ((s.sort (·≤·)).map (TreeFraction.repr ∘ q))=_
  rw [←List.map_map,product_repr _ (by intro a ha; obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha; exact hq b)]
  congr 1
  simpa only [Finset.sort_toFinset] using (List.prod_toFinset q (Finset.sort_nodup s (·≤·))).symm

variable [Fintype E] {V : Type} [Fintype V] [DecidableEq V] (ends : E→Sym2 V)
omit [Codec E] [Codec C] [Fintype E] [DecidableEq V] in
lemma pairWeight_repr (w z : C×E→Fraction) (c : C) (q r : E→ℚ) (hq : ∀ e,0≤q e) (hr : ∀ e,0 ≤ r e)
    (hw : ∀ e,w (c,e)=TreeFraction.repr (q e)) (hz : ∀ e,z (c,e)=TreeFraction.repr (r e))
    (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e)) :
    pairWeight w z (c,pairRepr ends a)=TreeFraction.repr (Transport.Sparse.rationalPairWeight ends q r a) := by
  unfold pairWeight pairRepr
  rw [weight_repr w c q hq hw,weight_repr z c r hr hz,mul_repr (Finset.prod_nonneg (fun e _=>hq e))
    (Finset.prod_nonneg (fun e _=>hr e))]
  rfl
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeSlotWeight
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma add_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    add (repr x,repr y)=repr (x+y) := by
  have h:=add_val (repr x) (repr y) x.pos.ne' y.pos.ne'
  rw [val_repr hx,val_repr hy] at h
  unfold add at h ⊢
  rw [normalize_val] at h
  rw [normalize_repr,h]
lemma repr_nat (n : ℕ) : repr (n:ℚ)=(n,1) := by simp [repr]

lemma fuelPower_repr (q : ℚ) (hq : 0≤q) (fuel : List Bool) :
    fuelPower (repr q,fuel)=repr (q^fuel.length) := by
  unfold fuelPower
  have he : fuel.map (fun _=>repr q)=(fuel.map (fun _=>q)).map repr := by simp
  rw [he,product_repr _ (by intro t ht; obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ht; exact hq)]
  congr 1
  simp
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped TreeFraction

lemma tierBase_repr (n : ℕ) : tierBase n=TreeFraction.repr (1+((n:ℚ)^2)⁻¹) := by
  unfold tierBase
  rw [←repr_nat (n*n)]
  have h1 : (1,1)=TreeFraction.repr (1:ℚ) := rfl
  rw [h1,div_repr (by decide) (by positivity),add_repr (by decide) (by positivity)]
  simp only [Nat.cast_mul,one_div,pow_two]

lemma tierPower_repr (n : ℕ) (fuel : List Bool) (r : ℕ) :
    tierPower ((n,fuel),r)=TreeFraction.repr ((1+((n:ℚ)^2)⁻¹)^(fuel.length-r)) := by
  unfold tierPower
  rw [tierBase_repr,fuelPower_repr _ (by positivity),List.length_take,min_eq_left (Nat.sub_le _ _)]

lemma slotWeight_repr (n : ℕ) (fuel : List Bool) (r : ℕ) (q : ℚ) (hq : 0≤q) :
    slotWeight (((n,fuel),r),TreeFraction.repr q)=TreeFraction.repr
      (max (((1+((n:ℚ)^2)⁻¹)^(fuel.length-r))⁻¹)
        (min ((1+((n:ℚ)^2)⁻¹)^(fuel.length-r)) q)) := by
  unfold slotWeight
  rw [tierPower_repr]
  have h1 : (1,1)=TreeFraction.repr (1:ℚ) := rfl
  rw [h1,div_repr (by decide) (by positivity),minimum_repr (by positivity) hq,
    maximum_repr (by positivity) (le_min (by positivity) hq)]
  simp only [one_div]

lemma slotWeight_source {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
    {bags : V→Finset L} {q : ℕ} (fuel : List Bool) (w : Transport.BagEdge bags→ℚ)
    (hw : ∀ e,0≤w e) (x : Replica.Ladder.Slot fuel.length q) (e : Transport.BagEdge bags) :
    slotWeight (((Fintype.card V,fuel),Replica.Ladder.rank x),TreeFraction.repr (w e))=
      TreeFraction.repr (Transport.rationalSlotWeight w x e) := by
  exact slotWeight_repr _ _ _ _ (hw e)
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeDPProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped

lemma privateNumber_perm {a b : Bags} (h : a.Perm b) (l : ℕ) : privateNumber a l=privateNumber b l :=
  (h.filter _).length_eq
lemma sharedNumber_perm {a b : Bags} (h : a.Perm b) (l : ℕ) : sharedNumber a l=sharedNumber b l :=
  (h.filter _).length_eq
lemma totalNumber_perm {a b : Bags} (h : a.Perm b) (l : ℕ) : totalNumber a l=totalNumber b l :=
  (h.filter _).length_eq
lemma context_perm {a b : Bags} (h : a.Perm b) (ps : Parents) (l : ℕ) (t : Table) :
    context ((a,ps),(l,t))=context ((b,ps),(l,t)) := by
  simp only [context,privateNumber_perm h,sharedNumber_perm h,totalNumber_perm h]

end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeDPCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped

lemma initial_eq (m B : ℕ) : initial (m,B)=UnitRefresh.Materialized.initial m B := by
  exact tabulate_materialized (fun x : ℕ×(ℕ×ℕ)=>UnitRefresh.pairingCount x.2.2) 0 m B

lemma map_range_ofFn {A : Type} (f : ℕ → A) (n : ℕ) :
    (List.range n).map f=List.ofFn (fun i : Fin n=>f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'; simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]

lemma finish_eq (t : Table) (m : ℕ) :
    finish (t,m)=∏ a : Fin m,UnitRefresh.Materialized.read t a.val 0 := by
  rw [finish,map_range_ofFn,List.prod_ofFn]
  rfl

end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeTierWeights
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma index_enum {I : Type} [Fintype I] [LinearOrder I]
    (i : Fin (Fintype.card I)) : index (UnitRefresh.orderedEnum I i)=i.val := by simp [index]
lemma range_slot_indices (T q : ℕ) : List.range ((T+1)*q)=
    List.ofFn (fun i : Fin (Fintype.card (Slot T q))=>index (UnitRefresh.orderedEnum (Slot T q) i)) := by
  simp only [index_enum]
  rw [show Fintype.card (Slot T q)=(T+1)*q from slot_card T q]
  simpa using (ExecutableDP.map_range_ofFn (fun n=>n) ((T+1)*q))

lemma weightRows_source {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
    {bags : V→Finset L} (w : Transport.BagEdge bags→ℚ) (hw : ∀ e,0≤w e)
    (ft fq : List Bool) :
    weightRows ((Fintype.card V,ft),(fq,List.ofFn (fun e=>TreeFraction.repr (w (UnitRefresh.orderedEnum _ e)))))=
      List.ofFn (fun i : Fin (Fintype.card (Slot ft.length fq.length))=>
        List.ofFn (fun e=>TreeFraction.repr
          (Transport.rationalSlotWeight w (UnitRefresh.orderedEnum _ i) (UnitRefresh.orderedEnum _ e)))) := by
  have hrow (slot : Slot ft.length fq.length) :
      weightRow (((Fintype.card V,ft),(fq,List.ofFn
        (fun edge=>TreeFraction.repr (w (UnitRefresh.orderedEnum _ edge))))),index slot)=
        List.ofFn (fun edge=>TreeFraction.repr
          (Transport.rationalSlotWeight w slot (UnitRefresh.orderedEnum _ edge))) := by
    unfold weightRow
    dsimp only
    rw [slot_index_div,List.map_ofFn]
    exact congrArg List.ofFn (funext (fun edge=>slotWeight_source ft w hw slot
      (UnitRefresh.orderedEnum (Transport.BagEdge bags) edge)))
  rw [weightRows,slots,slotCount,range_slot_indices,List.map_ofFn]
  exact congrArg List.ofFn (funext (fun slot=>hrow
    (UnitRefresh.orderedEnum (Slot ft.length fq.length) slot)))

end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeStateNormalize
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped Polynomial

variable {I E : Type} [Codec I] [Codec E] [DecidableEq I] [Inhabited I] [LinearOrder E]

omit [Codec I] [Codec E] [Inhabited I] in
lemma normalizeState_rep {Ω : Type} (keys : List I) (univ : Finset E) (e : Ω→Finset E)
    (he : ∀ a,e a⊆univ) (s : I→Ω) :
    normalizeState ((keys,univ),stateRep keys (e ∘ s))=stateRep keys (e ∘ s) := by
  unfold normalizeState stateRep
  apply List.map_congr_left
  intro i hi
  change (i,lookup ∅ (stateRep keys (e ∘ s),i)∩univ)=(i,e (s i))
  rw [lookup_stateRep ∅ keys (e ∘ s) i hi]
  simp only [Function.comp_apply,Finset.inter_eq_left.mpr (he (s i))]
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeMatchingCheck
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]

omit [Codec E] [Codec V] [Codec C] in
lemma matchingCheck_eq [Fintype E] [Fintype V] (p : C×(E×V)→Bool) (c : C) (inc : E→V→Prop)
    [DecidableRel inc] (hp : ∀ e v,p (c,(e,v))=decide (inc e v)) (M : Finset E) :
    matchingCheck p ((c,Finset.univ),M)=decide (Transport.MatchingOn inc M Finset.univ) := by
  apply Bool.eq_iff_iff.mpr
  simp only [matchingCheck,decide_eq_true_eq,Finset.mem_univ,forall_const,hp]
  unfold Transport.MatchingOn
  simp only [Finset.mem_univ,implies_true,true_and]
  apply forall_congr'
  intro v
  rw [Finset.card_eq_one_iff_existsUnique]
  simp
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeSwitchValid
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]

omit [Codec E] [Codec V] [Codec C] in
lemma switchValid_eq [Fintype E] [Fintype V] (ends : E→Sym2 V)
    (p : C×(E×(V×V))→Bool) (c : C)
    (hp : ∀ e v w,p (c,(e,(v,w)))=decide (ends e=s(v,w))) (M : Finset E) (q : Quad V×Quad E) :
    switchValid p ((c,M),q)=true ↔ (quadFn q.1,quadFn q.2)∈Transport.Sparse.switchPatterns ends M := by
  have he (e : E) (v w : V) : ends e=s(v,w) ↔ ∀ x,x∈ends e ↔ x=v ∨ x=w := by
    constructor
    · intro h; simp [h]
    · intro h; apply Sym2.ext; intro x; simpa using h x
  simp only [switchValid,decide_eq_true_eq,Transport.Sparse.switchPatterns,
    Finset.mem_filter,Finset.mem_univ,true_and,hp,Finset.insert_subset_iff,
    Finset.singleton_subset_iff]
  change (_ ∧ (∀ i,ends (quadFn q.2 i)=s(quadFn q.1 i,quadFn q.1 (i+1))) ∧ _ ∧ _ ∧ _) ↔ _
  simp_rw [he]
  rfl
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeSwitchRaw
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder

omit [Codec E] [Codec V] [Codec C] in
lemma switchRaw_eq [Fintype E] [Fintype V] (ends : E→Sym2 V)
    (p : C×(E×(V×V))→Bool) (c : C)
    (hp : ∀ e v w,p (c,(e,(v,w)))=decide (ends e=s(v,w))) (M : Finset E) :
    switchRaw p ((c,(Finset.univ,Finset.univ)),M)=Transport.Sparse.switchRaw ends M := by
  ext B
  simp only [switchRaw,List.mem_toFinset,List.mem_map,switchList,List.mem_filter]
  constructor
  · rintro ⟨⟨v,e⟩,⟨_,hv⟩,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(quadFn v,quadFn e),(switchValid_eq ends p c hp M (v,e)).mp hv,?_⟩
    rfl
  · intro h
    obtain ⟨⟨v,e⟩,hpatt,rfl⟩:=Finset.mem_image.mp h
    refine ⟨(quadOfFn v,quadOfFn e),⟨?_,?_⟩,rfl⟩
    · rw [mem_listProduct,mem_quads,mem_quads]
      simp only [Finset.mem_sort,Finset.mem_univ,implies_true,and_self]
    · apply (switchValid_eq ends p c hp M (quadOfFn v,quadOfFn e)).mpr
      simpa only [quadFn_ofFn] using hpatt
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeCategoricalValues
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
lemma cumulativeFraction_val_ofFn {r : ℕ} (q : Fin r → Fraction) (hq : ∀ i,0<(q i).2) (n : ℕ) :
    val (cumulativeFraction (List.ofFn q,n))=FiniteChoice.cumulative (fun i=>val (q i)) n := by
  rw [cumulativeFraction,sum_val]
  · simp only [List.map_take,List.map_ofFn,Function.comp_apply,List.sum_take_ofFn,
      FiniteChoice.cumulative,Finset.sum_filter]
  · intro b hb
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hb)
    subst b
    exact hq i
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableChoice
open TreeTyped TreeFraction

lemma choose_values {r K : ℕ} (q : Fin r → Fraction) (hq : ∀ i,0<(q i).2)
    (hs : ∑ i,val (q i)=1) (hK : 0<K) (J : Fin K) :
    choose (List.ofFn q,(J.val,K))=(FiniteChoice.choose (fun i=>val (q i)) hs hK J).val := by
  let j := FiniteChoice.choose (fun i=>val (q i)) hs hK J
  have hpred (i : ℕ) : predicate ((List.ofFn q,(J.val,K)),i)=
      decide ((J.val:ℚ)/K<FiniteChoice.cumulative (fun i=>val (q i)) (i+1)) := by
    rw [predicate,less_val (J.val,K) (cumulativeFraction (List.ofFn q,i+1)) hK (sum_den _),cumulativeFraction_val_ofFn q hq]
    rfl
  unfold choose
  simp only [List.length_ofFn]
  apply le_antisymm
  · apply listMin_le
    simp only [List.mem_filter,List.mem_range,hpred,decide_eq_true_eq]
    exact ⟨j.isLt,FiniteChoice.choose_upper _ hs hK J⟩
  · apply le_listMin j.isLt.le
    intro i hi
    simp only [List.mem_filter,List.mem_range,hpred,decide_eq_true_eq] at hi
    exact FiniteChoice.choose_le _ hs hK J ⟨i,hi.1⟩ hi.2

lemma bitValue_ofFn (k : ℕ) (bits : Fin k → Bool) :
    StackAddition.value (List.ofFn bits)=(FiniteChoice.tapeIndex k bits).val := by
  have hv' (k : ℕ) (bits : Fin k → Bool) :
      StackAddition.value (List.ofFn bits)=∑ i, (if bits i then 1 else 0)*2^i.val := by
    induction k with
    | zero => simp [StackAddition.value]
    | succ k ih =>
      rw [List.ofFn_succ,StackAddition.value,ih,Fin.sum_univ_succ]
      simp only [Fin.val_zero,pow_zero,Nat.mul_one,Fin.val_succ,pow_succ]
      rw [Finset.mul_sum]
      rw [Bool.toNat,Bool.cond_eq_ite]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
  rw [FiniteChoice.tapeIndex_value,hv']

lemma chooseBits_values {r k : ℕ} (q : Fin r → Fraction) (hq : ∀ i,0<(q i).2)
    (hs : ∑ i,val (q i)=1) (bits : Fin k → Bool) :
    chooseBits (List.ofFn q,List.ofFn bits)=
      (FiniteChoice.chooseBits (fun i=>val (q i)) hs k bits).val := by
  rw [chooseBits,bitDenominator_eq,List.length_ofFn,bitValue_ofFn]
  exact choose_values q hq hs (by positivity) (FiniteChoice.tapeIndex k bits)
end MatchingFPRAS.ExecutableChoice

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeDPRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP

lemma privateFlag_perm {b c : Bag} (h : b.Perm c) (l : ℕ) :
    privateFlag (l,b)=privateFlag (l,c) := by simp only [privateFlag,h.length_eq,h.mem_iff]
lemma sharedFlag_perm {b c : Bag} (h : b.Perm c) (l : ℕ) :
    sharedFlag (l,b)=sharedFlag (l,c) := by simp only [sharedFlag,privateFlag_perm h,h.mem_iff]
lemma totalFlag_perm {b c : Bag} (h : b.Perm c) (l : ℕ) :
    totalFlag (l,b)=totalFlag (l,c) := by simp only [totalFlag,h.mem_iff]

lemma forall₂_filter {A B : Type} {R : A → B → Prop} {as : List A} {bs : List B}
    (h : List.Forall₂ R as bs) (p : A → Bool) (q : B → Bool)
    (he : ∀ a b,R a b → p a=q b) : List.Forall₂ R (as.filter p) (bs.filter q) := by
  induction h with
  | nil => exact .nil
  | @cons a b as bs hab hs ih =>
    simp only [List.filter_cons,he a b hab]
    cases q b <;> simp only [Bool.false_eq_true,↓reduceIte]
    · exact ih
    · exact .cons hab ih

lemma privateNumber_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (l : ℕ) :
    privateNumber a l=privateNumber b l :=
  (forall₂_filter h _ _ (fun _ _ hh=>privateFlag_perm hh l)).length_eq
lemma sharedNumber_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (l : ℕ) :
    sharedNumber a l=sharedNumber b l :=
  (forall₂_filter h _ _ (fun _ _ hh=>sharedFlag_perm hh l)).length_eq
lemma totalNumber_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (l : ℕ) :
    totalNumber a l=totalNumber b l :=
  (forall₂_filter h _ _ (fun _ _ hh=>totalFlag_perm hh l)).length_eq
lemma trim_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (l : ℕ) :
    List.Forall₂ List.Perm (trim a l) (trim b l) :=
  forall₂_filter h _ _ (fun _ _ hh=>congrArg Bool.not (totalFlag_perm hh l))

lemma orderedRep_perm {n m : ℕ} (bags : Fin n → Finset (Fin m)) :
    (orderedRep bags).Perm (activeRep bags Finset.univ) := by
  unfold orderedRep activeRep
  change (List.ofFn ((bagRep ∘ bags) ∘ id)).Perm _
  rw [← List.map_ofFn]
  apply List.Perm.map
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact List.nodup_ofFn.mpr Function.injective_id
  · exact Finset.nodup_toList _
  · ext i; simp

end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeUnitBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh
lemma gapEquiv_val {n : ℕ} (a : Fin (n+1)) (i : Fin n) :
    (gapEquiv a i).val=a.succAbove i := rfl
lemma removePair_last_val {n : ℕ} (b : Fin (n+2)) (hb : b≠Fin.last (n+1)) (i : Fin n) :
    (removePairEquiv (Fin.last (n+1)) b hb i).val.val=if i.val<b.val then i.val else i.val+1 := by
  let e := gapEquiv (Fin.last (n+1))
  let b' := e.symm ⟨b,hb⟩
  have hb' : b'.val=b.val := by
    have h := congrArg (fun x=>x.val.val) (e.apply_symm_apply ⟨b,hb⟩)
    simpa only [e,gapEquiv_val,Fin.succAbove_last,Fin.val_castSucc] using h
  change ((gapEquiv (Fin.last (n+1)) (gapEquiv b' i).val).val).val=_
  rw [gapEquiv_val,Fin.succAbove_last,Fin.val_castSucc,gapEquiv_val]
  by_cases hi : i.val<b.val
  · rw [ite_eq_left hi,Fin.succAbove_of_castSucc_lt _ _ (show i.castSucc < b' from by change i.val < b'.val; omega)]
    rfl
  · rw [ite_eq_right hi,Fin.succAbove_of_le_castSucc _ _ (show b' ≤ i.castSucc from by change b'.val ≤ i.val; omega)]
    rfl
end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP

lemma residual_ordered {n m : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (b : Fin (n+2)) (hb : b≠Fin.last (n+1)) :
    residual (orderedRep bags,b.val)=
      orderedRep (fun i=>bags (UnitRefresh.removePairEquiv (Fin.last (n+1)) b hb i).val) := by
  unfold residual orderedRep
  simp only [List.length_ofFn, Nat.add_sub_cancel]
  rw [map_range_ofFn]
  apply List.ofFn_inj.mpr
  funext i
  have hv := UnitRefresh.removePair_last_val b hb i
  have hl : skip (i.val,b.val)<n+2 := by simp only [skip]; split_ifs <;> omega
  simp only [List.getD,List.getElem?_ofFn,hl,↓reduceDIte,Option.getD_some]
  congr 2
  apply Fin.ext
  exact hv.symm

lemma valid_eq {n m : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (ps : Parents) (ls : List ℕ) (b : Fin (n+2)) (c : Fin m) :
    valid (((orderedRep bags,ps),ls),(b.val,c.val))=
      decide (UnitRefresh.Materialized.validBranch bags (Fin.last (n+1)) (b,c)) := by
  have ha : n+2-1=n+1 := by omega
  have hget (i : Fin (n+2)) : (orderedRep bags).getD i.val []=bagRep (bags i) := by
    simp only [orderedRep,List.getD,List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some]
  have hgeta : (orderedRep bags).getD (n+1) []=bagRep (bags (Fin.last (n+1))) := hget (Fin.last (n+1))
  apply Bool.eq_iff_iff.mpr
  simp only [valid,show (orderedRep bags).length=n+2 from List.length_ofFn,ha,
    hgeta,hget,Bool.and_eq_true,decide_eq_true_eq,mem_bagRep,
    UnitRefresh.Materialized.validBranch]
  constructor
  · rintro ⟨⟨hb,hc⟩,hd⟩
    apply decide_eq_true
    exact ⟨by intro he; exact hb (congrArg Fin.val he),hc,hd⟩
  · intro h
    have hh := of_decide_eq_true h
    exact ⟨⟨by intro he; exact hh.1 (Fin.ext he),hh.2.1⟩,hh.2.2⟩

end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeUnitDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP TreeFraction

lemma decodeIndex_fin {n m : ℕ} (i : Fin (n*m)) :
    decodeIndex (i.val,m)=((finProdFinEquiv.symm i).1.val,(finProdFinEquiv.symm i).2.val) := rfl

end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeUnitAssemble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh
lemma removePair_last_symm_val {n : ℕ} (b : Fin (n+2)) (hb : b≠Fin.last (n+1))
    (x : withoutPair (Fin.last (n+1)) b) :
    ((removePairEquiv (Fin.last (n+1)) b hb).symm x).val =
      if x.val.val<b.val then x.val.val else x.val.val-1 := by
  let e := removePairEquiv (Fin.last (n+1)) b hb
  let j := e.symm x
  have hj := removePair_last_val b hb j
  have hx : (e j).val.val=x.val.val := congrArg (fun x=>x.val.val) (e.apply_symm_apply x)
  change (e j).val.val=_ at hj
  rw [hx] at hj
  change j.val=_
  by_cases h : j.val<b.val <;> simp only [h,↓reduceIte] at hj
  · rw [ite_eq_left (by omega)]
    omega
  · rw [ite_eq_right (by omega)]
    omega
end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP

lemma resultRep_getD {n m : ℕ} {bags : Fin n → Finset (Fin m)}
    (p : UnitRefresh.ColoredPairing bags) (i : Fin n) :
    (resultRep p).getD i.val (0,0)=((p.pair.mate i).val,(p.color i).val) := by
  simp [resultRep,List.getD]

lemma assemble_eq {n m : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (c : UnitRefresh.Partner bags (Fin.last (n+1)))
    (p : UnitRefresh.ColoredPairing (fun i=>bags (UnitRefresh.removePairEquiv (Fin.last (n+1)) c.val.1 c.property.1 i).val)) :
    assemble ((n,(c.val.1.val,c.val.2.val)),resultRep p)=
      resultRep ((UnitRefresh.ColoredPairing.map (UnitRefresh.residualBags bags (Fin.last (n+1)) c.val.1)
        (UnitRefresh.removePairEquiv (Fin.last (n+1)) c.val.1 c.property.1) p).insert (Fin.last (n+1)) c) := by
  rw [assemble,map_range_ofFn]
  apply List.ofFn_inj.mpr
  funext i
  let e := UnitRefresh.removePairEquiv (Fin.last (n+1)) c.val.1 c.property.1
  change assembleAt (((n,(c.val.1.val,c.val.2.val)),resultRep p),i.val)=_
  by_cases ha : i=Fin.last (n+1)
  · subst i
    simp only [assembleAt,Fin.val_last,↓reduceIte,UnitRefresh.ColoredPairing.insert,
      UnitRefresh.Pairing.insert,↓reduceDIte,true_or]
  by_cases hb : i=c.val.1
  · subst i
    have han : c.val.1.val≠n+1 := by intro he; exact ha (Fin.ext he)
    simp only [assembleAt,han,↓reduceIte,UnitRefresh.ColoredPairing.insert,
      UnitRefresh.Pairing.insert,ha,↓reduceDIte,or_true,Fin.val_last]
  · let x : UnitRefresh.withoutPair (Fin.last (n+1)) c.val.1 := ⟨i,ha,hb⟩
    have hi : i.val≠n+1 := by intro he; exact ha (Fin.ext he)
    have hi' : i.val≠c.val.1.val := by intro he; exact hb (Fin.ext he)
    have hj : unskip (i.val,c.val.1.val)=(e.symm x).val :=
      (UnitRefresh.removePair_last_symm_val c.val.1 c.property.1 x).symm
    simp only [assembleAt,hi,hi',↓reduceIte,hj,resultRep_getD,
      UnitRefresh.ColoredPairing.insert,UnitRefresh.Pairing.insert,ha,hb,↓reduceDIte,or_self]
    change (skip ((p.pair.mate (e.symm x)).val,c.val.1.val),(p.color (e.symm x)).val)=
      ((e (p.pair.mate (e.symm x))).val.val,(p.color (e.symm x)).val)
    rw [UnitRefresh.removePair_last_val]
    rfl
end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeCappedAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP Polynomial

lemma resultRep_mem {n m : ℕ} {bags : Fin n → Finset (Fin m)}
    (p : UnitRefresh.ColoredPairing bags) {z : ℕ×ℕ} (hz : z∈resultRep p) : z.1 < n ∧ z.2 < m := by
  simp only [resultRep,List.mem_ofFn] at hz
  obtain ⟨i,rfl⟩:=hz
  exact ⟨(p.pair.mate i).isLt,(p.color i).isLt⟩

lemma clippedAssemble_eq {n m : ℕ} (ctx : Context) (hn : n+2 ≤ ctx.1.1.length) (hm : m ≤ ctx.1.2.length)
    (bags : Fin (n+2) → Finset (Fin m))
    (c : UnitRefresh.Partner bags (Fin.last (n+1)))
    (p : UnitRefresh.ColoredPairing (fun i=>bags (UnitRefresh.removePairEquiv (Fin.last (n+1)) c.val.1 c.property.1 i).val)) :
    clippedAssemble (ctx,((n,(c.val.1.val,c.val.2.val)),resultRep p))=
      resultRep ((UnitRefresh.ColoredPairing.map (UnitRefresh.residualBags bags (Fin.last (n+1)) c.val.1)
        (UnitRefresh.removePairEquiv (Fin.last (n+1)) c.val.1 c.property.1) p).insert (Fin.last (n+1)) c) := by
  let f : Frame := (n,(c.val.1.val,c.val.2.val))
  have he :=assemble_eq bags c p
  change assemble (f,resultRep p)=_ at he
  unfold clippedAssemble
  dsimp only
  rw [min_eq_left (show n+2 ≤ ctx.1.1.length+2 by omega)]
  trans assemble (f,resultRep p)
  · unfold assemble
    apply List.map_congr_left
    intro i hi
    have hz : assembleAt ((f,resultRep p),i)∈assemble (f,resultRep p) := List.mem_map.mpr ⟨i,hi,rfl⟩
    rw [he] at hz
    obtain ⟨h1,h2⟩:=resultRep_mem _ hz
    have hc1 :(assembleAt ((f,resultRep p),i)).1 ≤ capacity ctx := by unfold capacity; omega
    have hc2 :(assembleAt ((f,resultRep p),i)).2 ≤ capacity ctx := by unfold capacity; omega
    exact Prod.ext (min_eq_left hc1) (min_eq_left hc2)
  · exact he
end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeCertify
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder

variable [Fintype E] [Fintype V] (ends : E→Sym2 V)
attribute [local instance] Transport.Sparse.pmOrder

omit [Codec E] [Codec V] [Codec C] in
lemma certify_eq (p : C×(E×V)→Bool) (c : C)
    (hp : ∀ e v,p (c,(e,v))=decide (v∈ends e)) (s : Finset (Finset E)) :
    certify p ((c,Finset.univ),s)=(Transport.Sparse.certify ends s).map (pmEmbedding ends).toEmbedding := by
  ext a
  simp only [certify,Finset.mem_filter,matchingCheck_eq p c _ hp,decide_eq_true_eq,
    Finset.mem_map,pmEmbedding]
  constructor
  · rintro ⟨ha,hm⟩
    exact ⟨⟨a,hm⟩,by simpa using ha,rfl⟩
  · rintro ⟨b,hb,rfl⟩
    exact ⟨by simpa using hb,b.property⟩
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_DPEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh.Materialized
open Finset

variable {V : Type} [Fintype V] {m : ℕ}

lemma mergeEnvelope_pos (w : Fin m → ℕ) (hw : ∀ a,1≤w a) (l p : Fin m) (s : ℕ) :
    ∀ a,1 ≤ mergeEnvelope w l p s a := by
  intro a
  unfold mergeEnvelope
  split_ifs
  · exact le_rfl
  · have hl := hw l
    have hp := hw p
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  · exact hw a

lemma mergeEnvelope_prod (w : Fin m → ℕ) (l p : Fin m) (h : p≠l) (s : ℕ) :
    (∏ a,mergeEnvelope w l p s a)=2^s*∏ a,w a := by
  have hp : p∈(univ : Finset (Fin m)).erase l := by simp [h]
  rw [←mul_prod_erase univ (mergeEnvelope w l p s) (mem_univ l),
    ←mul_prod_erase (univ.erase l) (mergeEnvelope w l p s) hp,
    ←mul_prod_erase univ w (mem_univ l),←mul_prod_erase (univ.erase l) w hp]
  have he : (∏ a∈(univ.erase l).erase p,mergeEnvelope w l p s a)=
      ∏ a∈(univ.erase l).erase p,w a := by
    apply prod_congr rfl
    intro a ha
    have hal : a≠l := (mem_erase.mp (mem_erase.mp ha).2).1
    have hap : a≠p := (mem_erase.mp ha).1
    simp [mergeEnvelope,hal,hap]
  rw [he]
  simp only [mergeEnvelope,↓reduceIte,h]
  ring

omit [Fintype V] in
lemma update_rowBound (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l : Fin m) (B : ℕ) (t : Table) (w : Fin m → ℕ)
    (hw : ∀ a,1≤w a) (ht : RowBound t w) :
    RowBound (update bags R parent l B t)
      (match parent l with | none=>w | some p=>mergeEnvelope w l p (sharedCount bags R l)) := by
  intro a r
  rw [update,read_tabulate]
  split_ifs
  · have h := entry_rowBound bags R parent l t w hw ht a r
    cases hh : parent l <;> simpa only [hh] using h
  · exact Nat.zero_le _

lemma sharedCount_le_card (bags : V → Finset (Fin m)) (R : Finset V) (l : Fin m) :
    sharedCount bags R l≤Fintype.card V := by
  exact (card_le_card (filter_subset _ _)).trans (card_le_univ _)

lemma pairingCount_pow_bound (n : ℕ) : pairingCount n ≤ 2^(n*n) := by
  calc
    _ ≤ n^(n/2) := pairingCount_le_half_power n
    _ ≤ (2^n)^(n/2) := Nat.pow_le_pow_left (Nat.le_of_lt n.lt_two_pow_self) _
    _ = 2^(n*(n/2)) := (pow_mul _ _ _).symm
    _ ≤ 2^(n*n) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.div_le_self _ _))

lemma initial_rowBound (B : ℕ) : RowBound (initial m B) (fun _ : Fin m=>2^(B*B)) := by
  intro a r
  rw [initial,read_tabulate]
  split_ifs with h
  · exact (pairingCount_pow_bound r).trans
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul h h))
  · exact Nat.zero_le _

end MatchingFPRAS.UnitRefresh.Materialized

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_ClippedEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh.Materialized
open Finset

variable {V : Type} [Fintype V] {m : ℕ}
omit [Fintype V] in
lemma nextEnvelope_pos (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l : Fin m) (w : Fin m → ℕ) (hw : ∀ a,1≤w a) :
    ∀ a,1≤nextEnvelope bags R parent l w a := by
  cases hp : parent l with
  | none => simpa only [nextEnvelope,hp] using hw
  | some p => simpa only [nextEnvelope,hp] using mergeEnvelope_pos w hw l p (sharedCount bags R l)
lemma nextEnvelope_product (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l : Fin m) (w : Fin m → ℕ)
    (hp : ∀ p,parent l=some p → p≠l) :
    (∏ a,nextEnvelope bags R parent l w a)≤2^(Fintype.card V)*(∏ a,w a) := by
  cases he : parent l with
  | none =>
    simp only [nextEnvelope,he]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  | some p =>
    simp only [nextEnvelope,he]
    rw [mergeEnvelope_prod w l p (hp p he)]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (sharedCount_le_card bags R l))
lemma nextEnvelope_power (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l : Fin m) (w : Fin m → ℕ)
    (hp : ∀ p,parent l=some p → p≠l) (E : ℕ) (he : (∏ a,w a)≤2^E) :
    (∏ a,nextEnvelope bags R parent l w a)≤2^(E+Fintype.card V) := by
  apply (nextEnvelope_product bags R parent l w hp).trans
  rw [pow_add]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (2^(Fintype.card V)) he
lemma entry_size_budget (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l : Fin m) (t : Table) (w : Fin m → ℕ)
    (hw : ∀ a,1≤w a) (ht : RowBound t w)
    (hp : ∀ p,parent l=some p → p≠l) (E K : ℕ) (he : (∏ a,w a)≤2^E)
    (hK : E+Fintype.card V+1≤K) (a : Fin m) (r : ℕ) :
    (entry bags R parent l a t r).size≤K := by
  have hv:=nextEnvelope_pos bags R parent l w hw
  have hb : entry bags R parent l a t r≤nextEnvelope bags R parent l w a := by
    cases h : parent l <;> simpa only [nextEnvelope,h] using entry_rowBound bags R parent l t w hw ht a r
  have hprod:=nextEnvelope_power bags R parent l w hp E he
  have hval : entry bags R parent l a t r≤2^(E+Fintype.card V) :=
    hb.trans ((single_le_prod' (fun x _=>hv x) (mem_univ a)).trans hprod)
  exact ((Nat.size_le_size hval).trans_eq (Nat.size_pow)).trans hK
end MatchingFPRAS.UnitRefresh.Materialized

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeClippedCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped Finset

lemma cappedStep_fold (o : CountInput) (ls : List ℕ) (bs : Bags) (t : Table) :
    ls.foldl (fun z l=>cappedStep (l,z)) (o,(ls.length,(bs,t)))=(o,(0,runCapped o ls bs t)) := by
  induction ls generalizing bs t with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.foldl_cons,List.length_cons,cappedStep,Nat.add_sub_cancel]
    exact ih _ _
lemma cappedCount_run (o : CountInput) :
    cappedCount o=finish ((runCapped o o.2 o.1.1 (initial (nLabels o,BInitial o))).2,nLabels o) := by
  unfold cappedCount
  rw [cappedStep_fold]

variable {V : Type} [Fintype V] [DecidableEq V] {m : ℕ}
variable (bags : V → Finset (Fin m)) (parent : Fin m → Option (Fin m))
lemma rawEntry_source (R : Finset V) (l a : Fin m) (r : ℕ) (t : Table) (bs : Bags)
    (hbs : bs.Perm (activeRep bags R)) :
    rawEntry (((bs,parentRep parent),(l.val,t)),(a.val,r))=UnitRefresh.Materialized.entry bags R parent l a t r := by
  unfold rawEntry
  rw [context_perm hbs]
  unfold context
  rw [parentRep_getD]
  simp only [privateNumber_activeRep,sharedNumber_activeRep,totalNumber_activeRep]
  exact entry_eq bags R parent l a t r

lemma cappedUpdate_source (o : CountInput) (hps : o.1.2=parentRep parent)
    (hn : nVertices o=Fintype.card V) (R : Finset V) (l : Fin m) (B : ℕ)
    (hB : B≤nPlan o) (t : Table) (bs : Bags) (hbs : bs.Perm (activeRep bags R))
    (hsize : ∀ (a : Fin m) r,(UnitRefresh.Materialized.entry bags R parent l a t r).size ≤ capBits o) :
    cappedUpdate ((o,((bs,o.1.2),(l.val,t))),B)=UnitRefresh.Materialized.update bags R parent l (Fintype.card V*B) t := by
  have hm : nLabels o=m := by simp only [nLabels,hps,parentRep_length]
  unfold cappedUpdate updateRows updateColumns
  dsimp only
  rw [hm,hn,Nat.min_eq_left hB]
  rw [tabulate_materialized]
  unfold UnitRefresh.Materialized.update
  congr 1
  funext a r
  unfold cappedEntry
  dsimp only
  rw [hps,rawEntry_source bags parent R l a r t bs hbs]
  exact clip_eq _ _ (hsize a r)

lemma runCapped_source (o : CountInput) (hps : o.1.2=parentRep parent)
    (hn : nVertices o=Fintype.card V)
    (hp : ∀ l p,parent l=some p → p≠l) (ls : List (Fin m)) (R : Finset V)
    (t : Table) (bs : Bags) (hbs : bs.Perm (activeRep bags R))
    (w : Fin m → ℕ) (hw : ∀ a,1≤w a) (ht : UnitRefresh.Materialized.RowBound t w)
    (E : ℕ) (he : (∏ a,w a)≤2^E)
    (hL : ls.length≤nPlan o) (hK : Fintype.card V*ls.length+E+1 ≤ capBits o) :
    (runCapped o (ls.map Fin.val) bs t).2=UnitRefresh.Materialized.run bags parent ls R t := by
  induction ls generalizing R bs t w E with
  | nil => rfl
  | cons l ls ih =>
    have hlen : ls.length≤nPlan o := by rw [List.length_cons] at hL; omega
    have hstepK : E+Fintype.card V+1 ≤ capBits o := by
      rw [List.length_cons,Nat.mul_add,Nat.mul_one] at hK
      omega
    have hsize := UnitRefresh.Materialized.entry_size_budget bags R parent l t w hw ht (hp l) E (capBits o) he hstepK
    have hup:=cappedUpdate_source bags parent o hps hn R l ls.length hlen t bs hbs hsize
    simp only [List.map_cons,runCapped,List.length_map,UnitRefresh.Materialized.run]
    rw [hup]
    let v:=UnitRefresh.Materialized.nextEnvelope bags R parent l w
    have hv : ∀ a,1≤v a := UnitRefresh.Materialized.nextEnvelope_pos bags R parent l w hw
    have hvt : UnitRefresh.Materialized.RowBound (UnitRefresh.Materialized.update bags R parent l (Fintype.card V*ls.length) t) v :=
      UnitRefresh.Materialized.update_rowBound bags R parent l _ t w hw ht
    have hvp : (∏ a,v a)≤2^(E+Fintype.card V) := UnitRefresh.Materialized.nextEnvelope_power bags R parent l w (hp l) E he
    apply ih (UnitRefresh.trim bags R l) _ (trim bs l) ((hbs.filter _).trans (trim_activeRep bags R l)) v hv hvt
      (E+Fintype.card V) hvp hlen
    rw [List.length_cons,Nat.mul_add,Nat.mul_one] at hK
    omega

lemma cappedCount_rep (ls : List (Fin m)) (bs : Bags) (hbs : bs.Perm (activeRep bags univ))
    (hp : ∀ l p,parent l=some p → p≠l) :
    cappedCount ((bs,parentRep parent),ls.map Fin.val)=UnitRefresh.Materialized.count bags parent ls := by
  let o : CountInput := ((bs,parentRep parent),ls.map Fin.val)
  have hn : nVertices o=Fintype.card V := by
    dsimp only [o,nVertices]
    rw [hbs.length_eq]
    simp [activeRep]
  have hm : nLabels o=m := by simp [o,nLabels]
  have hL : nPlan o=ls.length := by simp [o,nPlan]
  rw [cappedCount_run]
  change finish ((runCapped o (ls.map Fin.val) (bs) (initial (nLabels o,BInitial o))).2,nLabels o)=_
  rw [hm,initial_eq]
  let B:=BInitial o
  let E:=B*B*m
  have hw : ∀ a : Fin m,1≤2^(B*B) := fun _=>Nat.one_le_iff_ne_zero.mpr (by positivity)
  have he : (∏ a : Fin m,2^(B*B))≤2^E := by
    simp only [prod_const,card_univ,Fintype.card_fin,←pow_mul,E]
    exact le_rfl
  have hK : Fintype.card V*ls.length+E+1 ≤ capBits o := by
    unfold capBits
    rw [hn,hL]
    dsimp only [E,B]
    rw [hm,pow_two]
  rw [runCapped_source bags parent o rfl hn hp ls univ (UnitRefresh.Materialized.initial m B) (bs)
    hbs (fun _=>2^(B*B)) hw (UnitRefresh.Materialized.initial_rowBound B) E he (by rw [hL]) hK]
  rw [finish_eq]
  unfold UnitRefresh.Materialized.count
  rw [show B=Fintype.card V*m by dsimp only [B,BInitial]; rw [hn,hm]]

omit [Fintype V] [DecidableEq V] in
lemma cappedCount_ordered {n : ℕ} (bags : Fin n → Finset (Fin m)) (ls : List (Fin m))
    (hp : ∀ l p,parent l=some p → p≠l) :
    cappedCount ((orderedRep bags,parentRep parent),ls.map Fin.val)=UnitRefresh.Materialized.count bags parent ls :=
  cappedCount_rep bags parent ls _ (orderedRep_perm bags) hp

end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeLabelCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh
lemma ofFn_orderedEnum (A : Type) [Fintype A] [LinearOrder A] :
    List.ofFn (orderedEnum A)=(Finset.univ : Finset A).sort (· ≤ ·) := by
  apply List.ext_getElem
  · simp
  · intro i _ _
    simp only [List.getElem_ofFn]
    rfl
end MatchingFPRAS.UnitRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

attribute [local instance] Transport.prodOrder Transport.sumOrder

attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instLTProdOfLinearOrder_solutions
lemma pairwise_product {A B : Type} [LinearOrder A] [LinearOrder B]
    {as : List A} {bs : List B} (ha : as.Pairwise (· < ·)) (hb : bs.Pairwise (· < ·)) :
    (as.product bs).Pairwise (· < ·) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a _
    apply List.pairwise_map.mpr
    exact hb.imp (fun h=>Prod.Lex.right _ h)
  · apply ha.imp
    intro a b hab x hx y hy
    obtain ⟨u,hu,rfl⟩:=List.mem_map.mp hx
    obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hy
    exact Prod.Lex.left _ _ hab

lemma logicalEdges_pairwise (n : ℕ) :
    (logicalEdges (List.range n)).Pairwise (· < ·) :=
  List.Pairwise.filter _ (pairwise_product (List.pairwise_lt_range) (List.pairwise_lt_range))
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeNumberedSets
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {A : Type} [Fintype A] [LinearOrder A]
lemma sort_set (s : Finset A) : (set s).sort (·≤·)=(s.sort (·≤·)).map index := by
  symm
  exact Finset.map_sort embedding s (·≤·) (·≤·) (fun a _ b _=>(index_le a b).symm)
lemma encode_set (s : Finset A) : encode (set s)=encode s := by
  rw [encode_finset,sort_set,encode_finset]
  change TreeData.ofList (((s.sort (·≤·)).map index).map encode)=
    TreeData.ofList ((s.sort (·≤·)).map (fun a=>encode (index a)))
  simp only [List.map_map, Function.comp_def]
end MatchingFPRAS.TreeTyped.Numbered

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeGuideTables
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder

lemma slotUniverse_source (n : ℕ) (ft fq : List Bool) (ws : List Fraction) :
    slotUniverse ((n,ft),(fq,ws))=Numbered.set (Finset.univ : Finset (Slot ft.length fq.length)) := by
  ext j
  simp only [slotUniverse,slots,slotCount,List.toFinset_range,Finset.mem_range,Numbered.set,Finset.mem_map,
    Finset.mem_univ,true_and,Numbered.embedding]
  constructor
  · intro h
    let z : Fin (Fintype.card (Slot ft.length fq.length)) := ⟨j,by simpa only [slot_card] using h⟩
    exact ⟨UnitRefresh.orderedEnum _ z,index_enum z⟩
  · rintro ⟨z,rfl⟩
    change index z<(ft.length+1)*fq.length
    have h := ((UnitRefresh.orderedEnum (Slot ft.length fq.length)).symm z).isLt
    simpa only [index,slot_card] using h

lemma mem_guides_rank {T q : ℕ} (i j : Slot T q) :
    j∈guides i ↔ rank i<T ∧ rank j=rank i+1 := by
  unfold guides
  split_ifs with h
  · simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨h,rfl⟩
    · rintro ⟨_,he⟩
      refine ⟨(ofLex j).2,?_⟩
      apply ofLex.injective
      apply Prod.ext
      · exact Fin.ext he.symm
      · rfl
  · simp [h]

lemma guideSet_source (n : ℕ) (ft fq : List Bool) (ws : List Fraction) (i : Slot ft.length fq.length) :
    guideSet (((n,ft),(fq,ws)),index i)=Numbered.set (guides i) := by
  rw [guideSet,slotUniverse_source]
  ext j
  simp only [Finset.mem_filter,Numbered.set,Finset.mem_map,Finset.mem_univ,true_and,Numbered.embedding]
  constructor
  · rintro ⟨⟨z,rfl⟩,h⟩
    refine ⟨z,?_,rfl⟩
    rw [mem_guides_rank]
    simpa [guideTest,slot_index_div] using h
  · rintro ⟨z,h,rfl⟩
    refine ⟨⟨z,rfl⟩,?_⟩
    simpa [guideTest,slot_index_div] using (mem_guides_rank i z).mp h

lemma guideRows_source (n : ℕ) (ft fq : List Bool) (ws : List Fraction) :
    guideRows ((n,ft),(fq,ws))=List.ofFn
      (fun i : Fin (Fintype.card (Slot ft.length fq.length))=>
        (Numbered.set (guides (UnitRefresh.orderedEnum _ i))).sort (·≤·)) := by
  rw [guideRows,slots,slotCount,range_slot_indices,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact congrArg (fun values=>values.sort (·≤·))
    (guideSet_source n ft fq ws (UnitRefresh.orderedEnum _ i))

end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeProgramUnique
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RegisterProc
open Turing MachineCost

variable {K : Type} [DecidableEq K]
lemma Exec.unique {P : Proc K} {S T U : Stack K} {m n : ℕ}
    (h : Exec P S T m) (g : Exec P S U n) : T=U := by
  obtain ⟨i,hi,he⟩:=h
  obtain ⟨j,hj,hf⟩:=g
  have h₁ : MachineCost.run (TM2.step P.code) (i+j) ⟨some default,none,S⟩=⟨none,none,T⟩ := by
    rw [run_add,he,StackComposition.run_halted]
  have h₂ : MachineCost.run (TM2.step P.code) (i+j) ⟨some default,none,S⟩=⟨none,none,U⟩ := by
    rw [Nat.add_comm,run_add,hf,StackComposition.run_halted]
  exact congrArg TM2.Cfg.stk (h₁.symm.trans h₂)
end MatchingFPRAS.RegisterProc

namespace MatchingFPRAS.TreePost
open TreeTyped TreeData TreeFunction TreeMachine RegisterProc

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]
lemma stacks_eq_of_encode {a : A} {b : B} (h : TreeTyped.encode a=TreeTyped.encode b) :
    inputStacks a=inputStacks b := by simp only [inputStacks,h]
end MatchingFPRAS.TreePost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeFastUnitCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP TreeFraction

lemma fastBranch_eq {n m : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p < rank l) (b : Fin (n+2)) (hne' : b≠Fin.last (n+1)) :
    fastBranch (((orderedRep bags,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val),b.val)=
      UnitRefresh.Materialized.branchCount bags rank parent (Fin.last (n+1)) b := by
  rw [fastBranch,residual_ordered bags b hne',cappedCount_ordered (parent:=parent) _ _ (by
    intro l p hh; have :=hp l p hh; intro e; subst p; omega)]
  let e := UnitRefresh.removePairEquiv (Fin.last (n+1)) b hne'
  have hbe : UnitRefresh.RankedBags (fun i=>bags (e i).val) rank parent := fun v l hl r hr=>hb (e v).val l hl r hr
  rw [UnitRefresh.Materialized.computable_count_eq _ rank parent hbe (fun i=>hne (e i).val) hp]
  rw [Fintype.card_congr (UnitRefresh.ColoredPairing.equiv (UnitRefresh.residualBags bags (Fin.last (n+1)) b) e)]
  exact (UnitRefresh.Materialized.branchCount_eq bags rank parent hb hne hp _ _).symm

lemma fastEdgeCount_eq {n m : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p < rank l) (b : Fin (n+2)) (c : Fin m) :
    fastEdgeCount (((orderedRep bags,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val),(b.val,c.val))=
      UnitRefresh.Materialized.edgeCount bags rank parent (Fin.last (n+1)) (b,c) := by
  rw [fastEdgeCount,valid_eq]
  simp only [decide_eq_true_eq,UnitRefresh.Materialized.edgeCount]
  split_ifs with h
  · exact fastBranch_eq bags rank parent hb hne hp b h.1
  · rfl
lemma fastProbabilities_eq {n m : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p < rank l) :
    fastProbabilities ((orderedRep bags,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val)=
      List.ofFn (fun i : Fin ((n+2)*m)=>
        (UnitRefresh.Materialized.edgeCount bags rank parent (Fin.last (n+1)) (finProdFinEquiv.symm i),
         UnitRefresh.Materialized.count bags parent (UnitRefresh.Materialized.plan rank))) := by
  unfold fastProbabilities
  simp only [orderedRep,List.length_ofFn,parentRep_length]
  rw [map_range_ofFn]
  apply List.ofFn_inj.mpr
  funext i
  change fastProbability (((orderedRep bags,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val),i.val)=_
  rw [fastProbability,parentRep_length,decodeIndex_fin,fastEdgeCount_eq bags rank parent hb hne hp,cappedCount_ordered (parent:=parent) _ _ (by
    intro l p hh; have :=hp l p hh; intro e; subst p; omega)]

lemma fastDraw_eq {n m k : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p < rank l)
    (hz : 0<UnitRefresh.Materialized.count bags parent (UnitRefresh.Materialized.plan rank))
    (bits : Fin k → Bool) :
    fastDraw (((orderedRep bags,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val),List.ofFn bits)=
      ((UnitRefresh.Materialized.drawEdge bags rank parent hb hne hp (Fin.last (n+1)) hz k bits).val.val.1.val,
       (UnitRefresh.Materialized.drawEdge bags rank parent hb hne hp (Fin.last (n+1)) hz k bits).val.val.2.val) := by
  let q : Fin ((n+2)*m) → Fraction := fun i=>
    (UnitRefresh.Materialized.edgeCount bags rank parent (Fin.last (n+1)) (finProdFinEquiv.symm i),
     UnitRefresh.Materialized.count bags parent (UnitRefresh.Materialized.plan rank))
  have hq : ∀ i,0<(q i).2 := fun _=>hz
  have hs : ∑ i,val (q i)=1 :=
    UnitRefresh.Materialized.edgeProbability_sum bags rank parent hb hne hp _ hz
  rw [fastDraw,fastProbabilities_eq bags rank parent hb hne hp]
  change decodeIndex (ExecutableChoice.chooseBits (List.ofFn q,List.ofFn bits), (parentRep parent).length)=_
  rw [ExecutableChoice.chooseBits_values q hq hs,parentRep_length,decodeIndex_fin]
  rfl

end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeFastSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP

lemma fastSelected_eq_of_getD {n m k : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p < rank l)
    (hz : 0<UnitRefresh.Materialized.count bags parent (UnitRefresh.Materialized.plan rank))
    (bits : Fin (n+2) → Fin k → Bool) (bs : Bits)
    (hbs : bs.getD (n+1) []=List.ofFn (bits (Fin.last (n+1)))) :
    fastSelected (((orderedRep bags,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val),bs)=
      ((UnitRefresh.Materialized.drawEdge bags rank parent hb hne hp (Fin.last (n+1)) hz k (bits (Fin.last (n+1)))).val.val.1.val,
       (UnitRefresh.Materialized.drawEdge bags rank parent hb hne hp (Fin.last (n+1)) hz k (bits (Fin.last (n+1)))).val.val.2.val) := by
  have hl : (orderedRep bags).length-1=n+1 := by simp only [orderedRep,List.length_ofFn]; omega
  unfold fastSelected
  rw [hl,hbs]
  exact fastDraw_eq bags rank parent hb hne hp hz _

open UnitRefresh.Materialized

lemma fastRawSample_eq (cap : Context) (n : ℕ) {m k : ℕ}
    (hcapn : n ≤ cap.1.1.length) (hcapm : m ≤ cap.1.2.length) (bags : Fin n → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p < rank l)
    (hz : 0<UnitRefresh.Materialized.count bags parent (plan rank))
    (bits : Fin n → Fin k → Bool) (bs : Bits)
    (hbs : ∀ i : Fin n,bs.getD i.val []=List.ofFn (bits i))
    (fuel : ℕ) (hfuel : n≤fuel) :
    fastRawSample cap fuel ((orderedRep bags,parentRep parent),(plan rank).map Fin.val) bs=
      resultRep (sampleUnit k n bags rank parent hb hne hp hz bits) := by
  induction n using Nat.strong_induction_on generalizing fuel with
  | h n ih =>
    cases n with
    | zero =>
      cases fuel <;> simp [fastRawSample,orderedRep,resultRep]
    | succ n =>
      cases n with
      | zero =>
        have hzero := singleton_count_zero bags rank parent hb hne hp
        omega
      | succ n =>
        let a : Fin (n+2) := Fin.last (n+1)
        let c := drawEdge bags rank parent hb hne hp a hz k (bits a)
        let bags' := remainingBags bags a c.val
        have hb' := remainingRanked bags rank parent hb a c.val
        have hne' := remainingNonempty bags hne a c.val
        have hz' := remainingPositive bags rank parent hb hne hp a c
        let bits' : Fin n → Fin k → Bool := fun i=>bits i.castSucc.castSucc
        have hbits' : ∀ i : Fin n,bs.getD i.val []=List.ofFn (bits' i) :=
          fun i=>hbs i.castSucc.castSucc
        have hc := fastSelected_eq_of_getD bags rank parent hb hne hp hz bits bs (hbs a)
        change fastSelected (((orderedRep bags,parentRep parent),(plan rank).map Fin.val),bs)=
          (c.val.val.1.val,c.val.val.2.val) at hc
        have hnext : nextContext (((orderedRep bags,parentRep parent),(plan rank).map Fin.val),
            (c.val.val.1.val,c.val.val.2.val))=
            ((orderedRep bags',parentRep parent),(plan rank).map Fin.val) := by
          unfold nextContext
          rw [residual_ordered bags c.val.val.1 c.val.property.1]
          rfl
        cases fuel with
        | zero => omega
        | succ fuel =>
          have hr := ih n (by omega) (by omega) bags' hb' hne' hz' bits' hbits' fuel (by omega)
          have hl : (orderedRep bags).length=n+2 := List.length_ofFn
          rw [fastRawSample]
          simp only [hl,show 2≤n+2 by omega,↓reduceIte,hc,hnext,Nat.add_sub_cancel]
          rw [hr]
          rw [sampleUnit_step]
          exact clippedAssemble_eq cap hcapn hcapm bags c.val _

lemma fastSample_eq {n m k : ℕ} (bags : Fin n → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p < rank l)
    (hz : 0<UnitRefresh.Materialized.count bags parent (plan rank))
    (bits : Fin n → Fin k → Bool) :
    fastSample (((orderedRep bags,parentRep parent),(plan rank).map Fin.val),List.ofFn (fun i=>List.ofFn (bits i)))=
      resultRep (sampleUnit k n bags rank parent hb hne hp hz bits) := by
  unfold fastSample
  apply fastRawSample_eq _ n (by simp [orderedRep]) (by simp [parentRep_length]) bags rank parent hb hne hp hz bits
  · intro i
    simp only [List.getD,List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some]
  · simp only [orderedRep,List.length_ofFn,le_refl]
end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeSamplerRows
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
lemma context_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (l : ℕ) (t : Table) :
    context ((a,ps),(l,t))=context ((b,ps),(l,t)) := by
  simp only [context,privateNumber_rows h,sharedNumber_rows h,totalNumber_rows h]
lemma cappedUpdate_rows {a b as bs : Bags} (h : List.Forall₂ List.Perm a b)
    (ho : List.Forall₂ List.Perm as bs) (ps : Parents) (ls : List ℕ) (l r : ℕ) (t : Table) :
    cappedUpdate ((((as,ps),ls),((a,ps),(l,t))),r)=
      cappedUpdate ((((bs,ps),ls),((b,ps),(l,t))),r) := by
  simp only [cappedUpdate,tabulate,cappedEntry,capBits,BInitial,nVertices,nLabels,nPlan,
    updateRows,updateColumns,rawEntry,context_rows h,ho.length_eq]
lemma runCapped_rows {a b as bs : Bags} (h : List.Forall₂ List.Perm a b)
    (ho : List.Forall₂ List.Perm as bs) (ps : Parents) (ls ks : List ℕ) (t : Table) :
    (runCapped ((as,ps),ls) ks a t).2=(runCapped ((bs,ps),ls) ks b t).2 := by
  induction ks generalizing a b t with
  | nil=>rfl
  | cons k ks ih=>
    simp only [runCapped,cappedUpdate_rows h ho]
    exact ih (trim_rows h k) _
lemma cappedCount_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (ls : List ℕ) :
    cappedCount ((a,ps),ls)=cappedCount ((b,ps),ls) := by
  rw [cappedCount_run,cappedCount_run]
  simp only [nLabels,BInitial,nVertices,h.length_eq,runCapped_rows h h]
lemma rows_getD {a b : Bags} (h : List.Forall₂ List.Perm a b) (i : ℕ) :
    (a.getD i []).Perm (b.getD i []) := by
  induction h generalizing i with
  | nil=>exact List.Perm.refl []
  | @cons a b as bs hab _hs ih=>
    cases i with
    | zero=>exact hab
    | succ i=>exact ih i
end MatchingFPRAS.ExecutableDP

namespace MatchingFPRAS.ExecutableUnit
open ExecutableDP

lemma residual_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (v : ℕ) :
    List.Forall₂ List.Perm (residual (a,v)) (residual (b,v)) := by
  unfold residual
  rw [h.length_eq]
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_map_left_iff.mpr
  generalize List.range (b.length-2)=is
  induction is with
  | nil=>exact .nil
  | cons i is ih=>exact .cons (rows_getD h _) ih
lemma valid_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (ls : List ℕ) (e : ℕ×ℕ) :
    valid (((a,ps),ls),e)=valid (((b,ps),ls),e) := by
  simp only [valid,h.length_eq,(rows_getD h _).mem_iff]
lemma fastBranch_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (ls : List ℕ) (v : ℕ) :
    fastBranch (((a,ps),ls),v)=fastBranch (((b,ps),ls),v) :=
  cappedCount_rows (residual_rows h v) ps ls
lemma fastEdgeCount_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (ls : List ℕ) (e : ℕ×ℕ) :
    fastEdgeCount (((a,ps),ls),e)=fastEdgeCount (((b,ps),ls),e) := by
  simp only [fastEdgeCount,valid_rows h,fastBranch_rows h]
lemma fastProbabilities_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (ls : List ℕ) :
    fastProbabilities ((a,ps),ls)=fastProbabilities ((b,ps),ls) := by
  simp only [fastProbabilities,fastProbability,h.length_eq,fastEdgeCount_rows h,cappedCount_rows h]
lemma fastDraw_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (ls : List ℕ) (bits : List Bool) :
    fastDraw (((a,ps),ls),bits)=fastDraw (((b,ps),ls),bits) := by
  simp only [fastDraw,fastProbabilities_rows h]
lemma fastSelected_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (ls : List ℕ) (bits : Bits) :
    fastSelected (((a,ps),ls),bits)=fastSelected (((b,ps),ls),bits) := by
  simp only [fastSelected,h.length_eq,fastDraw_rows h]
lemma clippedAssemble_cap {as bs : Bags} (h : as.length=bs.length) (ps : Parents) (ls : List ℕ) (x : Frame×Result) :
    clippedAssemble (((as,ps),ls),x)=clippedAssemble (((bs,ps),ls),x) := by
  simp only [clippedAssemble,clippedAt,capacity,h]
lemma fastRawSample_rows {as bs : Bags} (ho : List.Forall₂ List.Perm as bs)
    (ps : Parents) (ls : List ℕ) (f : ℕ) {a b : Bags} (h : List.Forall₂ List.Perm a b) (bits : Bits) :
    fastRawSample ((as,ps),ls) f ((a,ps),ls) bits=fastRawSample ((bs,ps),ls) f ((b,ps),ls) bits := by
  induction f generalizing a b with
  | zero=>rfl
  | succ f ih=>
    simp only [fastRawSample,h.length_eq,fastSelected_rows h,nextContext]
    split_ifs
    · rw [ih (residual_rows h _),clippedAssemble_cap ho.length_eq]
    · rfl
lemma fastSample_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (ls : List ℕ) (bits : Bits) :
    fastSample (((a,ps),ls),bits)=fastSample (((b,ps),ls),bits) := by
  simp only [fastSample,h.length_eq,fastRawSample_rows h ps ls _ h]
lemma fastSample_represented {n m k : ℕ} (bags : Fin n → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p < rank l)
    (hz : 0<UnitRefresh.Materialized.count bags parent (UnitRefresh.Materialized.plan rank))
    (a : Bags) (h : List.Forall₂ List.Perm a (orderedRep bags)) (bits : Fin n → Fin k → Bool) :
    fastSample (((a,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val),List.ofFn (fun i=>List.ofFn (bits i)))=
      resultRep (UnitRefresh.Materialized.sampleUnit k n bags rank parent hb hne hp hz bits) := by
  rw [fastSample_rows h,fastSample_eq bags rank parent hb hne hp hz bits]
end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshIndexed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableUnit Polynomial

lemma ordered_eq (a b : ℕ) : ordered (a,b)=(min a b,max a b) := by
  by_cases h : a<b
  · simp [ordered,h,min_eq_left h.le,max_eq_right h.le]
  · simp [ordered,h,min_eq_right (le_of_not_gt h),max_eq_left (le_of_not_gt h)]

section Source
open Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
variable {n m : ℕ} {bags : Fin n→Finset (Fin m)}
lemma key_injective : Function.Injective (key (bags:=bags)) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Sym2.sortEquiv.injective
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext (congrArg (fun z=>z.1.1) h)
    · exact Fin.ext (congrArg (fun z=>z.1.2) h)
  · exact Fin.ext (congrArg Prod.snd h)
lemma rowKey_result (p : ColoredPairing bags) (i : Fin n) :
    rowKey (resultRep p,i.val)=key (p.edgeAt i) := by
  unfold rowKey
  rw [resultRep_getD,ordered_eq]
  rfl
end Source

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped ExecutableDP ExecutableSource Polynomial

open Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype Transport.prodOrder
variable {n m : ℕ} {bags : Fin n→Finset (Fin m)} {a : Bags}
local instance (priority := 2000) instLEProdOfLinearOrder_solutions_r2723a7_1 {A B : Type} [LinearOrder A] [LinearOrder B] : LE (A×B) := Transport.prodOrder.toLE
attribute [local instance] OAI.MatchingFPRAS.ExecutableRefresh.instLTProdOfLinearOrder_solutions
attribute [local instance] OAI.MatchingFPRAS.ExecutableRefresh.instPreorderProdOfLinearOrder_solutions
attribute [local instance] OAI.MatchingFPRAS.ExecutableRefresh.instLTSym2OfLinearOrder_solutions
lemma key_le (e f : BagEdge bags) : @LE.le Key Transport.prodOrder.toLE (key e) (key f) ↔ @LE.le _ Transport.bagEdgeOrder.toLE e f := by
  change toLex (key e) ≤ toLex (key f) ↔ toLex e.val.val ≤ toLex f.val.val
  simp only [Prod.Lex.le_iff,key,ofLex_toLex,Fin.le_def]
  have hlt : (e.val.val.1.inf.val,e.val.val.1.sup.val)<(f.val.val.1.inf.val,f.val.val.1.sup.val) ↔ e.val.val.1<f.val.val.1 := by
    change toLex (e.val.val.1.inf.val,e.val.val.1.sup.val)<toLex (f.val.val.1.inf.val,f.val.val.1.sup.val) ↔
      toLex (Sym2.sortEquiv e.val.val.1).val<toLex (Sym2.sortEquiv f.val.val.1).val
    simp only [Prod.Lex.lt_iff,ofLex_toLex,Fin.lt_def,Fin.val_inj,Sym2.sortEquiv]
    rfl
  have heq : (e.val.val.1.inf.val,e.val.val.1.sup.val)=(f.val.val.1.inf.val,f.val.val.1.sup.val) ↔ e.val.val.1=f.val.val.1 := by
    constructor
    · intro h
      apply Sym2.sortEquiv.injective
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h
    · intro h; rw [h]
  rw [hlt,heq]
lemma row_mem (ha : List.Forall₂ List.Perm a (orderedRep bags)) (i : Fin n) (j : ℕ) :
    j∈a.getD i.val [] ↔ ∃ c∈bags i,c.val=j := by
  rw [(rows_getD ha i.val).mem_iff]
  simp only [orderedRep,List.getD,List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some,bagRep,List.mem_map,Finset.mem_toList]
lemma storedCatalog_mem (ha : List.Forall₂ List.Perm a (orderedRep bags)) (e : Key) :
    e∈storedCatalog (a,List.range m) ↔ ∃ b : BagEdge bags,key b=e := by
  have hn : a.length=n := by simpa only [orderedRep,List.length_ofFn] using ha.length_eq
  constructor
  · intro he
    obtain ⟨he,hs⟩:=List.mem_filter.mp he
    obtain ⟨he,hc⟩:=List.mem_product.mp he
    obtain ⟨he,huv⟩:=List.mem_filter.mp he
    obtain ⟨hu,hv⟩:=List.mem_product.mp he
    have hu : e.1.1<n := by simpa only [List.mem_range,hn] using hu
    have hv : e.1.2<n := by simpa only [List.mem_range,hn] using hv
    have hc : e.2 < m := List.mem_range.mp hc
    have huv : e.1.1<e.1.2 := of_decide_eq_true huv
    have hs : e.2∈a.getD e.1.1 [] ∧ e.2∈a.getD e.1.2 [] := of_decide_eq_true hs
    have hcu': (⟨e.2,hc⟩ : Fin m)∈bags ⟨e.1.1,hu⟩ := by
      obtain ⟨l,hl,he⟩:=(row_mem ha ⟨e.1.1,hu⟩ e.2).mp hs.1
      have he' : l=(⟨e.2,hc⟩ : Fin m) := Fin.ext he
      simpa only [he'] using hl
    have hcv': (⟨e.2,hc⟩ : Fin m)∈bags ⟨e.1.2,hv⟩ := by
      obtain ⟨l,hl,he⟩:=(row_mem ha ⟨e.1.2,hv⟩ e.2).mp hs.2
      have he' : l=(⟨e.2,hc⟩ : Fin m) := Fin.ext he
      simpa only [he'] using hl
    have huv' : (⟨e.1.1,hu⟩ : Fin n)<⟨e.1.2,hv⟩ := huv
    let b : BagEdge bags:=⟨⟨(s((⟨e.1.1,hu⟩ : Fin n),⟨e.1.2,hv⟩),(⟨e.2,hc⟩ : Fin m)),by
      simp only [Sym2.mk_isDiag_iff]; exact ne_of_lt huv'⟩,by
      intro i hi
      rcases Sym2.mem_iff.mp hi with rfl|rfl
      · exact hcu'
      · exact hcv'⟩
    refine ⟨b,?_⟩
    simp only [key,b,Sym2.inf_mk,Sym2.sup_mk,inf_eq_left.mpr huv'.le,sup_eq_right.mpr huv'.le]
  · rintro ⟨b,rfl⟩
    have hlt : b.val.val.1.inf<b.val.val.1.sup := lt_of_le_of_ne b.val.val.1.inf_le_sup (by
      intro h
      apply b.val.property
      rw [←sym_mk_inf_sup b.val.val.1,h]
      exact Sym2.mk_isDiag_iff.mpr rfl)
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_product.mpr
      constructor
      · apply List.mem_filter.mpr
        constructor
        · exact List.mem_product.mpr ⟨List.mem_range.mpr (by simpa only [hn] using b.val.val.1.inf.isLt),
            List.mem_range.mpr (by simpa only [hn] using b.val.val.1.sup.isLt)⟩
        · exact decide_eq_true hlt
      · exact List.mem_range.mpr b.val.val.2.isLt
    · apply decide_eq_true
      constructor
      · exact (row_mem ha _ _).mpr ⟨b.val.val.2,b.property _ (sym_inf_mem _),rfl⟩
      · exact (row_mem ha _ _).mpr ⟨b.val.val.2,b.property _ (sym_sup_mem _),rfl⟩
lemma storedCatalog_eq (ha : List.Forall₂ List.Perm a (orderedRep bags)) :
    storedCatalog (a,List.range m)=catalog bags := by
  have hpair : (storedCatalog (a,List.range m)).Pairwise (· < ·) := by
    apply List.Pairwise.filter
    exact pairwise_product (logicalEdges_pairwise a.length) List.pairwise_lt_range
  have hn := hpair.imp (fun h=>h.ne)
  have hc : (catalog bags).Nodup := List.nodup_ofFn.mpr
    ((key_injective (bags:=bags)).comp (orderedEnum (BagEdge bags)).injective)
  have hp : (storedCatalog (a,List.range m)).Perm (catalog bags) := by
    apply (List.perm_ext_iff_of_nodup hn hc).mpr
    intro e
    rw [storedCatalog_mem ha]
    simp only [catalog,List.mem_ofFn]
    constructor
    · rintro ⟨b,rfl⟩; exact ⟨(orderedEnum _).symm b,by simp⟩
    · rintro ⟨i,rfl⟩; exact ⟨(orderedEnum _ i),rfl⟩
  apply hp.eq_of_pairwise (fun _ _ _ _ h₁ h₂=>@le_antisymm _ Transport.prodOrder.toPartialOrder _ _ h₁ h₂)
    (hpair.imp (fun h=>le_of_lt h))
  rw [catalog,show (fun i=>key (orderedEnum (BagEdge bags) i))=key ∘ orderedEnum (BagEdge bags) from rfl,
    ←List.map_ofFn,ofFn_orderedEnum]
  apply List.pairwise_map.mpr
  exact (Finset.pairwise_sort _ _).imp (fun h=>(key_le _ _).mpr h)
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshNumbered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableUnit Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype Transport.prodOrder
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L}
lemma sourceKey_injective : Function.Injective (sourceKey (bags:=bags)) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Sym2.sortEquiv.injective
    apply Subtype.ext
    apply Prod.ext
    · exact Numbered.index_injective (congrArg (fun z=>z.1.1) h)
    · exact Numbered.index_injective (congrArg (fun z=>z.1.2) h)
  · exact Numbered.index_injective (congrArg Prod.snd h)
lemma index_lt (a b : V) : Numbered.index a < Numbered.index b ↔ a<b := by
  rw [lt_iff_not_ge,lt_iff_not_ge,Numbered.index_le]
attribute [local instance] OAI.MatchingFPRAS.ExecutableRefresh.instLEProdOfLinearOrder_solutions_1
attribute [local instance] OAI.MatchingFPRAS.ExecutableRefresh.instLTProdOfLinearOrder_solutions_1
local instance (priority := 2000) instPreorderProdOfLinearOrder_solutions_1_r2723a7_1 {A B : Type} [LinearOrder A] [LinearOrder B] : Preorder (A×B) := Transport.prodOrder.toPreorder
attribute [local instance] OAI.MatchingFPRAS.ExecutableRefresh.instLTSym2OfLinearOrder_solutions_1
lemma sourceKey_le (e f : BagEdge bags) :
    @LE.le Key Transport.prodOrder.toLE (sourceKey e) (sourceKey f) ↔
      @LE.le _ Transport.bagEdgeOrder.toLE e f := by
  change toLex (sourceKey e)≤toLex (sourceKey f) ↔ toLex e.val.val≤toLex f.val.val
  simp only [Prod.Lex.le_iff,sourceKey,ofLex_toLex,Numbered.index_le]
  have hlt : (Numbered.index e.val.val.1.inf,Numbered.index e.val.val.1.sup)<
      (Numbered.index f.val.val.1.inf,Numbered.index f.val.val.1.sup) ↔ e.val.val.1<f.val.val.1 := by
    change toLex (Numbered.index e.val.val.1.inf,Numbered.index e.val.val.1.sup)<
      toLex (Numbered.index f.val.val.1.inf,Numbered.index f.val.val.1.sup) ↔
      toLex (Sym2.sortEquiv e.val.val.1).val<toLex (Sym2.sortEquiv f.val.val.1).val
    simp only [Prod.Lex.lt_iff,ofLex_toLex,index_lt,Numbered.index_injective.eq_iff]
    rfl
  have heq : (Numbered.index e.val.val.1.inf,Numbered.index e.val.val.1.sup)=
      (Numbered.index f.val.val.1.inf,Numbered.index f.val.val.1.sup) ↔ e.val.val.1=f.val.val.1 := by
    constructor
    · intro h
      apply Sym2.sortEquiv.injective
      apply Subtype.ext
      exact Prod.ext (Numbered.index_injective (congrArg Prod.fst h))
        (Numbered.index_injective (congrArg Prod.snd h))
    · intro h; rw [h]
  rw [hlt,heq]
lemma sourceCatalog_index (e : BagEdge bags) :
    (sourceCatalog bags).idxOf (sourceKey e)=Numbered.index e := by
  let i := (orderedEnum (BagEdge bags)).symm e
  have hn : (sourceCatalog bags).Nodup := List.nodup_ofFn.mpr
    ((sourceKey_injective (bags:=bags)).comp (orderedEnum (BagEdge bags)).injective)
  have hi : i.val<(sourceCatalog bags).length := by simp only [sourceCatalog,List.length_ofFn]; exact i.isLt
  dsimp only [sourceCatalog] at hi hn
  have h:=@List.Nodup.idxOf_getElem Key (inferInstance : BEq Key) inferInstance _ hn i.val hi
  have hh : (List.ofFn (fun j=>sourceKey (orderedEnum (BagEdge bags) j)))[i.val]'hi=sourceKey e := by
    rw [List.getElem_ofFn]
    simp only [Fin.eta,i,Equiv.apply_symm_apply]
  rw [hh] at h
  exact h
lemma sourceCatalog_pairwise : (sourceCatalog bags).Pairwise (· ≤ ·) := by
  rw [sourceCatalog,show (fun i=>sourceKey (orderedEnum (BagEdge bags) i))=
    sourceKey ∘ orderedEnum (BagEdge bags) from rfl,←List.map_ofFn,ofFn_orderedEnum]
  apply List.pairwise_map.mpr
  exact (Finset.pairwise_sort _ _).imp (fun h=>(sourceKey_le _ _).mpr h)
lemma key_downEdge (e : BagEdge bags) : key (downEdge e)=sourceKey e := by
  have h : (orderedEnum V).symm e.val.val.1.inf≤(orderedEnum V).symm e.val.val.1.sup := by
    change Numbered.index e.val.val.1.inf≤Numbered.index e.val.val.1.sup
    exact (Numbered.index_le _ _).mpr e.val.val.1.inf_le_sup
  simp only [key,downEdge,Sym2.inf_mk,Sym2.sup_mk,inf_eq_left.mpr h,sup_eq_right.mpr h,sourceKey,Numbered.index]

lemma sourceKey_upEdge (e : BagEdge (numberedBags bags)) : sourceKey (upEdge e)=key e := by
  have h : orderedEnum V e.val.val.1.inf≤orderedEnum V e.val.val.1.sup := by
    exact ((Numbered.index_le _ _).mp (by simpa only [Numbered.index_orderedEnum,Fin.le_def] using e.val.val.1.inf_le_sup))
  simp only [sourceKey,upEdge,Sym2.inf_mk,Sym2.sup_mk,inf_eq_left.mpr h,sup_eq_right.mpr h,Numbered.index_orderedEnum,key]

lemma sourceCatalog_eq : sourceCatalog bags=catalog (numberedBags bags) := by
  have ha : (sourceCatalog bags).Nodup := List.nodup_ofFn.mpr
    ((sourceKey_injective (bags:=bags)).comp (orderedEnum (BagEdge bags)).injective)
  have hb : (catalog (numberedBags bags)).Nodup := List.nodup_ofFn.mpr
    ((key_injective (bags:=numberedBags bags)).comp (orderedEnum (BagEdge (numberedBags bags))).injective)
  have hp : (sourceCatalog bags).Perm (catalog (numberedBags bags)) := by
    apply (List.perm_ext_iff_of_nodup ha hb).mpr
    intro k
    simp only [sourceCatalog,catalog,List.mem_ofFn]
    constructor
    · rintro ⟨i,rfl⟩
      refine ⟨(orderedEnum _).symm (downEdge (orderedEnum _ i)),?_⟩
      rw [Equiv.apply_symm_apply,key_downEdge]
    · rintro ⟨i,rfl⟩
      refine ⟨(orderedEnum _).symm (upEdge (orderedEnum _ i)),?_⟩
      rw [Equiv.apply_symm_apply,sourceKey_upEdge]
  apply hp.eq_of_pairwise (fun _ _ _ _ h₁ h₂=>@le_antisymm _ Transport.prodOrder.toPartialOrder _ _ h₁ h₂) sourceCatalog_pairwise
  rw [catalog,show (fun i=>key (orderedEnum (BagEdge (numberedBags bags)) i))=
    key ∘ orderedEnum (BagEdge (numberedBags bags)) from rfl,←List.map_ofFn,ofFn_orderedEnum]
  apply List.pairwise_map.mpr
  exact (Finset.pairwise_sort _ _).imp (fun h=>(key_le _ _).mpr h)
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefresh
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableUnit Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L}
lemma index_min (a b : V) : Numbered.index (min a b)=min (Numbered.index a) (Numbered.index b) := by
  by_cases h : a≤b
  · rw [min_eq_left h,min_eq_left ((Numbered.index_le _ _).mpr h)]
  · rw [min_eq_right (le_of_not_ge h),min_eq_right ((Numbered.index_le _ _).mpr (le_of_not_ge h))]
lemma index_max (a b : V) : Numbered.index (max a b)=max (Numbered.index a) (Numbered.index b) := by
  by_cases h : a≤b
  · rw [max_eq_right h,max_eq_right ((Numbered.index_le _ _).mpr h)]
  · rw [max_eq_left (le_of_not_ge h),max_eq_left ((Numbered.index_le _ _).mpr (le_of_not_ge h))]
lemma sourceKey_numbering (p : ColoredPairing (numberedBags bags)) (i : Fin (Fintype.card V)) :
    sourceKey ((numberingEquiv bags p).edgeAt (orderedEnum V i))=key (p.edgeAt i) := by
  simp only [sourceKey,key,ColoredPairing.edgeAt,Sym2.inf_mk,Sym2.sup_mk]
  change ((Numbered.index (min (orderedEnum V i) (orderedEnum V (p.pair.mate ((orderedEnum V).symm (orderedEnum V i))))),
    Numbered.index (max (orderedEnum V i) (orderedEnum V (p.pair.mate ((orderedEnum V).symm (orderedEnum V i)))))),
      Numbered.index (orderedEnum L (p.color ((orderedEnum V).symm (orderedEnum V i))))) = _
  simp only [Equiv.symm_apply_apply]
  simp only [index_min,index_max,Numbered.index_orderedEnum]
  rfl
lemma rowKey_numbering (p : ColoredPairing (numberedBags bags)) (i : Fin (Fintype.card V)) :
    rowKey (resultRep p,i.val)=sourceKey ((numberingEquiv bags p).edgeAt (orderedEnum V i)) := by
  rw [rowKey_result,sourceKey_numbering]
lemma matching_numbering (p : ColoredPairing (numberedBags bags)) :
    matching (sourceCatalog bags,resultRep p)=
      Numbered.set (Computable.toMatching (numberingEquiv bags p)).val := by
  ext j
  simp only [matching,resultRep,List.length_ofFn,List.mem_toFinset,List.mem_map,List.mem_range]
  change (∃ i,i<Fintype.card V ∧ entryIndex ((sourceCatalog bags,resultRep p),i)=j) ↔ _
  simp only [Numbered.set,Finset.mem_map,Numbered.embedding,Function.Embedding.coeFn_mk,
    Computable.toMatching,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi,hj⟩
    refine ⟨(numberingEquiv bags p).edgeAt (orderedEnum V ⟨i,hi⟩),⟨orderedEnum V ⟨i,hi⟩,rfl⟩,?_⟩
    rw [entryIndex,rowKey_numbering p ⟨i,hi⟩,sourceCatalog_index] at hj
    exact hj
  · rintro ⟨e,⟨i,rfl⟩,hj⟩
    refine ⟨Numbered.index i,((orderedEnum V).symm i).isLt,?_⟩
    change (sourceCatalog bags).idxOf (rowKey (resultRep p,((orderedEnum V).symm i).val))=j
    rw [rowKey_numbering p ((orderedEnum V).symm i),sourceCatalog_index,Equiv.apply_symm_apply]
    exact hj

lemma refresh_sampleMatching {k : ℕ} (bags : V→Finset L) (rank : L→ℕ) (parent : L→Option L)
    (hb : RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p < rank l) (M : BagPM bags)
    (a : Bags) (ha : List.Forall₂ List.Perm a (orderedRep (numberedBags bags)))
    (bits : Fin (Fintype.card V)→Fin k→Bool) :
    refresh ((storedCatalog (a,List.range (Fintype.card L)),
      ((a,parentRep (numberedParent parent)),(Materialized.plan (numberedRank rank)).map Fin.val)),
      List.ofFn (fun i=>List.ofFn (bits i)))=
    Numbered.set (sampleMatching k bags rank parent hb hne hp M bits).val := by
  unfold refresh
  rw [storedCatalog_eq ha,←sourceCatalog_eq]
  rw [fastSample_represented (numberedBags bags) (numberedRank rank) (numberedParent parent)
    (numberedRanked bags rank parent hb) (numberedNonempty bags hne) (numberedDecreasing rank parent hp)
    (numbered_count_pos bags rank parent hb hne hp (Computable.pairingEquiv M)) a ha bits,matching_numbering]
  rfl

open TreePost Turing

end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeOptionsAccept
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableOptions
open TreeTyped TreeFraction

variable {A C Ω : Type} [Codec A] [Codec C]

omit [Codec A] [Codec C] in
lemma accept_repr [Codec A] [Codec C] (e : Ω→A) (p : C×A→Fraction) (z : C) (a : Ω) (c : WeightedOptions Ω)
    (q : Ω→ℚ) (hq : ∀ a,0≤q a) (hq1 : ∀ a,q a≤1)
    (he : ∀ a,p (z,e a)=TreeFraction.repr (q a)) :
    accept p ((z,e a),repr e c)=repr e (c.accept a q hq hq1) := by
  have h1 : (1,1)=TreeFraction.repr 1 := rfl
  simp only [accept,repr,List.map_ofFn,h1]
  simp only [WeightedOptions.accept]
  rw [List.ofFn_add]
  apply congrArg₂ List.append <;> apply List.ofFn_inj.mpr <;> funext i
  · simp only [Function.comp_def,he]
    change (e (c.out i),mul (TreeFraction.repr (c.mass i),TreeFraction.repr (q (c.out i)))) =
      (e (Fin.addCases c.out (fun _=>a) (i.castAdd c.size)),TreeFraction.repr (Fin.addCases (fun i=>c.mass i*q (c.out i)) (fun i=>c.mass i*(1-q (c.out i))) (i.castAdd c.size)))
    simp only [Fin.addCases_left,mul_repr (c.nonneg i) (hq _)]
  · simp only [Function.comp_def,Fin.addCases_right,he]
    rw [sub_repr (by decide) (hq _) (hq1 _),mul_repr (c.nonneg i) (sub_nonneg.mpr (hq1 _))]

omit [Codec A] [Codec C] in
lemma metropolisProbability_repr [Codec A] [Codec C] (e : Ω→A) (w : C×A→Fraction) (z : C)
    (q : Ω→ℚ) (hq : ∀ a,0≤q a) (he : ∀ a,w (z,e a)=TreeFraction.repr (q a)) (a b : Ω) :
    metropolisProbability w ((z,e a),e b)=TreeFraction.repr (min 1 (q b/q a)) := by
  unfold metropolisProbability
  rw [he,he,div_repr (hq _) (hq _)]
  exact minimum_repr (x:=1) (y:=q b/q a) (by decide) (div_nonneg (hq _) (hq _))
end MatchingFPRAS.ExecutableOptions

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeOptionsMaps
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableOptions
variable {A Ω : Type} [LinearOrder A] [LinearOrder Ω]
omit [LinearOrder A] [LinearOrder Ω] in
lemma repr_map (e : Ω→A) (c : WeightedOptions Ω) :
    repr e c=(repr id c).map (fun a=>(e a.1,a.2)) := by
  simp only [repr,List.map_ofFn,Function.comp_def,id_eq]

lemma neighbors_map (e : Ω↪oA) (a : Ω) (s : Finset Ω) (d : ℕ) :
    neighbors ((e a,s.map e.toEmbedding),d)=
      (neighbors ((a,s),d)).map (fun a=>(e a.1,a.2)) := by
  unfold neighbors
  rw [Finset.card_map,←Finset.map_sort (r:=fun x y : Ω=>x≤y) (r':=fun x y : A=>x≤y)
    (f:=e.toEmbedding) (s:=s) (fun a _ b _=>(e.le_iff_le).symm)]
  simp only [List.map_map,List.map_append,List.map_cons,List.map_nil,Function.comp_def]
  rfl
lemma neighbors_repr_map (e : Ω↪oA) (a : Ω) (s : Finset Ω) (d : ℕ) (hd : s.card≤d) :
    neighbors ((e a,s.map e.toEmbedding),d)=repr e (WeightedOptions.neighbors a s d hd) := by
  rw [neighbors_map,neighbors_repr a s d hd,repr_map e]
end MatchingFPRAS.ExecutableOptions

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeSparseNeighbors
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped ExecutableOptions

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder

variable [Fintype E] [Fintype V] (ends : E→Sym2 V)
attribute [local instance] Transport.Sparse.pmOrder
variable (hloop : ∀ e,¬(ends e).IsDiag) (hpar : ∀ e,(Finset.univ.filter (fun f=>ends f=ends e)).card≤2)
omit [Codec E] [Codec V] [Codec C] in
lemma colorTable_eq (p : C×(E×V)→Bool) (q : C×(E×E)→Bool) (c : C)
    (hp : ∀ e v,p (c,(e,v))=decide (v∈ends e)) (hq : ∀ e f,q (c,(e,f))=decide (ends e=ends f))
    (a : Transport.PM (fun e v=>v∈ends e)) :
    colorTable p q ((c,(Finset.univ,Finset.univ)),a.val)=repr Subtype.val (Transport.Sparse.colorTable ends hloop hpar a) := by
  unfold colorTable
  have hraw : colorRaw q ((c,Finset.univ),a.val)=Transport.Sparse.colorRaw ends a.val := by
    simp only [colorRaw,Transport.Sparse.colorRaw,hq,decide_eq_true_eq]
  rw [hraw,certify_eq ends p c hp,Finset.card_univ]
  have he:=Finset.map_erase (pmEmbedding ends).toEmbedding (Transport.Sparse.colors ends a) a
  have hn:=neighbors_repr_map (pmEmbedding ends) a ((Transport.Sparse.colors ends a).erase a)
    (Fintype.card V) (Transport.Sparse.color_degree ends hloop hpar a)
  rw [he] at hn
  exact hn
omit [Codec E] [Codec V] [Codec C] in
lemma switchTable_eq (p : C×(E×V)→Bool) (q : C×(E×(V×V))→Bool) (c : C)
    (hp : ∀ e v,p (c,(e,v))=decide (v∈ends e)) (hq : ∀ e v w,q (c,(e,(v,w)))=decide (ends e=s(v,w)))
    (a : Transport.PM (fun e v=>v∈ends e)) :
    switchTable p q ((c,(Finset.univ,Finset.univ)),a.val)=repr Subtype.val (Transport.Sparse.switchTable ends hloop hpar a) := by
  unfold switchTable
  rw [switchRaw_eq ends q c hq,certify_eq ends p c hp,Finset.card_univ]
  have he:=Finset.map_erase (pmEmbedding ends).toEmbedding (Transport.Sparse.switches ends a) a
  have hn:=neighbors_repr_map (pmEmbedding ends) a ((Transport.Sparse.switches ends a).erase a)
    (degree (Fintype.card V)) (Transport.Sparse.switch_degree ends hloop hpar a)
  rw [he] at hn
  exact hn
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreePairTable
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped ExecutableOptions

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder

variable [Fintype E] [Fintype V] (ends : E→Sym2 V)
attribute [local instance] Transport.Sparse.pmOrder
variable (hloop : ∀ e,¬(ends e).IsDiag) (hpar : ∀ e,(Finset.univ.filter (fun f=>ends f=ends e)).card≤2)
omit [Codec E] [Codec V] [Codec C] in
lemma pairTable_eq (p : C×(E×V)→Bool) (q : C×(E×E)→Bool) (r : C×(E×(V×V))→Bool)
    (t : C×(E×E)→Bool) (c : C)
    (hp : ∀ e v,p (c,(e,v))=decide (v∈ends e)) (hq : ∀ e f,q (c,(e,f))=decide (ends e=ends f))
    (hr : ∀ e v w,r (c,(e,(v,w)))=decide (ends e=s(v,w)))
    (ht : ∀ e f,t (c,(e,f))=decide (∃ v,v∈ends e ∧ v∈ends f))
    (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e)) :
    pairTable p q r t ((c,(Finset.univ,Finset.univ)),pairRepr ends a)=
      repr (pairRepr ends) (Transport.Sparse.pairTable ends hloop hpar a) := by
  unfold pairTable
  simp only [pairRepr]
  rw [switchTable_eq ends hloop hpar p r c hp hr,colorTable_eq ends hloop hpar p q c hp hq]
  have hc:=cycleTable_eq ends t c ht a
  rw [show pairRepr ends a=(a.1.val,a.2.val) from rfl] at hc
  rw [hc]
  rw [map_repr Subtype.val (pairRepr ends) (fun b=>(b,a.2)) _ a.2.val (fun _=>rfl),
    map_repr Subtype.val (pairRepr ends) (fun b=>(b,a.2)) _ a.2.val (fun _=>rfl)]
  have h3 : (1,3)=TreeFraction.repr ((1:ℚ)/3) := by norm_num [TreeFraction.repr]
  have h2 : (1,2)=TreeFraction.repr ((1:ℚ)/2) := by norm_num [TreeFraction.repr]
  rw [h3,h2]
  rw [mix_repr _ _ (by norm_num) (by norm_num),mix_repr _ _ (by norm_num) (by norm_num)]
  rfl
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreePairStep
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped ExecutableOptions TreeFraction

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder

variable [Fintype E] [Fintype V] (ends : E→Sym2 V)
attribute [local instance] Transport.Sparse.pmOrder
variable (hloop : ∀ e,¬(ends e).IsDiag) (hpar : ∀ e,(Finset.univ.filter (fun f=>ends f=ends e)).card≤2)
variable (p : C×(E×V)→Bool) (q : C×(E×E)→Bool) (r : C×(E×(V×V))→Bool)
    (t : C×(E×E)→Bool) (w z : C×E→Fraction) (c : C)
    (hp : ∀ e v,p (c,(e,v))=decide (v∈ends e)) (hq : ∀ e f,q (c,(e,f))=decide (ends e=ends f))
    (hr : ∀ e v w,r (c,(e,(v,w)))=decide (ends e=s(v,w)))
    (ht : ∀ e f,t (c,(e,f))=decide (∃ v,v∈ends e ∧ v∈ends f))
    (u v : E→ℚ) (hu : ∀ e,0<u e) (hv : ∀ e,0<v e)
    (hw : ∀ e,w (c,e)=TreeFraction.repr (u e)) (hz : ∀ e,z (c,e)=TreeFraction.repr (v e))
include hp hq hr ht hw hz in
omit [Codec E] [Codec V] [Codec C] in
lemma pairStep_eq [Codec E] [Codec V] [Codec C]
    (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e)) :
    pairStepTable p q r t w z ((c,(Finset.univ,Finset.univ)),pairRepr ends a)=
      ExecutableOptions.repr (pairRepr ends) (Transport.Sparse.pairStepTable ends hloop hpar u v hu hv a) := by
  unfold pairStepTable
  rw [pairTable_eq ends hloop hpar p q r t c hp hq hr ht]
  unfold Transport.Sparse.pairStepTable WeightedOptions.metropolisChoice
  refine accept_repr (pairRepr ends) (metropolisProbability (pairWeight w z)) (c,pairRepr ends a) a
    (Transport.Sparse.pairTable ends hloop hpar a) _ _ _ ?_
  intro b
  exact metropolisProbability_repr (pairRepr ends) (pairWeight w z) c _
    (fun b=>(Transport.Sparse.rationalPairWeight_pos ends u v hu hv b).le)
    (pairWeight_repr ends w z c u v (fun e=>(hu e).le) (fun e=>(hv e).le) hw hz) a b
include hp hq hr ht hw hz in
omit [Codec E] [Codec V] [Codec C] in
lemma pairDraw_eq [Codec E] [Codec V] [Codec C]
    (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e))
    {k : ℕ} (bits : Fin k→Bool) :
    pairDraw p q r t w z (((c,(Finset.univ,Finset.univ)),pairRepr ends a),List.ofFn bits)=
      pairRepr ends ((Transport.Sparse.pairStepTable ends hloop hpar u v hu hv a).draw k bits) := by
  unfold pairDraw
  rw [pairStep_eq ends hloop hpar p q r t w z c hp hq hr ht u v hu hv hw hz]
  exact draw_repr _ _ _ bits
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeIndexedPairCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutablePair
open TreeTyped TreeFraction TreeTyped.SparseProgram TreeTyped.Numbered

variable {E V : Type} [Fintype E] [LinearOrder E] [Fintype V] [LinearOrder V]
lemma endpoints_rep (ends : E→Sym2 V) (w z : E→ℚ) (e : E) :
    endpoints (contextRep ends w z,index e)=endpointRep (ends e) := by
  simp [endpoints,contextRep,index,List.getD_eq_getElem?_getD]
lemma u_rep (ends : E→Sym2 V) (w z : E→ℚ) (e : E) :
    u (contextRep ends w z,index e)=TreeFraction.repr (w e) := by
  simp [u,contextRep,index,List.getD_eq_getElem?_getD]
lemma v_rep (ends : E→Sym2 V) (w z : E→ℚ) (e : E) :
    v (contextRep ends w z,index e)=TreeFraction.repr (z e) := by
  simp [v,contextRep,index,List.getD_eq_getElem?_getD]
omit [Fintype V] in
lemma pair_inf_sup [Fintype V] (s : Sym2 V) : s(s.inf,s.sup)=s := Sym2.sortEquiv.symm_apply_apply s
lemma incident_rep (s : Sym2 V) (x : V) :
    incident (endpointRep s,index x)=decide (x∈s) := by
  simp only [incident,endpointRep,(index_injective (A:=V)).eq_iff]
  congr 1
  rw [←pair_inf_sup s,Sym2.mem_iff]
  simp only [Sym2.inf_mk,Sym2.sup_mk]
  rw [min_eq_left (Sym2.inf_le_sup s),max_eq_right (Sym2.inf_le_sup s)]
  exact propext (by tauto)
lemma same_rep (s t : Sym2 V) :
    same (endpointRep s,endpointRep t)=decide (s=t) := by
  simp only [same,endpointRep,(index_injective (A:=V)).eq_iff]
  congr 1
  exact propext (by rw [←Sym2.eq_iff,pair_inf_sup,pair_inf_sup])
lemma same_pair_rep (s : Sym2 V) (a b : V) :
    same (endpointRep s,(index a,index b))=decide (s=s(a,b)) := by
  simp only [same,endpointRep,(index_injective (A:=V)).eq_iff]
  congr 1
  exact propext (by rw [←Sym2.eq_iff,pair_inf_sup])
lemma adjacent_rep (s t : Sym2 V) :
    adjacent (endpointRep s,endpointRep t)=decide (∃ v,v∈s ∧ v∈t) := by
  simp only [adjacent,endpointRep]
  change (incident (endpointRep s,index t.inf) || incident (endpointRep s,index t.sup))=_
  rw [incident_rep,incident_rep]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true,decide_eq_true_eq]
  constructor
  · rintro (h|h)
    · refine ⟨t.inf,h,?_⟩
      simpa only [pair_inf_sup] using (Sym2.mem_mk_left t.inf t.sup)
    · refine ⟨t.sup,h,?_⟩
      simpa only [pair_inf_sup] using (Sym2.mem_mk_right t.inf t.sup)
  · rintro ⟨a,ha,ht⟩
    rw [←pair_inf_sup t,Sym2.mem_iff] at ht
    rcases ht with h|h <;> subst a <;> simp [ha]

lemma p_rep (ends : E→Sym2 V) (w z : E→ℚ) (e : E) (x : V) :
    p (contextRep ends w z,(index e,index x))=decide (x∈ends e) := by
  unfold p
  rw [endpoints_rep,incident_rep]
lemma q_rep (ends : E→Sym2 V) (w z : E→ℚ) (e f : E) :
    q (contextRep ends w z,(index e,index f))=decide (ends e=ends f) := by
  unfold q
  rw [endpoints_rep,endpoints_rep,same_rep]
lemma r_rep (ends : E→Sym2 V) (w z : E→ℚ) (e : E) (a b : V) :
    r (contextRep ends w z,(index e,(index a,index b)))=decide (ends e=s(a,b)) := by
  unfold r
  rw [endpoints_rep,same_pair_rep]
lemma t_rep (ends : E→Sym2 V) (w z : E→ℚ) (e f : E) :
    t (contextRep ends w z,(index e,index f))=decide (∃ v,v∈ends e ∧ v∈ends f) := by
  unfold t
  rw [endpoints_rep,endpoints_rep,adjacent_rep]
end MatchingFPRAS.ExecutablePair

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeErasure
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData

variable {A B : Type} [Codec A] [Codec B]
lemma constantData_program (d : Data) :
    (constantData (A:=A) d).program=(constantData (A:=B) d).program := by
  induction d with
  | nil=>rfl
  | cons a b ih ihb=>
    change TreeFunction.pair _ _ = TreeFunction.pair _ _
    rw [ih,ihb]
lemma constant_program (a : A) (b : B) (h : encode a=encode b)
    {C D : Type} [Codec C] [Codec D] :
    (constant (A:=C) a).program=(constant (A:=D) b).program := by
  change (constantData (A:=C) (encode a)).program=(constantData (A:=D) (encode b)).program
  rw [h]
  exact constantData_program _
lemma encode_empty_finset {E : Type} [Codec E] [LinearOrder E] :
    encode (∅ : Finset E)=Data.nil := by
  simp only [encode_finset,Finset.sort_empty,encode_list_nil]
lemma head_program (a : A) (b : B) (h : encode a=encode b) :
    (head a).program=(head b).program := by
  change RegisterStructured.select 0 (constant a).program first.program =
    RegisterStructured.select 0 (constant b).program first.program
  rw [constant_program a b h (C:=List A) (D:=List B)]
  rfl
lemma getDFast_program (a : A) (b : B) (h : encode a=encode b) :
    (getDFast a).program=(getDFast b).program := by
  change RegisterProc.seq dropFast.program (head a).program =
    RegisterProc.seq dropFast.program (head b).program
  rw [head_program a b h]
  rfl
lemma draw_program (a : A) (b : B) (h : encode a=encode b) :
    (ExecutableOptions.drawRealizer a).program=(ExecutableOptions.drawRealizer b).program := by
  unfold ExecutableOptions.drawRealizer
  dsimp only [Realizer.congr, composition, pair]
  rw [getDFast_program a b h]
  rfl
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeIndexedPairUniform
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutablePair
open TreeTyped TreeFraction TreeTyped.SparseProgram TreeTyped.Numbered

variable {E V : Type} [Fintype E] [LinearOrder E] [Fintype V] [LinearOrder V]

lemma typedDraw_program : (typedDrawRealizer (E:=E) (V:=V)).program=drawRealizer.program := by
  simp only [typedDrawRealizer, drawRealizer, pairDrawRealizer, Realizer.congr,
    composition, pair]
  rw [draw_program ((∅,∅) : PairState E) ((∅,∅) : PairState ℕ) (by
    simp only [encode_prod,encode_empty_finset])]
  rfl

attribute [local instance] Transport.Sparse.pmOrder
lemma typedDraw_source (ends : E→Sym2 V) (hloop : ∀ e,¬(ends e).IsDiag)
    (hpar : ∀ e,(Finset.univ.filter (fun f=>ends f=ends e)).card≤2)
    (w z : E→ℚ) (hw : ∀ e,0<w e) (hz : ∀ e,0<z e)
    (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e))
    {k : ℕ} (bits : Fin k→Bool) :
    typedDraw (E:=E) (V:=V) (((contextRep ends w z,(Finset.univ,Finset.univ)),pairRepr ends a),List.ofFn bits)=
      pairRepr ends ((Transport.Sparse.pairStepTable ends hloop hpar w z hw hz a).draw k bits) := by
  exact pairDraw_eq ends hloop hpar typedP typedQ typedR typedT typedU typedV (contextRep ends w z)
    (p_rep ends w z) (q_rep ends w z) (r_rep ends w z) (t_rep ends w z) w z hw hz
    (u_rep ends w z) (v_rep ends w z) a bits
end MatchingFPRAS.ExecutablePair

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeIndexedPairPost
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutablePair
open TreeTyped TreeTyped.SparseProgram TreeTyped.Numbered TreePost Turing

variable {E V : Type} [Fintype E] [LinearOrder E] [Fintype V] [LinearOrder V]
lemma numericInput_encode (x : PairInput Context E V×List Bool) : encode (numericInput x)=encode x := by
  rcases x with ⟨⟨⟨c,e,v⟩,a,b⟩,bits⟩
  simp only [numericInput,encode_prod,Numbered.encode_set]

attribute [local instance] Transport.Sparse.pmOrder

end MatchingFPRAS.ExecutablePair

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeEncodingInjective
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeData
lemma encode_prefix_injective (a : Data) : ∀ b xs ys,
    encode a++xs=encode b++ys → a=b ∧ xs=ys := by
  induction a with
  | nil=>
    intro b xs ys h
    cases b with
    | nil=>simpa [encode] using h
    | cons b c=>simp [encode] at h
  | cons a c ia ic=>
    intro b xs ys h
    cases b with
    | nil=>simp [encode] at h
    | cons b d=>
      simp only [encode,List.cons_append,List.cons.injEq,true_and,List.append_assoc] at h
      obtain ⟨hab,he⟩:=ia b _ _ h
      obtain ⟨hcd,hxy⟩:=ic d xs ys he
      exact ⟨congrArg₂ Data.cons hab hcd,hxy⟩
lemma encode_injective : Function.Injective encode := by
  intro a b h
  exact (encode_prefix_injective a b [] [] (by simpa using h)).1
lemma ofList_injective : Function.Injective ofList := by
  intro a
  induction a with
  | nil=>intro b h; cases b <;> simp_all [ofList]
  | cons a as ih=>
    intro b h
    cases b with
    | nil=>simp [ofList] at h
    | cons b bs=>
      obtain ⟨rfl,he⟩:=Data.cons.inj h
      rw [ih he]
lemma bit_injective : Function.Injective bit := by
  intro a b h
  cases a <;> cases b <;> simp_all [bit]
lemma nat_injective : Function.Injective nat := by
  intro a b h
  have hh: a.bits=b.bits:=(List.map_injective_iff.mpr bit_injective) (ofList_injective h)
  have := congrArg StackAddition.value hh
  simpa only [StackAddition.value_bits] using this
end MatchingFPRAS.TreeData

namespace MatchingFPRAS.TreePost
open TreeTyped TreeData TreeFunction TreeMachine RegisterProc

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]
lemma sameProgram_encode {f : A→B} {g : C→D} (F : Realizer f) (G : Realizer g)
    (h : F.program=G.program) (a : A) (b : C) (hi : TreeTyped.encode a=TreeTyped.encode b) :
    TreeTyped.encode (f a)=TreeTyped.encode (g b) := by
  have hf:=F.correct a .nil
  have hg:=G.correct b .nil
  change Exec F.program (inputStacks a) (inputStacks (f a)) _ at hf
  change Exec G.program (inputStacks b) (inputStacks (g b)) _ at hg
  rw [h,stacks_eq_of_encode hi] at hf
  exact TreeData.encode_injective (congrFun (hf.unique hg) (.inl 0))
end MatchingFPRAS.TreePost

namespace MatchingFPRAS.TreeTyped
open TreeData

lemma list_encode_injective {A : Type} [Codec A] (hf : Function.Injective (encode (A:=A))) :
    Function.Injective (encode (A:=List A)) := by
  intro a b h
  exact (List.map_injective_iff.mpr hf) (ofList_injective h)
lemma nat_encode_injective : Function.Injective (encode (A:=ℕ)) := TreeData.nat_injective
lemma finsetNat_encode_injective : Function.Injective (encode (A:=Finset ℕ)) := by
  intro a b h
  change encode (a.sort (·≤·))=encode (b.sort (·≤·)) at h
  have hh:=list_encode_injective nat_encode_injective h
  have := congrArg List.toFinset hh
  simpa using this
lemma pair_encode_injective {A B : Type} [Codec A] [Codec B]
    (ha : Function.Injective (encode (A:=A))) (hb : Function.Injective (encode (A:=B))) :
    Function.Injective (encode (A:=A×B)) := by
  intro a b h
  exact Prod.ext (ha (TreeData.Data.cons.inj h).1) (hb (TreeData.Data.cons.inj h).2)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeIndexedPairResult
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutablePair
open TreeTyped TreeTyped.Numbered TreeTyped.SparseProgram TreePost

variable {E V : Type} [Fintype E] [LinearOrder E] [Fintype V] [LinearOrder V]
lemma numeric_draw (x : PairInput Context E V×List Bool) :
    draw (numericInput x)=(Numbered.set (typedDraw x).1,Numbered.set (typedDraw x).2) := by
  apply pair_encode_injective finsetNat_encode_injective finsetNat_encode_injective
  have h:=sameProgram_encode drawRealizer typedDrawRealizer typedDraw_program.symm _ _ (numericInput_encode x)
  have he : encode (Numbered.set (typedDraw x).1,Numbered.set (typedDraw x).2)=encode (typedDraw x) :=
    congrArg₂ TreeData.Data.cons (Numbered.encode_set _) (Numbered.encode_set _)
  exact h.trans he.symm
attribute [local instance] Transport.Sparse.pmOrder
lemma numeric_draw_source (ends : E→Sym2 V) (hloop : ∀ e,¬(ends e).IsDiag)
    (hpar : ∀ e,(Finset.univ.filter (fun f=>ends f=ends e)).card≤2)
    (w z : E→ℚ) (hw : ∀ e,0<w e) (hz : ∀ e,0<z e)
    (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e))
    {k : ℕ} (bits : Fin k→Bool) :
    draw ((((contextRep ends w z,(Numbered.set (Finset.univ : Finset V),Numbered.set (Finset.univ : Finset E))),
      (Numbered.set a.1.val,Numbered.set a.2.val)),List.ofFn bits))=
      (Numbered.set ((Transport.Sparse.pairStepTable ends hloop hpar w z hw hz a).draw k bits).1.val,
       Numbered.set ((Transport.Sparse.pairStepTable ends hloop hpar w z hw hz a).draw k bits).2.val) := by
  have h:=numeric_draw (E:=E) (V:=V) (((contextRep ends w z,(Finset.univ,Finset.univ)),pairRepr ends a),List.ofFn bits)
  rw [typedDraw_source ends hloop hpar w z hw hz a bits] at h
  exact h
end MatchingFPRAS.ExecutablePair

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeLocalSampler
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped

variable {I A B C : Type} [Codec I] [Codec A] [Codec B] [Codec C]
variable [DecidableEq I] [Inhabited I] [Inhabited A]

variable {Ω D : Type} [Fintype I] [Fintype Ω] [DecidableEq Ω] [Fintype D] [Nonempty D]
variable (e : Ω→A) (d : D→B) (c : C) (keys : List I) (hk : ∀ i,i∈keys)
variable (p : LocalPairInput C I A B→A×A) (r : LocalRefreshInput C I B→A)
variable (sp : I→I→(Ω×Ω)→D→Ω×Ω) (sr : I→D→Ω)
    (hp : ∀ i j a b,p ((c,(i,j)),((e a.1,e a.2),d b))=(e (sp i j a b).1,e (sp i j a b).2))
    (hr : ∀ i b,r ((c,i),d b)=e (sr i b))
omit [Codec I] [Codec A] [Codec B] [Codec C] [Inhabited I]
    [Fintype I] [Fintype Ω] [DecidableEq Ω] [Fintype D] [Nonempty D] in
include hp hr hk in
lemma localSampler_rep [Fintype I] [Fintype Ω] [DecidableEq Ω] [Fintype D] [Nonempty D]
    (s : I→Ω) (u : Option (Replica.Update I)) (b : D) :
    localSampler p r ((c,(stateRep keys (e ∘ s),d b)),u)=
      stateRep keys (e ∘ Replica.localSampler sp sr s u b) := by
  cases u with
  | none => rfl
  | some u=>cases u with
    | inl ij=>
      rcases ij with ⟨i,j⟩
      simp only [localSampler,Option.elim_some,Sum.elim_inl,localPair,
        lookup_stateRep default keys (e ∘ s) _ (hk _),Function.comp_apply,hp i j (s i,s j) b,setPair_rep,
        Replica.localSampler]
      congr 1
      funext z
      simp only [Replica.replacePair,Function.comp_apply,Function.update_apply]
      split_ifs <;> rfl
    | inr i=>
      simp only [localSampler,Option.elim_some,Sum.elim_inr,localRefresh,hr,setState_rep,
        Replica.localSampler]
      congr 1
      funext z
      simp only [Function.comp_apply,Function.update_apply]
      split_ifs <;> rfl
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeScanChoice
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped ExecutableOptions

variable {I C : Type} [Codec I] [Codec C] [Inhabited I] [LinearOrder I]
attribute [local instance] Transport.prodOrder Transport.sumOrder

variable [Fintype I]
variable (guides : I→Finset I) (base : Finset I) (hb : base.Nonempty)
variable (g : C×(I×I)→Bool) (c : C) (hg : ∀ i j,g (c,(i,j))=decide (j∈guides i))
omit [Codec I] [Codec C] [Inhabited I] in
include hg in
lemma updateSet_eq : (updateList g (c,(Finset.univ,base))).toFinset=Replica.updates guides base := by
  ext u
  cases u with
  | inl ij => rcases ij with ⟨i,j⟩; simp [updateList,Replica.updates,hg]
  | inr i => simp [updateList,Replica.updates]
omit [Codec I] [Codec C] [Inhabited I] in
include hg in
lemma scanChoice_eq : scanChoice g (c,(Finset.univ,base))=
    ExecutableOptions.repr id (Replica.scanChoice guides base hb) := by
  unfold scanChoice Replica.scanChoice
  rw [updateSet_eq guides base g c hg,uniform_repr _ (Replica.updates_nonempty guides base hb)]
  rw [map_repr id id Option.some (fun x : Bool×Replica.Update I=>Option.some x.2) false (fun _=>rfl)]
  have hp := pure_repr (id : Option (Replica.Update I)→_) (none : Option (Replica.Update I))
  dsimp only [id_eq] at hp
  rw [hp]
  have hh : (1,2)=TreeFraction.repr (1/2:ℚ) := by norm_num [TreeFraction.repr]
  rw [hh,mix_repr id (1/2) (by norm_num) (by norm_num)]
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeScan
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped ExecutableOptions

variable {I A B C : Type} [Codec I] [Codec A] [Codec B] [Codec C]
variable [LinearOrder I] [Inhabited I] [Inhabited A]
attribute [local instance] Transport.prodOrder Transport.sumOrder

variable {Ω D : Type} [Fintype I] [Fintype Ω] [DecidableEq Ω] [Fintype D] [Nonempty D]
variable (e : Ω→A) (d : D→B) (c : C) (keys : List I) (hk : ∀ i,i∈keys)
variable (guides : I→Finset I) (base : Finset I) (hb : base.Nonempty)
variable (g : C×(I×I)→Bool) (hg : ∀ i j,g (c,(i,j))=decide (j∈guides i))
variable (p : LocalPairInput C I A B→A×A) (r : LocalRefreshInput C I B→A)
variable (sp : I→I→(Ω×Ω)→D→Ω×Ω) (sr : I→D→Ω)
    (hp : ∀ i j a b,p ((c,(i,j)),((e a.1,e a.2),d b))=(e (sp i j a b).1,e (sp i j a b).2))
    (hr : ∀ i b,r ((c,i),d b)=e (sr i b))
omit [Codec I] [Codec A] [Codec B] [Codec C] [Inhabited I] in
include hp hr hk hg in
lemma scan_rep {k : ℕ} (s : I→Ω) (bs : Fin k→Bool) (b : D) :
    scan g p r (((c,(Finset.univ,base)),stateRep keys (e ∘ s)),(List.ofFn bs,d b))=
      stateRep keys (e ∘ Replica.sampleScan guides base hb sp sr k s (bs,b)) := by
  unfold scan
  rw [scanChoice_eq guides base hb g c hg]
  have hh := draw_repr id (Replica.scanChoice guides base hb) (none : Option (Replica.Update I)) bs
  dsimp only [id_eq] at hh
  rw [hh]
  exact localSampler_rep e d c keys hk p r sp sr hp hr s _ b
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeScanRun
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped Polynomial

variable {I E B C : Type} [Codec I] [Codec E] [Codec B] [Codec C]
variable [LinearOrder I] [Inhabited I] [LinearOrder E]
attribute [local instance] Transport.prodOrder Transport.sumOrder

variable {Ω D : Type} [Fintype I] [Fintype Ω] [DecidableEq Ω] [Fintype D] [Nonempty D]
variable (e : Ω→Finset E) (d : D→B) (c : C) (keys : List I) (hk : ∀ i,i∈keys)
    (univ : Finset E) (he : ∀ a,e a⊆univ)
variable (guides : I→Finset I) (base : Finset I) (hb : base.Nonempty)
variable (g : C×(I×I)→Bool) (hg : ∀ i j,g (c,(i,j))=decide (j∈guides i))
variable (p : LocalPairInput C I (Finset E) B→Finset E×Finset E) (r : LocalRefreshInput C I B→Finset E)
variable (sp : I→I→(Ω×Ω)→D→Ω×Ω) (sr : I→D→Ω)
    (hp : ∀ i j a b,p ((c,(i,j)),((e a.1,e a.2),d b))=(e (sp i j a b).1,e (sp i j a b).2))
    (hr : ∀ i b,r ((c,i),d b)=e (sr i b))
omit [Codec I] [Codec E] [Codec B] [Codec C] [Inhabited I] in
include hp hr hk hg he in
lemma scanRun_rep {k n : ℕ} (s : I→Ω) (bs : Fin n→((Fin k→Bool)×D)) :
    (List.ofFn (fun i=>(List.ofFn (bs i).1,d (bs i).2))).foldl
      (fun z b=>runStep g p r (b,z)) (((c,(Finset.univ,base)),(keys,univ)),stateRep keys (e ∘ s))=
    (((c,(Finset.univ,base)),(keys,univ)),stateRep keys
      (e ∘ Variation.runSample (Replica.sampleScan guides base hb sp sr k) s n bs)) := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [List.ofFn_succ_last,List.foldl_append]
    change runStep g p r ((List.ofFn (bs (Fin.last n)).1,d (bs (Fin.last n)).2),_)=_
    rw [ih (fun i=>bs i.castSucc)]
    unfold runStep
    rw [scan_rep e d c keys hk guides base hb g hg p r sp sr hp hr,
      normalizeState_rep keys univ e he]
    rfl
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeLadderContext
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeTyped.Numbered UnitRefresh ExecutablePair

variable {I E V : Type} [Fintype I] [LinearOrder I] [Fintype E] [LinearOrder E] [Fintype V] [LinearOrder V]
lemma row_rep (ends : E→Sym2 V) (w : I→E→ℚ) (guides : I→Finset I) (refresh : RefreshSetup) (i : I) :
    row (contextRep ends w guides refresh,index i)=List.ofFn (fun e=>TreeFraction.repr (w i (orderedEnum E e))) := by
  simp [row,contextRep,index,List.getD_eq_getElem?_getD]
lemma guides_rep (ends : E→Sym2 V) (w : I→E→ℚ) (guides : I→Finset I) (refresh : RefreshSetup) (i j : I) :
    guide (contextRep ends w guides refresh,(index i,index j))=decide (j∈guides i) := by
  simp [guide,contextRep,index,List.getD_eq_getElem?_getD,Numbered.set,Numbered.embedding,Numbered.index]
  constructor
  · rintro ⟨a,ha,h⟩
    have he : a=j := (orderedEnum I).symm.injective (Fin.ext h)
    simpa [he] using ha
  · intro hj; exact ⟨j,hj,rfl⟩
lemma pairContext_rep (ends : E→Sym2 V) (w : I→E→ℚ) (guides : I→Finset I) (refresh : RefreshSetup) (i j : I) :
    pairContext (contextRep ends w guides refresh,(index i,index j))=ExecutablePair.contextRep ends (w i) (w j) := by
  simp only [pairContext,row_rep]
  rfl
attribute [local instance] Transport.Sparse.pmOrder
lemma pairDraw_rep (ends : E→Sym2 V) (hloop : ∀ e,¬(ends e).IsDiag)
    (hpar : ∀ e,(Finset.univ.filter (fun f=>ends f=ends e)).card≤2)
    (w : I→E→ℚ) (hw : ∀ i e,0<w i e) (guides : I→Finset I) (refresh : RefreshSetup)
    (i j : I) (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e))
    {k : ℕ} (bits : Fin k→Bool) (other : ExecutableUnit.Bits) :
    pairDraw ((contextRep ends w guides refresh,(index i,index j)),
      ((Numbered.set a.1.val,Numbered.set a.2.val),(List.ofFn bits,other)))=
    (Numbered.set ((Transport.Sparse.pairStepTable ends hloop hpar (w i) (w j) (hw i) (hw j) a).draw k bits).1.val,
     Numbered.set ((Transport.Sparse.pairStepTable ends hloop hpar (w i) (w j) (hw i) (hw j) a).draw k bits).2.val) := by
  unfold pairDraw
  rw [pairContext_rep]
  exact numeric_draw_source ends hloop hpar (w i) (w j) (hw i) (hw j) a bits
end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeErasurePrimitives
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]
lemma program_constant (a : B) : (constant (A:=A) a).program=(constantData (A:=TreeData.Data) (encode a)).program := constantData_program _
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeLadderIndexed
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeTyped.Numbered ExecutableLadder

attribute [local instance] Transport.prodOrder Transport.sumOrder
variable {I : Type} [Fintype I] [LinearOrder I] [Inhabited I]

lemma inl_program_zero (hz : index (default : I)=0) :
    (TreeTyped.inl (A:=I×I) (B:=I)).program=(TreeTyped.inl (A:=ℕ×ℕ) (B:=ℕ)).program := by
  simp only [TreeTyped.inl,Realizer.recode,pair]
  rw [constant_program (default : I) (default : ℕ) (C:=I×I) (D:=ℕ×ℕ) (by change TreeData.nat (index (default : I))=TreeData.nat 0; rw [hz])]
  rfl
lemma inr_program_zero (hz : index (default : I)=0) :
    (TreeTyped.inr (A:=I×I) (B:=I)).program=(TreeTyped.inr (A:=ℕ×ℕ) (B:=ℕ)).program := by
  simp only [TreeTyped.inr,Realizer.recode,pair]
  rw [constant_program (default : I×I) (default : ℕ×ℕ) (C:=I) (D:=ℕ) (by
    change TreeData.Data.cons (TreeData.nat (index (default : I))) (TreeData.nat (index (default : I)))=
      TreeData.Data.cons (TreeData.nat 0) (TreeData.nat 0)
    rw [hz])]
  rfl
lemma lookup_program_zero (d : Finset ℕ) (hz : index (default : I)=0) :
    (lookupRealizer (I:=I) d Numbered.equal).program=(lookupRealizer (I:=ℕ) d natEqual).program := by
  dsimp only [lookupRealizer,filterWith,mapWith,mapStepRealizer,TreeTyped.map,TreeTyped.filter,
    Realizer.congr,composition,pair,choose,fold, Numbered.equal,Realizer.recode]
  simp only [program_constant,encode_list_nil]
  rw [head_program ((default : I),d) ((default : ℕ),d) (by
    change TreeData.Data.cons (TreeData.nat (index (default : I))) (encode d)=
      TreeData.Data.cons (TreeData.nat 0) (encode d)
    rw [hz])]
  rfl
lemma normalize_program_zero (hz : index (default : I)=0) :
    (normalizeStateRealizer (I:=I) (E:=ℕ) Numbered.equal natEqual).program=
      (normalizeStateRealizer (I:=ℕ) (E:=ℕ) natEqual natEqual).program := by
  dsimp only [normalizeStateRealizer,mapWith,mapStepRealizer,Realizer.congr,composition,pair,fold]
  simp only [program_constant,encode_list_nil]
  rw [lookup_program_zero ∅ hz]
  rfl
attribute [local instance] OAI.MatchingFPRAS.NumericLadder.instInhabitedUpdate
lemma none_encode_zero (hz : index (default : I)=0) :
    encode (none : Option (Replica.Update I))=encode (none : Option (Replica.Update ℕ)) := by
  have hd : encode (default : I)=encode (0 : ℕ) := by
    change TreeData.nat (index (default : I))=TreeData.nat 0; rw [hz]
  change encode (false,(false,(((default : I),(default : I)),(default : I))))=
    encode (false,(false,(((0 : ℕ),(0 : ℕ)),(0 : ℕ))))
  simp only [encode_prod,hd]
lemma choice_program_zero (hz : index (default : I)=0) :
    (scanChoiceRealizer (I:=I) typedGuideRealizer Numbered.equal Numbered.lessEqual).program=
      (scanChoiceRealizer guideRealizer natEqual leNat).program := by
  dsimp only [scanChoiceRealizer,updateSetRealizer,updateListRealizer, TreeTyped.map,
    Realizer.congr,composition,pair,fold]
  rw [inl_program_zero hz,inr_program_zero hz]
  rw [constant_program (none : Option (Replica.Update I)) (none : Option (Replica.Update ℕ))
    (none_encode_zero hz) (C:=ScanSetup Context I) (D:=ScanSetup Context ℕ)]
  simp only [program_constant,encode_list_nil]
  rfl
lemma local_program_zero (hz : index (default : I)=0) :
    (localSamplerRealizer (I:=I) typedPairRealizer typedRefreshRealizer Numbered.equal).program=
      (localSamplerRealizer pairRealizer refreshRealizer natEqual).program := by
  dsimp only [localSamplerRealizer,optionCases,sumCases,localPairRealizer,localRefreshRealizer,
    Realizer.congr,Realizer.recode,composition,pair,choose]
  rw [lookup_program_zero (default : Finset ℕ) hz]
  rfl
lemma scan_program_zero (hz : index (default : I)=0) :
    (scanRealizer (I:=I) typedGuideRealizer typedPairRealizer typedRefreshRealizer Numbered.equal Numbered.lessEqual).program=
      (scanRealizer guideRealizer pairRealizer refreshRealizer natEqual leNat).program := by
  dsimp only [scanRealizer,Realizer.congr,composition,pair]
  rw [choice_program_zero hz,local_program_zero hz,draw_program
    (none : Option (Replica.Update I)) (none : Option (Replica.Update ℕ)) (none_encode_zero hz)]
  rfl
lemma typedExecute_program (hz : index (default : I)=0) :
    (typedExecuteRealizer (I:=I)).program=executeRealizer.program := by
  dsimp only [typedExecuteRealizer,executeRealizer,fold,runStepRealizer,Realizer.congr,composition,pair]
  rw [scan_program_zero hz,normalize_program_zero hz]
  rfl
end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeLadderPost
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeTyped.Numbered ExecutableLadder TreePost Turing

variable {I : Type} [Fintype I] [LinearOrder I] [Inhabited I]
omit [Inhabited I] in
lemma encode_indices (xs : List I) : encode (xs.map index)=encode xs := by
  induction xs with
  | nil=>rfl
  | cons a as ih=>simp only [List.map_cons,encode_list_cons,ih]; rfl
omit [Inhabited I] in
lemma numericState_encode (x : StateTable I (Finset ℕ)) : encode (numericState x)=encode x := by
  induction x with
  | nil=>rfl
  | cons a as ih=>
    change TreeData.Data.cons (encode (index a.1,a.2)) (encode (numericState as))=TreeData.Data.cons (encode a) (encode as)
    rw [ih]
    rfl
omit [Inhabited I] in
lemma numericInput_encode (x : TypedInput I) : encode (numericInput x)=encode x := by
  rcases x with ⟨bits,⟨⟨c,u,b⟩,keys,e⟩,s⟩
  simp only [numericInput,numericSetup,encode_prod,Numbered.encode_set,encode_indices,numericState_encode]
end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeLadder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeTyped.Numbered ExecutableLadder UnitRefresh Transport Replica.Ladder

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L} {G : SimpleGraph L}
variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)
variable (rank : L→ℕ) (parent : L→Option L)
variable (hb : RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)
variable (hp : ∀ l p,parent l=some p → rank p < rank l)
variable {T q : ℕ} [Inhabited (Slot T q)]

omit [Inhabited (Slot T q)] in
lemma source_guide (w : BagEdge bags→ℚ) (a : ExecutableDP.Bags) (i j : Slot T q) :
    typedGuide (sourceContext (T:=T) (q:=q) rank parent w a,(i,j))=decide (j∈guides i) :=
  guides_rep (fun e : BagEdge bags=>e.val.val.1) (rationalSlotWeight (T:=T) (q:=q) w) guides
    (ExecutableRefresh.storedCatalog (a,List.range (Fintype.card L)),
      ((a,ExecutableDP.parentRep (numberedParent parent)),(Materialized.plan (numberedRank rank)).map Fin.val)) i j
omit [Inhabited (Slot T q)] in
lemma source_pair (w : BagEdge bags→ℚ) (a : ExecutableDP.Bags) (i j : Slot T q)
    (s : BagPM bags×BagPM bags) {k : ℕ} (bits : LocalBits V k) :
    typedPair ((sourceContext (T:=T) (q:=q) rank parent w a,(i,j)),
      ((Numbered.set s.1.val,Numbered.set s.2.val),localBitsRep bits))=
      (Numbered.set (Transport.pairDraw hbags hG w k i j s bits).1.val,
       Numbered.set (Transport.pairDraw hbags hG w k i j s bits).2.val) := by
  exact pairDraw_rep (fun e : BagEdge bags=>e.val.val.1) (fun e=>e.val.property)
    (parallels_bound hbags hG) (rationalSlotWeight w) (rationalSlotWeight_pos w) guides _ i j s bits.1 _
omit [Inhabited (Slot T q)] in
lemma source_refresh (w : BagEdge bags→ℚ) (M : BagPM bags)
    (a : ExecutableDP.Bags) (ha : List.Forall₂ List.Perm a (ExecutableDP.orderedRep (numberedBags bags)))
    (i : Slot T q) {k : ℕ} (bits : LocalBits V k) :
    typedRefresh ((sourceContext (T:=T) (q:=q) rank parent w a,i),localBitsRep bits)=
      Numbered.set (baseDraw rank parent hb hne hp M k bits).val := by
  exact ExecutableRefresh.refresh_sampleMatching bags rank parent hb hne hp M a ha bits.2

attribute [local instance] OAI.MatchingFPRAS.NumericLadder.instDecidableEqBagPM
omit [Inhabited (Slot T q)] in
lemma source_run (hq : 0<q) (w : BagEdge bags→ℚ) (M : BagPM bags)
    (a : ExecutableDP.Bags) (ha : List.Forall₂ List.Perm a (ExecutableDP.orderedRep (numberedBags bags)))
    {k n : ℕ} (s : Slot T q→BagPM bags) (bits : Fin n→ScanBits V k) :
    let keys := List.ofFn (orderedEnum (Slot T q))
    let c := sourceContext (T:=T) (q:=q) rank parent w a
    let setup := ((c,((Finset.univ : Finset (Slot T q)),base T q)),(keys,Numbered.set (Finset.univ : Finset (BagEdge bags))))
    typedExecute (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
      (setup,stateRep keys (fun i=>Numbered.set (s i).val)))=
      (setup,stateRep keys (fun i=>Numbered.set
        (ladderRun hbags hG rank parent hb hne hp hq w M k n s bits i).val)) := by
  dsimp only
  have hk : ∀ i : Slot T q,i∈List.ofFn (orderedEnum (Slot T q)) := by
    intro i
    simp only [List.mem_ofFn]
    exact ⟨(orderedEnum (Slot T q)).symm i,Equiv.apply_symm_apply _ _⟩
  have hu : ∀ m : BagPM bags,Numbered.set m.val⊆Numbered.set (Finset.univ : Finset (BagEdge bags)) := by
    intro m
    exact Finset.map_subset_map.mpr (Finset.subset_univ _)
  exact scanRun_rep (fun m : BagPM bags=>Numbered.set m.val) localBitsRep
    (sourceContext (T:=T) (q:=q) rank parent w a) (List.ofFn (orderedEnum (Slot T q))) hk _ hu
    guides (base T q) (base_nonempty T q hq) typedGuide (source_guide (T:=T) (q:=q) rank parent w a)
    typedPair typedRefresh (Transport.pairDraw hbags hG w k) (fun _=>baseDraw rank parent hb hne hp M k)
    (fun i j s b=>source_pair (T:=T) (q:=q) hbags hG rank parent w a i j s b) (fun i b=>source_refresh (T:=T) (q:=q) rank parent hb hne hp w M a ha i b) s bits

end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeNumericMarking
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction ExecutableLadder ExecutableMarking ExecutableOptions TreeTyped.Numbered UnitRefresh

variable {E : Type} [Fintype E] [LinearOrder E]
lemma table_rep (f : E→WeightedOptions (Fin 3)) (e : E) :
    table (tableRep f,index e)=ExecutableOptions.repr Fin.val (f e) := by
  simp only [table,tableRep,index,List.getD,List.getElem?_ofFn,
    ((orderedEnum E).symm e).isLt,↓reduceDIte,Fin.eta,Option.getD_some,Equiv.apply_symm_apply]

lemma assign_rep (f : E→WeightedOptions (Fin 3)) (keys : List E) (hk : ∀ e,e∈keys)
    (s : Finset E) {k : ℕ} (bits : E→Fin k→Bool) :
    assign ((tableRep f,keys.map (fun e=>(index e,List.ofFn (bits e)))),Numbered.set s)=
      numericMarks s (fun e=>(f e).draw k (bits e)) := by
  unfold assign ExecutableMarking.assign numericMarks
  rw [sort_set,List.map_map]
  apply List.map_congr_left
  intro e _
  dsimp only [Function.comp_def,markEdge]
  rw [table_rep,lookup_image [] keys index (fun e=>List.ofFn (bits e)) index_injective e (hk e),draw_repr Fin.val (f e) 0 (bits e)]

end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreePrepareLadder
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder

lemma baseSet_source (n : ℕ) (ft fq : List Bool) (ws : List Fraction) :
    baseSet ((n,ft),(fq,ws))=Numbered.set (base ft.length fq.length) := by
  rw [baseSet,slotUniverse_source]
  ext j
  simp only [Finset.mem_filter,Numbered.set,Finset.mem_map,Finset.mem_univ,true_and,Numbered.embedding]
  constructor
  · rintro ⟨⟨z,rfl⟩,h⟩
    refine ⟨z,?_,rfl⟩
    rw [mem_base]
    simpa [baseTest,slot_index_div] using h
  · rintro ⟨z,h,rfl⟩
    refine ⟨⟨z,rfl⟩,?_⟩
    simpa [baseTest,slot_index_div] using (mem_base z).mp h

end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreePrepared
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder UnitRefresh Transport

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

lemma execute_state {I : Type} [Fintype I] [LinearOrder I] [Inhabited I]
    (hz : index (default : I)=0) (x : TypedInput I) :
    (execute (numericInput x)).2=numericState (typedExecute x).2 := by
  apply list_encode_injective (pair_encode_injective nat_encode_injective finsetNat_encode_injective)
  have h:=TreePost.sameProgram_encode executeRealizer typedExecuteRealizer (typedExecute_program hz).symm
    _ _ (numericInput_encode x)
  exact (TreeData.Data.cons.inj h).2.trans (numericState_encode _).symm

variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L}

lemma prepareContext_source (rank : L→ℕ) (parent : L→Option L) (w : BagEdge bags→ℚ)
    (hw : ∀ e,0≤w e) (a : ExecutableDP.Bags) (ft fq : List Bool) :
    prepareContext (sourcePrepared rank parent w a ft fq)=
      sourceContext (T:=ft.length) (q:=fq.length) rank parent w a := by
  unfold prepareContext sourcePrepared
  dsimp only
  rw [weightRows_source w hw ft fq,guideRows_source]
  rfl

lemma slots_source (n : ℕ) (ft fq : List Bool) (ws : List Fraction) :
    slots ((n,ft),(fq,ws))=(List.ofFn (orderedEnum (Slot ft.length fq.length))).map index := by
  rw [List.map_ofFn]
  exact range_slot_indices ft.length fq.length

lemma prepareSetup_source
    (rank : L→ℕ) (parent : L→Option L) (w : BagEdge bags→ℚ)
    (hw : ∀ e,0≤w e) (a : ExecutableDP.Bags) (ft fq : List Bool) :
    prepareSetup (sourcePrepared rank parent w a ft fq)=numericSetup
      ((sourceContext (T:=ft.length) (q:=fq.length) rank parent w a,(Finset.univ,base ft.length fq.length)),
        (List.ofFn (orderedEnum (Slot ft.length fq.length)),Numbered.set (Finset.univ : Finset (BagEdge bags)))) := by
  unfold prepareSetup
  rw [prepareContext_source rank parent w hw a ft fq]
  dsimp only [sourcePrepared]
  rw [slotUniverse_source,baseSet_source,slots_source]
  rfl

lemma prepareState_source (ft fq : List Bool) [Inhabited (Slot ft.length fq.length)]
    (rank : L→ℕ) (parent : L→Option L) (w : BagEdge bags→ℚ)
    (hw : ∀ e,0≤w e) (a : ExecutableDP.Bags) (M : BagPM bags) :
    prepareState (sourcePrepared rank parent w a ft fq,Numbered.set M.val)=
      (numericSetup ((sourceContext (T:=ft.length) (q:=fq.length) rank parent w a,(Finset.univ,base ft.length fq.length)),
        (List.ofFn (orderedEnum (Slot ft.length fq.length)),Numbered.set (Finset.univ : Finset (BagEdge bags)))),
       numericState (stateRep (List.ofFn (orderedEnum (Slot ft.length fq.length))) (fun _=>Numbered.set M.val))) := by
  unfold prepareState
  dsimp only
  rw [prepareSetup_source rank parent w hw a ft fq]
  refine Prod.ext rfl ?_
  dsimp only [sourcePrepared]
  rw [slots_source]
  simp only [numericState,stateRep,List.map_map,Function.comp_def]

lemma lookup_numeric_state {I : Type} [Fintype I] [LinearOrder I] [Inhabited I]
    (keys : List I) (f : I→Finset ℕ) (i : I) (hi : i∈keys) :
    lookup ∅ (numericState (stateRep keys f),index i)=f i := by
  simp only [numericState,stateRep,List.map_map,Function.comp_def]
  exact lookup_image ∅ keys index f index_injective i hi
end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreePreparedTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder UnitRefresh Transport

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L} {G : SimpleGraph L}
variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)
variable (rank : L→ℕ) (parent : L→Option L)
variable (hb : RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)
variable (hp : ∀ l p,parent l=some p → rank p < rank l)

lemma preparedTop_source (ft fq : List Bool) (hq : 0<fq.length)
    (w : BagEdge bags→ℚ) (hw : ∀ e,0≤w e) (M : BagPM bags)
    (a : ExecutableDP.Bags) (ha : List.Forall₂ List.Perm a (ExecutableDP.orderedRep (numberedBags bags)))
    {k n : ℕ} (bits : Fin n→ScanBits V k) :
    preparedTop (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
      (sourcePrepared rank parent w a ft fq,Numbered.set M.val))=
      Numbered.set (ladderRun hbags hG rank parent hb hne hp hq w M k n (fun _=>M) bits
        (toLex ((0 : Fin (ft.length+1)),(⟨0,hq⟩ : Fin fq.length)))).val := by
  let z : Slot ft.length fq.length := toLex ((0 : Fin (ft.length+1)),(⟨0,hq⟩ : Fin fq.length))
  let : Inhabited (Slot ft.length fq.length) := ⟨z⟩
  have hz : index (default : Slot ft.length fq.length)=0 := slot_default_zero _ _ hq
  let keys := List.ofFn (orderedEnum (Slot ft.length fq.length))
  let setup := ((sourceContext (T:=ft.length) (q:=fq.length) rank parent w a,
    ((Finset.univ : Finset (Slot ft.length fq.length)),base ft.length fq.length)),
    (keys,Numbered.set (Finset.univ : Finset (BagEdge bags))))
  let tx : TypedInput (Slot ft.length fq.length) :=
    (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
      (setup,stateRep keys (fun _=>Numbered.set M.val)))
  have hi : (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
      prepareState (sourcePrepared rank parent w a ft fq,Numbered.set M.val))=numericInput tx := by
    refine Prod.ext rfl ?_
    exact prepareState_source ft fq rank parent w hw a M
  unfold preparedTop preparedRun
  dsimp only
  rw [hi,execute_state hz]
  have hr := source_run (T:=ft.length) (q:=fq.length) hbags hG rank parent hb hne hp hq w M a ha
    (fun _=>M) bits
  change typedExecute tx=(setup,stateRep keys (fun i=>Numbered.set
    (ladderRun hbags hG rank parent hb hne hp hq w M k n (fun _=>M) bits i).val)) at hr
  rw [hr]
  change lookup ∅ (numericState (stateRep keys (fun i=>Numbered.set
    (ladderRun hbags hG rank parent hb hne hp hq w M k n (fun _=>M) bits i).val)),0)=_
  have hz' : index z=0 := hz
  have hmem : z∈keys := by
    simp only [keys,List.mem_ofFn]
    exact ⟨(orderedEnum _).symm z,Equiv.apply_symm_apply _ _⟩
  have hl := lookup_numeric_state keys (fun i=>Numbered.set
    (ladderRun hbags hG rank parent hb hne hp hq w M k n (fun _=>M) bits i).val) z hmem
  simpa only [hz'] using hl

end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreePreparedMarked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction ExecutableLadder TreeTyped.Numbered UnitRefresh NumericLadder

open Replica.Ladder Transport

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L} {G : SimpleGraph L}
variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)
variable (rank : L→ℕ) (parent : L→Option L)
variable (hb : RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)
variable (hp : ∀ l p,parent l=some p → rank p < rank l)
lemma sample_source_oai (ft fq : List Bool) (hq : 0<fq.length)
    (w : BagEdge bags→ℚ) (hw : ∀ e,0≤w e) (M : BagPM bags)
    (a : ExecutableDP.Bags) (ha : List.Forall₂ List.Perm a (ExecutableDP.orderedRep (numberedBags bags)))
    (f : BagEdge bags→WeightedOptions (Fin 3))
    {k n km : ℕ} (bits : Fin n→ScanBits V k) (mb : BagEdge bags→Fin km→Bool) :
    sample (((sourcePrepared rank parent w a ft fq,Numbered.set M.val),tableRep f),
      (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
        (List.ofFn (orderedEnum (BagEdge bags))).map (fun e=>(index e,List.ofFn (mb e)))))=
      numericMarks (ladderRun hbags hG rank parent hb hne hp hq w M k n (fun _=>M) bits
        (toLex ((0 : Fin (ft.length+1)),(⟨0,hq⟩ : Fin fq.length)))).val
          (fun e=>(f e).draw km (mb e)) := by
  rw [sample,preparedTop_source hbags hG rank parent hb hne hp ft fq hq w hw M a ha bits]
  apply assign_rep
  intro e
  exact List.mem_ofFn.mpr ⟨(orderedEnum _).symm e,Equiv.apply_symm_apply _ _⟩
end MatchingFPRAS.NumericMarking

end OAI
end

theorem solution : type_of% @OAI.MatchingFPRAS.NumericMarking.sample_source_oai := @OAI.MatchingFPRAS.NumericMarking.sample_source_oai
