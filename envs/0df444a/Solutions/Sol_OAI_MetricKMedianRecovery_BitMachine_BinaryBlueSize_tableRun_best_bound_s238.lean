-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryBlueSize.tableRun_best_bound_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:26:26.078399+00:00
-- url     : https://prove2.me/submissions/c81958aa-6e60-40d8-b0d8-05305760a5f5

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K020
import Definitions.Def_Q238K022

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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
attribute [local irreducible] WordList.mapWith WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run IntegerArray.sumWords 
open WordOperations BinaryArithmetic
namespace WordList
lemma length_member_le_encode {ws : List (List Bool)} {w : List Bool} (hw : w∈ws) :
    w.length≤(encode ws).length := by
  induction ws with
  | nil => simp only [List.not_mem_nil] at hw
  | cons v vs ih =>
    simp only [List.mem_cons] at hw
    rw [encode,length_cons]
    rcases hw with rfl|hv
    · omega
    · have hh := ih hv
      omega
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Height
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalHeight
open scoped BigOperators

lemma Height.mono {q : ℚ} {b c : ℕ} (h : Height q b) (hc : b ≤ c) : Height q c :=
  ⟨h.1.trans (Nat.pow_le_pow_right (by norm_num) hc),h.2.trans (Nat.pow_le_pow_right (by norm_num) hc)⟩

lemma zero (b : ℕ) : Height 0 b := by
  constructor
  · simp
  · simpa using (one_le_pow₀ (by norm_num : (1:ℕ)≤2) : 1≤2^b)

lemma of_fraction (p : ℤ) (d b : ℕ) (hd : 0<d) (hp : p.natAbs≤2^b) (hdb : d≤2^b) :
    Height ((p:ℚ)/(d:ℚ)) b := by
  constructor
  · by_cases hz : p=0
    · simp [hz]
    · have hh := Rat.num_dvd p (by exact_mod_cast hd.ne' : (d:ℤ)≠0)
      rw [←Rat.intCast_div_eq_divInt] at hh
      simp only [Int.cast_natCast] at hh
      exact (Nat.le_of_dvd (by omega : 0<p.natAbs) (Int.natAbs_dvd_natAbs.mpr hh)).trans hp
  · have hh := Rat.den_dvd p (d:ℤ)
    rw [←Rat.intCast_div_eq_divInt] at hh
    simp only [Int.cast_natCast] at hh
    exact (Nat.le_of_dvd hd (Int.natCast_dvd_natCast.mp hh)).trans hdb

lemma Height.add {q r : ℚ} {b c : ℕ} (hq : Height q b) (hr : Height r c) :
    Height (q+r) (b+c+1) := by
  have hn : (q.num*(r.den:ℤ)+r.num*(q.den:ℤ)).natAbs≤2^(b+c+1) := by
    calc
      _ ≤ q.num.natAbs*r.den+r.num.natAbs*q.den := by
        simpa only [Int.natAbs_mul,Int.natAbs_natCast] using
          Int.natAbs_add_le (q.num*(r.den:ℤ)) (r.num*(q.den:ℤ))
      _ ≤ 2^b*2^c+2^c*2^b := Nat.add_le_add (Nat.mul_le_mul hq.1 hr.2) (Nat.mul_le_mul hr.1 hq.2)
      _ = _ := by rw [pow_succ,pow_add]; ring
  have hd : q.den*r.den≤2^(b+c+1) := by
    have hh := Nat.mul_le_mul hq.2 hr.2
    rw [←pow_add] at hh
    exact hh.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have he : q+r=((q.num*(r.den:ℤ)+r.num*(q.den:ℤ):ℤ):ℚ)/(q.den*r.den:ℕ) := by
    nth_rw 1 [←Rat.num_div_den q]
    nth_rw 1 [←Rat.num_div_den r]
    push_cast
    convert div_add_div (q.num:ℚ) (r.num:ℚ) (by exact_mod_cast q.den_nz : (q.den:ℚ)≠0) (by exact_mod_cast r.den_nz : (r.den:ℚ)≠0) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  rw [he]
  exact of_fraction _ _ _ (Nat.mul_pos q.den_pos r.den_pos) hn hd

end MetricKMedianRecovery.RationalHeight

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Iterate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalHeight
lemma list_sum (xs : List ℚ) (b : ℕ) (hx : ∀ q∈xs,Height q b) :
    Height xs.sum (xs.length*(b+1)) := by
  induction xs with
  | nil => simpa using zero 0
  | cons x xs ih =>
    simp only [List.sum_cons,List.length_cons]
    have hh := (hx x (by simp)).add (ih (fun q hq=>hx q (by simp [hq])))
    convert hh using 1 <;> first | rfl | ring
end MetricKMedianRecovery.RationalHeight

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
lemma input_height (q : ℚ) : RationalHeight.Height q (encode q).length := by
  rw [encode_length]
  constructor
  · apply Nat.le_of_lt
    apply Nat.size_le.mp
    omega
  · apply Nat.le_of_lt
    apply Nat.size_le.mp
    omega
end BinaryRational
namespace RationalArray
open RationalHeight
lemma input_height (xs : List ℚ) (q : ℚ) (hq : q∈xs) : Height q (encode xs).length := by
  exact (BinaryRational.input_height q).mono
    (WordList.length_member_le_encode (List.mem_map.mpr ⟨q,hq,rfl⟩))
end RationalArray
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
variable {n : ℕ}
lemma values_sort (S : Finset (Fin n)) : (values S).sort (·≤·)=(S.sort (·≤·)).map Fin.val := by
  let f : Fin n ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
  have hh := Finset.map_sort f S (·≤·) (·≤·) (fun a _ b _=>show a≤b↔a.val≤b.val from Iff.rfl)
  simpa only [f,Finset.map_eq_image,values,Function.Embedding.coeFn_mk] using hh.symm
lemma encode_eq (S : Finset (Fin n)) : encode S=WordList.encode ((S.sort (·≤·)).map (fun i=>i.val.bits)) := by
  rw [encode,BinaryNatSet.encode,BinaryNatSet.pack,values_sort,List.map_map]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryFinSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordSubsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Subsets
open WordOperations
variable {A : Type*}
lemma encode_bound (ws : List (List Bool)) (B : ℕ) (h : ∀ w∈ws,w.length≤B) :
    (encode ws).length≤ws.length*(2*B+2) := by
  induction ws with
  | nil=>simp [encode]
  | cons w ws ih=>
    have hw:=h w (by simp)
    have ht:=ih (fun x hx=>h x (by simp [hx]))
    simp only [encode,length_cons,List.length_cons]
    nlinarith
end MetricKMedianRecovery.BitMachine.WordList.Subsets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueTable
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L A : Type*} [LinearOrder L]
lemma lookup_map (vs : List (Finset L)) (f : Finset L→Candidate (List A)) (U : Finset L) (h : U∈vs) :
    lookup U (vs.map (fun V=>(V,f V)))=f U := by
  induction vs with
  | nil=>simp at h
  | cons V vs ih=>
    simp only [List.map_cons,lookup]
    by_cases he : U=V
    · simp [he]
    · rw [ite_eq_right he]
      exact ih (List.mem_cons.mp h |>.resolve_left he)
lemma mem_states (U V : Finset L) : V∈states U ↔ V⊆U := by
  simp only [states,List.mem_map,List.mem_sublists]
  constructor
  · rintro ⟨xs,hxs,rfl⟩
    intro l hl
    exact (Finset.mem_sort (·≤·)).mp (hxs.subset (List.mem_toFinset.mp hl))
  · intro h
    refine ⟨(U.sort (·≤·)).filter (fun l=>l∈V),List.filter_sublist,?_⟩
    ext l
    simp only [List.mem_toFinset,List.mem_filter,Finset.mem_sort,decide_eq_true_eq]
    exact ⟨And.right,fun hv=>⟨h hv,hv⟩⟩
lemma states_length (U : Finset L) : (states U).length=2^U.card := by
  simp [states,List.length_sublists]
lemma tables_eq (C : Finset L→Candidate (List A)) (U : Finset L) (t : ℕ) :
    tables C U t=(states U).map (fun V=>(V,recurrence C t V)) := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    simp only [tables,nextTable,ih]
    apply List.map_congr_left
    intro W hW
    have hWU := (mem_states U W).mp hW
    congr 1
    conv_rhs => rw [recurrence]
    congr 1
    apply List.map_congr_left
    intro V _
    rw [lookup_map _ _ _ ((mem_states U (W\V)).mpr ((Finset.sdiff_subset).trans hWU))]
lemma lookup_tables (C : Finset L→Candidate (List A)) (U W : Finset L) (t : ℕ) (hW : W⊆U) :
    lookup W (tables C U t)=recurrence C t W := by
  rw [tables_eq,lookup_map _ _ _ ((mem_states U W).mpr hW)]
lemma tableRun_spec (C : Finset L→Candidate (List A)) (U : Finset L) (c : ℕ) :
    tableRun C U c=(tables C U c,select ((List.range c).map (fun t=>recurrence C (t+1) U))) := by
  induction c with
  | zero=>rfl
  | succ c ih=>
    rw [tableRun,Function.iterate_succ_apply']
    change tableStep C U (tableRun C U c)=_
    rw [ih]
    simp only [tableStep,show nextTable C U (tables C U c)=tables C U (c+1) from rfl,
      lookup_tables C U U (c+1) le_rfl,List.range_succ,List.map_append,
      List.map_singleton,select,List.foldl_append,List.foldl_cons,List.foldl_nil]
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BluePlan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y]
omit [LinearOrder R] [LinearOrder Y] in
lemma route_length (U : Finset L) (xs : List (Atom L R Y)) (h : Route U xs) : xs.length=U.card := by
  rw [←h.2,List.toFinset_card_of_nodup h.1]
  exact (List.length_map ..).symm
end MetricKMedianRecovery.BlueDP
namespace MetricKMedianRecovery.BitMachine.BinaryBlueSize
open WordOperations WordList RationalHeight
variable {L R : Type*} [LinearOrder L] [LinearOrder R] {n : ℕ}
omit [LinearOrder L] in
lemma atom_bound (el : L→List Bool) (er : R→List Bool) (B : Finset R) (F : Finset (Fin n))
    (label : R→L) (q : R→Fin n→ℚ) (a : BlueDP.Atom L R (Fin n)) (h : a.2.1∈B ∧ label a.2.1=a.1 ∧ a.2.2∈F) :
    let N:=(BinaryBlueItem.records el er B label q).length
    (BinaryBlueItem.atomEnc el er a).length≤5*N+2 ∧ Height (q a.2.1 a.2.2) N := by
  dsimp only
  have hr : (BinaryBlueItem.record el er label q a.2.1).length≤(BinaryBlueItem.records el er B label q).length :=
    length_member_le_encode (List.mem_map.mpr ⟨a.2.1,(Finset.mem_sort (·≤·)).mpr h.1,rfl⟩)
  have hq := RationalArray.input_height (List.ofFn (q a.2.1)) (q a.2.1 a.2.2) (List.mem_ofFn.mpr ⟨a.2.2,rfl⟩)
  have hn : n≤(RationalArray.encode (List.ofFn (q a.2.1))).length := by
    simpa only [RationalArray.encode,List.length_map,List.length_ofFn] using
      length_le_encode ((List.ofFn (q a.2.1)).map BinaryRational.encode)
  have hb : a.2.2.val.bits.length≤n := (by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr Nat.lt_two_pow_self : a.2.2.val.bits.length≤a.2.2.val).trans (Nat.le_of_lt a.2.2.isLt)
  simp only [BinaryBlueItem.record,pairBits_length] at hr
  refine ⟨?_,hq.mono (by omega)⟩
  simp only [BinaryBlueItem.atomEnc,pairBits_length]
  rw [←h.2.1]
  omega
lemma candidate_bound (el : L→List Bool) (er : R→List Bool) (B : Finset R) (F : Finset (Fin n))
    (label : R→L) (q : R→Fin n→ℚ) (U : Finset L) (c : ℕ) (x : BlueDP.Candidate (List (BlueDP.Atom L R (Fin n))))
    (hx : BlueDP.Spec B F label q U c x) :
    let N:=(BinaryBlueItem.records el er B label q).length
    (BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueItem.atomEnc el er)) x).length≤
      40*(U.card+1)*(N+1) := by
  dsimp only
  cases x with
  | none=>simp [BinaryBlueChoice.encode]
  | some x=>
    rcases x with ⟨k,xs⟩
    obtain ⟨hr,hv,_,hk⟩:=hx
    have hl:=BlueDP.route_length U xs hr
    have ha (a) (hax : a∈xs):=(atom_bound el er B F label q a (hv a hax)).1
    have hheight : Height k (xs.length*((BinaryBlueItem.records el er B label q).length+1)) := by
      rw [hk]
      simpa only [BlueDP.cost,List.length_map] using RationalHeight.list_sum
        (xs.map (fun a=>q a.2.1 a.2.2)) (BinaryBlueItem.records el er B label q).length (by
          intro z hz
          obtain ⟨a,hax,rfl⟩:=List.mem_map.mp hz
          exact (atom_bound el er B F label q a (hv a hax)).2)
    have hscore := BinaryRational.encode_height hheight
    have hlist := Subsets.encode_bound (xs.map (BinaryBlueItem.atomEnc el er))
      (5*(BinaryBlueItem.records el er B label q).length+2) (by
        intro z hz
        obtain ⟨a,hax,rfl⟩:=List.mem_map.mp hz
        exact ha a hax)
    simp only [List.length_map] at hlist
    simp only [BinaryBlueChoice.encode,WordList.encode,length_cons,List.length_nil,pairBits_length,BinaryBlueMerge.listEnc]
    rw [←hl]
    nlinarith
end MetricKMedianRecovery.BitMachine.BinaryBlueSize

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueTableSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueSize
open WordOperations WordList RationalHeight
variable {n m : ℕ} {R : Type*} [LinearOrder R]
lemma states_bounds (U : Finset (Fin m)) (N : ℕ) (hN : (encode ((BlueDP.states U).map BinaryFinSet.encode)).length≤N) :
    U.card≤N ∧ 2^U.card≤N ∧ ∀ W⊆U,(BinaryFinSet.encode W).length≤N := by
  have hw (W : Finset (Fin m)) (hW : W⊆U) : (BinaryFinSet.encode W).length≤N :=
    (length_member_le_encode (List.mem_map.mpr ⟨W,(BlueDP.mem_states U W).mpr hW,rfl⟩)).trans hN
  have hc : U.card≤(BinaryFinSet.encode U).length := by
    simpa only [BinaryFinSet.encode_eq,List.length_map,Finset.length_sort] using
      length_le_encode ((U.sort (·≤·)).map (fun i=>i.val.bits))
  refine ⟨hc.trans (hw U le_rfl),?_,hw⟩
  have hp : 2^U.card≤(encode ((BlueDP.states U).map BinaryFinSet.encode)).length := by
    simpa only [List.length_map,BlueDP.states_length] using length_le_encode ((BlueDP.states U).map BinaryFinSet.encode)
  exact hp.trans hN
lemma tableRun_best_bound_s238_oai (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m)
    (q : R→Fin n→ℚ) (U : Finset (Fin m)) (t N : ℕ)
    (hr : (BinaryBlueItem.records (fun i=>i.val.bits) er B label q).length≤N)
    (hs : (encode ((BlueDP.states U).map BinaryFinSet.encode)).length≤N) :
    (BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueItem.atomEnc (fun i : Fin m=>i.val.bits) er))
      (BlueDP.tableRun (BlueDP.block B F label q) U t).2).length≤40*(N+1)^2 := by
  rw [BlueDP.tableRun_spec]
  dsimp only
  have hp : BlueDP.Spec B F label q U t (BlueDP.select ((List.range t).map (fun j=>BlueDP.recurrence (BlueDP.block B F label q) (j+1) U))) := by
    apply BlueDP.select_spec _ _ trivial
    intro z hz
    obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hz
    exact BlueDP.spec_mono B F label q U (j+1) t (by have hh:=List.mem_range.mp hj;omega) _ (BlueDP.recurrence_spec B F label q (j+1) U)
  apply (candidate_bound (fun i : Fin m=>i.val.bits) er B F label q U t _ hp).trans
  have hu := (states_bounds U N hs).1
  calc
    _ ≤40*(N+1)*(N+1) := by gcongr
    _ = _ := by ring
end MetricKMedianRecovery.BitMachine.BinaryBlueSize

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryBlueSize.tableRun_best_bound_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.BitMachine.BinaryBlueSize.tableRun_best_bound_s238_oai.{u_1}
