-- Prove2me | solution 1 for OAI.UniformKServer.UniformWrapper.live_next
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:59:42.643625+00:00
-- url     : https://prove2.me/submissions/ecce8ecd-c56a-42a9-83c0-33aabb6210e6

import Mathlib
import Definitions.Def_UniformKServer
import Definitions.Def_Q220Uk007
import Definitions.Def_Q220Uk008

section
-- module Solutions.Q220_UK.UniformKServer_RawTyped
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits _root_.OAI.UniformKServer.lazyPath_nil_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section

namespace UniformKServer.RawTyped
open RawArithmetic RawWords RawTable RawPath

theorem config_get {n k : ℕ} (c : Configuration n k) (j : Fin k) :
    (config c).getD j.val 0=(c j).val := by
  rw [List.getD_eq_getElem _ _ (by simp [config])]
  simp [config]

theorem config_set {n k : ℕ} (c : Configuration n k) (r : Fin n) (j : Fin k) :
    (config c).set j.val r.val=config (serve c r j) := by
  apply List.ext_getElem
  · simp [config]
  · intro i hi hj
    simp only [List.length_set,List.length_ofFn,config] at hi hj ⊢
    rw [List.getElem_set]
    simp only [List.getElem_ofFn,serve,Function.update_apply]
    by_cases h : j.val=i
    · have he : (⟨i,hj⟩:Fin k)=j := Fin.ext h.symm
      simp [h,he]
    · have he : (⟨i,hj⟩:Fin k)≠j := by intro he;exact h (congrArg Fin.val he).symm
      simp [h,he]

end UniformKServer.RawTyped

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawBinary
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawProgram.unpack_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawBinary
open Primrec RawCertificate
attribute [fun_prop] Primrec.list_tail

theorem value_bits (a : ℕ) : value a.bits=a := by
  induction a using Nat.binaryRec' with
  | zero=>rfl
  | bit b n h ih=>rw [Nat.bits_append_bit n b h,value_cons,ih]

@[simp] theorem read_natCode (a : ℕ) (w : List Bool) : readNat (natCode a++w)=(a,w) := by
  have ht : ((natCode a++w).takeWhile id).length=a.bits.length := by
    simp [natCode,List.append_assoc]
  dsimp only [readNat]
  rw [ht]
  have hd : (natCode a++w).drop (a.bits.length+1)=a.bits++w := by
    simp [natCode,List.append_assoc,List.drop_append]
  rw [hd]
  simp [value_bits]

@[simp] theorem read_rationalCode (a : ℚ) (w : List Bool) :
    readQ (rationalCode a++w)=(RawMetric.present a,w) := by
  simp only [readQ,rationalCode,List.cons_append,List.tail_cons,List.append_assoc,read_natCode,
    RawMetric.present]

end UniformKServer.RawBinary

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawBits
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                              
section

namespace UniformKServer.RawBits
open Primrec

 theorem bits_value (w : List Bool) : (RawBinary.value (w++[true])).bits=w++[true] := by
  induction w with
  | nil=>simp
  | cons b w ih=>
    simp only [List.cons_append,RawBinary.value_cons]
    rw [Nat.bits_append_bit _ _ (fun h=>by
      have hh:=congrArg Nat.bits h
      rw [ih] at hh
      simp at hh),ih]

open Turing.PartrecToTM2

end UniformKServer.RawBits

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BitSampling
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.BitSampling

theorem exact_row_proof {k b : ℕ} (N : Fin k → ℕ) (hN : ∑ j, N j = 2^b) :
    (∀ coins, 0 < N (row N hN coins)) ∧
    (∀ coins, cumulative N (row N hN coins) ≤ (bitsEquiv b coins).val ∧
      (bitsEquiv b coins).val < cumulative N (row N hN coins) + N (row N hN coins)) ∧
    (∀ f : Fin k → ℝ,
      (∑ coins : Fin b → Bool, f (row N hN coins)) / (2^b : ℕ) =
        ∑ j, (N j : ℝ) / (2^b : ℕ) * f j) := by
  let e : (Fin b → Bool) ≃ ((j : Fin k) × Fin (N j)) :=
    (bitsEquiv b).trans ((finCongr hN).symm.trans finSigmaFinEquiv.symm)
  refine ⟨?_, ?_, ?_⟩
  · intro coins
    exact Nat.zero_lt_of_lt (e coins).2.isLt
  · intro coins
    have he := congrArg Fin.val (finSigmaFinEquiv.apply_symm_apply
      ((finCongr hN).symm (bitsEquiv b coins)))
    rw [finSigmaFinEquiv_apply] at he
    change cumulative N (row N hN coins) + (e coins).2.val = (bitsEquiv b coins).val at he
    have ht := (e coins).2.isLt
    change (e coins).2.val < N (row N hN coins) at ht
    omega
  · intro f
    have hs : (∑ coins : Fin b → Bool, f (row N hN coins)) =
        ∑ j, (N j : ℝ) * f j := by
      calc
        _ = ∑ v : (j : Fin k) × Fin (N j), f v.1 :=
          e.sum_comp (fun v => f v.1)
        _ = _ := by simp [Fintype.sum_sigma]
    rw [hs, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring


end UniformKServer.BitSampling



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawMarks
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawFallback.endpoint_bits _root_.OAI.UniformKServer.RawFallback.nextSeen_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                               
section

namespace UniformKServer.RawMarks
open RawTyped

theorem length_bits {a : ℕ} (A : Finset (Fin a)) : (bits A).length=a := by simp [bits]

@[simp] theorem pick_bits {a : ℕ} (ha : 0<a) (A : Finset (Fin a)) :
    pick (bits A)=(Fallback.pick ha A).val := by
  by_cases h : A.Nonempty
  · let j:=A.min' h
    have hj : j.val<(bits A).length := by simp [length_bits]
    have hf : (bits A).findIdx id=j.val := by
      apply (List.findIdx_eq hj).mpr
      constructor
      · simpa [bits] using Finset.min'_mem A h
      · intro i hi
        simp only [bits,List.getElem_ofFn,id_eq,decide_eq_false_iff_not]
        intro hm
        have hh:=Finset.min'_le A (⟨i,lt_trans hi j.isLt⟩ : Fin a) hm
        exact (Nat.not_le_of_lt hi) hh
    simp only [pick,hf,ite_eq_left hj,Fallback.pick,dite_eq_left h,j]
  · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst A
    have hf : (bits (∅ : Finset (Fin a))).findIdx id=a := by
      calc
        _ = (bits (∅ : Finset (Fin a))).length := List.findIdx_eq_length_of_false (by
          intro b hb
          simp [bits] at hb
          simp [hb])
        _ = a := length_bits _
    simp [pick,hf,length_bits,Fallback.pick]

end UniformKServer.RawMarks

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawFallback
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawControl.initial_state
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                  
section

namespace UniformKServer.RawFallback
open RawTyped RawMarks

@[simp] theorem choose_bits {n k : ℕ} (hk : 0<k) (c : Configuration n k)
    (A : Finset (Fin k)) (r : Fin n) :
    choose (config c) (bits A) r.val=(Fallback.choose hk ⟨c,A⟩ r).val := by
  simp only [choose,covers_bits,card_bits,Finset.card_pos,Bool.cond_decide,
    complement_bits,pick_bits hk,Fallback.choose]
  split_ifs <;> simp_all

@[simp] theorem label_bits {n k : ℕ} (hk : 0<k) (s : Fallback.RawState n k) (r : Fin n) :
    label k (config s.marking.position) (bits s.marking.marked) (bits s.seen) r.val=
      (Fallback.rawChoice hk s r).val := by
  by_cases he : Fallback.isEndpoint s r
  · have he' : k<(Insert.insert r s.seen).card := he
    simp only [label,endpoint_bits,Bool.cond_decide,ite_eq_left he',covers_bits,pick_bits hk,
      Fallback.rawChoice,ite_eq_left he]
  · have he' : ¬k<(Insert.insert r s.seen).card := he
    simp only [label,endpoint_bits,Bool.cond_decide,ite_eq_right he',choose_bits hk,
      Fallback.rawChoice,ite_eq_right he]

theorem step_bits {n k : ℕ} (hk : 0<k) (s : Fallback.RawState n k) (r : Fin n) :
    let j:=label k (config s.marking.position) (bits s.marking.marked) (bits s.seen) r.val
    ((config s.marking.position).set j r.val,
      nextMarked k (bits s.marking.marked) (bits s.seen) r.val j,
      nextSeen n k (bits s.seen) r.val)=
    (config (Fallback.rawStep hk s r).marking.position,
      bits (Fallback.rawStep hk s r).marking.marked,bits (Fallback.rawStep hk s r).seen) := by
  dsimp only
  rw [label_bits hk,config_set]
  by_cases he : Fallback.isEndpoint s r
  · have he' : k<(Insert.insert r s.seen).card := he
    simp only [nextMarked,nextSeen,endpoint_bits,Bool.cond_decide,ite_eq_left he',
      Fallback.rawStep,ite_eq_left he,empty_bits]
  · have he' : ¬k<(Insert.insert r s.seen).card := he
    simp only [nextMarked,nextSeen,endpoint_bits,Bool.cond_decide,ite_eq_right he',
      Fallback.rawStep,ite_eq_right he,Fallback.rawChoice,Fallback.step,insert_bits]

end UniformKServer.RawFallback

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawFilter
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawFallback.choose_bits _root_.OAI.UniformKServer.RawFallback.label_bits _root_.OAI.UniformKServer.RawMarks.covers_bits _root_.OAI.UniformKServer.RawProgram.unpack_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawFilter
open RawTyped

@[simp] theorem expand_entry {n k : ℕ} (M : ℕ) (r : Fin n) (e : UniformKServer.Entry n k) :
    expand k M r.val (entry e)=(UniformKServer.expand M r e).map entry := by
  rw [expand,cover_entry]
  simp only [Bool.cond_decide,UniformKServer.expand]
  change (if Covers e r then [entry e] else
    if e.moves<M then (List.range k).map (fun j=>(config e.position |>.set j r.val,e.moves+1)) else []) = _
  split_ifs with hcov hm
  · rfl
  · simp only [List.map_map]
    rw [RawExpansion.range_eq_ofFn, List.map_ofFn, ←List.ofFn_eq_map]
    apply congrArg List.ofFn
    funext j
    simp only [Function.comp_apply,entry,config_set]
    rfl
  · rfl

@[simp] theorem step_state {n k : ℕ} (M : ℕ) (s : UniformKServer.FilterState n k) (r : Fin n) :
    step k M (state s) r.val=state (UniformKServer.step M s r) := by
  simp only [step,allCover_state,Bool.cond_decide,UniformKServer.step]
  split_ifs with h
  · rfl
  · simp only [state,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def,
      expand_entry,births_entry,requests,List.map_append,List.map_cons,List.map_nil]

end UniformKServer.RawFilter

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawRowSelect
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawFallback.choose_bits _root_.OAI.UniformKServer.RawFallback.label_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                   
section

namespace UniformKServer.RawRowSelect
open RawTyped RawTable

theorem partialMass_succ (T p c : List ℕ) (r j : ℕ) :
    partialMass T p c r (j+1)=partialMass T p c r j+entry T p c r j := by
  simp [partialMass,List.range_succ,List.map_append,List.sum_append]

theorem partialMass_mono (T p c : List ℕ) (r : ℕ) : Monotone (partialMass T p c r) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [partialMass_succ]
  omega

theorem partialMass_cumulative {n k : ℕ} (T : List ℕ) (p : List (Fin n))
    (c : Configuration n k) (r : Fin n) (N : Fin k→ℕ)
    (hrep : ∀j,entry T (requests p) (config c) r.val j.val=N j) (j : Fin k) :
    partialMass T (requests p) (config c) r.val j.val=BitSampling.cumulative N j := by
  rw [partialMass,RawExpansion.range_eq_ofFn,List.map_ofFn,List.sum_ofFn]
  unfold BitSampling.cumulative
  apply Finset.sum_congr rfl
  intro i hi
  exact hrep (Fin.castLE j.isLt.le i)

theorem choose_eq {n k b : ℕ} (T : List ℕ) (p : List (Fin n))
    (c : Configuration n k) (r : Fin n) (N : Fin k→ℕ)
    (hrep : ∀j,entry T (requests p) (config c) r.val j.val=N j)
    (hN : ∑j,N j=2^b) (coins : Fin b→Bool) :
    choose k T (requests p) (config c) r.val (BitSampling.bitsEquiv b coins).val=
      (BitSampling.row N hN coins).val := by
  let j:=BitSampling.row N hN coins
  let a:=(BitSampling.bitsEquiv b coins).val
  let A:=(List.range k).map (fun i=>decide (a<partialMass T (requests p) (config c) r.val (i+1)))
  have hj : j.val<A.length := by simp [A]
  have hp:= (BitSampling.exact_row_proof N hN).2.1 coins
  have he:=partialMass_cumulative T p c r N hrep j
  have hf : A.findIdx id=j.val := by
    apply (List.findIdx_eq hj).mpr
    constructor
    · have hu : a<partialMass T (requests p) (config c) r.val (j.val+1) := by
        rw [partialMass_succ,he,hrep]
        exact hp.2
      simpa [A] using hu
    · intro i hi
      have hu : partialMass T (requests p) (config c) r.val (i+1)≤a :=
        (partialMass_mono T (requests p) (config c) r.val (by omega : i+1≤j.val)).trans (he ▸ hp.1)
      simpa [A] using Nat.not_lt_of_ge hu
  change RawMarks.pick A=j.val
  simp only [RawMarks.pick,hf,ite_eq_left hj]

end UniformKServer.RawRowSelect

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawControl
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawProgram.unpack_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                 
section

namespace UniformKServer.RawControl
open RawTyped RawMarks

@[simp] theorem nextEntry_state {n k : ℕ} (e : Entry n k) (r : Fin n) (j : Fin k) :
    nextEntry (RawFilter.entry e) r.val j.val=RawFilter.entry (EpochShadow.nextEntry e r j) := by
  simp only [nextEntry,RawFilter.entry,config_set,config_get,Bool.cond_decide,
    EpochShadow.nextEntry,Fin.ext_iff]

/-- Local representation lemma: only the current causal selector value is needed. -/
theorem label_state {n k : ℕ} (hk : 0<k) (T coins : List ℕ) (U : EpochShadow.Selector n k)
    (s : EpochControl.State n k) (r : Fin n)
    (hselect : trackingLabel k T coins (state s) r.val=(U s.filter.kept s.virtual.position r).val) :
    label k T coins (state s) r.val=(EpochControl.label hk U s r).val := by
  have hf:=RawFallback.label_bits hk (EpochControl.asRaw s) r
  simp only [EpochControl.asRaw] at hf
  simp only [label,state,RawFilter.entry,RawFilter.allCover_state,hf,
    RawMarks.covers_bits,RawMarks.pick_bits hk,Bool.cond_eq_ite,decide_eq_true_eq,
    EpochControl.label]
  change (if s.fallback=true then _ else if ∀z∈s.filter.live,Covers z r then _ else
    trackingLabel k T coins (state s) r.val)=_
  rw [hselect]
  split_ifs <;> rfl

theorem step_state {n k : ℕ} (hk : 0<k) (M : ℕ) (T coins : List ℕ) (U : EpochShadow.Selector n k)
    (s : EpochControl.State n k) (r : Fin n)
    (hselect : trackingLabel k T coins (state s) r.val=(U s.filter.kept s.virtual.position r).val) :
    step n k M T coins (state s) r.val=state (EpochControl.step hk M U s r) := by
  have hf:=RawFallback.step_bits hk (EpochControl.asRaw s) r
  simp only [EpochControl.asRaw] at hf
  by_cases hb : s.fallback=true
  · simp only [step,state,RawFilter.entry,hb,Bool.cond_true,EpochControl.step,
      RawFilter.step_state,ite_true, if_true]
    have hp:=congrArg Prod.fst hf
    have hm:=congrArg (fun x=>x.2.1) hf
    have hs:=congrArg (fun x=>x.2.2) hf
    dsimp only at hp hm hs
    rw [hp,hm,hs]
    rfl
  · have hb' : s.fallback=false := Bool.eq_false_iff.mpr hb
    by_cases hc : ∀z∈s.filter.live,Covers z r
    · simp only [step,state,RawFilter.allCover_state,RawFilter.entry,hb',Bool.cond_false,
        Bool.cond_decide,ite_eq_left hc,EpochControl.step,RawFallback.nextSeen_bits,Bool.false_eq_true,ite_false, if_false]
    · simp only [step,EpochControl.step,state,RawFilter.entry,RawFilter.allCover_state,hb',
        Bool.cond_false,Bool.cond_decide,ite_eq_right hc,Bool.false_eq_true,ite_false, if_false]
      change (RawFilter.step k M (RawFilter.state s.filter) r.val,
        nextEntry (RawFilter.entry s.virtual) r.val (trackingLabel k T coins (state s) r.val),
        empty k,RawFallback.nextSeen n k (bits s.seen) r.val,
        decide (M<(nextEntry (RawFilter.entry s.virtual) r.val
          (trackingLabel k T coins (state s) r.val)).2)) = _
      rw [hselect,RawFilter.step_state,nextEntry_state,empty_bits,RawFallback.nextSeen_bits]
      rfl

end UniformKServer.RawControl

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawTape
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawGlobal.chosen_state
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                              
section

namespace UniformKServer.RawTape
open RawTyped

theorem zeros (b : ℕ) : (BitSampling.bitsEquiv b (fun _=>false)).val=0 := by
  simp [BitSampling.bitsEquiv,Equiv.trans_apply,finPiFinEquiv_apply,finTwoEquiv]

theorem get_tape {H b : ℕ} (coins : Fin H→Fin b→Bool) (t : ℕ) :
    (tape coins).getD t 0=(BitSampling.bitsEquiv b (EpochExpectation.extend coins t)).val := by
  by_cases h : t<H
  · simp [tape,EpochExpectation.extend,h]
  · rw [List.getD_eq_default _ _ (by simpa [tape] using Nat.le_of_not_gt h)]
    simp [EpochExpectation.extend,h,zeros]

theorem tracking {n k M b : ℕ} (hk : 0<k) (T : List ℕ)
    (hT : RawCertificate.rowsOK n k (horizon k M) b T=true)
    (s : EpochControl.State n k) (hs : EpochControl.Bounded M s) (r : Fin n)
    (coins : Fin (horizon k M)→Fin b→Bool) :
    RawControl.trackingLabel k T (tape coins) (RawControl.state s) r.val=
      (EpochExpectation.selector (RawRows.complete hk (horizon k M) b T)
        (RawRows.total hk hT) (EpochExpectation.extend coins) s.filter.kept s.virtual.position r).val := by
  have hp : s.filter.kept.length≤horizon k M := by
    have h₁:=hs.1.2.1
    have h₂:=hs.1.2.2
    omega
  unfold RawControl.trackingLabel
  simp only [RawControl.state,RawFilter.state,RawFilter.entry,requests,List.length_map,get_tape]
  exact RawRowSelect.choose_eq T s.filter.kept s.virtual.position r
    (RawRows.complete hk (horizon k M) b T (s.filter.kept,s.virtual.position) r)
    (by intro j;simp only [RawRows.complete,ite_eq_left hp,RawExpansion.kernel])
    (RawRows.total hk hT _ _) _

end UniformKServer.RawTape

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawGlobal
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawProgram.unpack_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawGlobal
open RawTyped

@[simp] theorem label_state {n k M R b : ℕ} (hk : 0<k) (T : List ℕ)
    (hT : RawCertificate.rowsOK n k (horizon k M) b T=true)
    (s : TapeController.State n k M R b) (r : Fin n) (fresh : TapeController.Tape k M b) :
    label k T (state s) r.val (RawTape.tape fresh)=
      (TapeController.choose hk (RawRows.complete hk (horizon k M) b T) (RawRows.total hk hT) s r fresh).val := by
  simp only [label,chosen_state]
  apply RawControl.label_state
  exact RawTape.tracking hk T hT s.localState.val s.localState.property r _

@[simp] theorem step_state {n k M R b : ℕ} (hk : 0<k) (hkn : k≤n) (hR : 0<R) (T : List ℕ)
    (hT : RawCertificate.rowsOK n k (horizon k M) b T=true)
    (s : TapeController.State n k M R b) (r : Fin n) (fresh : TapeController.Tape k M b) :
    step n k M R T (state s) r.val (RawTape.tape fresh)=
      state (TapeController.step hk hR (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)
        (RawRows.complete hk (horizon k M) b T) (RawRows.total hk hT) s r fresh) := by
  simp only [step,boundary_state,Bool.cond_decide,TapeController.step]
  by_cases h : TapeController.boundary s r
  · simp only [ite_eq_left h,dite_eq_left h]
    exact initial_state hkn hR
  · simp only [ite_eq_right h,dite_eq_right h]
    rw [chosen_state]
    have hh:=RawControl.step_state hk M T (RawTape.tape (TapeController.chosen s fresh))
      (EpochExpectation.selector (RawRows.complete hk (horizon k M) b T) (RawRows.total hk hT)
        (EpochExpectation.extend (TapeController.chosen s fresh))) s.localState.val r
      (RawTape.tracking hk T hT s.localState.val s.localState.property r _)
    change (RawControl.step n k M T _ (RawControl.state s.localState.val) r.val,_,_)=_
    rw [hh]
    simp only [state,RawControl.state,RawFallback.endpoint_bits,Bool.cond_decide,Option.map_some,
      EpochControl.boundedStep]

end UniformKServer.RawGlobal

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawProgram
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                 
section

namespace UniformKServer.RawProgram
open Primrec RawCertificate
attribute [fun_prop] RawBits.primitive_bits

@[simp] theorem request_code (r : ℕ) :
    request (RawBinary.value (natCode (r+1)++[true]))=r := by
  simp only [request,RawBits.bits_value,RawBinary.read_natCode,Nat.add_sub_cancel]

end UniformKServer.RawProgram

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BinaryTape
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                 
section

namespace UniformKServer.BinaryTape
open RawBinary

 theorem value_sum {b : ℕ} (v : Fin b→Bool) :
    value (List.ofFn v)=∑i : Fin b,(if v i then 1 else 0)*2^i.val := by
  induction b with
  | zero=>simp [value]
  | succ b ih=>
    rw [List.ofFn_succ,RawBinary.value_cons,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ]
    rw [ih]
    simp_rw [←Nat.mul_assoc,←Finset.sum_mul]
    cases v 0 <;> simp only [Nat.bit_val,Bool.toNat_false,Bool.toNat_true,
      Bool.false_eq_true,ite_false, if_false,ite_true, if_true] <;> omega

 theorem bits_value {b : ℕ} (v : Fin b→Bool) :
    (BitSampling.bitsEquiv b v).val=value (List.ofFn v) := by
  rw [value_sum]
  simp only [BitSampling.bitsEquiv,Equiv.trans_apply,finPiFinEquiv_apply,
    finCongr_apply,Fin.val_cast,Equiv.piCongrRight_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  cases h:v i <;> simp [finTwoEquiv,h]

 theorem word_ofFn {H b : ℕ} (v : Fin H→Fin b→Bool) :
    word v=List.ofFn (fun z : Fin (H*b)=>v (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) := by
  rw [List.ofFn_mul]
  unfold word
  congr 1
  apply List.ofFn_inj.mpr
  funext i
  apply List.ofFn_inj.mpr
  funext j
  have h : (⟨i.val*b+j.val,by nlinarith [i.isLt,j.isLt]⟩ : Fin (H*b))=finProdFinEquiv (i,j) := by
    apply Fin.ext;simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
  simp only [h,Equiv.symm_apply_apply]

 theorem slice_word {H b : ℕ} (v : Fin H→Fin b→Bool) (i : Fin H) :
    (((word v)++[true]).drop (b*i.val)).take b=List.ofFn (v i) := by
  rw [word_ofFn]
  have hbound : b*i.val+b≤H*b := by nlinarith [i.isLt]
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_append,List.length_ofFn,List.length_singleton]
    omega
  · intro j h₁ h₂
    have hj : j<b := by simpa only [List.length_ofFn] using h₂
    have hidx : b*i.val+j<H*b := by nlinarith [i.isLt]
    simp only [List.getElem_take,List.getElem_drop]
    rw [List.getElem_append_left (by simpa only [List.length_ofFn] using hidx),List.getElem_ofFn]
    have hh : (⟨b*i.val+j,hidx⟩ : Fin (H*b))=finProdFinEquiv (i,⟨j,hj⟩) := by
      apply Fin.ext;simp [finProdFinEquiv,Nat.add_comm]
    rw [hh,Equiv.symm_apply_apply]
    simp only [List.getElem_ofFn]

 theorem fresh_token {k M b : ℕ} (v : TapeController.Tape k M b) :
    RawProgram.fresh k M b (token v)=RawTape.tape v := by
  unfold RawProgram.fresh token
  rw [RawBits.bits_value,RawMetric.horizon_eq,RawExpansion.range_eq_ofFn]
  simp only [List.map_ofFn,RawTape.tape]
  apply List.ofFn_inj.mpr
  funext i
  change value (((word v++[true]).drop (b*i.val)).take b)=(BitSampling.bitsEquiv b (v i)).val
  rw [slice_word,bits_value]

end UniformKServer.BinaryTape

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StackTape
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.StackCompiler.instFintypeHeadMove
attribute [-simp] _root_.OAI.UniformKServer.UniformWrapper.ofWord_tape _root_.OAI.UniformKServer.UniformWrapper.tape_shift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

/-! A stack is physically stored at a tape head. Padding is literal blank
cells, not a unit-cost unbounded register. Each push/pop uses at most two
transitions. -/
namespace UniformKServer.StackTape

theorem head {s : List Bool} {t : BitTape} (h : Rep s t) : t.head=s.head? := by
  obtain ⟨l,r,rfl⟩:=h
  cases s <;> rfl

theorem push_rep (b : Bool) {s : List Bool} {t : BitTape} (h : Rep s t) :
    Rep (b::s) (push b t) := by
  obtain ⟨l,r,rfl⟩:=h
  cases s with
  | nil =>
    cases l with
    | zero => exact ⟨0,r+1,by simp [push,encode,BitTape.shift,List.replicate_succ]⟩
    | succ l => exact ⟨l,r+1,by simp [push,encode,BitTape.shift,List.replicate_succ]⟩
  | cons a s =>
    cases l with
    | zero => exact ⟨0,r,by simp [push,encode,BitTape.shift]⟩
    | succ l => exact ⟨l,r,by simp [push,encode,BitTape.shift,List.replicate_succ]⟩

theorem pop_rep {s : List Bool} {t : BitTape} (h : Rep s t) : Rep s.tail (pop t) := by
  obtain ⟨l,r,rfl⟩:=h
  cases s with
  | nil => exact ⟨l,r,by simp [pop,encode]⟩
  | cons b s =>
    cases s with
    | nil =>
      cases r with
      | zero => exact ⟨l+1,0,by simp [pop,encode,BitTape.shift,List.replicate_succ]⟩
      | succ r => exact ⟨l+1,r,by simp [pop,encode,BitTape.shift,List.replicate_succ]⟩
    | cons a s => exact ⟨l+1,r,by simp [pop,encode,BitTape.shift,List.replicate_succ]⟩

end UniformKServer.StackTape

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StackCompiler
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Finite-control, finite-alphabet stack processors, compiled to the exact
binary multitape model. There is no unit-cost arithmetic oracle. -/
namespace UniformKServer.StackCompiler
open scoped Classical

theorem decode_none (g : ℕ) : decode (fun _ : Fin g=>none)=none := by
  have hn : ¬∃ a : Fin g,∀j,(none : Option Bool)=some (code a j) := by
    rintro ⟨a,h⟩
    cases (h a)
  exact dite_eq_right hn

theorem decode_code {g : ℕ} (a : Fin g) : decode (fun j=>some (code a j))=some a := by
  unfold decode
  split_ifs with h
  · congr 1
    have he: code a a=code (Classical.choose h) a := Option.some.inj (Classical.choose_spec h a)
    exact of_decide_eq_true (he.symm.trans (by simp [code]))
  · exact False.elim (h ⟨a,fun _=>rfl⟩)

theorem matches_install {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) (h : Matches P s z) (input : List Bool) :
    Matches P (install s input) ((machine P).install z input) :=
  ⟨h.control,rfl,rfl,rfl,h.work⟩

theorem matches_heads {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) (h : Matches P s z) (i : Fin m) :
    decode (fun j=>(z.work (wire m g (i,j))).head)=(s.store i).head? := by
  have he : (fun j=>(z.work (wire m g (i,j))).head)=
      fun j=> ((s.store i).map (fun a=>code a j)).head? := funext (fun j=>StackTape.head (h.work i j))
  rw [he]
  cases hs:s.store i with
  | nil => exact decode_none _
  | cons a as => exact decode_code a

end UniformKServer.StackCompiler

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StackSimulation
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.UniformWrapper.ofWord_tape _root_.OAI.UniformKServer.UniformWrapper.tape_shift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.StackCompiler
open scoped Classical

private theorem write_none (t : BitTape) (ht : t.head=none) :
    {t with head:=none}=t := by
  cases t with
  | mk l h r =>
    change h=none at ht
    subst h
    rfl

theorem first_step {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) (h : Matches P s z) (hs : s.yielded=false) (coin : Bool) :
    (machine P).step z coin = middle P
      (P.transition s.control s.input.head (fun i=>(s.store i).head?) coin) z := by
  have hh : (fun i=>decode (fun j=>(z.work (wire m g (i,j))).head))=
      fun i=>(s.store i).head? := funext (matches_heads P s z h)
  simp only [BitMachine.step,h.yielded,hs,Bool.false_eq_true,↓reduceIte,
    machine,h.control,Equiv.symm_apply_apply,h.input,hh]
  unfold middle
  congr 1
  · rw [h.input]
  · funext v
    cases hp:(P.transition s.control s.input.head (fun i=>(s.store i).head?) coin).stackOp
        (((wire m g).symm v).1) with
    | keep => rfl
    | push a => rfl
    | pop =>
      simp only [beginOp,StackTape.pop]
      split_ifs with ht
      · simp only [BitTape.shift]
        exact write_none (z.work v) ht
      · rfl

theorem last_step {q m g : ℕ} (P : Processor q m g) (a : Action q m g)
    (z : MachineState (machine P)) (coin : Bool) :
    (machine P).step (middle P a z) coin = last P a (middle P a z) := by
  simp only [BitMachine.step,middle,Bool.false_eq_true,↓reduceIte,machine,
    Equiv.symm_apply_apply,last,BitTape.shift]
  congr 1
  funext v
  cases a.stackOp (((wire m g).symm v).1) <;> rfl

theorem op_rep {g : ℕ} (o : Op g) (j : Fin g) (l : List (Fin g)) (t : BitTape)
    (h : StackTape.Rep (l.map (fun a=>code a j)) t) :
    StackTape.Rep ((applyOp o l).map (fun a=>code a j)) (finishOp o j (beginOp o t)) := by
  cases o with
  | keep=>exact h
  | push a=>exact StackTape.push_rep (code a j) h
  | pop=>simpa only [applyOp,List.map_tail,beginOp,finishOp] using StackTape.pop_rep h

theorem matches_step {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) (h : Matches P s z) (coin unused : Bool) :
    Matches P (step P s coin) ((machine P).step ((machine P).step z coin) unused) := by
  cases hs:s.yielded with
  | true=> simpa [step,hs,BitMachine.step,h.yielded] using h
  | false=>
    rw [first_step P s z h hs,last_step]
    let a:=P.transition s.control s.input.head (fun i=>(s.store i).head?) coin
    change Matches P (step P s coin) (last P a (middle P a z))
    refine ⟨?_,?_,?_,?_,?_⟩
    · simp only [last,step,hs,Bool.false_eq_true,↓reduceIte]
      rfl
    · simp only [last,middle,step,hs,Bool.false_eq_true,↓reduceIte,h.input]
      rfl
    · simp only [last,middle,step,hs,Bool.false_eq_true,↓reduceIte,h.output]
      rfl
    · simp only [last,step,hs,Bool.false_eq_true,↓reduceIte]
      rfl
    · intro i j
      simpa only [last,middle,step,hs,Bool.false_eq_true,↓reduceIte,
        Equiv.symm_apply_apply] using op_rep (a.stackOp i) j (s.store i) _ (h.work i j)
end UniformKServer.StackCompiler

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StackRun
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.UniformWrapper.ofWord_tape _root_.OAI.UniformKServer.UniformWrapper.tape_shift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.StackCompiler

theorem run_halted {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (hy : s.yielded=true) (bs : List Bool) : run P s bs=s := by
  induction bs with
  | nil=>rfl
  | cons b bs ih=>simpa [run_cons,step,hy] using ih

theorem capped_after {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    {t B : ℕ} (h : (run P s (List.replicate t false)).yielded=true) (htB : t≤B) :
    run P s (List.replicate B false)=run P s (List.replicate t false) := by
  obtain ⟨a,rfl⟩:=Nat.exists_eq_add_of_le htB
  rw [List.replicate_add,run_append]
  exact run_halted P _ h _

end UniformKServer.StackCompiler

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LiteralBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.LiteralBound
open Turing StackCompiler StackPrimitive
open scoped Classical

 theorem correct_at {t u r a : ℕ} (h : finishes t u r a=true) :
    ∀i,(run program (Init u r a) (List.replicate t false)).store i=
      ((Turing.PartrecToTM2.halt (RawProgram.run (⟨[u,r,a],rfl⟩ : List.Vector ℕ 3)).val).stk
        (FlatTM2.keys.symm i)).map FlatTM2.letters := by
  let v : List.Vector ℕ 3:=⟨[u,r,a],rfl⟩
  have he : (RawProgram.run v).val∈Turing.ToPartrec.Code.eval LiteralVector.activeCode v.val := by
    rw [LiteralVector.active_eval]
    exact Part.mem_some _
  obtain ⟨T,hT,hS⟩:=LiteralPartrec.halts he
  rw [finishes_run] at h
  have heq : run program (Init u r a) (List.replicate t false)=
      run program (Init u r a) (List.replicate T false) := by
    rcases le_total t T with ht|ht
    · exact (capped_after _ _ h ht).symm
    · exact capped_after _ _ hT ht
  rw [heq]
  exact hS

end UniformKServer.LiteralBound

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawTypedCoins
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.RawFinite
open RawProgram RawCertificate
open scoped Classical

 theorem choose_token {n k : ℕ} (hk : 0<k) (v : Certificate)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (s : TapeController.State n k (cap v) (restart v) (bits v)) (r : Fin n)
    (bs : TapeController.Tape k (cap v) (bits v)) :
    RawProgram.chosen (repr v s) (requestToken r.val) (BinaryTape.token bs)=
      (TapeController.choose hk (RawRows.complete hk (UniformKServer.horizon k (cap v)) (bits v) (table v))
        (RawRows.total hk hT) s r bs).val := by
  simp only [RawProgram.chosen,repr,payload,requestToken,request_code,BinaryTape.fresh_token]
  exact RawGlobal.label_state hk (table v) hT s r bs

 theorem next_token {n k : ℕ} (hk : 0<k) (hkn : k≤n) (v : Certificate) (hR : 0 < restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (s : TapeController.State n k (cap v) (restart v) (bits v)) (r : Fin n)
    (bs : TapeController.Tape k (cap v) (bits v)) :
    RawProgram.next (repr v s) (requestToken r.val) (BinaryTape.token bs)=
      repr v (TapeController.step hk hR (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)
        (RawRows.complete hk (UniformKServer.horizon k (cap v)) (bits v) (table v))
        (RawRows.total hk hT) s r bs) := by
  simp only [RawProgram.next,repr,payload,requestToken,request_code,BinaryTape.fresh_token]
  rw [RawGlobal.step_state hk hkn hR (table v) hT]

 theorem initial_repr {n k : ℕ} (hkn : k≤n) (v : Certificate) (hR : 0 < restart v) :
    RawProgram.initial n k v=repr v (TapeController.initial (M:=cap v) (b:=bits v) hR
      (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)) := by
  unfold RawProgram.initial repr
  rw [RawGlobal.initial_state hkn hR]

end UniformKServer.RawFinite

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StackCoins
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.StackCompiler

 theorem matches_alternate {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) (h : Matches P s z) (bs : List Bool) (he : Even bs.length) :
    Matches P (run P s (alternate bs)) ((machine P).run z bs) := by
  induction bs using alternate.induct generalizing s z with
  | case1=>exact h
  | case2 a=>simp at he
  | case3 a b bs ih=>
    have hb : Even bs.length:=by
      obtain ⟨c,hc⟩:=he
      refine ⟨c-1,?_⟩
      simp only [List.length_cons] at hc
      omega
    exact ih _ _ (matches_step P s z h a b) hb

 theorem alternate_get (bs : List Bool) (i : ℕ) (hi : 2*i<bs.length) :
    (alternate bs)[i]'(by rw [alternate_length];omega)=bs[2*i] := by
  induction bs using alternate.induct generalizing i with
  | case1=>simp at hi
  | case2 a=>have hh : i=0:=by simp only [List.length_cons,List.length_nil] at hi;omega
             subst i;rfl
  | case3 a b bs ih=>
    cases i with
    | zero=>rfl
    | succ i=>
      simpa only [alternate,List.getElem_cons_succ,show 2*(i+1)=2*i+2 by omega] using
        ih i (by simp only [List.length_cons] at hi;omega)

end UniformKServer.StackCompiler

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TypedStack
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.TypedStack
open StackCompiler
open scoped Classical

variable {Q K : Type*} {g : ℕ}

theorem encode_step [Fintype Q] [Fintype K] (P : Processor Q K g) (s : State Q K g) (b : Bool) :
    encode (step P s b)=StackCompiler.step (compile P) (encode s) b := by
  cases hy:s.yielded <;> simp only [step,StackCompiler.step,encode,compile,hy,
    Bool.false_eq_true,↓reduceIte,Equiv.symm_apply_apply]
  all_goals rfl

theorem encode_run [Fintype Q] [Fintype K] (P : Processor Q K g) (s : State Q K g) (bs : List Bool) :
    encode (run P s bs)=StackCompiler.run (compile P) (encode s) bs := by
  induction bs generalizing s with
  | nil=>rfl
  | cons b bs ih=>
    change encode (run P (step P s b) bs)=StackCompiler.run (compile P) (StackCompiler.step (compile P) (encode s) b) bs
    rw [ih,encode_step]

theorem run_cons (P : Processor Q K g) (s : State Q K g) (b : Bool) (bs : List Bool) :
    run P s (b::bs)=run P (step P s b) bs := rfl

theorem run_append (P : Processor Q K g) (s : State Q K g) (as bs : List Bool) :
    run P s (as++bs)=run P (run P s as) bs := List.foldl_append

theorem run_yielded (P : Processor Q K g) (s : State Q K g) (h : s.yielded=true) (bs : List Bool) :
    run P s bs=s := by
  induction bs with
  | nil=>rfl
  | cons b bs ih=>simpa only [run_cons,step,h,Bool.true_eq,↓reduceIte] using ih

end UniformKServer.TypedStack

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.TypedStack
variable {Q K : Type*} {g : ℕ}

theorem uniform_zero (P : Processor Q K g) (s : State Q K g) : UniformRun P s 0 s := by
  intro bs h;have hh:=List.eq_nil_of_length_eq_zero h;subst bs;rfl

theorem uniform_step (P : Processor Q K g) (s z : State Q K g) (h : ∀b,step P s b=z) :
    UniformRun P s 1 z := by
  intro bs hb
  cases bs with
  | nil=>simp at hb
  | cons b bs=>
    have he : bs=[]:=List.eq_nil_of_length_eq_zero (by simpa using hb)
    subst bs
    exact h b

theorem UniformRun.trans {P : Processor Q K g} {s z w : State Q K g} {t u : ℕ}
    (h : UniformRun P s t z) (h' : UniformRun P z u w) : UniformRun P s (t+u) w := by
  intro bs hb
  rw [←List.take_append_drop t bs,run_append,h (bs.take t) (by simp only [List.length_take,hb];omega)]
  exact h' _ (by simp only [List.length_drop,hb];omega)

theorem UniformRun.mono {P : Processor Q K g} {s z : State Q K g} {t u : ℕ}
    (h : UniformRun P s t z) (hy : z.yielded=true) (hu : t≤u) : UniformRun P s u z := by
  intro bs hb
  rw [←List.take_append_drop t bs,run_append,h (bs.take t) (by simp only [List.length_take,hb];omega)]
  exact run_yielded P z hy _

end UniformKServer.TypedStack

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

theorem read_step (q exit : Control qc qa)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=read q exit inp)
    (l : List (Option Bool)) (b : Bool) (w : List Bool) (m p buf : List (Fin g))
    (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q (tape l (b::w)) m p buf out) coin=
      wordState q (tape (some b::l) w) m p (digit b::buf) out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,read,write]
  apply wordState_ext
  · rfl
  · exact tape_shift _ _ _
  · intro k;cases k with
    | base k=>cases k <;> rfl
    | pay=>rfl
    | buf=>rfl
  · rfl
  · rfl

theorem read_empty (q exit : Control qc qa)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=read q exit inp)
    (l : List (Option Bool)) (m p buf : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q (tape l []) m p buf out) coin=
      wordState exit (tape l []) m p buf out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,read,pass,tape,BitTape.shift]
  rfl

theorem read_run (q exit : Control qc qa)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=read q exit inp)
    (l : List (Option Bool)) (w : List Bool) (m p buf : List (Fin g)) (out : List Bool) :
    UniformRun (processor C A) (wordState q (tape l w) m p buf out) (w.length+1)
      (wordState exit (tape (w.reverse.map some++l) []) m p ((w.map digit).reverse++buf) out) := by
  induction w generalizing l buf with
  | nil=>
    simpa only [List.length_nil,Nat.zero_add,List.reverse_nil,List.map_nil,List.nil_append] using
      uniform_step _ _ _ (read_empty C A q exit h l m p buf out)
  | cons b w ih=>
    have hs:=uniform_step _ _ _ (read_step C A q exit h l b w m p buf out)
    have hi:=ih (some b::l) (digit b::buf)
    convert hs.trans hi using 1 <;>
      (simp only [List.length_cons,List.reverse_cons,List.map_append,
        List.map_cons,List.append_assoc,List.singleton_append,List.map_nil]; try omega)

theorem buf_empty (q exit : Control qc qa) (y : Bool)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=
      match hd .buf with | none=>pass exit y | some a=>move q .buf main a)
    (i : BitTape) (m p : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q i m p [] out) coin=
      wordState exit i m p [] out y := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,List.head?_nil,pass,BitTape.shift]
  rfl

theorem buf_run (q exit : Control qc qa) (y : Bool)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=
      match hd .buf with | none=>pass exit y | some a=>move q .buf main a)
    (i : BitTape) (xs m p : List (Fin g)) (out : List Bool) :
    UniformRun (processor C A) (wordState q i m p xs out) (xs.length+1)
      (wordState exit i (xs.reverse++m) p [] out y) := by
  induction xs generalizing m with
  | nil=>simpa only [List.length_nil,Nat.zero_add,List.reverse_nil,List.nil_append] using
      uniform_step _ _ _ (buf_empty C A q exit y h i m p out)
  | cons a xs ih=>
    have hs:=uniform_step _ _ _ (buf_step C A q exit y h i a xs m p out)
    convert hs.trans (ih (a::m)) using 1 <;>
      (simp only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append]; try omega)

theorem pay_step (q exit : Control qc qa)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=drain q exit .pay hd)
    (i : BitTape) (a : Fin g) (xs m b : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q i m (a::xs) b out) coin=
      wordState q i (a::m) xs b out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,drain,List.head?_cons,move,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

theorem pay_empty (q exit : Control qc qa)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=drain q exit .pay hd)
    (i : BitTape) (m b : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q i m [] b out) coin=
      wordState exit i m [] b out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,drain,List.head?_nil,pass,BitTape.shift]
  rfl

theorem pay_run (q exit : Control qc qa)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=drain q exit .pay hd)
    (i : BitTape) (xs m b : List (Fin g)) (out : List Bool) :
    UniformRun (processor C A) (wordState q i m xs b out) (xs.length+1)
      (wordState exit i (xs.reverse++m) [] b out) := by
  induction xs generalizing m with
  | nil=>simpa only [List.length_nil,Nat.zero_add,List.reverse_nil,List.nil_append] using
      uniform_step _ _ _ (pay_empty C A q exit h i m b out)
  | cons a xs ih=>
    have hs:=uniform_step _ _ _ (pay_step C A q exit h i a xs m b out)
    convert hs.trans (ih (a::m)) using 1 <;>
      (simp only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append]; try omega)

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperInterpreter
attribute [-simp] _root_.OAI.UniformKServer.UniformWrapper.ofWord_tape _root_.OAI.UniformKServer.UniformWrapper.tape_shift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa q' : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

theorem active_step (hA : StackPrimitive.Deterministic A)
    (s : StackCompiler.State qa (Fintype.card K') g) (hy : s.yielded=false)
    (i : BitTape) (coin : Bool) :
    TypedStack.step (processor C A) (activeState (qc:=qc) s i) coin=
      activeState (StackCompiler.step A s false) i := by
  unfold StackPrimitive.Deterministic at hA
  unfold TypedStack.step activeState inside
  simp only [hy,Bool.false_eq_true,↓reduceIte,Bool.cond_false,processor,lift,
    Equiv.apply_symm_apply,BitTape.shift,StackCompiler.step,hA]
  apply wordState_ext <;> try rfl
  intro k;cases k <;> rfl

theorem active_run (hA : StackPrimitive.Deterministic A)
    (s : StackCompiler.State qa (Fintype.card K') g) (t : ℕ)
    (ht : ∀j<t,(StackCompiler.run A s (List.replicate j false)).yielded=false) (i : BitTape) :
    UniformRun (processor C A) (activeState s i) t
      (activeState (StackCompiler.run A s (List.replicate t false)) i) := by
  induction t with
  | zero=>exact uniform_zero _ _
  | succ t ih=>
    have h₁:=ih (fun j hj=>ht j (by omega))
    have h₂:=uniform_step _ _ _ (active_step C A hA _ (ht t (by omega)) i)
    rw [cap_succ]
    exact h₁.trans h₂

theorem literal_input (c : Turing.ToPartrec.Code) (v : List ℕ) (i : BitTape) :
    activeState (qc:=qc) (LiteralPartrec.input c v) i=
      wordState (.active (LiteralPartrec.processor c).start) i ((trList v).map FlatTM2.letters) [] [] := by
  have h:=LiteralInput.input_config c v
  have hc:=congrArg (fun s=>s.1) h
  have hs:=congrArg (fun s=>s.2.1) h
  have hy:=congrArg (fun s=>s.2.2) h
  change (LiteralPartrec.input c v).control=(LiteralPartrec.processor c).start at hc
  change (LiteralPartrec.input c v).yielded=false at hy
  apply wordState_ext
  · simp only [activeState,inside,hy,Bool.cond_false,hc,wordState]
  · rfl
  · intro k
    cases k with
    | base k=>
      change (LiteralPartrec.input c v).store (FlatTM2.keys k)=_
      have hh:=congrFun hs (FlatTM2.keys k)
      change (LiteralPartrec.input c v).store (FlatTM2.keys k)=
        (if FlatTM2.keys k=FlatTM2.keys K'.main then (trList v).map FlatTM2.letters else []) at hh
      rw [hh]
      cases k <;> simp [wordState]
    | pay=>rfl
    | buf=>rfl
  · rfl
  · rfl

theorem literal_output {c : Turing.ToPartrec.Code} {v w : List ℕ}
    {t : ℕ} (hy : (StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
      (List.replicate t false)).yielded=true)
    (hs : ∀i,(StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
      (List.replicate t false)).store i=((halt w).stk (FlatTM2.keys.symm i)).map FlatTM2.letters)
    (i : BitTape) :
    activeState (qc:=qc) (StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
      (List.replicate t false)) i=wordState .emit i ((trList w).map FlatTM2.letters) [] [] := by
  apply wordState_ext
  · simp only [activeState,inside,hy,Bool.cond_true,wordState]
  · rfl
  · intro k;cases k with
    | base k=>
      simp only [activeState,inside,hs,Equiv.symm_apply_apply,halt,wordState]
      cases k <;> rfl
    | pay=>rfl
    | buf=>rfl
  · rfl
  · rfl

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperPrefix
attribute [-simp] _root_.OAI.UniformKServer.UniformWrapper.ofWord_tape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.TypedStack
variable {Q K : Type*} {g : ℕ}

 theorem SlowLink.run {P : Processor Q K g} {a b : State Q K g} (h : SlowLink P a b)
    (w bs : List Bool) (hb : 1≤bs.length) :
    run P (install a w) bs=retape b (BitTape.ofWord w) := by
  cases bs with
  | nil=>simp at hb
  | cons c bs=>
    rw [run_cons,h.2.2]
    exact run_yielded P (retape b (BitTape.ofWord w)) h.1 bs

end UniformKServer.TypedStack

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.TypedStack
open scoped Classical
variable {Q K : Type*} [Fintype Q] [Fintype K] {g : ℕ}

 theorem CoreRep.yielded {P : Processor Q K g} {s : State Q K g}
    {z : MachineState (StackCompiler.machine (compile P))} (h : CoreRep P s z) : z.yielded=true := by
  obtain ⟨i,out,h⟩:=h
  exact h.yielded

 theorem matches_core {P : Processor Q K g} {s : State Q K g}
    {z : MachineState (StackCompiler.machine (compile P))}
    (h : StackCompiler.Matches (compile P) (encode s) z) (hy : s.yielded=true) : CoreRep P s z := by
  refine ⟨s.input,s.outputRev,?_⟩
  have he : frame s s.input s.outputRev=s := by cases s;simp_all only [frame]
  rw [he]
  exact h

 theorem CoreRep.install {P : Processor Q K g} {s : State Q K g}
    {z : MachineState (StackCompiler.machine (compile P))} (h : CoreRep P s z) (w : List Bool) :
    StackCompiler.Matches (compile P) (encode (install s w))
      ((StackCompiler.machine (compile P)).install z w) := by
  obtain ⟨i,out,h⟩:=h
  have hh:=StackCompiler.matches_install _ _ _ h w
  exact hh

 theorem matches_coins {P : Processor Q K g} {s : State Q K g}
    {z : MachineState (StackCompiler.machine (compile P))}
    (h : StackCompiler.Matches (compile P) (encode s) z) (bs : List Bool) (he : Even bs.length) :
    StackCompiler.Matches (compile P) (encode (run P s (StackCompiler.alternate bs)))
      ((StackCompiler.machine (compile P)).run z bs) := by
  rw [encode_run]
  exact StackCompiler.matches_alternate _ _ _ h bs he

 theorem CoreRep.slow {P : Processor Q K g} {s t : State Q K g}
    {z : MachineState (StackCompiler.machine (compile P))} (h : CoreRep P s z) (w bs : List Bool)
    (he : Even bs.length) (hb : 2≤bs.length) (hs : SlowLink P s t) :
    CoreRep P t ((StackCompiler.machine (compile P)).run ((StackCompiler.machine (compile P)).install z w) bs) ∧
      ((StackCompiler.machine (compile P)).run ((StackCompiler.machine (compile P)).install z w) bs).outputRev=[] := by
  have hh:=matches_coins (h.install w) bs he
  rw [hs.run w _ (by rw [StackCompiler.alternate_length];omega)] at hh
  refine ⟨?_,?_⟩
  · obtain ⟨hy,ho,hl⟩:=hs
    have hc:=matches_core hh hy
    exact hc
  · exact hh.output.trans hs.2.1

end UniformKServer.TypedStack

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical

 theorem request_even (L t : ℕ) : Even (requestBudget 64 1 L t) := by
  refine ⟨32*(L+Nat.clog 2 (t+1)+1),?_⟩
  simp only [requestBudget,polynomialBudget,pow_one]
  omega
 theorem request_half (L t : ℕ) (bs : List Bool) (h : bs.length=requestBudget 64 1 L t) :
    (StackCompiler.alternate bs).length=32*(L+Nat.clog 2 (t+1)+1) := by
  rw [StackCompiler.alternate_length,h]
  simp only [requestBudget,polynomialBudget,pow_one]
  omega
 theorem request_ge (L t : ℕ) : 2 ≤ requestBudget 64 1 L t := by
  simp only [requestBudget,polynomialBudget,pow_one];omega
 theorem process_bound (L t T d : ℕ) (hd : 2^T≤d) (ht : d≤t) :
    16*(T+1)≤32*(L+Nat.clog 2 (t+2)+1) := by
  have hp : (2:ℕ)^T<t+2:=by omega
  have hc : T≤Nat.clog 2 (t+2) := by
    exact Nat.le_of_lt ((Nat.lt_clog_iff_pow_lt (by decide : 1 < (2:ℕ))).mpr hp)
  omega

 theorem bitValue_eq (w : List Bool) : bitValue w=RawBinary.value w := by
  induction w with
  | nil=>rfl
  | cons b w ih=>
    simp only [bitValue,RawBinary.value_cons,Nat.bit_val,ih]
    cases b <;> simp [Bool.toNat,Nat.add_comm]

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

theorem push_main (q exit : Control qc qa) (a : Fin g)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=write exit main a)
    (i : BitTape) (m p b : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q i m p b out) coin=
      wordState exit i (a::m) p b out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,write,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

theorem pop_main (q exit : Control qc qa) (y : Bool)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=pop exit main y)
    (i : BitTape) (a : Fin g) (m p b : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q i (a::m) p b out) coin=
      wordState exit i m p b out y := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,pop,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

theorem save_step (i : BitTape) (a : Bool) (m p b : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .savePayload i (digit a::m) p b out) coin=
      wordState .savePayload i m (digit a::p) b out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,processor,List.head?_cons,
    Option.some.injEq,digit_ne_sep,↓reduceIte,move,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

theorem save_end (i : BitTape) (p b : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .savePayload i [sep] p b out) coin=
      wordState .randomCons i [] p b out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,processor,List.head?_cons,↓reduceIte,pop,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

theorem save_run (i : BitTape) (w : List Bool) (p b : List (Fin g)) (out : List Bool) :
    UniformRun (processor C A) (wordState .savePayload i (w.map digit++[sep]) p b out) (w.length+1)
      (wordState .randomCons i [] ((w.map digit).reverse++p) b out) := by
  induction w generalizing p with
  | nil=>simpa only [List.length_nil,Nat.zero_add,List.map_nil,List.nil_append,List.reverse_nil] using
      uniform_step _ _ _ (save_end C A i p b out)
  | cons a w ih=>
    have hs:=uniform_step _ _ _ (save_step C A i a (w.map digit++[sep]) p b out)
    convert hs.trans (ih (digit a::p)) using 1 <;>
      simp only [List.length_cons,List.map_cons,List.reverse_cons,List.cons_append,List.append_assoc,
        List.nil_append]
    omega

theorem sample_step (i : BitTape) (m p b : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .sample i (digit false::m) p b out) coin=
      wordState .sample i m p (digit coin::b) out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,processor,List.head?_cons,↓reduceIte,move,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

theorem sample_run (i : BitTape) (bs : List Bool) (m p b : List (Fin g)) (out : List Bool) :
    TypedStack.run (processor C A)
      (wordState .sample i (List.replicate bs.length (digit false)++m) p b out) bs=
      wordState .sample i m p ((bs.map digit).reverse++b) out := by
  induction bs generalizing b with
  | nil=>simp only [List.length_nil,List.replicate_zero,List.nil_append,TypedStack.run,List.foldl_nil,
      List.map_nil,List.reverse_nil]
  | cons a bs ih=>
    simp only [List.length_cons,List.replicate_succ,List.cons_append,TypedStack.run_cons,sample_step,ih,
      List.map_cons,List.reverse_cons,List.append_assoc,List.nil_append]

theorem sample_end (i : BitTape) (m p b : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .sample i (digit true::m) p b out) coin=
      wordState .sampleSep i m p b out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,processor,List.head?_cons,
    Option.some.injEq,digit_eq_digit,Bool.true_eq_false,↓reduceIte,pop,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

 theorem pow_bits (b : ℕ) : (2^b).bits=List.replicate b false++[true] := by
  induction b with
  | zero=>rfl
  | succ b ih=>
    rw [pow_succ,show 2^b*2=Nat.bit false (2^b) from by simp [Nat.bit_val,Nat.mul_comm]]
    rw [Nat.bits_append_bit _ _ (fun hn=>False.elim ((pow_ne_zero b (by decide : (2:ℕ)≠0)) hn)),ih]
    simp only [List.replicate_succ,List.cons_append]

 theorem encodedNat (u : ℕ) : (trNat u).map FlatTM2.letters=u.bits.map digit := by
  rw [RawBits.trNat_bits,List.map_map]
  rfl
 theorem encodedList (u : ℕ) (xs : List ℕ) :
    (trList (u::xs)).map FlatTM2.letters=u.bits.map digit++sep::(trList xs).map FlatTM2.letters := by
  simp only [trList,List.map_append,List.map_cons,encodedNat]

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperEmit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

 theorem emit_step (i : BitTape) (a : Bool) (m : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .emit i (digit a::m) [] [] out) coin=
      wordState .emit i m [] [] (a::out) := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,processor,List.head?_cons,
    Option.some.injEq,digit_ne_sep,↓reduceIte,pop,BitTape.shift,digit_eq_digit]
  apply wordState_ext <;> try rfl
  · intro k;cases k with
    | base k=>cases k <;> rfl
    | pay=>rfl
    | buf=>rfl
  · cases a <;> rfl

 theorem emit_end (i : BitTape) (m : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .emit i (sep::m) [] [] out) coin=
      wordState .sample i m [] [] out true := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,processor,List.head?_cons,↓reduceIte,pop,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

 theorem emit_run (i : BitTape) (w : List Bool) (m : List (Fin g)) (out : List Bool) :
    UniformRun (processor C A) (wordState .emit i (w.map digit++sep::m) [] [] out) (w.length+1)
      (wordState .sample i m [] [] (w.reverse++out) true) := by
  induction w generalizing out with
  | nil=>simpa only [List.length_nil,Nat.zero_add,List.map_nil,List.nil_append,List.reverse_nil] using
      uniform_step _ _ _ (emit_end C A i m out)
  | cons a w ih=>
    have hs:=uniform_step _ _ _ (emit_step C A i a (w.map digit++sep::m) out)
    convert hs.trans (ih (a::out)) using 1 <;>
      simp only [List.length_cons,List.map_cons,List.reverse_cons,List.cons_append,List.append_assoc,
        List.nil_append]; omega

 theorem first_finish (u r a T : ℕ) (h : LiteralBound.finishes T u r a=true) :
    ∃t≤T,LiteralBound.finishes t u r a=true ∧
      ∀j<t,(StackCompiler.run LiteralBound.program (LiteralBound.Init u r a)
        (List.replicate j false)).yielded=false := by
  have he : ∃t,LiteralBound.finishes t u r a=true:=⟨T,h⟩
  refine ⟨Nat.find he,Nat.find_min' he h,Nat.find_spec he,?_⟩
  intro j hj
  have hn:=Nat.find_min he hj
  rw [LiteralBound.finishes_run] at hn
  cases hh:(StackCompiler.run LiteralBound.program (LiteralBound.Init u r a)
    (List.replicate j false)).yielded <;> simp_all

 theorem active_correct (u r a t : ℕ) (ht : LiteralBound.finishes t u r a=true)
    (hp : ∀j<t,(StackCompiler.run LiteralBound.program (LiteralBound.Init u r a)
      (List.replicate j false)).yielded=false) (i : BitTape) :
    UniformRun (processor C LiteralBound.program)
      (wordState (.active LiteralBound.program.start) i ((trList [u,r,a]).map FlatTM2.letters) [] []) t
      (wordState .emit i
        ((trList [RawProgram.chosen (RawProgram.unpack u) r a,
          2^RawProgram.randomCount (RawProgram.unpack u),
          Encodable.encode (RawProgram.next (RawProgram.unpack u) r a)]).map FlatTM2.letters) [] []) := by
  have hrun:=active_run C LiteralBound.program (StackPrimitive.literal_deterministic _)
    (LiteralBound.Init u r a) t hp i
  rw [literal_input] at hrun
  rw [literal_output (by rwa [←LiteralBound.finishes_run]) (LiteralBound.correct_at ht)] at hrun
  exact hrun

 theorem active_response (u r a T : ℕ) (h : LiteralBound.finishes T u r a=true) (i : BitTape) :
    ∃t≤T+(RawProgram.chosen (RawProgram.unpack u) r a).bits.length+1,
      UniformRun (processor C LiteralBound.program)
        (wordState (.active LiteralBound.program.start) i ((trList [u,r,a]).map FlatTM2.letters) [] []) t
        (wordState .sample i
          ((trList [2^RawProgram.randomCount (RawProgram.unpack u),
            Encodable.encode (RawProgram.next (RawProgram.unpack u) r a)]).map FlatTM2.letters)
          [] [] (RawProgram.chosen (RawProgram.unpack u) r a).bits.reverse true) := by
  obtain ⟨t,hT,ht,hp⟩:=first_finish u r a T h
  have hrun:=active_correct C u r a t ht hp i
  rw [encodedList (RawProgram.chosen (RawProgram.unpack u) r a)] at hrun
  have hem:=emit_run C LiteralBound.program i (RawProgram.chosen (RawProgram.unpack u) r a).bits
    ((trList [2^RawProgram.randomCount (RawProgram.unpack u),
      Encodable.encode (RawProgram.next (RawProgram.unpack u) r a)]).map FlatTM2.letters) []
  simp only [List.append_nil] at hem
  exact ⟨t+((RawProgram.chosen (RawProgram.unpack u) r a).bits.length+1),by omega,hrun.trans hem⟩

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperPrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

 theorem prepare (u : ℕ) (w bs : List Bool) :
    UniformRun (processor C A)
      (wordState .sample (BitTape.ofWord w)
        (digit true::sep::(u.bits.map digit++[sep])) [] (bs.map digit).reverse)
      (2*u.bits.length+2*w.length+bs.length+12)
      (wordState (.active A.start) (tape (w.reverse.map some) [])
        ((trList [u,RawBinary.value (w++[true]),RawBinary.value (bs++[true])]).map FlatTM2.letters) [] []) := by
  let i:=BitTape.ofWord w
  let j:=tape (w.reverse.map some) []
  let p:=(u.bits.map digit).reverse
  let b:=(bs.map digit).reverse
  have h₀:=uniform_step _ _ _ (sample_end C A i (sep::(u.bits.map digit++[sep])) [] b [])
  have h₁:=uniform_step _ _ _ (pop_main C A .sampleSep .savePayload false (by intros;rfl)
    i sep (u.bits.map digit++[sep]) [] b [])
  have h₂:=save_run C A i u.bits [] b []
  simp only [List.append_nil] at h₂
  have h₃:=uniform_step _ _ _ (push_main C A .randomCons .randomOne sep (by intros;rfl) i [] p b [])
  have h₄:=uniform_step _ _ _ (push_main C A .randomOne .randomDrain (digit true) (by intros;rfl)
    i [sep] p b [])
  have h₅:=buf_run C A .randomDrain .requestCons false (by intros;rfl) i b [digit true,sep] p []
  simp only [b,List.reverse_reverse,List.length_reverse,List.length_map] at h₅
  have h₆:=uniform_step _ _ _ (push_main C A .requestCons .requestRead sep (by intros;rfl)
    i (bs.map digit++[digit true,sep]) p [] [])
  have h₇:=read_run C A .requestRead .requestOne (by intros;rfl) [] w
    (sep::(bs.map digit++[digit true,sep])) p [] []
  simp only [List.append_nil,←ofWord_tape] at h₇
  have h₈:=uniform_step _ _ _ (push_main C A .requestOne .requestDrain (digit true) (by intros;rfl)
    j (sep::(bs.map digit++[digit true,sep])) p (w.map digit).reverse [])
  have h₉:=buf_run C A .requestDrain .payloadCons false (by intros;rfl) j (w.map digit).reverse
    (digit true::sep::(bs.map digit++[digit true,sep])) p []
  simp only [List.reverse_reverse,List.length_reverse,List.length_map] at h₉
  have h₁₀:=uniform_step _ _ _ (push_main C A .payloadCons .payloadDrain sep (by intros;rfl) j
    (w.map digit++digit true::sep::(bs.map digit++[digit true,sep])) p [] [])
  have h₁₁:=pay_run C A .payloadDrain (.active A.start) (by intros;rfl) j p
    (sep::(w.map digit++digit true::sep::(bs.map digit++[digit true,sep]))) [] []
  simp only [p,List.reverse_reverse,List.length_reverse,List.length_map] at h₁₁
  have h:=(((((((((((h₀.trans h₁).trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).trans h₈).trans h₉).trans h₁₀).trans h₁₁)
  convert h using 1
  · omega
  · simp only [trList,List.map_append,List.map_cons,encodedNat,RawBits.bits_value,
      List.append_assoc,List.cons_append,List.nil_append,List.map_nil,j]

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)

 theorem value_lt (w : List Bool) : RawBinary.value w<2^w.length := by
  induction w with
  | nil=>simp [RawBinary.value]
  | cons b w ih=>
    rw [RawBinary.value_cons,Nat.bit_val,List.length_cons,pow_succ]
    cases b <;> simp only [Bool.toNat,Bool.cond_false,Bool.cond_true] <;> omega

 theorem sample_ready (b u : ℕ) (w bs : List Bool) (hb : bs.length=b) :
    TypedStack.run (processor C LiteralBound.program) (ready b u (BitTape.ofWord w)) bs=
      wordState .sample (BitTape.ofWord w)
        (digit true::sep::(u.bits.map digit++[sep])) [] (bs.map digit).reverse := by
  unfold ready
  rw [encodedList,encodedList,pow_bits,List.map_append,List.map_replicate,List.map_singleton]
  simp only [List.append_assoc,List.singleton_append,trList,List.map_nil]
  rw [←hb,sample_run]
  simp only [List.append_nil]

 theorem response_fixed (b u r a T : ℕ) (w bs : List Bool)
    (hb : bs.length=b) (hr : r=RawBinary.value (w++[true]))
    (ha : a=RawBinary.value (bs++[true])) (hc : RawProgram.randomCount (RawProgram.unpack u)=b)
    (hf : LiteralBound.finishes T u r a=true) :
    ∃t≤2*u.bits.length+2*w.length+b+12+T+(RawProgram.chosen (RawProgram.unpack u) r a).bits.length+1,
      UniformRun (processor C LiteralBound.program)
        (TypedStack.run (processor C LiteralBound.program) (ready b u (BitTape.ofWord w)) bs) t
        (ready b (Encodable.encode (RawProgram.next (RawProgram.unpack u) r a))
          (tape (w.reverse.map some) []) (RawProgram.chosen (RawProgram.unpack u) r a).bits.reverse true) := by
  obtain ⟨t,ht,hs⟩:=active_response C u r a T hf (tape (w.reverse.map some) [])
  have hp:=prepare C LiteralBound.program u w bs
  rw [←hr,←ha,hb] at hp
  rw [hc] at hs
  refine ⟨(2*u.bits.length+2*w.length+b+12)+t,by omega,?_⟩
  rw [sample_ready C b u w bs hb]
  exact hp.trans hs

 theorem response (b u r T : ℕ) (bs : List Bool)
    (hlen : 16*(T+1)≤bs.length) (hb : b+1≤T)
    (hu : u.bits.length+1≤T) (hw : (natCode (r+1)).length+1≤T)
    (hc : RawProgram.randomCount (RawProgram.unpack u)=b)
    (hf : ∀a<2^(b+1), (RawProgram.chosen (RawProgram.unpack u) (RawFinite.requestToken r) a).bits.length≤T ∧
      LiteralBound.finishes T u (RawFinite.requestToken r) a=true) :
    TypedStack.run (processor C LiteralBound.program) (ready b u (BitTape.ofWord (natCode (r+1)))) bs=
      ready b (Encodable.encode (RawProgram.next (RawProgram.unpack u) (RawFinite.requestToken r)
        (RawBinary.value (bs.take b++[true]))))
        (tape ((natCode (r+1)).reverse.map some) [])
        (RawProgram.chosen (RawProgram.unpack u) (RawFinite.requestToken r)
          (RawBinary.value (bs.take b++[true]))).bits.reverse true := by
  have htake : (bs.take b).length=b:=by simp only [List.length_take];omega
  have ha : RawBinary.value (bs.take b++[true])<2^(b+1):=by
    simpa only [List.length_append,List.length_singleton,htake] using value_lt (bs.take b++[true])
  obtain ⟨t,ht,hs⟩:=response_fixed C b u (RawFinite.requestToken r)
    (RawBinary.value (bs.take b++[true])) T (natCode (r+1)) (bs.take b) htake rfl rfl hc (hf _ ha).2
  have hbnd : t≤(bs.drop b).length:=by
    have hj:=(hf _ ha).1
    simp only [List.length_drop]
    omega
  conv_lhs => rw [←List.take_append_drop b bs,TypedStack.run_append]
  exact hs.mono rfl hbnd _ rfl

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperActive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical

 theorem physical_active (mult L t n k : ℕ) (v : RawCertificate.Certificate)
    (c : RuntimeCertificate.Cert) (hc : RuntimeCertificate.verify n k v c=true)
    (u : ℕ) (hu : u∈c.1)
    (hrc : RawProgram.randomCount (RawProgram.unpack u)=RuntimeCertificate.B k v)
    (z : MachineState (machine mult))
    (hz : CoreRep (uniform mult) (ready (RuntimeCertificate.B k v) u BitTape.blank [] true) z)
    (ht : 16*(c.2+1)≤32*(L+Nat.clog 2 (t+2)+1))
    (r : Fin n) (coins : Fin (requestBudget 64 1 L (t+1))→Bool) :
    let a:=RawBinary.value ((StackCompiler.alternate (List.ofFn coins)).take (RuntimeCertificate.B k v)++[true])
    let u':=Encodable.encode (RawProgram.next (RawProgram.unpack u) (RawFinite.requestToken r.val) a)
    let z':=requestStep (machine mult) 64 1 L (t+1) z r coins
    CoreRep (uniform mult) (ready (RuntimeCertificate.B k v) u' BitTape.blank [] true) z' ∧
      u'∈c.1 ∧ outputValue z'=RawProgram.chosen (RawProgram.unpack u) (RawFinite.requestToken r.val) a ∧
      outputValue z'<k := by
  dsimp only
  let bs:=StackCompiler.alternate (List.ofFn coins)
  let b:=RuntimeCertificate.B k v
  let a:=RawBinary.value (bs.take b++[true])
  have hv:=(RuntimeCertificate.verify_iff n k v c).mp hc
  have hn:=hv.2.2 u hu
  have hs:=(hn.2 r.val r.isLt)
  have hb : bs.length=32*(L+Nat.clog 2 (t+2)+1) := by
    exact request_half L (t+1) (List.ofFn coins) (by simp only [List.length_ofFn])
  have hlen : 16*(c.2+1)≤bs.length := by omega
  have ha : a<2^(b+1) := by
    have htlen : (bs.take b).length=b:=by simp only [List.length_take];dsimp [b] at *;omega
    simpa only [List.length_append,List.length_singleton,htlen] using value_lt (bs.take b++[true])
  have hf:=hs.2 a ha
  have hm:=matches_coins (hz.install (natCode (r.val+1))) (List.ofFn coins)
    (by rw [List.length_ofFn];exact request_even L (t+1))
  have he:=response (literalC mult) b u r.val c.2 bs hlen hv.2.1 hn.1 hs.1 hrc
    (fun a ha=>(hs.2 a ha).2.2)
  change TypedStack.run (uniform mult)
    (install (ready b u BitTape.blank [] true) (natCode (r.val+1))) bs=_ at he
  rw [he] at hm
  have hmout := hm.output
  have ho : outputValue (requestStep (machine mult) 64 1 L (t+1) z r coins)=
      RawProgram.chosen (RawProgram.unpack u) (RawFinite.requestToken r.val) a := by
    simp only [machine,requestStep] at ⊢
    rw [outputValue,hmout]
    simp only [TypedStack.encode,ready,wordState]
    rw [List.reverse_reverse,bitValue_eq,RawBinary.value_bits]
  refine ⟨?_,hf.2.1,ho,ho.trans_lt hf.1⟩
  refine ⟨tape ((natCode (r.val+1)).reverse.map some) [],
    (RawProgram.chosen (RawProgram.unpack u) (RawFinite.requestToken r.val) a).bits.reverse,?_⟩
  simpa only [machine,requestStep,frame,ready,wordState] using hm

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open scoped Classical

 theorem tapeCoins_word {H b N : ℕ} (hn : 2*(H*b)≤N) (bs : Fin N→Bool) :
    BinaryTape.word (tapeCoins hn bs)=(StackCompiler.alternate (List.ofFn bs)).take (H*b) := by
  rw [BinaryTape.word_ofFn]
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_take,StackCompiler.alternate_length]
    omega
  · intro i h₁ h₂
    simp only [List.length_ofFn] at h₁
    simp only [List.getElem_ofFn,List.getElem_take]
    rw [StackCompiler.alternate_get _ i (by simp only [List.length_ofFn];omega),List.getElem_ofFn]
    unfold tapeCoins coinIndex
    congr 1
    apply Fin.ext
    simp only [Prod.mk.eta,Equiv.apply_symm_apply]

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperSlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open TypedStack RawCertificate
open scoped Classical

 theorem slow_request {n k : ℕ} (mult L t : ℕ) (hk : 0<k)
    (a b : State _ _)
    (h : SlowLink (uniform mult) a b) (z : MachineState (machine mult))
    (hz : CoreRep (uniform mult) a z) (r : Fin n)
    (coins : Fin (requestBudget 64 1 L (t+1))→Bool) :
    let z':=requestStep (machine mult) 64 1 L (t+1) z r coins
    CoreRep (uniform mult) b z' ∧ selectedLabel hk z'=⟨0,hk⟩ ∧
      z'.yielded=true ∧ outputValue z'<k := by
  dsimp only
  have hh:=hz.slow (natCode (r.val+1)) (List.ofFn coins)
    (by simpa only [List.length_ofFn] using request_even L (t+1))
    (by simpa only [List.length_ofFn] using request_ge L (t+1)) h
  have ho : outputValue (requestStep (machine mult) 64 1 L (t+1) z r coins)=0 := by
    have hout : (requestStep (machine mult) 64 1 L (t+1) z r coins).outputRev=[] := hh.2
    simp only [outputValue,hout,List.reverse_nil,bitValue]
  refine ⟨hh.1,?_,hh.1.yielded,by omega⟩
  apply Fin.ext
  simp only [selectedLabel,ho,Nat.zero_mod]

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperTyped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open TypedStack RawCertificate
open scoped Classical

 theorem typed_step {n k : ℕ} (mult L t : ℕ) (hk : 0<k) (hkn : k≤n)
    (v : Certificate) (hR : 0 < restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (c : RuntimeCertificate.Cert) (hc : RuntimeCertificate.verify n k v c=true)
    (s : TC n k v) (z : MachineState (machine mult)) (hz : represents mult v c s z)
    (ht : 16*(c.2+1)≤32*(L+Nat.clog 2 (t+2)+1))
    (r : Fin n) (coins : Fin (requestBudget 64 1 L (t+1))→Bool) :
    let bs:=tapeCoins (sample_bound L t n k v c hc ht) coins
    let z':=requestStep (machine mult) 64 1 L (t+1) z r coins
    represents mult v c (tcNext hk hkn v hR hT s r bs) z' ∧
      selectedLabel hk z'=tcLabel hk v hT s r bs ∧ z'.yielded=true ∧ outputValue z'<k := by
  dsimp only
  let bs:=tapeCoins (sample_bound L t n k v c hc ht) coins
  have ha : RawBinary.value ((StackCompiler.alternate (List.ofFn coins)).take (RuntimeCertificate.B k v)++[true])=
      BinaryTape.token bs := by
    unfold BinaryTape.token
    rw [tapeCoins_word,RuntimeCertificate.B,RawMetric.horizon_eq]
  have hh:=physical_active mult L t n k v c hc (Encodable.encode (RawFinite.repr v s)) hz.1
    (by rw [RawProgram.unpack_encode];rfl) z hz.2 ht r coins
  dsimp only at hh
  rw [RawProgram.unpack_encode,ha,RawFinite.next_token hk hkn v hR hT s r bs,
    RawFinite.choose_token hk v hT s r bs] at hh
  refine ⟨⟨hh.2.1,hh.1⟩,?_,hh.1.yielded,hh.2.2.2⟩
  apply Fin.ext
  change outputValue _ % k=(tcLabel hk v hT s r bs).val
  rw [hh.2.2.1,Nat.mod_eq_of_lt (Fin.isLt _)]

 theorem initial_represents {n k : ℕ} (mult : ℕ) (hkn : k≤n) (v : Certificate) (hR : 0 < restart v)
    (c : RuntimeCertificate.Cert) (hc : RuntimeCertificate.verify n k v c=true)
    (z : MachineState (machine mult))
    (hz : CoreRep (uniform mult) (ready (RuntimeCertificate.B k v)
      (Encodable.encode (RawProgram.initial n k v)) BitTape.blank [] true) z) :
    represents mult v c (tcInitial hkn v hR) z := by
  have hh:=((RuntimeCertificate.verify_iff n k v c).mp hc).1
  rw [RawFinite.initial_repr hkn v hR] at hh hz
  exact ⟨hh,hz⟩

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperReachable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open TypedStack RawCertificate
open scoped Classical

 theorem live_next_oai {n k : ℕ} (mult L : ℕ) (hk : 0<k) (hkn : k≤n)
    (v : Certificate) (hR : 0 < restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (c : RuntimeCertificate.Cert) (hc : RuntimeCertificate.verify n k v c=true)
    (delay : ℕ) (hd : 2^c.2≤delay) (a : CoreState mult)
    (p : Prefix (uniform mult) a (ready (RuntimeCertificate.B k v)
      (Encodable.encode (RawProgram.initial n k v)) BitTape.blank [] true) delay)
    (t : ℕ) (z : MachineState (machine mult)) (hz : Live (n:=n) (k:=k) mult v c delay p.state t z)
    (r : Fin n) (coins : Fin (requestBudget 64 1 L (t+1))→Bool) :
    let z':=requestStep (machine mult) 64 1 L (t+1) z r coins
    Live (n:=n) (k:=k) mult v c delay p.state (t+1) z' ∧ z'.yielded=true ∧ outputValue z'<k := by
  dsimp only
  rcases hz with ⟨ht,hz⟩|⟨ht,b,hz⟩
  · have hh:=slow_request mult L t hk _ _ (p.next t ht) z hz r coins
    dsimp only at hh
    refine ⟨?_,hh.2.2⟩
    by_cases ht' : t+1<delay
    · exact Or.inl ⟨ht',hh.1⟩
    · have he : t+1=delay:=by omega
      have hh':=hh.1
      have hstate : p.state (t+1)=ready (RuntimeCertificate.B k v)
          (Encodable.encode (RawProgram.initial n k v)) BitTape.blank [] true :=
        (congrArg p.state he).trans p.finish
      rw [hstate] at hh'
      exact Or.inr ⟨by omega,tcInitial hkn v hR,initial_represents mult hkn v hR c hc _ hh'⟩
  · have hh:=typed_step mult L t hk hkn v hR hT c hc b z hz (process_bound L t c.2 delay hd ht) r coins
    dsimp only at hh
    exact ⟨Or.inr ⟨by omega,_,hh.1⟩,hh.2.2⟩

end UniformKServer.UniformWrapper

end

end OAI
end

theorem solution : type_of% @OAI.UniformKServer.UniformWrapper.live_next_oai := @OAI.UniformKServer.UniformWrapper.live_next_oai
