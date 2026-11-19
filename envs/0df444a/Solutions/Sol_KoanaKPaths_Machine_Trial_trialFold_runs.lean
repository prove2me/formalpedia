-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.trialFold_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:38.450364+00:00
-- url     : https://prove2.me/submissions/ca51033e-cbe3-4ba5-8f94-0c5b7f41bd50

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Definitions.Def_KoanaKPaths_TapeSampling
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_Balanced_insert_exec
import Theorems.Thm_KoanaKPaths_Machine_Trial_nativeTrial_runs
import Theorems.Thm_KoanaKPaths_Main_denseLayer_correct
import Theorems.Thm_KoanaKPaths_Main_graphNorm_width
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_compile_correct
import Theorems.Thm_NLogN_smul_runs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

namespace KoanaKPaths.Machine.Native
open NLogN
variable {S P : ℕ} {I : List Sym} {iprog : Fin P→IStmt S P} {p q : IStmt S P} {s s1 s2 : IState S} {c d : ℕ}

lemma mono (h : IRuns I iprog p s s1 c) (hc : c ≤ d) : IRuns I iprog p s s1 d := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t,ht.trans hc,h⟩
lemma of_exec (h : IExec I iprog p s s1 c) : IRuns I iprog p s s1 c := ⟨c,le_rfl,h⟩


lemma seq (h1 : IRuns I iprog p s s1 c) (h2 : IRuns I iprog q s1 s2 d) :
    IRuns I iprog (.seq p q) s s2 (c+d) := by
  obtain ⟨c',hc,h1⟩ := h1
  obtain ⟨d',hd,h2⟩ := h2
  exact ⟨c'+d',Nat.add_le_add hc hd,.seq h1 h2⟩


lemma loopT {i : Fin S} {f : Cls → Bool} (hf : f (s.cl i) = true)
    (h1 : IRuns I iprog p s s1 c) (h2 : IRuns I iprog (.loop i f p) s1 s2 d) :
    IRuns I iprog (.loop i f p) s s2 (c+d+30) := by
  obtain ⟨c',hc,h1⟩ := h1
  obtain ⟨d',hd,h2⟩ := h2
  exact ⟨c'+d'+30,by omega,.loopT hf h1 h2⟩
lemma loopF {i : Fin S} {f : Cls → Bool} (hf : f (s.cl i) = false) :
    IRuns I iprog (.loop i f p) s s 30 := of_exec (.loopF hf)

end KoanaKPaths.Machine.Native

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine

variable {S : ℕ}



@[simp] lemma upd_G_self (s : IState S) (i : Fin S) (L : List Item) : (s.upd i L).G i = L := by
  simp [IState.upd]
@[simp] lemma upd_G_ne (s : IState S) {i j : Fin S} (h : j ≠ i) (L : List Item) :
    (s.upd i L).G j = s.G j := by simp [IState.upd,h]
@[simp] lemma upd_same (s : IState S) (i : Fin S) : s.upd i (s.G i) = s := by
  cases s
  simp [IState.upd]

@[simp] lemma upd_upd (s : IState S) (i : Fin S) (L M : List Item) :
    (s.upd i L).upd i M = s.upd i M := by
  cases s
  simp [IState.upd,Function.update_idem]




















end KoanaKPaths.Machine

end

section

namespace KoanaKPaths.Machine
open NLogN
variable {S P : ℕ}



lemma liftClosed_exec (I : List Sym) (prog : Fin P → IStmt S P)
    {p : IStmt S 0} {s s' : IState S} {c : ℕ}
    (h : IExec I Fin.elim0 p s s' c) : IExec I prog (liftClosed p) s s' c := by
  induction h with
  | skip s => exact .skip s
  | op h => exact .op h
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | iteT h _ ih => exact .iteT h ih
  | iteF h _ ih => exact .iteF h ih
  | loopT h _ _ ih1 ih2 => exact .loopT h ih1 ih2
  | loopF h => exact .loopF h
  | call => exact Fin.elim0 ‹Fin 0›

lemma liftClosed_runs (I : List Sym) (prog : Fin P → IStmt S P)
    {p : IStmt S 0} {s s' : IState S} {c : ℕ}
    (h : IRuns I Fin.elim0 p s s' c) : IRuns I prog (liftClosed p) s s' c := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t,ht,liftClosed_exec I prog h⟩

end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 400000
open scoped BigOperators
namespace KoanaKPaths.ExteriorCoordinates


























lemma subsetOrder_length (k : ℕ) : (subsetOrder k).length = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [subsetOrder,ih,pow_succ]; omega











lemma zipWith_same_map {α β γ δ : Type} (L : List α) (f : α → β) (g : α → γ) (h : β → γ → δ) :
    List.zipWith h (L.map f) (L.map g) = L.map (fun x => h (f x) (g x)) := by
  induction L <;> simp_all













lemma subsetOrder_last (k : ℕ) : (subsetOrder k).getLast? = some Finset.univ := by
  induction k with
  | zero => simp [subsetOrder]
  | succ k ih =>
    have hu : upperSet (Finset.univ : Finset (Fin k)) = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro r
      refine Fin.lastCases ?_ (fun x => ?_) r
      · simp [upperSet]
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_map.mpr ⟨x,Finset.mem_univ x,rfl⟩
    have hn : (subsetOrder k).map upperSet ≠ [] := by
      have hl := subsetOrder_length k
      intro he
      have := congrArg List.length he
      simp only [List.length_map,List.length_nil] at this
      have hp : 0 < 2^k := by positivity
      omega
    rw [subsetOrder,List.getLast?_append_of_ne_nil _ hn,List.getLast?_map,ih]
    simp [hu]

lemma coefficientList_last {k : ℕ} (A : Coordinates k) :
    (coefficientList A).getLast? = some (A Finset.univ) := by
  simp [coefficientList,List.getLast?_map,subsetOrder_last]

lemma coefficientList_add {k : ℕ} (A B : Coordinates k) :
    coefficientList (A+B) = List.zipWith (·+·) (coefficientList A) (coefficientList B) := by
  simp only [coefficientList,zipWith_same_map]
  rfl



lemma coefficientList_zero (k : ℕ) : coefficientList (0 : Coordinates k) = List.replicate (2^k) 0 := by
  change (subsetOrder k).map (fun _ => (0 : ℤ)) = _
  simp [List.map_const,subsetOrder_length]







end KoanaKPaths.ExteriorCoordinates

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}








lemma itemState_ext {s t : IState S} (hG : ∀ i, s.G i=t.G i) (hip : s.ip=t.ip)
    (hout : s.out=t.out) : s=t := by
  cases s with
  | mk G ip o =>
    cases t with
    | mk H jp p =>
      have hh : G=H := funext hG
      cases hh
      cases hip
      cases hout
      rfl

end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates

lemma arrayFold_coeff {k : ℕ} (as : List (Coordinates k)) (a : Coordinates k) :
    (as.map coefficientList).foldl (List.zipWith (·+·)) (coefficientList a) =
      coefficientList (a+as.sum) := by
  induction as generalizing a with
  | nil => simp
  | cons b as ih =>
    simp only [List.map_cons,List.foldl_cons,List.sum_cons]
    rw [← coefficientList_add,ih]
    congr 1
    exact add_assoc _ _ _

lemma arraySum_coeff {k : ℕ} (as : List (Coordinates k)) :
    arraySum k (as.map coefficientList)=coefficientList as.sum := by
  unfold arraySum
  rw [← coefficientList_zero,arrayFold_coeff,zero_add]



lemma sum_finRange {A : Type} [AddCommMonoid A] (n : ℕ) (f : Fin n→A) :
    ((List.finRange n).map f).sum=∑ i, f i := by
  rw [← List.sum_toFinset _ (List.nodup_finRange n),List.toFinset_finRange]








lemma denseOutput_correct {n k ℓ : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k ℓ) (a : Fin ℓ) :
    denseOutput arcs σ R a=coefficientList (graphOutput arcs σ R a) := by
  unfold denseOutput
  simp only [denseLayer_correct]
  have hm : (List.finRange n).map (fun v => coefficientList (graphLayer arcs σ R k v a)) =
      ((List.finRange n).map (fun v => graphLayer arcs σ R k v a)).map coefficientList := by
    simp only [List.map_map,Function.comp_def]
  rw [hm,arraySum_coeff,sum_finRange]
  rfl

lemma denseTrial_correct {n k ℓ : ℕ} (hk : 1≤k) (arcs : List (Fin n × Fin n))
    (σ : Labels n k) (R : SketchSigns n k ℓ) :
    denseTrial arcs σ R=(sketchFrobSq (walkTensor n arcs k) σ R k).toNat := by
  unfold denseTrial
  simp only [denseOutput_correct,coefficientList_last,Option.getD_some]
  rw [sum_finRange,graph_dp_sketch hk]

lemma denseTrial_eq_trialNumerator {n k : ℕ} (hk : 1≤k) (arcs : List (Fin n × Fin n))
    (σ : Labels n k) (R : SketchSigns n k k) :
    denseTrial arcs σ R=trialNumerator (walkTensor n arcs k) (σ,R) :=
  denseTrial_correct hk arcs σ R

end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
open scoped BigOperators
namespace KoanaKPaths.Main





lemma graphNorm_nonneg {n k ℓ : ℕ} (arcs : List (Fin n × Fin n))
    (σ : Labels n k) (R : SketchSigns n k ℓ) :
    0≤ ∑ a : Fin ℓ, (graphOutput arcs σ R a Finset.univ)^2 :=
  Finset.sum_nonneg (fun a _ => sq_nonneg _)



lemma denseTrial_cast {n k ℓ : ℕ} (arcs : List (Fin n × Fin n))
    (σ : Labels n k) (R : SketchSigns n k ℓ) :
    (denseTrial arcs σ R : ℤ)=∑ a : Fin ℓ, (graphOutput arcs σ R a Finset.univ)^2 := by
  unfold denseTrial
  simp only [denseOutput_correct,ExteriorCoordinates.coefficientList_last,Option.getD_some]
  rw [sum_finRange]
  exact Int.toNat_of_nonneg (graphNorm_nonneg arcs σ R)

lemma denseTrial_width {n k ℓ : ℕ} (arcs : List (Fin n × Fin n))
    (σ : Labels n k) (R : SketchSigns n k ℓ) :
    zsz (denseTrial arcs σ R : ℤ)≤ trialWidth n k ℓ := by
  rw [denseTrial_cast]
  exact graphNorm_width arcs σ R

lemma trialWidth_polynomial (n k : ℕ) : trialWidth n k k≤20*(1+n+k)^2 := by
  unfold trialWidth outputExponent
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (n*k)]

end KoanaKPaths.Main

namespace KoanaKPaths.Machine.Norm




end KoanaKPaths.Machine.Norm

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main









lemma Ready.upd {n k : ℕ} {s : IState NS} {arcs : List (Fin n × Fin n)} (h : Ready (k := k) s arcs)
    (j : Fin NS) (hj : j∉readyRegisters) (xs : List Item) : Ready (k := k) (s.upd j xs) arcs := by
  intro r hr
  have hne : r≠j := by rintro rfl; exact hj hr
  simpa [IState.upd,hne] using h r hr



end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
lemma trialNumerator_word_width {n k : ℕ} (ω : Fin (trialBits n k)→Bool)
    (arcs : List (Fin n × Fin n)) (hk : 1≤ k) :
    zsz (trialNumerator (walkTensor n arcs k) (trialEquiv n k ω) : ℤ)≤ wordWidth n k := by
  rw [←denseTrial_eq_trialNumerator hk]
  have h := denseTrial_width arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2
  have hp := trialWidth_polynomial n k
  unfold wordWidth
  omega
end KoanaKPaths.Machine.Trial

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Balanced



















lemma carryInsert_count (l : ℕ) (x : ℤ) (cs : List Chunk) :
    chunkCount (carryInsert l x cs)=2^l+chunkCount cs := by
  induction cs generalizing l x with
  | nil => simp [chunkCount,carryInsert]
  | cons c cs ih =>
    rcases c with ⟨j,y⟩
    simp only [carryInsert]
    split_ifs with h
    · subst j
      rw [ih]
      simp only [chunkCount,List.map_cons,List.sum_cons,pow_succ]
      omega
    · simp [chunkCount]












lemma carryInsert_order (l : ℕ) (x : ℤ) (cs : List Chunk)
    (hcs : cs.Pairwise (fun a b => a.1<b.1)) (hl : ∀ c∈cs, l≤ c.1) :
    (carryInsert l x cs).Pairwise (fun a b => a.1<b.1) ∧ ∀ c∈carryInsert l x cs, l≤ c.1 := by
  induction cs generalizing l x with
  | nil => simp [carryInsert]
  | cons c cs ih =>
    rcases c with ⟨j,y⟩
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hcs
    have hj : l≤ j := hl (j,y) (by simp)
    simp only [carryInsert]
    split_ifs with he
    · subst j
      have hnext : ∀ c∈cs, l+1≤ c.1 := by intro c hc; have hh := hhead c hc; omega
      have hh := ih (l+1) (x+y) htail hnext
      exact ⟨hh.1,fun c hc => (by have := hh.2 c hc; omega)⟩
    · constructor
      · apply List.Pairwise.cons
        · intro c hc
          have hh : j≤ c.1 := by
            simp only [List.mem_cons] at hc
            rcases hc with rfl|hc
            · exact le_rfl
            · exact Nat.le_of_lt (hhead c hc)
          omega
        · exact hcs
      · intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl|hc
        · exact le_rfl
        · exact hl c (by simpa only [List.mem_cons] using hc)











end KoanaKPaths.Machine.Balanced

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Balanced



lemma counterCode_shift (l j : ℕ) (y : ℤ) (cs : List Chunk) (h : l<j) :
    counterCode l ((j,y)::cs)=.int 0::counterCode (l+1) ((j,y)::cs) := by
  have hh : j-l=(j-(l+1))+1 := by omega
  simp only [counterCode,hh,List.replicate_succ,List.cons_append]

lemma counterCode_carry_shift (l : ℕ) (x : ℤ) (cs : List Chunk)
    (hs : cs.Pairwise (fun a b => a.1<b.1)) (hl : ∀ c∈cs, l+1≤ c.1) :
    counterCode l (carryInsert (l+1) x cs)=.int 0::counterCode (l+1) (carryInsert (l+1) x cs) := by
  have hbound := (carryInsert_order (l+1) x cs hs hl).2
  have hn : carryInsert (l+1) x cs ≠ [] := by
    have hc := carryInsert_count (l+1) x cs
    intro he
    rw [he] at hc
    have hpos : 0<2^(l+1) := by positivity
    simp only [chunkCount,List.map_nil,List.sum_nil] at hc
    omega
  cases hh : carryInsert (l+1) x cs with
  | nil => exact False.elim (hn hh)
  | cons c rest =>
    rcases c with ⟨j,y⟩
    apply counterCode_shift
    have h := hbound (j,y) (by simp [hh])
    change l+1≤ j at h
    omega

/-- The occupancy representation determines exactly the initial carry run. -/
lemma carry_encoding (l : ℕ) (x : ℤ) (cs : List Chunk)
    (hs : cs.Pairwise (fun a b => a.1<b.1)) (hl : ∀ c∈cs, l≤ c.1) :
    ∃ (ys rest : List ℤ) (zero : Bool) (bt : List Item),
      cs.map Prod.snd=ys++rest ∧
      counterCode l cs=List.replicate ys.length (.int 1) ++ stopBits zero bt ∧
      (carryInsert l x cs).map Prod.snd=(x+ys.sum)::rest ∧
      counterCode l (carryInsert l x cs)=List.replicate ys.length (.int 0) ++
        .int 1::nextBits zero bt ∧
      carryCharge l x cs=mergeCost x ys+33*ys.length+
        2*moveCost (zsz (x+ys.sum))+79 := by
  induction cs generalizing l x with
  | nil =>
    refine ⟨[],[],false,[],?_,?_,?_,?_,?_⟩ <;>
      simp [counterCode,carryInsert,carryCharge,mergeCost,stopBits,nextBits]
    omega
  | cons c cs ih =>
    rcases c with ⟨j,y⟩
    obtain ⟨hh,ht⟩ := List.pairwise_cons.mp hs
    have hj : l≤ j := hl (j,y) (by simp)
    by_cases he : j=l
    · subst j
      have ht' : ∀ c∈cs, l+1≤ c.1 := by intro c hc; have h := hh c hc; omega
      obtain ⟨ys,rest,z,bt,hv,hb,hi,hbi,hcost⟩ := ih (l+1) (x+y) ht ht'
      refine ⟨y::ys,rest,z,bt,?_,?_,?_,?_,?_⟩
      · simp [hv]
      · simp [counterCode,hb,List.replicate_succ]
      · simpa [carryInsert,List.sum_cons,add_assoc] using hi
      · simp only [carryInsert,ite_true]
        rw [counterCode_carry_shift l (x+y) cs ht ht',hbi]
        simp [List.replicate_succ]
      · simp only [carryCharge,ite_true]
        rw [hcost]
        simp only [mergeCost,List.length_cons,List.sum_cons,← add_assoc]
        omega
    · have hj' : l<j := by omega
      refine ⟨[],y::cs.map Prod.snd,true,
        counterCode (l+1) ((j,y)::cs),?_,?_,?_,?_,?_⟩
      · simp
      · simpa [stopBits] using counterCode_shift l j y cs hj'
      · simp [carryInsert,he]
      · simp [carryInsert,he,counterCode,nextBits]
      · simp [carryCharge,he,mergeCost]; omega

lemma insertCost_le (x : ℤ) (ys : List ℤ) (zero : Bool) :
    insertCost x ys zero ≤ mergeCost x ys+33*ys.length+
      2*moveCost (zsz (x+ys.sum))+79 := by
  cases zero <;> simp [insertCost] <;> omega

end KoanaKPaths.Machine.Balanced

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Balanced
attribute [local simp] Partials Bits Carry Restore Sum

lemma insert_runs (I : List Sym) (s : IState NS) (x : ℤ) (cs : List Chunk)
    (bt pt ct : List Item) (hs : cs.Pairwise (fun a b => a.1<b.1))
    (hb : s.G Bits=counterCode 0 cs ++ bt)
    (hp : s.G Partials=(cs.map Prod.snd).map Item.int ++ pt)
    (hc : s.G Carry=.int x::ct) (hr : s.G Restore=[]) :
    IRuns I Fin.elim0 insert s
      (((s.upd Bits (counterCode 0 (carryInsert 0 x cs) ++ bt)).upd Partials
        (((carryInsert 0 x cs).map Prod.snd).map Item.int ++ pt)).upd Carry ct)
      (carryCharge 0 x cs) := by
  obtain ⟨ys,rest,z,tail,hv,hb',hi,hbi,hcost⟩ :=
    carry_encoding 0 x cs hs (by intro c hc; omega)
  have hbits : s.G Bits=List.replicate ys.length (.int 1) ++ stopBits z (tail++bt) := by
    rw [hb,hb']
    cases z <;> simp [stopBits,List.append_assoc]
  have hpart : s.G Partials=ys.map Item.int ++ (rest.map Item.int ++ pt) := by
    rw [hp,hv,List.map_append,List.append_assoc]
  have hh := insert_exec I s x ys z (tail++bt) (rest.map Item.int ++ pt) ct hbits hpart hc hr
  have he : (((s.upd Bits (List.replicate ys.length (.int 0) ++
      .int 1::nextBits z (tail++bt))).upd Partials
      (.int (x+ys.sum)::(rest.map Item.int ++ pt))).upd Carry ct) =
      (((s.upd Bits (counterCode 0 (carryInsert 0 x cs) ++ bt)).upd Partials
        (((carryInsert 0 x cs).map Prod.snd).map Item.int ++ pt)).upd Carry ct) := by
    rw [hi,hbi]
    cases z <;> simp [nextBits,List.append_assoc]
  rw [he] at hh
  exact Native.mono (Native.of_exec hh) (by rw [hcost]; exact insertCost_le x ys z)





end KoanaKPaths.Machine.Balanced

end

section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main Balanced

attribute [local simp] TrialCounter Coins Norm.Sum Balanced.Carry Balanced.Bits Balanced.Partials Balanced.Restore










lemma trialFold_runs (I : List Sym) (s : IState NS) {n k : ℕ}
    (arcs : List (Fin n × Fin n)) (os : List (Fin (trialBits n k)→Bool))
    (cs : List Chunk) (tail bt pt : List Item) (hk : 1≤ k) (hr : Ready (k := k) s arcs)
    (hc : s.G TrialCounter=List.replicate os.length .mark)
    (hCoins : s.G Coins=trialStream os++tail)
    (hBits : s.G Balanced.Bits=counterCode 0 cs++bt)
    (hPart : s.G Balanced.Partials=(cs.map Prod.snd).map Item.int ++ pt)
    (hRestore : s.G Balanced.Restore=[]) (hs : cs.Pairwise (fun a b => a.1< b.1)) :
    IRuns I Wedge.prog trialFold s (trialFoldState s arcs os cs tail bt pt)
      (trialFoldBaseCost n k arcs.length*os.length+accumulateCharge cs (numerators arcs os)+30) := by
  induction os generalizing s cs with
  | nil =>
    have he : trialFoldState (k := k) s arcs [] cs tail bt pt=s := by
      simp only [trialFoldState,numerators,List.map_nil,accumulate]
      have hc0 : s.G TrialCounter=[] := by simpa using hc
      have hco : s.G Coins=tail := by simpa [trialStream] using hCoins
      rw [←hc0,←hco,←hBits,←hPart]
      simp
    rw [he]
    simpa [trialFold,numerators,accumulateCharge] using
      (Native.loopF (I := I) (iprog := Wedge.prog) (p := .seq (.op (.unmark TrialCounter))
        (.seq nativeTrial (.seq (.op (.mv Norm.Sum Balanced.Carry)) (liftClosed Balanced.insert))))
        (s := s) (by simp [IState.cl,hc,cls]))
  | cons ω os ih =>
    let x : ℤ := trialNumerator (walkTensor n arcs k) (trialEquiv n k ω)
    let nextCs := carryInsert 0 x cs
    let rest := trialStream os++tail
    let s0 := s.upd TrialCounter (List.replicate os.length .mark)
    let s1 := (s0.upd Coins rest).upd Norm.Sum (.int x::s.G Norm.Sum)
    let s2 := (s1.upd Norm.Sum (s.G Norm.Sum)).upd Balanced.Carry (.int x::s.G Balanced.Carry)
    let s3 := ((s2.upd Balanced.Bits (counterCode 0 nextCs++bt)).upd Balanced.Partials
      ((nextCs.map Prod.snd).map Item.int ++ pt)).upd Balanced.Carry (s.G Balanced.Carry)
    have h0 : IExec I Wedge.prog (.op (.unmark TrialCounter)) s s0 1 :=
      .op (.unmark (by simpa [List.replicate_succ] using hc))
    have h1 : IRuns I Wedge.prog nativeTrial s0 s1 (nativeTrialCost n k arcs.length) := by
      have h := nativeTrial_runs I s0 ω arcs rest hk (hr.upd TrialCounter (by decide) _) (by
        simpa [s0,trialStream,rest,List.map_append,List.append_assoc] using hCoins)
      simpa [s1,s0,x] using h
    have h2 : IExec I Wedge.prog (.op (.mv Norm.Sum Balanced.Carry)) s1 s2 (2*moveCost (zsz x)+19) := by
      have h := IExec.op (I := I) (iprog := Wedge.prog) (IOp.Step.mv (s := s1) (i := Norm.Sum)
        (j := Balanced.Carry) (a := x) (L := s.G Norm.Sum) (by decide) (by simp [s1]))
      simpa [s2,s1,s0] using h
    have h3 : IRuns I Wedge.prog (liftClosed Balanced.insert) s2 s3 (carryCharge 0 x cs) := by
      exact liftClosed_runs I Wedge.prog (Balanced.insert_runs I s2 x cs bt pt (s.G Balanced.Carry) hs
        (by simp [s2,s1,s0,hBits]) (by simp [s2,s1,s0,hPart]) (by simp [s2])
        (by simp [s2,s1,s0,hRestore]))
    have hs3 : s3=(((s.upd TrialCounter (List.replicate os.length .mark)).upd Coins rest).upd Balanced.Bits
        (counterCode 0 nextCs++bt)).upd Balanced.Partials ((nextCs.map Prod.snd).map Item.int ++ pt) := by
      apply itemState_ext
      · intro r
        by_cases h79 : r=79 <;> by_cases h104 : r=104 <;>
          simp [s3,s2,s1,s0,IState.upd,Function.update_apply,h79,h104]
      · rfl
      · rfl
    have hr3 : Ready (k := k) s3 arcs := by
      rw [hs3]
      exact (((hr.upd TrialCounter (by decide) _).upd Coins (by decide) _).upd Balanced.Bits (by decide) _).upd Balanced.Partials (by decide) _
    have ht := ih s3 nextCs hr3 (by simp [s3,s2,s1,s0]) (by simp [s3,s2,s1,s0,rest])
      (by simp [s3]) (by simp [s3]) (by simp [s3,s2,s1,s0,hRestore])
      ((carryInsert_order 0 x cs hs (by intro c hc; omega)).1)
    have hpost : trialFoldState s3 arcs os nextCs tail bt pt=trialFoldState s arcs (ω::os) cs tail bt pt := by
      apply itemState_ext
      · intro r
        by_cases h101 : r=101 <;> by_cases h52 : r=52 <;> by_cases h103 : r=103 <;> by_cases h102 : r=102 <;>
          simp [trialFoldState,hs3,numerators,accumulate,nextCs,x,IState.upd,Function.update_apply,h101,h52,h103,h102]
      · rfl
      · rfl
    rw [hpost] at ht
    have hcond : decide (s.cl TrialCounter=Cls.mark)=true := by simp [IState.cl,hc,List.replicate_succ,cls]
    have hbody := Native.seq (Native.of_exec h0) (Native.seq h1 (Native.seq (Native.of_exec h2) h3))
    have hh := Native.loopT hcond hbody ht
    change IRuns I Wedge.prog trialFold s _ _ at hh
    apply Native.mono hh
    have hw : zsz x≤ wordWidth n k := trialNumerator_word_width ω arcs hk
    have hm : 2*moveCost (zsz x)+19≤1000*(wordWidth n k+1) := by unfold moveCost; omega
    simp only [numerators,List.map_cons,accumulateCharge,List.length_cons]
    unfold trialFoldBaseCost
    dsimp only [x,nextCs] at *
    nlinarith

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (os : List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool))
  (cs : List.{0} KoanaKPaths.Machine.Balanced.Chunk) (tail bt pt : List.{0} NLogN.Item)
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
  (hr : @KoanaKPaths.Machine.Trial.Ready n k s arcs)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.TrialCounter)
      (@List.replicate.{0} NLogN.Item (@List.length.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool) os)
        NLogN.Item.mark))
  (hCoins :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Coins)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@KoanaKPaths.Machine.Trial.trialStream n k os) tail))
  (hBits :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Balanced.Bits)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.Balanced.counterCode (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) cs) bt))
  (hPart :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Balanced.Partials)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.map.{0, 0} (Prod.{0, 0} Nat Int) Int (@Prod.snd.{0, 0} Nat Int) cs))
        pt))
  (hRestore :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Balanced.Restore)
      (@List.nil.{0} NLogN.Item))
  (hs :
    @List.Pairwise.{0} KoanaKPaths.Machine.Balanced.Chunk
      (fun (a b : KoanaKPaths.Machine.Balanced.Chunk) =>
        @LT.lt.{0} Nat instLTNat (@Prod.fst.{0, 0} Nat Int a) (@Prod.fst.{0, 0} Nat Int b))
      cs),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.trialFold s
    (@KoanaKPaths.Machine.Trial.trialFoldState n k s arcs os cs tail bt pt)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (KoanaKPaths.Machine.Trial.trialFoldBaseCost n k (@List.length.{0} (Prod.{0, 0} (Fin n) (Fin n)) arcs))
          (@List.length.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool) os))
        (KoanaKPaths.Machine.Balanced.accumulateCharge cs (@KoanaKPaths.Machine.Trial.numerators n k arcs os)))
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by
  exact @KoanaKPaths.Machine.Trial.trialFold_runs
