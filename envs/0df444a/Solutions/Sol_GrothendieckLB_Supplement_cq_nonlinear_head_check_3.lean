-- Prove2me | solution 3 for GrothendieckLB.Supplement.cq_nonlinear_head_check
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:15:19.15283+00:00
-- url     : https://prove2.me/submissions/e842295d-85d8-48c0-ab5c-179720279224
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_cq_packed_full_coefficient_bounds
import Definitions.Def_GrothendieckLB_Supplement_cqReplayInitial
import Definitions.Def_GrothendieckLB_Supplement_cqReplaySums
import Mathlib
import Theorems.Thm_GrothendieckLB_Supplement_cq_packed_base_checks
import Theorems.Thm_GrothendieckLB_Supplement_cq_packed_initial_hermite_rows
import Theorems.Thm_GrothendieckLB_Supplement_cq_packed_cubic_grid_strips
import Theorems.Thm_GrothendieckLB_Supplement_cq_packed_rho_power_rows
open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQHeadArithmetic
open GrothendieckLB.Supplement.CQHeadCertificate
namespace CubicCertificate
set_option maxHeartbeats 600000

private theorem every {f : ℕ → Bool} {n : ℕ} (h : (List.range n).all f = true) {i : ℕ} (hi : i < n) : f i=true :=
  List.all_eq_true.mp h i (List.mem_range.mpr hi)
private theorem allOf {f : ℕ → Bool} {n : ℕ} (h : ∀ i, i < n → f i=true) : (List.range n).all f=true :=
  List.all_eq_true.mpr fun i hi => h i (List.mem_range.mp hi)
@[simp] private theorem tabSize {α : Type} (n : ℕ) (f : ℕ → α) : (tab n f).size=n := by simp [tab]
private theorem tabGet {α : Type} (d : α) {n i : ℕ} {f : ℕ → α} (hi : i < n) :
    entry d (tab n f) i = f i := by simp [entry,tab,hi]
private theorem pushGet {α : Type} (d : α) (xs : Array α) (x : α) (i : ℕ) :
    entry d (xs.push x) i = if i=xs.size then x else entry d xs i := by
  by_cases h : i=xs.size <;> simp [entry,Array.getElem?_push,h]
private theorem rawSize (n : ℕ) : (momentRows n).size = n+6 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [momentRows,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
private theorem sumCongA (f g : ℕ → MomentCombination) (n : ℕ) (h : ∀ i, i < n → f i=g i) :
    sumCombinations f n=sumCombinations g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumCombinations,sumCombinations,ih (fun i hi => h i (by omega)), h n (by omega)]
private theorem sumCongB (f g : ℕ → Interval) (n : ℕ) (h : ∀ i, i < n → f i=g i) :
    sumIntervals f n=sumIntervals g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumIntervals,sumIntervals,ih (fun i hi => h i (by omega)),h n (by omega)]

private theorem rawEq (hr : rawChecks=true) (hi : initialChecks=true) (n : ℕ) (hn : n≤748) :
    ∀ i, i < n+6 → entry zeroCombination (momentRows n) i = raw i := by
  have hbase := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hi).1).2
  induction n with
  | zero =>
    intro i h
    exact (of_decide_eq_true (every hbase h)).symm
  | succ n ih =>
    intro i h
    change entry zeroCombination ((momentRows n).push _) i = raw i
    rw [pushGet,rawSize]
    by_cases he : i=n+6
    · rw [if_pos he]
      subst i
      have ht := of_decide_eq_true (every (f:=rawOK) hr (i:=n) (by omega))
      change raw (n+6)=rawStep n _ _ _ at ht
      rw [ht]
      unfold rawStep
      rw [ih (by omega) n (by omega),ih (by omega) (n+2) (by omega),ih (by omega) (n+4) (by omega)]
    · rw [if_neg he]
      exact ih (by omega) i (by omega)

private theorem facEq (hf : factChecks=true) (n : ℕ) (hn : n≤753) : fac n=n.factorial := by
  obtain ⟨hb, hs⟩ := Bool.and_eq_true_iff.mp hf
  have h0 := of_decide_eq_true hb
  induction n with
  | zero => exact h0.1
  | succ n ih =>
    have h := (of_decide_eq_true (every (f:=factOK) hs (i:=n) (by omega))).1
    rw [h,ih (by omega),Nat.factorial_succ]
private theorem dfacEq (hf : factChecks=true) (n : ℕ) (hn : n≤753) : dfac n=n.doubleFactorial := by
  obtain ⟨hb, hs⟩ := Bool.and_eq_true_iff.mp hf
  have h0 := of_decide_eq_true hb
  induction n using Nat.twoStepInduction with
  | zero => exact h0.2.1
  | one => exact h0.2.2
  | more n ih ih' =>
    have h := (of_decide_eq_true (every (f:=factOK) hs (i:=n) (by omega))).2
    rw [h,ih (by omega),Nat.doubleFactorial_add_two]

private theorem firstEq (hr : rawChecks=true) (hi : initialChecks=true) (hf : factChecks=true)
    (hc' : ∀ c, c < 24 → firstChecks c=true) (b : ℕ) (hb : b < 754) :
    entry zeroCombination (startAt 251) b=first b := by
  change entry zeroCombination (tab 754 (hStart (momentRows 748))) b=_
  rw [tabGet _ hb,hStart]
  by_cases pe : b%2=0
  · rw [if_pos pe]
    let c := b/2/16
    have hx := every (f:=_) (hc' c (by dsimp [c]; omega)) (i:=b/2%16) (by omega)
    change (if 2*(16*c+b/2%16)<754 then startOK (2*(16*c+b/2%16)) else true)=true at hx
    have he : 2*(16*c+b/2%16)=b := by dsimp [c]; omega
    rw [he,if_pos hb,startOK,if_pos pe] at hx
    rw [of_decide_eq_true hx]
    apply sumCongA
    intro k hk
    rw [rawEq hr hi 748 (by omega) k (by omega)]
    simp only [hc,hermiteCoeff,facEq hf b (by omega),facEq hf k (by omega),facEq hf (b-k) (by omega),dfacEq hf (b-k-1) (by omega)]
  · rw [if_neg pe]
    simp [first,getA,pe]

private def Matches (xs : Array MomentCombination) (f : ℕ → MomentCombination) : Prop :=
  ∀ i, i < xs.size → entry zeroCombination xs i=f i
private theorem shiftMatch {xs : Array MomentCombination} {f : ℕ → MomentCombination} (h : Matches xs f) :
    Matches (shift xs) (shiftAt f) := by
  intro i hi
  simp only [shift,tabSize] at hi
  rw [shift,tabGet _ hi,shiftAt,h (i+1) (by omega),h (i-1) (by omega)]
private theorem nextSize (p : ℕ) (prev cur : Array MomentCombination) :
    (nextRow p prev cur).size=cur.size-3 := by simp only [nextRow,shift,tabSize]; omega
private theorem nextMatch (p : ℕ) {prev cur : Array MomentCombination} {l r : ℕ → MomentCombination}
    (hl : Matches prev l) (hr : Matches cur r) (hs : cur.size≤prev.size) :
    Matches (nextRow p prev cur) (nextAt p l r) := by
  intro b hb
  have h1 := shiftMatch hr
  have h3 := shiftMatch (shiftMatch h1)
  rw [nextSize] at hb
  rw [nextRow,tabGet _ (by simp [shift]; omega),nextAt,h1 b (by simp [shift]; omega),
    h3 b (by simp [shift]; omega),hl b (by omega)]

private theorem facWeight (hf : factChecks=true) (p b : ℕ) (hp : p < 251) (hb : b≤251) (x : MomentCombination) :
    toWeight (p+1) b x=weightAt p b x := by
  simp only [toWeight,weightAt,Nat.add_sub_cancel,facEq hf (p+1) (by omega),facEq hf b (by omega)]

private theorem zeroWeightEq (hf : factChecks=true) {x : Array MomentCombination} (hx : Matches x first)
    (hs : x.size=754) (b : ℕ) (hb : b < 252) : entry zeroInterval (zeroWeights 251 x) b=zeroWeightAt b := by
  rw [zeroWeights,tabGet _ hb,zeroWeightAt,facEq hf b (by omega)]
  rw [hx (b-1) (by omega),(shiftMatch (shiftMatch hx)) (b-1) (by simp [shift,hs]; omega)]


private def st (p : ℕ) := grid 251 (startAt 251) p
private theorem sizes (p : ℕ) (hp : p≤251) :
    (st p).cur.size=rowLength p ∧ (st p).cur.size≤(st p).prev.size ∧ (st p).weights.size=p+1 := by
  induction p with
  | zero => simp [st,grid,startAt,rowLength]
  | succ p ih =>
    obtain ⟨hc,_,hw⟩ := ih (by omega)
    change (nextRow p (st p).prev (st p).cur).size=rowLength (p+1) ∧
      (nextRow p (st p).prev (st p).cur).size≤(st p).cur.size ∧ ((st p).weights.push _).size=p+1+1
    simp only [nextSize,hc,Array.size_push,hw,rowLength]
    exact ⟨by rw [Nat.sub_sub,Nat.mul_succ], Nat.sub_le _ _, trivial⟩

private def CorrectAt (p : ℕ) (l r : Packed) : Prop :=
  Matches (st p).prev (getA l ((p-1)%2)) ∧ Matches (st p).cur (getA r (p%2))
private theorem moveRow (p : ℕ) (hp : p < 251) {l r s : Packed} (h : CorrectAt p l r)
    (hc : (List.range (rowLength (p+1))).all (rowTest p l r s)=true) : CorrectAt (p+1) r s := by
  refine ⟨h.2,?_⟩
  intro b hb
  rw [(sizes (p+1) (by omega)).1] at hb
  have hv := of_decide_eq_true (every (f:=rowTest p l r s) hc hb)
  change getA s ((p+1)%2) b=nextAt p _ _ b at hv
  rw [hv]
  apply nextMatch p h.1 h.2 (sizes p (by omega)).2.1
  change b < (st (p+1)).cur.size
  rw [(sizes (p+1) (by omega)).1]; exact hb

private theorem flow (c : ℕ) (hc : c < 16) (xs : Array Packed) (h : stripChecks c xs=true)
    (hs : CorrectAt (16*c) (checkpoint c).1 (checkpoint c).2) (k : ℕ) (hk : k ≤ stripLen c) :
    CorrectAt (16*c+k) (beforeStrip c xs k) (inStrip c xs k) := by
  induction k with
  | zero => simpa [beforeStrip,inStrip] using hs
  | succ k ih =>
    have hk' : k < stripLen c := by omega
    have hm := (Bool.and_eq_true_iff.mp (every (Bool.and_eq_true_iff.mp h).2 hk')).1
    have hb : 16*c+k < 251 := by simp only [stripLen] at hk'; omega
    have ht := moveRow (16*c+k) hb (ih (by omega)) hm
    simpa only [beforeStrip,Nat.succ_ne_zero,if_false,Nat.add_sub_cancel,Nat.add_assoc] using ht

private theorem checkpointsAgree (hr : rawChecks=true) (hi : initialChecks=true) (hf : factChecks=true)
    (hs : ∀ c, c < 24 → firstChecks c=true) (hg : ∀ c, c < 16 → ∃ xs, stripChecks c xs=true)
    (c : ℕ) (hc : c≤16) : CorrectAt (min (16*c) 251) (checkpoint c).1 (checkpoint c).2 := by
  induction c with
  | zero =>
    have h := of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hi).1).1
    rw [h.1,h.2]
    have hrow : Matches (startAt 251) first := by
      intro i hei
      exact firstEq hr hi hf hs i (by simpa [startAt] using hei)
    simp only [Nat.mul_zero,Nat.zero_min,CorrectAt,st,grid,Nat.zero_sub,Nat.zero_mod]
    exact ⟨hrow,hrow⟩
  | succ c ih =>
    have hc' : c < 16 := by omega
    have hc0 : min (16*c) 251=16*c := by omega
    obtain ⟨xs,hx⟩ := hg c hc'
    have hp : 0 < stripLen c := by simp only [stripLen]; omega
    have he := of_decide_eq_true (Bool.and_eq_true_iff.mp hx).1
    have hi' := ih (by omega); rw [hc0] at hi'
    have ht := flow c hc' xs hx hi' (stripLen c) le_rfl
    have hh : 16*c+stripLen c=min (16*(c+1)) 251 := by simp only [stripLen]; omega
    have hl : beforeStrip c xs (stripLen c)=(checkpoint (c+1)).1 := by
      rw [beforeStrip,if_neg (by omega),he]
    have hright : inStrip c xs (stripLen c)=(checkpoint (c+1)).2 := by
      rw [inStrip,if_neg (by omega),if_pos rfl]
    rwa [hh,hl,hright] at ht

private theorem recordedWeight (p a b : ℕ) (hp : p≤251) (ha : a≤p) (hb : a+b≤251) :
    entry zeroInterval (entry #[] (st p).weights a) b =
      if a=0 then entry zeroInterval (zeroWeights 251 (startAt 251)) b else
        toWeight a b (entry zeroCombination (st (a-1)).cur b) := by
  induction p with
  | zero =>
    obtain rfl : a=0 := by omega
    simp [st,grid,entry]
  | succ p ih =>
    change entry zeroInterval (entry #[] ((st p).weights.push _) a) b=_
    rw [pushGet,(sizes p (by omega)).2.2]
    by_cases e : a=p+1
    · subst a
      rw [if_pos rfl,if_neg (by omega),Nat.add_sub_cancel,tabGet _ (by omega)]
      rfl
    · rw [if_neg e]
      exact ih (by omega) (by omega)

private theorem weightEq (hr : rawChecks=true) (hi : initialChecks=true) (hf : factChecks=true)
    (hs : ∀ c, c < 24 → firstChecks c=true) (hg : ∀ c, c < 16 → ∃ xs, stripChecks c xs=true)
    (a b : ℕ) (hb : a+b≤251) :
    entry zeroInterval (entry #[] (st 251).weights a) b=weight a b := by
  rw [recordedWeight 251 a b (by omega) (by omega) hb]
  cases a with
  | zero =>
    have hw := (of_decide_eq_true (every (Bool.and_eq_true_iff.mp hi).2 (i:=b) (by omega))).1
    rw [if_pos rfl,hw]
    apply zeroWeightEq hf _ (by simp [startAt]) _ (by omega)
    intro i h
    exact firstEq hr hi hf hs i (by simpa [startAt] using h)
  | succ p =>
    let c := p/16
    let k := p%16
    have hc : c < 16 := by dsimp [c]; omega
    have he : 16*c+k=p := by dsimp [c,k]; omega
    have hk : k < stripLen c := by dsimp [stripLen,c,k]; omega
    obtain ⟨xs,hx⟩ := hg c hc
    have h0 := checkpointsAgree hr hi hf hs hg c (by omega)
    rw [min_eq_left (by omega)] at h0
    have ht := flow c hc xs hx h0 k hk.le
    rw [he] at ht
    have hw := of_decide_eq_true (every (Bool.and_eq_true_iff.mp (every (Bool.and_eq_true_iff.mp hx).2 hk)).2 (i:=b) (by omega))
    change weight (16*c+k+1) b = weightAt (16*c+k) b (getA (inStrip c xs k) ((16*c+k)%2) b) at hw
    rw [he] at hw
    rw [if_neg (by omega),Nat.add_sub_cancel,facWeight hf p b (by omega) (by omega),hw,ht.2]
    rw [(sizes p (by omega)).1]; dsimp [rowLength]; omega


private theorem powersSize (p : ℕ) : (rhoPowers 251 p).size=p+1 := by
  induction p with
  | zero => rfl
  | succ p ih => rw [rhoPowers,Array.size_push,ih]

private theorem powerEq (hi : initialChecks=true) (hp : ∀ c, c < 16 → powerChecks c=true)
    (p : ℕ) (hpc : p≤251) (a j : ℕ) (ha : a≤p) (hj : j≤251) :
    entry zeroInterval (entry #[] (rhoPowers 251 p) a) j=power a j := by
  induction p generalizing a j with
  | zero =>
    obtain rfl : a=0 := by omega
    have h := (of_decide_eq_true (every (Bool.and_eq_true_iff.mp hi).2 (i:=j) (by omega))).2
    change entry zeroInterval (entry #[] #[tab 252 (fun k => if k=0 then fixed coefficientScale else zeroInterval)] 0) j=_
    rw [show ∀ (xs : Array Interval), entry #[] #[xs] 0 =xs by intro xs; rfl,tabGet _ (by omega),h]
  | succ p ih =>
    rw [rhoPowers,pushGet,powersSize]
    by_cases hp1 : a=p+1
    · subst a
      rw [if_pos rfl,rhoNext,tabGet _ (by omega)]
      have hshift (k : ℕ) : shifted (entry #[] (rhoPowers 251 p) p) k j =
          if k≤j then power p (j-k) else zeroInterval := by
        unfold shifted
        split <;> simp_all only [ih (by omega) p (j-k) (by omega) (by omega)]
      rw [hshift,hshift,hshift]
      let c := p/16
      let k := p%16
      have hc : c < 16 := by dsimp [c]; omega
      have hk : k < min 16 (251-16*c) := by dsimp [c,k]; omega
      have he : 16*c+k=p := by dsimp [c,k]; omega
      have hy := of_decide_eq_true (every (every (hp c hc) hk) (i:=j) (by omega))
      change power (16*c+k+1) j=powerAt (16*c+k) j at hy
      rw [he] at hy
      exact hy.symm
    · rw [if_neg hp1]
      exact ih (by omega) a j (by omega) hj


private theorem wholeAlt (hr : rawChecks=true) (hi : initialChecks=true) (hf : factChecks=true)
    (hs : ∀ c, c < 24 → firstChecks c=true) (hg : ∀ c, c < 16 → ∃ xs, stripChecks c xs=true)
    (hp : ∀ c, c < 16 → powerChecks c=true) : cqNonlinearHeadCheck=true := by
  apply allOf
  intro j hj
  let m := 2*j+3
  have hm : m≤251 := by dsimp [m]; omega
  have he : fullSum (st 251).weights (rhoPowers 251 251) m=sumIntervals (part m) (m+1) := by
    unfold fullSum
    apply sumCongB
    intro a ha
    change _=sumIntervals (term m a) (m+1-a)
    apply sumCongB
    intro b hb
    rw [term,weightEq hr hi hf hs hg a b (by omega),powerEq hi hp 251 (by omega) a (m-b) (by omega) (by omega)]
  change decide (max (-(fullSum (st 251).weights (rhoPowers 251 251) m).lo)
      (fullSum (st 251).weights (rhoPowers 251 251) m).hi * 10^40 ≤
      coefficientScale*2*314159265358979323846*(cqHeadUnits[j]?.getD 0))=true
  rw [he]
  exact decide_eq_true (cq_packed_full_coefficient_bounds j hj)
end CubicCertificate
open CubicCertificate in
theorem solution : cqNonlinearHeadCheck=true := by
  obtain ⟨hr,hi,hf,_⟩ := cq_packed_base_checks
  exact wholeAlt hr hi hf cq_packed_initial_hermite_rows cq_packed_cubic_grid_strips cq_packed_rho_power_rows
