-- Prove2me | solution 2 for GrothendieckLB.Supplement.cq_packed_initial_hermite_rows
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:36:05.736266+00:00
-- url     : https://prove2.me/submissions/9eb67782-ce6e-444d-b262-a105c3baa68c

import Theorems.Thm_GrothendieckLB_Supplement_cq_packed_base_checks
import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite251_initial_grid
open GrothendieckLB.Supplement CQHeadArithmetic CQHeadCertificate CQHermite251
namespace FromCertifiedInitialGrid
set_option maxRecDepth 120000
set_option maxHeartbeats 60000000
set_option Elab.async false
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


private def seg (f : ℕ → Bool) (l n : ℕ) := (List.range n).all fun i => f (l+i)
private theorem join {f : ℕ → Bool} {l n m : ℕ}
    (hn : seg f l n=true) (hm : seg f (l+n) m=true) : seg f l (n+m)=true := by
  apply List.all_eq_true.mpr
  intro x hx
  have hx' := List.mem_range.mp hx
  by_cases h : x < n
  · exact List.all_eq_true.mp hn x (List.mem_range.mpr h)
  · have hh := List.all_eq_true.mp hm (x-n) (List.mem_range.mpr (by omega))
    change f (l+n+(x-n))=true at hh
    rwa [show l+n+(x-n)=l+x by omega] at hh
private theorem full {f : ℕ → Bool} {n : ℕ} (h : seg f 0 n=true) : (List.range n).all f=true := by
  simpa only [seg,Nat.zero_add] using h


private def candidate : List MomentCombination := eval% (tab 754 first).toList
private theorem agrees : (pair 0).2=candidate := by rfl
private def matchEven (i : ℕ) : Bool :=
  decide (first (2*i)=candidate[2*i]?.getD zeroCombination)
private theorem match0to5 : seg matchEven 0 5=true := by decide +kernel
private theorem match5to11 : seg matchEven 5 6=true := by decide +kernel
private theorem match0to11 : seg matchEven 0 11=true := join (l:=0) (n:=5) (m:=6) match0to5 match5to11
private theorem match11to17 : seg matchEven 11 6=true := by decide +kernel
private theorem match17to23 : seg matchEven 17 6=true := by decide +kernel
private theorem match11to23 : seg matchEven 11 12=true := join (l:=11) (n:=6) (m:=6) match11to17 match17to23
private theorem match0to23 : seg matchEven 0 23=true := join (l:=0) (n:=11) (m:=12) match0to11 match11to23
private theorem match23to29 : seg matchEven 23 6=true := by decide +kernel
private theorem match29to35 : seg matchEven 29 6=true := by decide +kernel
private theorem match23to35 : seg matchEven 23 12=true := join (l:=23) (n:=6) (m:=6) match23to29 match29to35
private theorem match35to41 : seg matchEven 35 6=true := by decide +kernel
private theorem match41to47 : seg matchEven 41 6=true := by decide +kernel
private theorem match35to47 : seg matchEven 35 12=true := join (l:=35) (n:=6) (m:=6) match35to41 match41to47
private theorem match23to47 : seg matchEven 23 24=true := join (l:=23) (n:=12) (m:=12) match23to35 match35to47
private theorem match0to47 : seg matchEven 0 47=true := join (l:=0) (n:=23) (m:=24) match0to23 match23to47
private theorem match47to52 : seg matchEven 47 5=true := by decide +kernel
private theorem match52to58 : seg matchEven 52 6=true := by decide +kernel
private theorem match47to58 : seg matchEven 47 11=true := join (l:=47) (n:=5) (m:=6) match47to52 match52to58
private theorem match58to64 : seg matchEven 58 6=true := by decide +kernel
private theorem match64to70 : seg matchEven 64 6=true := by decide +kernel
private theorem match58to70 : seg matchEven 58 12=true := join (l:=58) (n:=6) (m:=6) match58to64 match64to70
private theorem match47to70 : seg matchEven 47 23=true := join (l:=47) (n:=11) (m:=12) match47to58 match58to70
private theorem match70to76 : seg matchEven 70 6=true := by decide +kernel
private theorem match76to82 : seg matchEven 76 6=true := by decide +kernel
private theorem match70to82 : seg matchEven 70 12=true := join (l:=70) (n:=6) (m:=6) match70to76 match76to82
private theorem match82to88 : seg matchEven 82 6=true := by decide +kernel
private theorem match88to94 : seg matchEven 88 6=true := by decide +kernel
private theorem match82to94 : seg matchEven 82 12=true := join (l:=82) (n:=6) (m:=6) match82to88 match88to94
private theorem match70to94 : seg matchEven 70 24=true := join (l:=70) (n:=12) (m:=12) match70to82 match82to94
private theorem match47to94 : seg matchEven 47 47=true := join (l:=47) (n:=23) (m:=24) match47to70 match70to94
private theorem match0to94 : seg matchEven 0 94=true := join (l:=0) (n:=47) (m:=47) match0to47 match47to94
private theorem match94to99 : seg matchEven 94 5=true := by decide +kernel
private theorem match99to105 : seg matchEven 99 6=true := by decide +kernel
private theorem match94to105 : seg matchEven 94 11=true := join (l:=94) (n:=5) (m:=6) match94to99 match99to105
private theorem match105to111 : seg matchEven 105 6=true := by decide +kernel
private theorem match111to117 : seg matchEven 111 6=true := by decide +kernel
private theorem match105to117 : seg matchEven 105 12=true := join (l:=105) (n:=6) (m:=6) match105to111 match111to117
private theorem match94to117 : seg matchEven 94 23=true := join (l:=94) (n:=11) (m:=12) match94to105 match105to117
private theorem match117to123 : seg matchEven 117 6=true := by decide +kernel
private theorem match123to129 : seg matchEven 123 6=true := by decide +kernel
private theorem match117to129 : seg matchEven 117 12=true := join (l:=117) (n:=6) (m:=6) match117to123 match123to129
private theorem match129to135 : seg matchEven 129 6=true := by decide +kernel
private theorem match135to141 : seg matchEven 135 6=true := by decide +kernel
private theorem match129to141 : seg matchEven 129 12=true := join (l:=129) (n:=6) (m:=6) match129to135 match135to141
private theorem match117to141 : seg matchEven 117 24=true := join (l:=117) (n:=12) (m:=12) match117to129 match129to141
private theorem match94to141 : seg matchEven 94 47=true := join (l:=94) (n:=23) (m:=24) match94to117 match117to141
private theorem match141to146 : seg matchEven 141 5=true := by decide +kernel
private theorem match146to152 : seg matchEven 146 6=true := by decide +kernel
private theorem match141to152 : seg matchEven 141 11=true := join (l:=141) (n:=5) (m:=6) match141to146 match146to152
private theorem match152to158 : seg matchEven 152 6=true := by decide +kernel
private theorem match158to164 : seg matchEven 158 6=true := by decide +kernel
private theorem match152to164 : seg matchEven 152 12=true := join (l:=152) (n:=6) (m:=6) match152to158 match158to164
private theorem match141to164 : seg matchEven 141 23=true := join (l:=141) (n:=11) (m:=12) match141to152 match152to164
private theorem match164to170 : seg matchEven 164 6=true := by decide +kernel
private theorem match170to176 : seg matchEven 170 6=true := by decide +kernel
private theorem match164to176 : seg matchEven 164 12=true := join (l:=164) (n:=6) (m:=6) match164to170 match170to176
private theorem match176to182 : seg matchEven 176 6=true := by decide +kernel
private theorem match182to188 : seg matchEven 182 6=true := by decide +kernel
private theorem match176to188 : seg matchEven 176 12=true := join (l:=176) (n:=6) (m:=6) match176to182 match182to188
private theorem match164to188 : seg matchEven 164 24=true := join (l:=164) (n:=12) (m:=12) match164to176 match176to188
private theorem match141to188 : seg matchEven 141 47=true := join (l:=141) (n:=23) (m:=24) match141to164 match164to188
private theorem match94to188 : seg matchEven 94 94=true := join (l:=94) (n:=47) (m:=47) match94to141 match141to188
private theorem match0to188 : seg matchEven 0 188=true := join (l:=0) (n:=94) (m:=94) match0to94 match94to188
private theorem match188to193 : seg matchEven 188 5=true := by decide +kernel
private theorem match193to199 : seg matchEven 193 6=true := by decide +kernel
private theorem match188to199 : seg matchEven 188 11=true := join (l:=188) (n:=5) (m:=6) match188to193 match193to199
private theorem match199to205 : seg matchEven 199 6=true := by decide +kernel
private theorem match205to211 : seg matchEven 205 6=true := by decide +kernel
private theorem match199to211 : seg matchEven 199 12=true := join (l:=199) (n:=6) (m:=6) match199to205 match205to211
private theorem match188to211 : seg matchEven 188 23=true := join (l:=188) (n:=11) (m:=12) match188to199 match199to211
private theorem match211to217 : seg matchEven 211 6=true := by decide +kernel
private theorem match217to223 : seg matchEven 217 6=true := by decide +kernel
private theorem match211to223 : seg matchEven 211 12=true := join (l:=211) (n:=6) (m:=6) match211to217 match217to223
private theorem match223to229 : seg matchEven 223 6=true := by decide +kernel
private theorem match229to235 : seg matchEven 229 6=true := by decide +kernel
private theorem match223to235 : seg matchEven 223 12=true := join (l:=223) (n:=6) (m:=6) match223to229 match229to235
private theorem match211to235 : seg matchEven 211 24=true := join (l:=211) (n:=12) (m:=12) match211to223 match223to235
private theorem match188to235 : seg matchEven 188 47=true := join (l:=188) (n:=23) (m:=24) match188to211 match211to235
private theorem match235to240 : seg matchEven 235 5=true := by decide +kernel
private theorem match240to246 : seg matchEven 240 6=true := by decide +kernel
private theorem match235to246 : seg matchEven 235 11=true := join (l:=235) (n:=5) (m:=6) match235to240 match240to246
private theorem match246to252 : seg matchEven 246 6=true := by decide +kernel
private theorem match252to258 : seg matchEven 252 6=true := by decide +kernel
private theorem match246to258 : seg matchEven 246 12=true := join (l:=246) (n:=6) (m:=6) match246to252 match252to258
private theorem match235to258 : seg matchEven 235 23=true := join (l:=235) (n:=11) (m:=12) match235to246 match246to258
private theorem match258to264 : seg matchEven 258 6=true := by decide +kernel
private theorem match264to270 : seg matchEven 264 6=true := by decide +kernel
private theorem match258to270 : seg matchEven 258 12=true := join (l:=258) (n:=6) (m:=6) match258to264 match264to270
private theorem match270to276 : seg matchEven 270 6=true := by decide +kernel
private theorem match276to282 : seg matchEven 276 6=true := by decide +kernel
private theorem match270to282 : seg matchEven 270 12=true := join (l:=270) (n:=6) (m:=6) match270to276 match276to282
private theorem match258to282 : seg matchEven 258 24=true := join (l:=258) (n:=12) (m:=12) match258to270 match270to282
private theorem match235to282 : seg matchEven 235 47=true := join (l:=235) (n:=23) (m:=24) match235to258 match258to282
private theorem match188to282 : seg matchEven 188 94=true := join (l:=188) (n:=47) (m:=47) match188to235 match235to282
private theorem match282to287 : seg matchEven 282 5=true := by decide +kernel
private theorem match287to293 : seg matchEven 287 6=true := by decide +kernel
private theorem match282to293 : seg matchEven 282 11=true := join (l:=282) (n:=5) (m:=6) match282to287 match287to293
private theorem match293to299 : seg matchEven 293 6=true := by decide +kernel
private theorem match299to305 : seg matchEven 299 6=true := by decide +kernel
private theorem match293to305 : seg matchEven 293 12=true := join (l:=293) (n:=6) (m:=6) match293to299 match299to305
private theorem match282to305 : seg matchEven 282 23=true := join (l:=282) (n:=11) (m:=12) match282to293 match293to305
private theorem match305to311 : seg matchEven 305 6=true := by decide +kernel
private theorem match311to317 : seg matchEven 311 6=true := by decide +kernel
private theorem match305to317 : seg matchEven 305 12=true := join (l:=305) (n:=6) (m:=6) match305to311 match311to317
private theorem match317to323 : seg matchEven 317 6=true := by decide +kernel
private theorem match323to329 : seg matchEven 323 6=true := by decide +kernel
private theorem match317to329 : seg matchEven 317 12=true := join (l:=317) (n:=6) (m:=6) match317to323 match323to329
private theorem match305to329 : seg matchEven 305 24=true := join (l:=305) (n:=12) (m:=12) match305to317 match317to329
private theorem match282to329 : seg matchEven 282 47=true := join (l:=282) (n:=23) (m:=24) match282to305 match305to329
private theorem match329to335 : seg matchEven 329 6=true := by decide +kernel
private theorem match335to341 : seg matchEven 335 6=true := by decide +kernel
private theorem match329to341 : seg matchEven 329 12=true := join (l:=329) (n:=6) (m:=6) match329to335 match335to341
private theorem match341to347 : seg matchEven 341 6=true := by decide +kernel
private theorem match347to353 : seg matchEven 347 6=true := by decide +kernel
private theorem match341to353 : seg matchEven 341 12=true := join (l:=341) (n:=6) (m:=6) match341to347 match347to353
private theorem match329to353 : seg matchEven 329 24=true := join (l:=329) (n:=12) (m:=12) match329to341 match341to353
private theorem match353to359 : seg matchEven 353 6=true := by decide +kernel
private theorem match359to365 : seg matchEven 359 6=true := by decide +kernel
private theorem match353to365 : seg matchEven 353 12=true := join (l:=353) (n:=6) (m:=6) match353to359 match359to365
private theorem match365to371 : seg matchEven 365 6=true := by decide +kernel
private theorem match371to377 : seg matchEven 371 6=true := by decide +kernel
private theorem match365to377 : seg matchEven 365 12=true := join (l:=365) (n:=6) (m:=6) match365to371 match371to377
private theorem match353to377 : seg matchEven 353 24=true := join (l:=353) (n:=12) (m:=12) match353to365 match365to377
private theorem match329to377 : seg matchEven 329 48=true := join (l:=329) (n:=24) (m:=24) match329to353 match353to377
private theorem match282to377 : seg matchEven 282 95=true := join (l:=282) (n:=47) (m:=48) match282to329 match329to377
private theorem match188to377 : seg matchEven 188 189=true := join (l:=188) (n:=94) (m:=95) match188to282 match282to377
private theorem match0to377 : seg matchEven 0 377=true := join (l:=0) (n:=188) (m:=189) match0to188 match188to377

private theorem observed (b : ℕ) (hb : b < 754) (pe : b%2=0) :
    first b=entry zeroCombination (startAt 251) b := by
  have h : startAt 251=(pair 0).2.toArray := congrArg Grid.cur cq_hermite251_initial_grid
  have K := of_decide_eq_true (every (f:=matchEven) (full match0to377) (i:=b/2) (by omega))
  change first (2*(b/2))=candidate[2*(b/2)]?.getD zeroCombination at K
  rw [show 2*(b/2)=b by omega] at K
  simpa only [h,agrees,entry,List.getElem?_toArray] using K
private theorem firstRecovered (b : ℕ) (hb : b < 754) (pe : b%2=0) :
    first b=sumCombinations (fun k => scaleCombination (hc b k) (raw k)) (b+1) := by
  obtain ⟨hr,hi,hf,_⟩ := cq_packed_base_checks
  rw [observed b hb pe]
  change entry zeroCombination (tab 754 (hStart (momentRows 748))) b=_
  rw [tabGet _ hb,hStart,if_pos pe]
  apply sumCongA
  intro k hk
  rw [rawEq hr hi 748 (by omega) k (by omega)]
  simp only [hc,hermiteCoeff,facEq hf b (by omega),facEq hf k (by omega),facEq hf (b-k) (by omega),dfacEq hf (b-k-1) (by omega)]
end FromCertifiedInitialGrid

open FromCertifiedInitialGrid in
theorem solution : ∀ c : ℕ, c < 24 → firstChecks c=true := by
  intro c _
  apply List.all_eq_true.mpr
  intro j _
  let b := 2*(16*c+j)
  change (if b < 754 then startOK b else true)=true
  split
  · rename_i hb
    have hp : b%2=0 := by dsimp [b]; omega
    rw [startOK,if_pos hp]
    exact decide_eq_true (firstRecovered b hb hp)
  · rfl
