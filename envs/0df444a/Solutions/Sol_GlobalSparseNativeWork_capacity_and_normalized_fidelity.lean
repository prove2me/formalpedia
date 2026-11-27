-- Prove2me | solution 1 for GlobalSparseNativeWork.capacity_and_normalized_fidelity
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T22:23:24.431535+00:00
-- url     : https://prove2.me/submissions/7ddf50d7-1adf-4e17-aaf3-4f6b1d14a5f6

import Definitions.Def_GlobalSparseWorkTapes

open Turing.MultiTapeTM.Universal TrimmedWorkTape GlobalSparseNativeWork

private theorem trim_cons (a : Option ℕ) (xs : List (Option ℕ)) :
    trim (a :: xs) = if a = none ∧ trim xs = [] then [] else a :: trim xs := by
  cases a <;> simp [trim]

private theorem equal_none_of_all_blank (xs : List (Option ℕ))
    (blank : ∀ i : ℕ, xs[i]?.join = none) : trim xs = [] := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have head : a = none := by simpa using blank 0
    have tail : ∀ i : ℕ, xs[i]?.join = none := fun i => by simpa using blank (i+1)
    rw [trim_cons,head,ih tail]
    simp

private theorem trim_eq_of_relative_reads {xs ys : List (Option ℕ)}
    (agree : ∀ i : ℕ, xs[i]?.join = ys[i]?.join) : trim xs = trim ys := by
  induction xs generalizing ys with
  | nil =>
    have blank : ∀ i : ℕ, ys[i]?.join = none := fun i => by simpa using (agree i).symm
    exact (equal_none_of_all_blank ys blank).symm
  | cons a xs ih =>
    cases ys with
    | nil =>
      have blank : ∀ i : ℕ, (a::xs)[i]?.join = none := fun i => by simpa using agree i
      exact equal_none_of_all_blank _ blank
    | cons b ys =>
      have head : a = b := by simpa using agree 0
      have tail : ∀ i : ℕ, xs[i]?.join = ys[i]?.join := fun i => by simpa using agree (i+1)
      rw [trim_cons,trim_cons,head,ih tail]

private theorem boundedSymbol_eq {alphabet a b : ℕ}
    (aBound : a ≤ alphabet) (bBound : b ≤ alphabet)
    (eq : boundedSymbol alphabet a = boundedSymbol alphabet b) : a = b := by
  simpa only [boundedSymbol,Nat.mod_eq_of_lt (Nat.lt_succ_of_le aBound),
    Nat.mod_eq_of_lt (Nat.lt_succ_of_le bBound)] using congrArg Fin.val eq

private theorem mem_sparseHalf_iff {window alphabet : ℕ} {tape : List (Option ℕ)}
    {i : Fin window} {tag : Fin (alphabet+1)} :
    (i,tag) ∈ sparseHalf window alphabet tape ↔
      ∃ a, tape[i.val]?.join = some a ∧ boundedSymbol alphabet a = tag := by
  constructor
  · intro present
    obtain ⟨j,_,entry⟩ := List.mem_filterMap.mp present
    cases observed : tape[j.val]?.join with
    | none => simp [observed] at entry
    | some a =>
      simp only [observed,Option.map_some,Option.some.injEq,Prod.mk.injEq] at entry
      obtain ⟨rfl,matchTag⟩ := entry
      exact ⟨a,observed,matchTag⟩
  · rintro ⟨a,observed,matchTag⟩
    apply List.mem_filterMap.mpr
    exact ⟨i,List.mem_finRange i,by simp [observed,matchTag]⟩

private theorem observed_bounded {xs : List (Option ℕ)} {index alphabet value : ℕ}
    (symbols : ∀ a, some a ∈ xs → a ≤ alphabet)
    (observed : xs[index]?.join = some value) : value ≤ alphabet := by
  cases result : xs[index]? with
  | none => simp [result] at observed
  | some resultValue =>
    have elem : resultValue ∈ xs := List.mem_of_getElem? result
    simp only [result,Option.join_some] at observed
    exact symbols value (observed ▸ elem)

/-- Matching sparse profiles determine the entire trimmed zipper half, even
when the original halves contain different quantities of explicit blanks. -/
private theorem sparseHalf_faithful {window alphabet : ℕ} {xs ys : List (Option ℕ)}
    (xWindow : xs.length ≤ window) (yWindow : ys.length ≤ window)
    (xSymbols : ∀ a, some a ∈ xs → a ≤ alphabet)
    (ySymbols : ∀ a, some a ∈ ys → a ≤ alphabet)
    (equal : sparseHalf window alphabet xs = sparseHalf window alphabet ys) :
    trim xs = trim ys := by
  apply trim_eq_of_relative_reads
  intro i
  by_cases within : i < window
  · let j : Fin window := ⟨i,within⟩
    cases xValue : xs[i]?.join with
    | some a =>
      have present : (j,boundedSymbol alphabet a) ∈ sparseHalf window alphabet xs :=
        mem_sparseHalf_iff.mpr ⟨a,xValue,rfl⟩
      rw [equal] at present
      obtain ⟨b,yValue,same⟩ := mem_sparseHalf_iff.mp present
      have valueEq := boundedSymbol_eq (observed_bounded ySymbols yValue)
        (observed_bounded xSymbols xValue) same
      change ys[i]?.join = some b at yValue
      rw [yValue,valueEq]
    | none =>
      cases yValue : ys[i]?.join with
      | none => rfl
      | some b =>
        have present : (j,boundedSymbol alphabet b) ∈ sparseHalf window alphabet ys :=
          mem_sparseHalf_iff.mpr ⟨b,yValue,rfl⟩
        rw [← equal] at present
        obtain ⟨a,contrary,_⟩ := mem_sparseHalf_iff.mp present
        change xs[i]?.join = some a at contrary
        rw [xValue] at contrary
        cases contrary
  · have xPast : xs.length ≤ i := xWindow.trans (Nat.le_of_not_gt within)
    have yPast : ys.length ≤ i := yWindow.trans (Nat.le_of_not_gt within)
    simp only [List.getElem?_eq_none_iff.mpr xPast,List.getElem?_eq_none_iff.mpr yPast]

private theorem filterTagged {I V : Type*} [DecidableEq I]
    (keys : List I) (values : I → List V) (q : I) (unique : keys.Nodup) :
    (keys.flatMap fun k => (values k).map fun v => (k,v)).filterMap
      (fun pair => if pair.1 = q then some pair.2 else none) =
    if q ∈ keys then values q else [] := by
  induction keys with
  | nil => simp
  | cons k ks ih =>
    obtain ⟨absent,distinct⟩ := List.nodup_cons.mp unique
    rw [List.flatMap_cons,List.filterMap_append,ih distinct,List.filterMap_map]
    by_cases same : k = q
    · subst k
      simp [absent]
    · simp [Ne.symm same,same]

private theorem projectGlobalSparse (count window alphabet : ℕ) (tapes : List Tape)
    (address : Fin count × Bool) :
    (globalSparseProfile count window alphabet tapes).filterMap
      (fun pair => if pair.1 = address then some pair.2 else none) =
    sparseHalf window alphabet (zipperHalf ((tapes[address.1.val]?).getD default) address.2) := by
  rw [globalSparseProfile,filterTagged]
  · rcases address with ⟨i,b⟩
    cases b <;> simp [List.mem_finRange]
  · exact (List.nodup_finRange count).product (by decide)

private theorem globalSparseWorkCode_capacity (count window alphabet entries : ℕ) :
    Fintype.card (GlobalSparseWorkCode count window alphabet entries) =
      (2*count*window*(alphabet+1)+1)^entries := by
  have base : (count * 2) * (window * (alphabet+1)) = 2*count*window*(alphabet+1) := by ring
  simp only [GlobalSparseWorkCode,GlobalSparseEntry,Fintype.card_fun,
    Fintype.card_fin,Fintype.card_option,Fintype.card_prod,Fintype.card_bool,base]

private theorem normalized_eq_of_globalSparseProfile {count window alphabet : ℕ}
    {xs ys : List Tape} (xCount : xs.length = count) (yCount : ys.length = count)
    (xFits : ∀ t ∈ xs, GlobalSparseHalfFits window alphabet t.left ∧ GlobalSparseHalfFits window alphabet t.right)
    (yFits : ∀ t ∈ ys, GlobalSparseHalfFits window alphabet t.left ∧ GlobalSparseHalfFits window alphabet t.right)
    (profile : globalSparseProfile count window alphabet xs = globalSparseProfile count window alphabet ys) :
    xs.map normalizeTape = ys.map normalizeTape := by
  apply List.ext_getElem?
  intro i
  by_cases inRange : i < count
  · have xIn : i < xs.length := xCount ▸ inRange
    have yIn : i < ys.length := yCount ▸ inRange
    let a : Fin count := ⟨i,inRange⟩
    let x := xs[i]
    let y := ys[i]
    have halves (s : Bool) :
        sparseHalf window alphabet (zipperHalf x s) = sparseHalf window alphabet (zipperHalf y s) := by
      have equal := congrArg (fun p : List (GlobalSparseEntry count window alphabet) =>
        p.filterMap (fun pair => if pair.1 = (a,s) then some pair.2 else none)) profile
      rw [projectGlobalSparse,projectGlobalSparse] at equal
      simpa only [a,getElem?_pos xs i xIn,getElem?_pos ys i yIn,Option.getD_some,x,y] using equal
    rw [List.getElem?_map,List.getElem?_map,getElem?_pos xs i xIn,getElem?_pos ys i yIn]
    apply congrArg some
    obtain ⟨xl,xr⟩ := xFits x (List.getElem_mem _)
    obtain ⟨yl,yr⟩ := yFits y (List.getElem_mem _)
    have left : trim x.left = trim y.left :=
      sparseHalf_faithful xl.1 yl.1 xl.2 yl.2 (halves false)
    have right : trim x.right = trim y.right :=
      sparseHalf_faithful xr.1 yr.1 xr.2 yr.2 (halves true)
    change normalizeTape x = normalizeTape y
    simp only [normalizeTape,left,right]
  · rw [List.getElem?_map,List.getElem?_map,
      List.getElem?_eq_none_iff.mpr (xCount ▸ Nat.le_of_not_gt inRange),
      List.getElem?_eq_none_iff.mpr (yCount ▸ Nat.le_of_not_gt inRange)]

/-- The packed code with one shared nonblank budget faithfully determines
all normalized work tapes. The original tapes may have extra blank suffixes. -/
private theorem packGlobalSparseWork_faithful {count window alphabet entries : ℕ} {xs ys : List Tape}
    (xFits : GlobalSparseWorkFits count window alphabet entries xs)
    (yFits : GlobalSparseWorkFits count window alphabet entries ys)
    (equal : packGlobalSparseWork count window alphabet entries xs =
      packGlobalSparseWork count window alphabet entries ys) :
    xs.map normalizeTape = ys.map normalizeTape := by
  apply normalized_eq_of_globalSparseProfile xFits.1 yFits.1 xFits.2.1 yFits.2.1
  apply List.ext_getElem?
  intro i
  by_cases inside : i < entries
  · exact congrFun equal ⟨i,inside⟩
  · have past := Nat.le_of_not_gt inside
    rw [List.getElem?_eq_none_iff.mpr (xFits.2.2.trans past),
      List.getElem?_eq_none_iff.mpr (yFits.2.2.trans past)]

theorem solution (count window alphabet entries : ℕ) :
    (Fintype.card (GlobalSparseWorkCode count window alphabet entries) =
      (2*count*window*(alphabet+1)+1)^entries) ∧
    (∀ (xs ys : List Tape),
      GlobalSparseWorkFits count window alphabet entries xs →
      GlobalSparseWorkFits count window alphabet entries ys →
      packGlobalSparseWork count window alphabet entries xs =
        packGlobalSparseWork count window alphabet entries ys →
      xs.map normalizeTape = ys.map normalizeTape) := by
  exact ⟨globalSparseWorkCode_capacity _ _ _ _,fun _ _ => packGlobalSparseWork_faithful⟩

#print axioms solution
