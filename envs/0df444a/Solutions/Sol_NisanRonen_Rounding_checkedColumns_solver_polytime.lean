-- Prove2me | solution 1 for NisanRonen.Rounding.checkedColumns_solver_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:01:43.112003+00:00
-- url     : https://prove2.me/submissions/1fa202fa-8835-4df6-a251-ab33698edf36

import Mathlib
import Theorems.Thm_Turing_MultiTapeTM_computableInPolyTime_to_tm2
import Theorems.Thm_NisanRonen_Rounding_loadStates_length_le
import Definitions.Def_NisanRonen_Rounding_checkedColumns
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_EraseDupsBy
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Fold

open Turing.MultiTapeTM NisanRonen.Rounding
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

set_option autoImplicit false
set_option maxHeartbeats 3000000

private abbrev PolyCert {α β : Type} (f : α → β) (ein : α ↪ List Bool) (eout : β ↪ List Bool) :=
  ComputableTidilyInPolyTime f ein eout

private def encVector (n : ℕ) : (Fin n → ℕ) ↪ List Bool :=
  ⟨fun v => encList encNat (List.ofFn v), fun _ _ h =>
    List.ofFn_inj.mp ((encList encNat).injective h)⟩

private abbrev encState (n : ℕ) : LoadState n ↪ List Bool :=
  encPair (encVector n) (encList (encAgent n))

private abbrev encTable (n : ℕ) : List (LoadState n) ↪ List Bool :=
  encList (encState n)

private def vectorList {n : ℕ} : (Fin n → ℕ) → List ℕ := List.ofFn

private theorem vectorList_poly (n : ℕ) :
    PolyCert (vectorList (n := n)) (encVector n) (encList encNat) :=
  ComputableTidilyInPolyTime.of_eq fun _ => rfl

private theorem getD_list_poly (idx : ℕ) :
    PolyCert (fun l : List ℕ => l[idx]?.getD 0) (encList encNat) encNat := by
  exact (optionGetD encNat).comp ((ComputableTidilyInPolyTime.getElem? id' (const idx)).prod (const 0))

private theorem vectorAt_poly {n : ℕ} (i : Fin n) :
    PolyCert (fun v : Fin n → ℕ => v i) (encVector n) encNat := by
  apply ((getD_list_poly i.val).comp (vectorList_poly n)).of_enc_eq
  intro v
  simp [vectorList]

private theorem vectorOfComponents_poly {α : Type} {e : α ↪ List Bool} {n : ℕ}
    (f : α → Fin n → ℕ) (h : ∀ i, PolyCert (fun a => f a i) e encNat) :
    PolyCert f e (encVector n) := by
  apply (mapConst (List.finRange n) (fun i _ => h i)).of_enc_eq
  intro a
  change encList encNat (List.ofFn (f a)) = encList encNat ((List.finRange n).map (f a))
  simp [List.finRange, List.map_ofFn, Function.comp_def]

private theorem prependJob_poly (n : ℕ) :
    PolyCert (fun p : ((Fin n → ℕ) × LoadState n) × Fin n => prependJob p.1.1 p.1.2 p.2)
      (encPair (encPair (encVector n) (encState n)) (encAgent n)) (encState n) := by
  let e := encPair (encPair (encVector n) (encState n)) (encAgent n)
  have ht : PolyCert (fun p : ((Fin n → ℕ) × LoadState n) × Fin n => p.1.1) e (encVector n) := by
    dsimp [e]
    fun_prop
  have hr : PolyCert (fun p : ((Fin n → ℕ) × LoadState n) × Fin n => p.1.2) e (encState n) := by
    dsimp [e]
    fun_prop
  have ha : PolyCert (fun p : ((Fin n → ℕ) × LoadState n) × Fin n => p.2) e (encAgent n) := by
    dsimp [e]
    fun_prop
  have hload (j : Fin n) : PolyCert (fun p : ((Fin n → ℕ) × LoadState n) × Fin n =>
      (if j = p.2 then p.1.1 j else 0) + p.1.2.1 j) e encNat := by
    refine binary_add' ?_ ?_
    · exact ite_decide (decide_eq' (const j) ha) ((vectorAt_poly j).comp ht) (const 0)
    · exact (vectorAt_poly j).comp (hr.fst')
  have hw : PolyCert (fun p : ((Fin n → ℕ) × LoadState n) × Fin n => p.2 :: p.1.2.2)
      e (encList (encAgent n)) :=
    (cons (encAgent n)).comp (ha.prod hr.snd')
  exact (vectorOfComponents_poly _ hload).prod hw

private theorem extendStates_poly (n : ℕ) :
    PolyCert (fun p : (Fin n → ℕ) × List (LoadState n) =>
      p.2.flatMap fun state => (List.finRange n).map (prependJob p.1 state))
      (encPair (encVector n) (encTable n)) (encTable n) := by
  let e := encPair (encVector n) (encTable n)
  have hstep : PolyCert (fun p : ((Fin n → ℕ) × List (LoadState n)) × LoadState n =>
      (List.finRange n).map (prependJob p.1.1 p.2))
      (encPair e (encState n)) (encTable n) := by
    apply mapConst (List.finRange n)
    intro i _
    have hl : PolyCert (fun p : ((Fin n → ℕ) × List (LoadState n)) × LoadState n => p.1.1)
        (encPair e (encState n)) (encVector n) :=
      (fst (encVector n) (encTable n)).comp (fst e (encState n))
    exact (prependJob_poly n).comp ((hl.prod (snd e (encState n))).prod (const i))
  exact flatMapWithInput (snd (encVector n) (encTable n)) hstep

private theorem keepLoadStates_poly (n : ℕ) :
    PolyCert (keepLoadStates (n := n)) (encTable n) (encTable n) := by
  unfold keepLoadStates
  apply computableInPolyTime_iff_computableTidilyInPolyTime.mp
  apply ComputableInPolyTime.eraseDupsByWithInput (encIn := encTable n) ComputableInPolyTime.id'
  exact (decide_eq' ((fst (encVector n) (encList (encAgent n))).comp
      ((snd (encTable n) (encState n)).comp (fst (encPair (encTable n) (encState n)) (encState n))))
    ((fst (encVector n) (encList (encAgent n))).comp
      (snd (encPair (encTable n) (encState n)) (encState n)))).computableInPolyTime

private def allocationLoads {n : ℕ} :
    List (Fin n → ℕ) → List (Fin n) → Fin n → ℕ
  | column :: columns, agent :: agents, i =>
      (if i = agent then column i else 0) + allocationLoads columns agents i
  | _, _, _ => 0

private theorem mem_keepLoadStates {n : ℕ} {states : List (LoadState n)} {s : LoadState n}
    (h : s ∈ keepLoadStates states) : s ∈ states := by
  cases states with
  | nil => simp [keepLoadStates] at h
  | cons t states =>
    rw [keepLoadStates, List.eraseDupsBy_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · have hm := mem_keepLoadStates (show s ∈ keepLoadStates _ from h)
      exact List.mem_cons_of_mem t (List.mem_filter.mp hm).1
termination_by states.length
decreasing_by
  subst_vars
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem state_sound {n : ℕ} {columns : List (Fin n → ℕ)} {s : LoadState n}
    (h : s ∈ loadStates columns) :
    s.2.length = columns.length ∧ s.1 = allocationLoads columns s.2 := by
  induction columns generalizing s with
  | nil =>
    simp only [loadStates, List.mem_singleton] at h
    subst s
    exact ⟨rfl, rfl⟩
  | cons column columns ih =>
    rw [loadStates] at h
    obtain ⟨t, ht, hs⟩ := List.mem_flatMap.mp (mem_keepLoadStates h)
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hlen, hload⟩ := ih ht
    refine ⟨by simp [prependJob, hlen], ?_⟩
    funext j
    simp [prependJob, allocationLoads, hload]

private theorem allocationLoads_le {n : ℕ} (cap : ℕ) (columns : List (Fin n → ℕ))
    (agents : List (Fin n)) (hc : ∀ c ∈ columns, ∀ i, c i ≤ cap) (i : Fin n) :
    allocationLoads columns agents i ≤ columns.length * cap := by
  induction columns generalizing agents with
  | nil => simp [allocationLoads]
  | cons c cs ih =>
    cases agents with
    | nil => simp [allocationLoads]
    | cons a as =>
      have hc0 := hc c List.mem_cons_self i
      have hcs := ih as (fun d hd => hc d (List.mem_cons_of_mem c hd))
      have hfirst : (if i = a then c i else 0) ≤ cap := by split <;> omega
      rw [allocationLoads, List.length_cons, Nat.succ_mul]
      omega

private def loadStep {n : ℕ} (table : List (LoadState n)) (c : Fin n → ℕ) :
    List (LoadState n) :=
  keepLoadStates (table.flatMap fun s => (List.finRange n).map (prependJob c s))

private theorem loadStep_poly (n : ℕ) :
    PolyCert (fun p : List (LoadState n) × (Fin n → ℕ) => loadStep p.1 p.2)
      (encPair (encTable n) (encVector n)) (encTable n) :=
  (keepLoadStates_poly n).comp ((extendStates_poly n).comp
    ((snd (encTable n) (encVector n)).prod (fst (encTable n) (encVector n))))

private theorem states_as_fold {n : ℕ} (cols : List (Fin n → ℕ)) :
    loadStates cols = cols.reverse.foldl loadStep [(fun _ => 0, [])] := by
  induction cols with
  | nil => rfl
  | cons c cs ih =>
    rw [List.reverse_cons, List.foldl_append, ← ih]
    rfl

private def stateBitBudget (n cap m : ℕ) : ℕ :=
  2 * (n * (2 * (m * cap) + 1)) + 1 + m * (2 * n + 1)

private def tableBitBudget (n cap m : ℕ) : ℕ :=
  (m * cap + 1) ^ n * (2 * stateBitBudget n cap m + 1)

private theorem state_bits_le {n cap : ℕ} {cs : List (Fin n → ℕ)}
    (hc : ∀ c ∈ cs, ∀ i, c i ≤ cap) {s : LoadState n} (hs : s ∈ loadStates cs) :
    (encState n s).length ≤ stateBitBudget n cap cs.length := by
  have hs' := state_sound hs
  have hvec : (encVector n s.1).length ≤ n * (2 * (cs.length * cap) + 1) := by
    change (encList encNat (List.ofFn s.1)).length ≤ _
    have hv : ∀ v ∈ List.ofFn s.1, (encNat v).length ≤ cs.length * cap := by
      intro v hv
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      have hl := allocationLoads_le cap cs s.2 hc i
      rw [← hs'.2] at hl
      have hnat : (encNat (s.1 i)).length ≤ s.1 i := by
        change (s.1 i).bits.length ≤ s.1 i
        rw [Nat.size_eq_bits_len]
        exact Nat.size_le.mpr Nat.lt_two_pow_self
      exact hnat.trans hl
    simpa only [List.length_ofFn] using length_encList_le encNat (List.ofFn s.1) hv
  have halloc : (encList (encAgent n) s.2).length ≤ cs.length * (2 * n + 1) := by
    rw [← hs'.1]
    apply length_encList_le
    intro i _
    change (List.replicate i.val true).length ≤ n
    simpa only [List.length_replicate] using i.isLt.le
  rw [encState, length_encPair]
  dsimp [stateBitBudget]
  omega

private theorem table_bits_le {n cap : ℕ} (cs : List (Fin n → ℕ))
    (hc : ∀ c ∈ cs, ∀ i, c i ≤ cap) :
    (encTable n (loadStates cs)).length ≤ tableBitBudget n cap cs.length := by
  exact (length_encList_le (encState n) (loadStates cs) (fun _ hs => state_bits_le hc hs)).trans
    (Nat.mul_le_mul_right _ (loadStates_length_le cap cs hc))

private theorem table_budget_mono (n cap : ℕ) : Monotone (tableBitBudget n cap) := by
  intro i j h
  unfold tableBitBudget stateBitBudget
  gcongr

private theorem table_budget_polynomial {α : Type} (size len : α → ℕ)
    (h : ∀ a, len a ≤ size a) (n cap : ℕ) :
    PolyBounded size (fun x => tableBitBudget n cap (len x)) := by
  have hlen : PolyBounded size len := PolyBounded.self.mono h
  have hmul : PolyBounded size (fun x => len x * cap) :=
    hlen.mul (PolyBounded.const cap)
  have hpower := (hmul.add (PolyBounded.const 1)).pow n
  have hvec := (PolyBounded.const n).mul
    (((PolyBounded.const 2).mul hmul).add (PolyBounded.const 1))
  have hstate := (((PolyBounded.const 2).mul hvec).add (PolyBounded.const 1)).add
    (hlen.mul (PolyBounded.const (2 * n + 1)))
  exact hpower.mul (((PolyBounded.const 2).mul hstate).add (PolyBounded.const 1))

private theorem fold_sanitized_states_poly {γ : Type} {ein : γ ↪ List Bool} {n cap : ℕ}
    (cols : γ → List (Fin n → ℕ)) (hcols : PolyCert cols ein (encList (encVector n)))
    (hcap : ∀ a c, c ∈ cols a → ∀ i, c i ≤ cap)
    (hlen : ∀ a, (cols a).length ≤ (ein a).length) :
    PolyCert (fun a => loadStates (cols a)) ein (encTable n) := by
  have he := foldl' (listReverseWithInput hcols) (const [(fun _ => 0, [])])
    (loadStep_poly n) (table_budget_polynomial (fun a => (ein a).length)
      (fun a => (cols a).length) hlen n cap)
    (by
      intro a i hi
      let front := (cols a).reverse.take i
      have hb (c) (hc : c ∈ front.reverse) : ∀ j, c j ≤ cap := by
        apply hcap
        exact List.mem_reverse.mp (List.mem_of_mem_take (List.mem_reverse.mp hc))
      have hm : front.reverse.length ≤ (cols a).length := by simp [front]
      change (encTable n (front.foldl loadStep [(fun _ => 0, [])])).length ≤ _
      have heq := states_as_fold front.reverse
      rw [List.reverse_reverse] at heq
      rw [← heq]
      exact (table_bits_le front.reverse hb).trans (table_budget_mono n cap hm))
  exact he.of_enc_eq (fun a => congrArg (fun l => encTable n l) (states_as_fold (cols a)))

private theorem supVector_poly {n : ℕ} (S : Finset (Fin n)) :
    PolyCert (fun v : Fin n → ℕ => S.sup v) (encVector n) encNat := by
  classical
  induction S using Finset.induction_on with
  | empty => exact const 0
  | insert a S ha ih =>
    have hx := vectorAt_poly a
    have hm := ite_decide (binary_le' hx ih) ih hx
    apply hm.of_enc_eq
    intro v
    rw [Finset.sup_insert]
    change encNat (max (v a) (S.sup v)) = encNat (if v a ≤ S.sup v then S.sup v else v a)
    rw [max_def]

private theorem argStep_poly (n : ℕ) :
    PolyCert (fun p : Option (LoadState n) × LoadState n =>
      List.argAux (fun a b : LoadState n => Finset.univ.sup a.1 < Finset.univ.sup b.1) p.1 p.2)
      (encPair (encOption (encState n)) (encState n)) (encOption (encState n)) := by
  let stateCodec := encState n
  let e := encPair (encOption stateCodec) stateCodec
  have hnew : PolyCert (fun p : Option (LoadState n) × LoadState n => some p.2)
      e (encOption stateCodec) :=
    (optionSome stateCodec).comp (snd (encOption stateCodec) stateCodec)
  have hbody : PolyCert (fun p : (Option (LoadState n) × LoadState n) × LoadState n =>
      if Finset.univ.sup p.1.2.1 < Finset.univ.sup p.2.1 then some p.1.2 else some p.2)
      (encPair e stateCodec) (encOption stateCodec) := by
    have hcand := (snd (encOption stateCodec) stateCodec).comp (fst e stateCodec)
    have hbest := snd e stateCodec
    have hscore := (supVector_poly (n := n) Finset.univ).comp
      (fst (encVector n) (encList (encAgent n)))
    exact ite_decide (binary_lt' (hscore.comp hcand) (hscore.comp hbest))
      ((optionSome stateCodec).comp hcand) ((optionSome stateCodec).comp hbest)
  apply (optionElimWithInput
    (body := fun p old =>
      if Finset.univ.sup p.2.1 < Finset.univ.sup old.1 then some p.2 else some old)
    (fst (encOption stateCodec) stateCodec) hnew hbody).of_enc_eq
  rintro ⟨(_ | _), _⟩ <;> rfl

private theorem bestState_poly (n : ℕ) :
    PolyCert (fun l : List (LoadState n) => l.argmin (fun s => Finset.univ.sup s.1))
      (encTable n) (encOption (encState n)) := by
  unfold List.argmin
  apply foldl' id' (const none) (argStep_poly n)
    (PolyBounded.self.add (PolyBounded.const 1))
  intro l i _
  let initialSegment := l.take i
  change (encOption (encState n) (initialSegment.argmin (fun s => Finset.univ.sup s.1))).length ≤ _
  cases h : initialSegment.argmin (fun s => Finset.univ.sup s.1) with
  | none => simp
  | some s =>
    have hm : s ∈ initialSegment.argmin (fun s => Finset.univ.sup s.1) := by simp [h]
    have hs := List.mem_of_mem_take (List.argmin_mem hm)
    simpa only [encOption_some, List.length_cons] using
      Nat.add_le_add_right (length_le_encList_of_mem (encState n) hs) 1

private theorem extractWitness_poly (n : ℕ) :
    PolyCert (fun o : Option (LoadState n) => (o.map Prod.snd).getD [])
      (encOption (encState n)) (encList (encAgent n)) := by
  have h := optionElimWithInput (value := (id : Option (LoadState n) → Option (LoadState n)))
    (fallback := fun _ => ([] : List (Fin n))) (body := fun _ s => s.2)
    id' (const []) ((snd (encVector n) (encList (encAgent n))).comp
      (snd (encOption (encState n)) (encState n)))
  apply h.of_enc_eq
  intro o
  cases o <;> rfl

private def hasCap {n : ℕ} (cap : ℕ) (c : Fin n → ℕ) : Bool :=
  (List.finRange n).all (fun i => decide (c i ≤ cap))

private def useBoundedColumns {n : ℕ} (cap : ℕ) (cols : List (Fin n → ℕ)) :
    List (Fin n → ℕ) :=
  if cols.all (hasCap cap) then cols else []

private theorem hasCap_poly (n cap : ℕ) : PolyCert (hasCap (n := n) cap) (encVector n) encBool :=
  allConst (List.finRange n) (fun i _ => binary_le' (vectorAt_poly i) (const cap))

private theorem useBoundedColumns_poly (n cap : ℕ) :
    PolyCert (useBoundedColumns (n := n) cap) (encList (encVector n)) (encList (encVector n)) :=
  cond (allWithInput id' ((hasCap_poly n cap).comp (snd (encList (encVector n)) (encVector n))))
    id' (const [])

private theorem boundedLoadDP_tidy (n cap : ℕ) :
    PolyCert (boundedLoadDP (n := n) cap) (encList (encVector n)) (encList (encAgent n)) := by
  have ht := fold_sanitized_states_poly (useBoundedColumns (n := n) cap) (useBoundedColumns_poly n cap)
    (cap := cap)
    (by
      intro cols c hm i
      unfold useBoundedColumns at hm
      split at hm
      · rename_i h
        have hc := List.all_eq_true.mp h c hm
        exact of_decide_eq_true (List.all_eq_true.mp hc i (List.mem_finRange i))
      · simp at hm)
    (by
      intro cols
      unfold useBoundedColumns
      split
      · exact length_le_length_encList _ _
      · exact Nat.zero_le _)
  apply ((extractWitness_poly n).comp ((bestState_poly n).comp ht)).of_enc_eq
  intro cols
  unfold boundedLoadDP useBoundedColumns hasCap
  by_cases hc : (cols.all fun c => (List.finRange n).all (fun i => decide (c i ≤ cap))) = true
  · simp only [hc, if_pos, Function.comp_apply]
  · simp only [hc, Function.comp_apply]
    rfl

private def decodeColumns {n : ℕ} (cols : List (Option (List ℕ))) : List (Fin n → ℕ) :=
  if cols.all Option.isSome then cols.map (fun c i => ((c.getD [])[i.val]?).getD 0) else []

private theorem decodeColumns_poly (n : ℕ) :
    PolyCert (decodeColumns (n := n)) encCheckedColumns (encList (encVector n)) := by
  let e := encOption (encList encNat)
  have hcol : PolyCert (fun c : Option (List ℕ) => fun i : Fin n => ((c.getD [])[i.val]?).getD 0)
      e (encVector n) :=
    vectorOfComponents_poly _ (fun i => (getD_list_poly i.val).comp
      (optionGetDWithInput id' (const [])))
  exact cond (allWithInput id' (optionIsSome (snd (encList e) e))) (map hcol) (const [])

private theorem solveCheckedColumns_tidy (n cap : ℕ) :
    PolyCert (solveCheckedColumns n cap) encCheckedColumns (encList (encAgent n)) := by
  apply ((boundedLoadDP_tidy n cap).comp (decodeColumns_poly n)).of_enc_eq
  intro cols
  unfold solveCheckedColumns decodeColumns
  by_cases hc : cols.all Option.isSome = true
  · simp only [hc, if_pos, Function.comp_apply]
  · simp only [hc, Function.comp_apply]
    rfl


theorem solution (n cap : ℕ) :
    Nonempty (Turing.TM2ComputableInPolyTime encCheckedColumns
      (encList (encAgent n)) (solveCheckedColumns n cap)) :=
  computableInPolyTime_to_tm2 (solveCheckedColumns_tidy n cap).computableInPolyTime
