-- Prove2me | solution 1 for NisanRonen.Rounding.unitMakespan_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:04:46.890583+00:00
-- url     : https://prove2.me/submissions/fe927e84-539c-4727-8791-caf60b7db179

import Mathlib
import Definitions.Def_NisanRonen_Rounding_unitMakespan
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
import Theorems.Thm_Turing_MultiTapeTM_computableInPolyTime_to_tm2
import Theorems.Thm_Turing_TM2ComputableInPolyTime_comp_of_polytime
import Definitions.Def_NisanRonen_Rounding_encodeInstanceAlloc
import Definitions.Def_NisanRonen_Rounding_checkedColumns
import Theorems.Thm_Turing_SubsequentialTransducer_tm2_polytime

open Turing Turing.MultiTapeTM Turing.SubsequentialTransducer NisanRonen.Rounding
open Computability (Γ')
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

set_option autoImplicit false

private def encVector (n : ℕ) : (Fin n → ℕ) ↪ List Bool :=
  ⟨fun v => encList encNat (List.ofFn v), fun _ _ h =>
    List.ofFn_inj.mp ((encList encNat).injective h)⟩

private abbrev bonusCodec (n : ℕ) :=
  encPair (encList (encVector n)) (encList (encAgent n))

private theorem encodePosNum_bits (m : PosNum) :
    Computability.encodePosNum m = (m : ℕ).bits := by
  induction m with
  | one => rfl
  | bit0 m ih =>
    rw [PosNum.cast_bit0, ← two_mul, Nat.bit0_bits _ (PosNum.to_nat_pos _).ne']
    exact congrArg (false :: ·) ih
  | bit1 m ih =>
    rw [PosNum.cast_bit1, ← two_mul, Nat.bit1_bits]
    exact congrArg (true :: ·) ih

private theorem encodeNat_bits (m : ℕ) : Computability.encodeNat m = m.bits := by
  have h (v : Num) : Computability.encodeNum v = (v : ℕ).bits := by
    cases v with
    | zero => rfl
    | pos v => exact encodePosNum_bits v
  have hm := h (m : Num)
  rw [show ((m : Num) : ℕ) = m from Num.of_natCast (α := ℕ) m] at hm
  exact hm

private def quoteBits (w : List Bool) : List Bool := w.flatMap fun b => [true, b]

private theorem quote_append (v w : List Bool) :
    quoteBits (v ++ w) = quoteBits v ++ quoteBits w := by simp [quoteBits]

private theorem frame_eq_quote (w : List Bool) : frame w = quoteBits w ++ [false] := rfl

private def recodeColumnSymbol : Γ' → List Bool
  | .bit b => quoteBits (quoteBits [true, b])
  | .comma => quoteBits (quoteBits [false])
  | .ket => quoteBits [false]
  | _ => []

private theorem recodeNumber (m : ℕ) :
    (((Computability.encodeNat m).map Γ'.bit) ++ [Γ'.comma]).flatMap recodeColumnSymbol =
      quoteBits (quoteBits (frame (encNat m))) := by
  rw [encodeNat_bits]
  rw [List.flatMap_append]
  change (List.map Γ'.bit m.bits).flatMap recodeColumnSymbol ++
      quoteBits (quoteBits [false]) = _
  rw [encNat_apply, frame_eq_quote, quote_append, quote_append]
  congr 1
  generalize m.bits = w
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [List.map_cons, List.flatMap_cons, recodeColumnSymbol, ih]
    change quoteBits (quoteBits [true, b]) ++ quoteBits (quoteBits (quoteBits w)) =
      quoteBits (quoteBits ([true, b] ++ quoteBits w))
    rw [quote_append, quote_append]

private theorem recodeNumbers (xs : List ℕ) :
    (xs.flatMap fun m => (Computability.encodeNat m).map Γ'.bit ++ [Γ'.comma]).flatMap
      recodeColumnSymbol = quoteBits (quoteBits (encList encNat xs)) := by
  induction xs with
  | nil => rfl
  | cons m xs ih =>
    rw [List.flatMap_cons, List.flatMap_append, recodeNumber, ih, encList_cons,
      quote_append, quote_append]

private theorem recodeColumns {n : ℕ} (cols : List (Fin n → ℕ)) :
    (encodeInstance cols).flatMap recodeColumnSymbol = quoteBits (encList (encVector n) cols) := by
  induction cols with
  | nil => rfl
  | cons c cols ih =>
    change (([Γ'.bra] ++
      (List.finRange n).flatMap (fun i => (Computability.encodeNat (c i)).map Γ'.bit ++ [Γ'.comma]) ++
      [Γ'.ket]) ++ encodeInstance cols).flatMap recodeColumnSymbol = _
    have hmap : (List.finRange n).map c = List.ofFn c := by
      simp [List.finRange, List.map_ofFn, Function.comp_def]
    have hnumbers : ((List.finRange n).flatMap fun i =>
        (Computability.encodeNat (c i)).map Γ'.bit ++ [Γ'.comma]).flatMap recodeColumnSymbol =
        quoteBits (quoteBits (encList encNat (List.ofFn c))) := by
      have hm := recodeNumbers (List.ofFn c)
      rw [← hmap, List.flatMap_map, hmap] at hm
      exact hm
    rw [List.flatMap_append, List.flatMap_append, List.flatMap_append, hnumbers, ih, encList_cons,
      quote_append, frame_eq_quote, quote_append]
    rfl

private def bonusStep {n : ℕ} (inAlloc : Bool) :
    Γ' ⊕ Fin n → Bool × List Bool
  | .inl a => (inAlloc, recodeColumnSymbol a)
  | .inr i => (true, if inAlloc then frame (encAgent n i) else false :: frame (encAgent n i))

private def bonusFinish (inAlloc : Bool) : List Bool := if inAlloc then [] else [false]

private theorem run_right {n : ℕ} (x : List (Fin n)) :
    run bonusStep bonusFinish true (x.map (Sum.inr (α := Γ'))) = encList (encAgent n) x := by
  induction x with
  | nil => rfl
  | cons i x ih => simp [run, bonusStep, ih]

private theorem run_right_start {n : ℕ} (x : List (Fin n)) :
    run bonusStep bonusFinish false (x.map (Sum.inr (α := Γ'))) =
      false :: encList (encAgent n) x := by
  cases x with
  | nil => rfl
  | cons i x => simp [run, bonusStep, run_right]

private theorem run_left_right {n : ℕ} (w : List Γ') (x : List (Fin n)) :
    run bonusStep bonusFinish false (w.map Sum.inl ++ x.map Sum.inr) =
      w.flatMap recodeColumnSymbol ++ false :: encList (encAgent n) x := by
  induction w with
  | nil => simpa using run_right_start x
  | cons a w ih => simp [run, bonusStep, ih, List.append_assoc]

private theorem bonus_input_recode {n : ℕ} (p : List (Fin n → ℕ) × List (Fin n)) :
    run bonusStep bonusFinish false (encodeInstanceAlloc p) = bonusCodec n p := by
  rw [encodeInstanceAlloc, run_left_right, recodeColumns, encPair_apply, frame_eq_quote,
    List.append_assoc]
  rfl

private theorem bonus_input_polytime (n : ℕ) :
    Nonempty (TM2ComputableInPolyTime (encodeInstanceAlloc (n := n)) (bonusCodec n)
      (id : List (Fin n → ℕ) × List (Fin n) → List (Fin n → ℕ) × List (Fin n))) := by
  obtain ⟨m⟩ := Turing.SubsequentialTransducer.tm2_polytime
    (bonusStep (n := n)) bonusFinish false
  refine ⟨{ toTM2ComputableAux := m.toTM2ComputableAux, time := m.time, outputsFun := ?_ }⟩
  intro p
  simpa only [id_eq, bonus_input_recode] using m.outputsFun (encodeInstanceAlloc p)
private abbrev PolyCert {α β : Type} (f : α → β) (ein : α ↪ List Bool) (eout : β ↪ List Bool) :=
  ComputableTidilyInPolyTime f ein eout

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

private theorem loadForAgent_poly {n : ℕ} (i : Fin n) :
    PolyCert (fun p : List (Fin n → ℕ) × List (Fin n) =>
      (((p.1.zip p.2).filter (fun q => decide (q.2 = i))).map (fun q => q.1 i)).sum)
      (bonusCodec n) encNat := by
  let code := encPair (encVector n) (encAgent n)
  have hz : PolyCert (fun p : List (Fin n → ℕ) × List (Fin n) => p.1.zip p.2)
      (bonusCodec n) (encList code) :=
    ComputableTidilyInPolyTime.zip (encVector n) (encAgent n)
  have ht : PolyCert (fun q : (Fin n → ℕ) × Fin n => decide (q.2 = i)) code encBool :=
    decide_eq' (snd (encVector n) (encAgent n)) (const i)
  have hv : PolyCert (fun q : (Fin n → ℕ) × Fin n => q.1 i) code encNat :=
    (vectorAt_poly i).comp (fst (encVector n) (encAgent n))
  exact binary_sum.comp ((map hv).comp ((filter ht).comp hz))

private theorem unitMakespan_tidy (n : ℕ) :
    PolyCert (unitMakespan (n := n)) (bonusCodec n) encNat :=
  (supVector_poly (n := n) Finset.univ).comp
    (vectorOfComponents_poly _ loadForAgent_poly)

theorem solution (n : ℕ) :
    Nonempty (TM2ComputableInPolyTime (encodeInstanceAlloc (n := n))
      Computability.encodeNat (unitMakespan (n := n))) := by
  obtain ⟨input⟩ := bonus_input_polytime n
  obtain ⟨core⟩ := computableInPolyTime_to_tm2 (unitMakespan_tidy n).computableInPolyTime
  obtain ⟨m⟩ := TM2ComputableInPolyTime.comp_of_polytime input core
  refine ⟨{ toTM2ComputableAux := m.toTM2ComputableAux, time := m.time, outputsFun := ?_ }⟩
  intro p
  simpa only [encodeNat_bits, encNat_apply, Function.comp_def, id_eq] using m.outputsFun p
