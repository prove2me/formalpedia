-- Prove2me | solution 1 for MSKleene.subst_family
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-08T15:48:55.277896+00:00
-- url     : https://prove2.me/submissions/2515fd54-1ace-4911-b4c2-1a05dcac7efc

import Definitions.Def_MSKleene_Subst
import Definitions.Def_MSKleene_SubstFam

open MSKleene
open Classical

theorem substFamAux_exact {S : Type} {sig : Signature S} {X : SSet S}
    {u : S} (z : X u) :
    (∀ {s : S} (t : Term sig X s) (qs : List (Term sig X u)),
      qs.length = Term.occ z t → ∀ rest,
        Term.substFamAux z t (qs ++ rest) =
          ((Term.substFamAux z t qs).1, rest)) ∧
    (∀ {w : List S} (ts : TermVec sig X w) (qs : List (Term sig X u)),
      qs.length = TermVec.occ z ts → ∀ rest,
        TermVec.substFamAux z ts (qs ++ rest) =
          ((TermVec.substFamAux z ts qs).1, rest)) := by
  let motiveT : ∀ s : S, Term sig X s → Prop := fun _ t =>
    ∀ qs : List (Term sig X u), qs.length = Term.occ z t → ∀ rest,
      Term.substFamAux z t (qs ++ rest) =
        ((Term.substFamAux z t qs).1, rest)
  let motiveV : ∀ w : List S, TermVec sig X w → Prop := fun _ ts =>
    ∀ qs : List (Term sig X u), qs.length = TermVec.occ z ts → ∀ rest,
      TermVec.substFamAux z ts (qs ++ rest) =
        ((TermVec.substFamAux z ts qs).1, rest)
  have ht : ∀ {s : S} (t : Term sig X s), motiveT s t :=
    @Term.rec _ _ _ motiveT motiveV
      (fun {s} x qs hlen rest => by
        by_cases h : s = u
        · cases h
          by_cases hx : x = z
          · subst x
            simp only [Term.occ, dite_true, if_pos, Term.substFamAux]
            simp [Term.occ] at hlen
            rcases List.length_eq_one_iff.mp hlen with ⟨q, rfl⟩
            rfl
          · simp [Term.occ, Term.substFamAux, hx] at hlen ⊢
            exact hlen ▸ rfl
        · simp [Term.occ, Term.substFamAux, h] at hlen ⊢
          exact hlen ▸ rfl)
      (fun {w} {s} σ ts ih qs hlen rest => by
        dsimp [motiveT, motiveV] at ih ⊢
        simp only [Term.occ, Term.substFamAux]
        exact congrArg (fun p => (Term.app σ p.1, p.2)) (ih qs hlen rest))
      (fun qs hlen rest => by
        have hq : qs = [] := List.length_eq_zero_iff.mp hlen
        subst qs
        rfl)
      (fun t ts iht ihv qs hlen rest => by
        dsimp [motiveT, motiveV] at iht ihv ⊢
        let n := Term.occ z t
        let lt := qs.take n
        let lv := qs.drop n
        have hn : n ≤ qs.length := by
          dsimp [n]
          rw [hlen, TermVec.occ]
          exact Nat.le_add_right _ _
        have hlt : lt.length = Term.occ z t := by
          simp [lt, n, List.length_take, Nat.min_eq_left hn]
        have hlv : lv.length = TermVec.occ z ts := by
          simp [lv, n, List.length_drop, hlen, TermVec.occ]
        have hq : lt ++ lv = qs := by
          exact List.take_append_drop n qs
        have hleft := iht lt hlt (lv ++ rest)
        have hright := ihv lv hlv rest
        have hleft0 := iht lt hlt lv
        have hright0 := ihv lv hlv ([] : List (Term sig X u))
        rw [← hq]
        simp only [List.append_assoc, TermVec.substFamAux]
        rw [hleft, hright]
        simp only [List.append_nil] at hright0
        rw [hleft0, hright0])
  have hv : ∀ {w : List S} (ts : TermVec sig X w), motiveV w ts :=
    @TermVec.rec _ _ _ motiveT motiveV
      (fun {s} x qs hlen rest => by
        by_cases h : s = u
        · cases h
          by_cases hx : x = z
          · subst x
            simp only [Term.occ, dite_true, if_pos, Term.substFamAux]
            simp [Term.occ] at hlen
            rcases List.length_eq_one_iff.mp hlen with ⟨q, rfl⟩
            rfl
          · simp [Term.occ, Term.substFamAux, hx] at hlen ⊢
            exact hlen ▸ rfl
        · simp [Term.occ, Term.substFamAux, h] at hlen ⊢
          exact hlen ▸ rfl)
      (fun {w} {s} σ ts ih qs hlen rest => by
        dsimp [motiveT, motiveV] at ih ⊢
        simp only [Term.occ, Term.substFamAux]
        exact congrArg (fun p => (Term.app σ p.1, p.2)) (ih qs hlen rest))
      (fun qs hlen rest => by
        have hq : qs = [] := List.length_eq_zero_iff.mp hlen
        subst qs
        rfl)
      (fun t ts iht ihv qs hlen rest => by
        dsimp [motiveT, motiveV] at iht ihv ⊢
        let n := Term.occ z t
        let lt := qs.take n
        let lv := qs.drop n
        have hn : n ≤ qs.length := by
          dsimp [n]
          rw [hlen, TermVec.occ]
          exact Nat.le_add_right _ _
        have hlt : lt.length = Term.occ z t := by
          simp [lt, n, List.length_take, Nat.min_eq_left hn]
        have hlv : lv.length = TermVec.occ z ts := by
          simp [lv, n, List.length_drop, hlen, TermVec.occ]
        have hq : lt ++ lv = qs := by
          exact List.take_append_drop n qs
        have hleft := iht lt hlt (lv ++ rest)
        have hright := ihv lv hlv rest
        have hleft0 := iht lt hlt lv
        have hright0 := ihv lv hlv ([] : List (Term sig X u))
        rw [← hq]
        simp only [List.append_assoc, TermVec.substFamAux]
        rw [hleft, hright]
        simp only [List.append_nil] at hright0
        rw [hleft0, hright0])
  exact ⟨ht, hv⟩

private theorem subst_ofArgs_toArgs {S : Type} {sig : Signature S} {X : SSet S} :
    ∀ {w : List S} (ts : TermVec sig X w), TermVec.ofArgs (TermVec.toArgs ts) = ts
  | [], .nil => rfl
  | _ :: _, .cons t ts => congrArg (TermVec.cons t) (subst_ofArgs_toArgs ts)

theorem substHom_list_sem {S : Type} {sig : Signature S} {X : SSet S}
    {u : S} (z : X u) (L : Set (Term sig X u)) :
    (∀ {s : S} (t : Term sig X s) (R : Term sig X s),
      R ∈ (show Set (Term sig X s) from
        Term.eval (powerAlgebra (freeAlgebra sig X)) (substAssign z L) t) ↔
        ∃ qs : List (Term sig X u),
          qs.length = Term.occ z t ∧
          (∀ q ∈ qs, q ∈ L) ∧ Term.substFamAux z t qs = (R, [])) ∧
    (∀ {w : List S} (ts : TermVec sig X w)
        (xs : Args (Term sig X) w),
      Args.pmem xs (show Args (fun r => Set (Term sig X r)) w from
          TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
            (substAssign z L) ts) ↔
        ∃ qs : List (Term sig X u),
          qs.length = TermVec.occ z ts ∧
          (∀ q ∈ qs, q ∈ L) ∧
          TermVec.substFamAux z ts qs = (TermVec.ofArgs xs, [])) := by
  let motiveT := fun (s : S) (t : Term sig X s) => ∀ R : Term sig X s,
    R ∈ (show Set (Term sig X s) from
      Term.eval (powerAlgebra (freeAlgebra sig X)) (substAssign z L) t) ↔
      ∃ qs : List (Term sig X u),
        qs.length = Term.occ z t ∧
        (∀ q ∈ qs, q ∈ L) ∧ Term.substFamAux z t qs = (R, [])
  let motiveV := fun (w : List S) (ts : TermVec sig X w) =>
    ∀ xs : Args (Term sig X) w,
      Args.pmem xs (show Args (fun r => Set (Term sig X r)) w from
          TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
            (substAssign z L) ts) ↔
        ∃ qs : List (Term sig X u),
          qs.length = TermVec.occ z ts ∧
          (∀ q ∈ qs, q ∈ L) ∧
          TermVec.substFamAux z ts qs = (TermVec.ofArgs xs, [])
  have ht : ∀ {s : S} (t : Term sig X s), motiveT s t :=
    @Term.rec _ _ _ motiveT motiveV
      (fun {s} x R => by
        dsimp [motiveT]
        by_cases h : s = u
        · cases h
          by_cases hx : x = z
          · subst x
            constructor
            · intro hR
              change R ∈ (show Set (Term sig X u) from substAssign z L u z) at hR
              simp [substAssign] at hR
              refine ⟨[R], by simp [Term.occ], ?_, ?_⟩
              · simpa using hR
              · simp [Term.substFamAux]
            · rintro ⟨qs, hlen, hall, haux⟩
              simp [Term.occ] at hlen
              rcases List.length_eq_one_iff.mp hlen with ⟨q, rfl⟩
              simp only [Term.substFamAux, dite_true, if_pos] at haux
              have hq : q = R := congrArg Prod.fst haux
              change R ∈ (show Set (Term sig X u) from substAssign z L u z)
              simpa [substAssign, hq] using hall q (by simp)
          · change R ∈ (show Set (Term sig X u) from substAssign z L u x) ↔ _
            simp [substAssign, Term.occ, Term.substFamAux, hx, eq_comm]
        · change R ∈ (show Set (Term sig X s) from substAssign z L s x) ↔ _
          simp [substAssign, Term.occ, Term.substFamAux, h, eq_comm])
      (fun {w} {s} σ ts ih R => by
        dsimp [motiveT, motiveV] at ih ⊢
        simp only [substHom, evalHom, Term.eval, powerAlgebra_op, powerOp,
          Set.mem_setOf_eq, freeAlgebra, Term.occ, Term.substFamAux]
        constructor
        · rintro ⟨xs, hxs, hR⟩
          rcases (ih xs).mp hxs with ⟨qs, hlen, hall, haux⟩
          refine ⟨qs, hlen, hall, ?_⟩
          rw [haux]
          simpa using hR.symm
        · rintro ⟨qs, hlen, hall, haux⟩
          let rs := (TermVec.substFamAux z ts qs).1
          refine ⟨TermVec.toArgs rs, (ih _).mpr ⟨qs, hlen, hall, ?_⟩, ?_⟩
          · simpa [rs, subst_ofArgs_toArgs] using
              (substFamAux_exact z).2 ts qs hlen ([] : List (Term sig X u))
          · have hfst := congrArg Prod.fst haux
            simpa [rs, subst_ofArgs_toArgs] using hfst.symm)
      (fun xs => by
        dsimp [motiveV]
        refine ⟨fun _ => ⟨[], rfl, by simp, rfl⟩, ?_⟩
        rintro ⟨qs, hlen, hall, haux⟩
        trivial)
      (fun t ts iht ihv xs => by
        dsimp [motiveT, motiveV] at iht ihv ⊢
        rcases xs with ⟨x, xs⟩
        simp only [TermVec.evalArgs, Args.pmem]
        constructor
        · rintro ⟨hx, hxs⟩
          rcases (iht x).mp hx with ⟨lt, hlt, hallt, hauxt⟩
          rcases (ihv xs).mp hxs with ⟨lv, hlv, hallv, hauxv⟩
          refine ⟨lt ++ lv, by simp [TermVec.occ, hlt, hlv], ?_, ?_⟩
          · intro q hq
            rcases List.mem_append.mp hq with hq | hq
            · exact hallt q hq
            · exact hallv q hq
          · simp only [TermVec.occ, TermVec.substFamAux]
            have hsuffix := (substFamAux_exact z).1 t lt hlt lv
            rw [hauxt] at hsuffix
            simp only at hsuffix
            rw [hsuffix, hauxv]
            rfl
        · rintro ⟨qs, hlen, hall, haux⟩
          let n := Term.occ z t
          let lt := qs.take n
          let lv := qs.drop n
          have hn : n ≤ qs.length := by
            dsimp [n]
            rw [hlen, TermVec.occ]
            exact Nat.le_add_right _ _
          have hlt : lt.length = Term.occ z t := by
            simp [lt, n, List.length_take, Nat.min_eq_left hn]
          have hlv : lv.length = TermVec.occ z ts := by
            simp [lv, n, List.length_drop, hlen, TermVec.occ]
          have hq : lt ++ lv = qs := List.take_append_drop n qs
          have hte := (substFamAux_exact z).1 t lt hlt lv
          have hve := (substFamAux_exact z).2 ts lv hlv []
          simp only [List.append_nil] at hve
          have hcalc : TermVec.substFamAux z (TermVec.cons t ts) qs =
              (TermVec.cons (Term.substFamAux z t lt).1
                (TermVec.substFamAux z ts lv).1, []) := by
            rw [← hq]
            simp only [TermVec.substFamAux]
            rw [hte, hve]
          have hcons : TermVec.cons (Term.substFamAux z t lt).1
                (TermVec.substFamAux z ts lv).1 =
              TermVec.cons x (TermVec.ofArgs xs) := by
            exact congrArg Prod.fst (hcalc.symm.trans haux)
          have hhead : (Term.substFamAux z t lt).1 = x := by
            injection hcons
          have htail : (TermVec.substFamAux z ts lv).1 = TermVec.ofArgs xs := by
            injection hcons
          constructor
          · apply (iht x).mpr
            refine ⟨lt, hlt, ?_, ?_⟩
            · intro q hmem
              exact hall q (List.mem_of_mem_take hmem)
            · have ht0 := (substFamAux_exact z).1 t lt hlt []
              simpa [hhead] using ht0
          · apply (ihv xs).mpr
            refine ⟨lv, hlv, ?_, ?_⟩
            · intro q hmem
              exact hall q (List.mem_of_mem_drop hmem)
            · simpa [htail] using hve)
  have hv : ∀ {w : List S} (ts : TermVec sig X w), motiveV w ts :=
    @TermVec.rec _ _ _ motiveT motiveV
      (fun {s} x R => by
        dsimp [motiveT]
        by_cases h : s = u
        · cases h
          by_cases hx : x = z
          · subst x
            constructor
            · intro hR
              change R ∈ (show Set (Term sig X u) from substAssign z L u z) at hR
              simp [substAssign] at hR
              refine ⟨[R], by simp [Term.occ], ?_, ?_⟩
              · simpa using hR
              · simp [Term.substFamAux]
            · rintro ⟨qs, hlen, hall, haux⟩
              simp [Term.occ] at hlen
              rcases List.length_eq_one_iff.mp hlen with ⟨q, rfl⟩
              simp only [Term.substFamAux, dite_true, if_pos] at haux
              have hq : q = R := congrArg Prod.fst haux
              change R ∈ (show Set (Term sig X u) from substAssign z L u z)
              simpa [substAssign, hq] using hall q (by simp)
          · change R ∈ (show Set (Term sig X u) from substAssign z L u x) ↔ _
            simp [substAssign, Term.occ, Term.substFamAux, hx, eq_comm]
        · change R ∈ (show Set (Term sig X s) from substAssign z L s x) ↔ _
          simp [substAssign, Term.occ, Term.substFamAux, h, eq_comm])
      (fun {w} {s} σ ts ih R => by
        dsimp [motiveT, motiveV] at ih ⊢
        simp only [substHom, evalHom, Term.eval, powerAlgebra_op, powerOp,
          Set.mem_setOf_eq, freeAlgebra, Term.occ, Term.substFamAux]
        constructor
        · rintro ⟨xs, hxs, hR⟩
          rcases (ih xs).mp hxs with ⟨qs, hlen, hall, haux⟩
          refine ⟨qs, hlen, hall, ?_⟩
          rw [haux]
          simpa using hR.symm
        · rintro ⟨qs, hlen, hall, haux⟩
          let rs := (TermVec.substFamAux z ts qs).1
          refine ⟨TermVec.toArgs rs, (ih _).mpr ⟨qs, hlen, hall, ?_⟩, ?_⟩
          · simpa [rs, subst_ofArgs_toArgs] using
              (substFamAux_exact z).2 ts qs hlen ([] : List (Term sig X u))
          · have hfst := congrArg Prod.fst haux
            simpa [rs, subst_ofArgs_toArgs] using hfst.symm)
      (fun xs => by
        dsimp [motiveV]
        refine ⟨fun _ => ⟨[], rfl, by simp, rfl⟩, ?_⟩
        rintro ⟨qs, hlen, hall, haux⟩
        trivial)
      (fun t ts iht ihv xs => by
        dsimp [motiveT, motiveV] at iht ihv ⊢
        rcases xs with ⟨x, xs⟩
        simp only [TermVec.evalArgs, Args.pmem]
        constructor
        · rintro ⟨hx, hxs⟩
          rcases (iht x).mp hx with ⟨lt, hlt, hallt, hauxt⟩
          rcases (ihv xs).mp hxs with ⟨lv, hlv, hallv, hauxv⟩
          refine ⟨lt ++ lv, by simp [TermVec.occ, hlt, hlv], ?_, ?_⟩
          · intro q hq
            rcases List.mem_append.mp hq with hq | hq
            · exact hallt q hq
            · exact hallv q hq
          · simp only [TermVec.occ, TermVec.substFamAux]
            have hsuffix := (substFamAux_exact z).1 t lt hlt lv
            rw [hauxt] at hsuffix
            simp only at hsuffix
            rw [hsuffix, hauxv]
            rfl
        · rintro ⟨qs, hlen, hall, haux⟩
          let n := Term.occ z t
          let lt := qs.take n
          let lv := qs.drop n
          have hn : n ≤ qs.length := by
            dsimp [n]
            rw [hlen, TermVec.occ]
            exact Nat.le_add_right _ _
          have hlt : lt.length = Term.occ z t := by
            simp [lt, n, List.length_take, Nat.min_eq_left hn]
          have hlv : lv.length = TermVec.occ z ts := by
            simp [lv, n, List.length_drop, hlen, TermVec.occ]
          have hq : lt ++ lv = qs := List.take_append_drop n qs
          have hte := (substFamAux_exact z).1 t lt hlt lv
          have hve := (substFamAux_exact z).2 ts lv hlv []
          simp only [List.append_nil] at hve
          have hcalc : TermVec.substFamAux z (TermVec.cons t ts) qs =
              (TermVec.cons (Term.substFamAux z t lt).1
                (TermVec.substFamAux z ts lv).1, []) := by
            rw [← hq]
            simp only [TermVec.substFamAux]
            rw [hte, hve]
          have hcons : TermVec.cons (Term.substFamAux z t lt).1
                (TermVec.substFamAux z ts lv).1 =
              TermVec.cons x (TermVec.ofArgs xs) := by
            exact congrArg Prod.fst (hcalc.symm.trans haux)
          have hhead : (Term.substFamAux z t lt).1 = x := by
            injection hcons
          have htail : (TermVec.substFamAux z ts lv).1 = TermVec.ofArgs xs := by
            injection hcons
          constructor
          · apply (iht x).mpr
            refine ⟨lt, hlt, ?_, ?_⟩
            · intro q hmem
              exact hall q (List.mem_of_mem_take hmem)
            · have ht0 := (substFamAux_exact z).1 t lt hlt []
              simpa [hhead] using ht0
          · apply (ihv xs).mpr
            refine ⟨lv, hlv, ?_, ?_⟩
            · intro q hmem
              exact hall q (List.mem_of_mem_drop hmem)
            · simpa [htail] using hve)
  exact ⟨ht, hv⟩

theorem solution {S : Type} (sig : Signature S) (X : SSet S) {u s : S}
    (z : X u) (L : Set (Term sig X u)) (P : Term sig X s) :
    ((substHom z L).toFun s P
      = { R | ∃ qs : Fin (Term.occ z P) → Term sig X u,
              (∀ α, qs α ∈ L) ∧ R = substFam z P qs })
  ∧ (∀ K : Set (Term sig X s),
      substP z L s K = ⋃ Q ∈ K, (substHom z L).toFun s Q) := by
  constructor
  · change (show Set (Term sig X s) from (substHom z L).toFun s P) =
        { R | ∃ qs : Fin (Term.occ z P) → Term sig X u,
          (∀ α, qs α ∈ L) ∧ R = substFam z P qs }
    ext R
    change (R ∈ (show Set (Term sig X s) from
      Term.eval (powerAlgebra (freeAlgebra sig X)) (substAssign z L) P)) ↔ _
    constructor
    · intro hR
      rcases ((substHom_list_sem z L).1 P R).mp hR with
        ⟨ls, hlen, hall, haux⟩
      let f : Fin ls.length → Term sig X u := fun i => ls.get i
      let qs : Fin (Term.occ z P) → Term sig X u :=
        fun i => f (Fin.cast hlen.symm i)
      refine ⟨qs, ?_, ?_⟩
      · intro α
        exact hall (qs α) (by
          dsimp [qs, f]
          exact List.get_mem _ _)
      · unfold substFam
        have hof : List.ofFn qs = ls := by
          calc
            List.ofFn qs = List.ofFn f := (List.ofFn_congr hlen f).symm
            _ = ls := List.ofFn_get _
        rw [hof]
        exact (congrArg Prod.fst haux).symm
    · rintro ⟨qs, hall, hEq⟩
      apply ((substHom_list_sem z L).1 P R).mpr
      refine ⟨List.ofFn qs, by simp, ?_, ?_⟩
      · exact List.forall_mem_ofFn_iff.mpr hall
      · have hexact := (substFamAux_exact z).1 P (List.ofFn qs) (by simp)
            ([] : List (Term sig X u))
        simp only [List.append_nil] at hexact
        calc
          Term.substFamAux z P (List.ofFn qs) =
              ((Term.substFamAux z P (List.ofFn qs)).1, []) := hexact
          _ = (R, []) := by
            apply congrArg (fun q => (q, []))
            simpa [substFam] using hEq.symm
  · intro K
    rfl
