-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock22528
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T07:31:00.938886+00:00
-- url     : https://prove2.me/submissions/33afd934-e5b5-4ad2-85c8-3e0be4d941ca

import Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentStarBit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

namespace IntMul.Kappa.R8.Bit.Oppbank.RankCheck

open Module Submodule Matrix Pnd SupG Cent

def active (sup : ℕ) (c : Fin 23) : List (Fin 23) :=
  (List.finRange 23).filter fun p => (p != c) && (sup &&& starC p.val != 0)

def hub (sup : ℕ) (es : List (Fin 23)) : Option (Fin 23) :=
  es.find? fun a =>
    let incident := sup &&& starC a.val
    (incident != sup) && es.all (fun p => p == a || (incident &&& starC p.val != 0))

def hubTest (n sup : ℕ) : Bool :=
  if hc : centF n < 23 then
    let c : Fin 23 := ⟨centF n, hc⟩
    let es := active sup c
    (sup < 2^1771) && centredStar sup c.val && (es.length == dimF n) && (hub sup es).isSome
  else false

def leafPart (sup : ℕ) (p : Fin 23) : ℕ :=
  let m := sup &&& starC p.val
  if (m != 0) && ((m &&& (m-1)) == 0) then m else 0

def leafCover (sup : ℕ) : ℕ :=
  (List.finRange 23).foldr (fun p r => leafPart sup p ||| r) 0

def leafTest (n sup : ℕ) : Bool :=
  if hc : centF n < 23 then
    (sup < 2^1771) && centredStar sup (⟨centF n,hc⟩ : Fin 23).val &&
    (leafCover sup == sup) &&
    let is := bitIndices 1771 sup
    (is.length == dimF n) && decide is.Nodup
  else false


noncomputable def nodeFast (n : ℕ) : Bool :=
  let sup := densSupG n
  hubTest n sup || leafTest n sup || nodeCheck n

end IntMul.Kappa.R8.Bit.Oppbank.RankCheck

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

namespace IntMul.Kappa.R8.Bit.Oppbank.RankCheck

open Module Submodule Matrix Pnd SupG Cent

@[simp] theorem sign_false : sign false = 1 := rfl
@[simp] theorem sign_true : sign true = -1 := rfl
@[simp] theorem sign_sq (b : Bool) : sign b * sign b = 1 := by cases b <;> norm_num
@[simp] theorem sign_ne_zero (b : Bool) : sign b ≠ 0 := by cases b <;> norm_num

theorem pivot_some {p : Fin 23} {r : Row} {b : Bool}
    {t : Option (Fin 23 × Bool)} (hr : r.valid) (h : r.atPivot p = some (b,t)) :
    r.vec = sign b • (unit p + term t) ∧ term t p = 0 := by
  cases r with
  | zero => simp [Row.atPivot] at h
  | one i =>
    simp only [Row.atPivot] at h
    split at h
    · obtain ⟨rfl,rfl⟩ := Option.some.inj h
      subst i
      simp [Row.vec, term]
    · contradiction
  | two i j neg =>
    simp only [Row.atPivot] at h
    split at h
    · obtain ⟨rfl,rfl⟩ := Option.some.inj h
      subst i
      exact ⟨by simp [Row.vec, term], by simp [term, unit, Pi.single_eq_of_ne hr]⟩
    · rename_i hpi
      split at h
      · obtain ⟨rfl,rfl⟩ := Option.some.inj h
        subst j
        exact ⟨by simp [Row.vec, term, smul_add, smul_smul, add_comm],
          by simp [term, unit, Pi.single_eq_of_ne hpi]⟩
      · contradiction

theorem pivot_none {p : Fin 23} {r : Row} (h : r.atPivot p = none) :
    r.vec p = 0 := by
  cases r with
  | zero => rfl
  | one i =>
    simp only [Row.atPivot] at h
    split at h
    · contradiction
    · rename_i hp
      simp [Row.vec, unit, Pi.single_eq_of_ne hp]
  | two i j b =>
    simp only [Row.atPivot] at h
    split at h
    · contradiction
    · rename_i hi
      split at h
      · contradiction
      · rename_i hj
        simp [Row.vec, unit, Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hj]

theorem diff_spec (t u : Option (Fin 23 × Bool)) :
    (diff t u).1.valid ∧ (diff t u).2 ≠ 0 ∧
      term t - term u = (diff t u).2 • (diff t u).1.vec := by
  cases t with
  | none =>
    cases u with
    | none => simp [diff, Row.valid, Row.vec, term]
    | some u => obtain ⟨i,b⟩ := u; simp [diff, Row.valid, Row.vec, term]
  | some t =>
    obtain ⟨a,b⟩ := t
    cases u with
    | none => simp [diff, Row.valid, Row.vec, term]
    | some u =>
      obtain ⟨c,d⟩ := u
      by_cases h : a = c
      · subst c
        cases b <;> cases d <;>
          simp [diff, Row.valid, Row.vec, term, sub_eq_add_neg] <;> module
      · cases b <;> cases d <;>
          simp [diff, h, Row.valid, Row.vec, term, Bool.xor, sub_eq_add_neg, smul_add]

theorem spanRows_cons (r : Row) (rs : List Row) :
    spanRows (r :: rs) = span ℚ {r.vec} ⊔ spanRows rs := by
  rw [spanRows, spanRows, ← span_union]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, List.mem_cons, exists_eq_or_imp, Set.mem_union,
    Set.mem_singleton_iff]

theorem spanRows_nil : spanRows [] = ⊥ := by
  unfold spanRows
  rw [show {v : V | ∃ r ∈ ([] : List Row), v = r.vec} = ∅ by simp, span_empty]

theorem clear_spec {p : Fin 23} {r pivot : Row} {b : Bool}
    {t : Option (Fin 23 × Bool)} (hr : r.valid) (hp : pivot.valid)
    (h : pivot.atPivot p = some (b,t)) :
    let s := clear p t r
    s.valid ∧ s.vec p = 0 ∧
    span ℚ {pivot.vec} ⊔ span ℚ {s.vec} = span ℚ {pivot.vec} ⊔ span ℚ {r.vec} := by
  dsimp only
  have ⟨hpv, htp⟩ := pivot_some hp h
  cases hq : r.atPivot p with
  | none => simp [clear, hq, hr, pivot_none hq]
  | some u =>
    obtain ⟨c,u⟩ := u
    have ⟨hrv, hup⟩ := pivot_some hr hq
    have ⟨hs, hk, he⟩ := diff_spec u t
    let s := (diff u t).1
    let k := (diff u t).2
    have hstep : sign c • r.vec - sign b • pivot.vec = k • s.vec := by
      rw [hrv, hpv, smul_smul, smul_smul, sign_sq, sign_sq, one_smul, one_smul, ← he]
      abel
    have hsz : s.vec p = 0 := by
      have hh := congrFun he p
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hup, htp, sub_zero] at hh
      exact (mul_eq_zero.mp hh.symm).resolve_left hk
    rw [clear, hq]
    refine ⟨hs, hsz, le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)⟩
    · apply span_le.mpr
      intro v hv
      rw [Set.mem_singleton_iff.mp hv]
      have hrm : r.vec ∈ span ℚ {pivot.vec} ⊔ span ℚ {r.vec} :=
        show r.vec ∈ span ℚ {pivot.vec} ⊔ span ℚ {r.vec} from
          (show span ℚ {r.vec} ≤ span ℚ {pivot.vec} ⊔ span ℚ {r.vec} from le_sup_right)
            (subset_span (by simp))
      have hpm : pivot.vec ∈ span ℚ {pivot.vec} ⊔ span ℚ {r.vec} :=
        (show span ℚ {pivot.vec} ≤ span ℚ {pivot.vec} ⊔ span ℚ {r.vec} from le_sup_left)
          (subset_span (by simp))
      have hmem := (span ℚ {pivot.vec} ⊔ span ℚ {r.vec}).sub_mem
        ((span ℚ {pivot.vec} ⊔ span ℚ {r.vec}).smul_mem (sign c) hrm)
        ((span ℚ {pivot.vec} ⊔ span ℚ {r.vec}).smul_mem (sign b) hpm)
      rw [hstep] at hmem
      exact (Submodule.smul_mem_iff_of_isUnit _ (isUnit_iff_ne_zero.mpr hk)).mp hmem
    · apply span_le.mpr
      intro v hv
      rw [Set.mem_singleton_iff.mp hv]
      let W : Submodule ℚ V := span ℚ {pivot.vec} ⊔ span ℚ {s.vec}
      have hsm : s.vec ∈ W := (show span ℚ {s.vec} ≤ W from le_sup_right) (subset_span (by simp))
      have hpm : pivot.vec ∈ W := (show span ℚ {pivot.vec} ≤ W from le_sup_left) (subset_span (by simp))
      have hadd := W.add_mem (W.smul_mem k hsm) (W.smul_mem (sign b) hpm)
      rw [← hstep, sub_add_cancel] at hadd
      exact (Submodule.smul_mem_iff_of_isUnit _ (isUnit_iff_ne_zero.mpr (sign_ne_zero c))).mp hadd

theorem Echelon.insert_spec {e : Echelon} {r : Row} (he : e.good) (hr : r.valid) :
    (e.insert r).good ∧ (e.insert r).space = e.space ⊔ span ℚ {r.vec} := by
  induction e generalizing r with
  | nil =>
      cases r <;> simp_all [Echelon.insert, Echelon.good, Echelon.space,
        Row.vec, Row.atPivot, Row.valid]
  | cons p pivot b t rest ih =>
      obtain ⟨hp, h, hg, hz⟩ := he
      obtain ⟨hs, hsz, hspace⟩ := clear_spec hr hp h
      obtain ⟨hgood, hh⟩ := ih hg hs
      simp only [Echelon.insert, Echelon.good, Echelon.space, hh]
      refine ⟨⟨hp, h, hgood, ?_⟩, ?_⟩
      · intro v hv
        obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hv
        obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hy
        simp [hz x hx, hsz]
      · calc
          (rest.space ⊔ span ℚ {(clear p t r).vec}) ⊔ span ℚ {pivot.vec}
              = rest.space ⊔ (span ℚ {pivot.vec} ⊔ span ℚ {(clear p t r).vec}) := by
                ac_rfl
          _ = rest.space ⊔ (span ℚ {pivot.vec} ⊔ span ℚ {r.vec}) := by rw [hspace]
          _ = (rest.space ⊔ span ℚ {pivot.vec}) ⊔ span ℚ {r.vec} := by ac_rfl

set_option backward.isDefEq.respectTransparency false in
theorem Echelon.finrank_space {e : Echelon} (he : e.good) :
    finrank ℚ e.space = e.size := by
  induction e with
  | nil => exact finrank_bot ℚ V
  | cons p pivot b t rest ih =>
    obtain ⟨hp, h, hg, hz⟩ := he
    obtain ⟨hpv, htp⟩ := pivot_some hp h
    have hne : pivot.vec ∉ rest.space := by
      intro hm
      have hh := hz _ hm
      rw [hpv] at hh
      simp [unit, htp] at hh
    rw [Echelon.space, Echelon.size, ← ih hg]
    exact Submodule.finrank_sup_span_singleton hne

theorem fold_insert {rs : List Row} {e : Echelon} (he : e.good)
    (hr : ∀ r ∈ rs, Row.valid r) :
    let out := rs.foldl (fun e r => e.insert r) e
    out.good ∧ out.space = e.space ⊔ spanRows rs := by
  induction rs generalizing e with
  | nil => simp [he, spanRows_nil]
  | cons r rs ih =>
    have ⟨hg, hs⟩ := Echelon.insert_spec he (hr r (by simp))
    have hh := ih hg (fun r h => hr r (by simp [h]))
    simpa [List.foldl, hs, spanRows_cons, sup_assoc] using hh

theorem rankRows_eq {rs : List Row} (hr : ∀ r ∈ rs, Row.valid r) :
    rankRows rs = finrank ℚ (spanRows rs) := by
  obtain ⟨hg, hs⟩ := fold_insert (e := .nil) trivial hr
  have hf := Echelon.finrank_space hg
  rw [hs, Echelon.space, bot_sup_eq] at hf
  exact hf.symm

theorem hiBit_bounds {k w : ℕ} (hz : w ≠ 0) (hw : w < 2 ^ (2 ^ k)) :
    2 ^ (hiBit k w) ≤ w ∧ w < 2 ^ (hiBit k w + 1) := by
  induction k generalizing w with
  | zero =>
    simp only [hiBit, pow_zero, zero_add, pow_one] at *
    omega
  | succ k ih =>
    let q := 2 ^ k
    let p := 2 ^ q
    have hp : 0 < p := Nat.two_pow_pos _
    have hw' : w < p * p := by
      rw [pow_succ (2 : ℕ) k, Nat.mul_two, pow_add] at hw
      exact hw
    simp only [hiBit, Nat.one_shiftLeft, Nat.shiftRight_eq_div_pow]
    change 2 ^ (if w / p = 0 then hiBit k w else q + hiBit k (w/p)) ≤ w ∧
      w < 2 ^ ((if w/p = 0 then hiBit k w else q + hiBit k (w/p)) + 1)
    by_cases h : w / p = 0
    · have hlt : w < p := (Nat.div_lt_iff_lt_mul hp).mp (by omega) |>.trans_eq (Nat.one_mul _)
      simpa only [if_pos h] using ih hz hlt
    · have hr : w / p < p := (Nat.div_lt_iff_lt_mul hp).mpr hw'
      obtain ⟨h1,h2⟩ := ih h hr
      have le := (Nat.le_div_iff_mul_le hp).mp h1
      have lt := (Nat.div_lt_iff_lt_mul hp).mp h2
      simp only [if_neg h]
      constructor
      · rw [pow_add]
        simpa only [Nat.mul_comm] using le
      · rw [add_assoc, pow_add]
        simpa only [Nat.mul_comm] using lt

theorem hiBit_eq_log2 {w : ℕ} (hz : w ≠ 0) (hw : w < 2 ^ 2048) :
    hiBit 11 w = w.log2 :=
  (Nat.log2_eq_iff hz).mpr (hiBit_bounds (k := 11) hz hw) |>.symm

theorem mem_bitIndices {fuel w i : ℕ} (hFuel : fuel ≤ 2048) (hw : w < 2 ^ fuel) :
    i ∈ bitIndices fuel w ↔ w.testBit i = true := by
  induction fuel generalizing w with
  | zero =>
    have : w = 0 := by simpa using hw
    simp [bitIndices, this]
  | succ fuel ih =>
    by_cases hz : w = 0
    · simp [bitIndices, hz]
    have hhi : w.log2 ≤ fuel := by
      have hp := Nat.log2_self_le hz
      by_contra h
      exact (not_le_of_gt hw) ((Nat.pow_le_pow_right (by decide) (by omega)).trans hp)
    have hb : w % (1 <<< w.log2) < 2 ^ fuel := by
      rw [Nat.one_shiftLeft]
      exact (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le
        (Nat.pow_le_pow_right (by decide) hhi)
    have hL := hiBit_eq_log2 hz (hw.trans_le (Nat.pow_le_pow_right (by decide) hFuel))
    rw [bitIndices, if_neg hz, hL, List.mem_cons, ih (by omega) hb, Nat.one_shiftLeft,
      Nat.testBit_mod_two_pow]
    obtain h | rfl | h := lt_trichotomy i w.log2
    · simp [h, ne_of_lt h]
    · simp [Nat.testBit_log2 hz]
    · have hf := Nat.testBit_eq_false_of_lt
        ((Nat.lt_log2_self (n := w)).trans_le
          (Nat.pow_le_pow_right (by decide) h))
      simp [not_lt_of_gt h, ne_of_gt h, hf]

theorem drop_apply (c : Fin 23) (v : V) (i : Fin 23) :
    drop c v i = if i = c then 0 else v i := rfl

theorem drop_unit (c i : Fin 23) :
    drop c (unit i) = if i = c then 0 else unit i := by
  by_cases h : i = c
  · subst i
    funext j
    by_cases hj : j = c <;> simp [drop_apply, hj, unit, Pi.single_eq_of_ne]
  · funext j
    by_cases hj : j = c
    · subst j
      simp [drop_apply, h, unit]
    · simp [drop_apply, h, hj]

theorem dropped_dim (s : Submodule ℚ V) (c : Fin 23)
    (hc : ∀ v ∈ s, ∑ p, v p = 3 * v c) :
    finrank ℚ (s.map (drop c)) = finrank ℚ s := by
  have hRange : LinearMap.range ((drop c).comp s.subtype) = s.map (drop c) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← hRange]
  apply LinearMap.finrank_range_of_inj
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change drop c (v : V) = 0 at hv
  have hz : ∀ j ≠ c, (v : V) j = 0 := by
    intro j hj
    simpa [drop_apply, hj] using congrFun hv j
  have hsum : (∑ p, (v : V) p) = (v : V) c := by
    apply Finset.sum_eq_single c
    · intro j _ hj
      exact hz j hj
    · simp
  have hvc := hc (v : V) v.property
  rw [hsum] at hvc
  have h0 : (v : V) c = 0 := by linarith
  apply Subtype.ext
  funext j
  by_cases hj : j = c
  · simpa [hj] using h0
  · exact hz j hj

theorem triple_vec {i : ℕ} {a b d : Fin 23}
    (ha : ptsL i 0 = a) (hb : ptsL i 1 = b) (hd : ptsL i 2 = d)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    tvQ i = unit a + unit b + unit d := by
  funext p
  have hab' : (a : ℕ) ≠ b := fun h => hab (Fin.ext h)
  have had' : (a : ℕ) ≠ d := fun h => had (Fin.ext h)
  have hbd' : (b : ℕ) ≠ d := fun h => hbd (Fin.ext h)
  simp only [tvQ, triL, ha, hb, hd, Nat.shiftLeft_eq', Nat.one_shiftLeft, Nat.lor_eq,
    Nat.testBit_lor, Nat.testBit_two_pow, Pi.add_apply]
  by_cases hpa : p = a
  · subst p
    simp [hab, had, hab'.symm, had'.symm, unit, Pi.single_eq_of_ne]
  by_cases hpb : p = b
  · subst p
    simp [hab.symm, hbd, hab', hbd'.symm, unit, Pi.single_eq_of_ne]
  by_cases hpd : p = d
  · subst p
    simp [had.symm, hbd.symm, had', hbd', unit, Pi.single_eq_of_ne]
  have hpa' : (p : ℕ) ≠ a := fun h => hpa (Fin.ext h)
  have hpb' : (p : ℕ) ≠ b := fun h => hpb (Fin.ext h)
  have hpd' : (p : ℕ) ≠ d := fun h => hpd (Fin.ext h)
  simp [hpa, hpb, hpd, hpa'.symm, hpb'.symm, hpd'.symm, unit, Pi.single_eq_of_ne]

theorem sum_unit (i : Fin 23) : ∑ p, unit i p = 1 := by
  simp [unit]

theorem sum_of_triple {c a b d : Fin 23} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hc : c = a ∨ c = b ∨ c = d) :
    (∑ p, (unit a + unit b + unit d) p) = 3 * (unit a + unit b + unit d) c := by
  rcases hc with rfl | rfl | rfl <;>
    norm_num [Finset.sum_add_distrib, sum_unit, unit, Pi.single_eq_of_ne, hab, had, hbd,
      hab.symm, had.symm, hbd.symm]

theorem decode_spec {i : ℕ} {c : Fin 23} {r : Row} (h : decode c i = some r) :
    r.valid ∧ drop c (tvQ i) = r.vec ∧ (∑ p, tvQ i p) = 3 * tvQ i c := by
  unfold decode at h
  dsimp only at h
  split at h
  · rename_i hlt
    let a : Fin 23 := ⟨ptsL i 0, by omega⟩
    let b : Fin 23 := ⟨ptsL i 1, by omega⟩
    let d : Fin 23 := ⟨ptsL i 2, hlt.2.2⟩
    have hab : a ≠ b := by intro he; have := congrArg Fin.val he; exact (not_lt_of_ge (le_of_eq this.symm)) hlt.1
    have had : a ≠ d := by intro he; have := congrArg Fin.val he; exact (not_lt_of_ge (le_of_eq this.symm)) (hlt.1.trans hlt.2.1)
    have hbd : b ≠ d := by intro he; have := congrArg Fin.val he; exact (not_lt_of_ge (le_of_eq this.symm)) hlt.2.1
    have hv : tvQ i = unit a + unit b + unit d := triple_vec rfl rfl rfl hab had hbd
    rw [hv]
    change (if c = a then some (.two b d false) else if c = b then some (.two a d false)
      else if c = d then some (.two a b false) else none) = some r at h
    split at h
    · rename_i hc
      cases h
      exact ⟨hbd, by simp [Row.vec, hc, drop_unit, hab.symm, had.symm],
        sum_of_triple hab had hbd (Or.inl hc)⟩
    · split at h
      · rename_i hc
        cases h
        exact ⟨had, by simp [Row.vec, hc, drop_unit, hab, hbd.symm],
          sum_of_triple hab had hbd (Or.inr (Or.inl hc))⟩
      · split at h
        · rename_i hc
          cases h
          exact ⟨hab, by simp [Row.vec, hc, drop_unit, had, hbd],
            sum_of_triple hab had hbd (Or.inr (Or.inr hc))⟩
        · contradiction
  · contradiction

theorem rowsOf_spec {c : Fin 23} {is : List ℕ} {rs : List Row}
    (h : rowsOf c is = some rs) :
    ∀ r, r ∈ rs ↔ ∃ i ∈ is, decode c i = some r := by
  induction is generalizing rs with
  | nil =>
    simp [rowsOf] at h
    subst rs
    simp
  | cons i is ih =>
    cases hd : decode c i with
    | none => simp [rowsOf, hd] at h
    | some ri =>
      cases ht : rowsOf c is with
      | none => simp [rowsOf, hd, ht] at h
      | some rs' =>
        simp [rowsOf, hd, ht] at h
        subst rs
        intro r
        simp [hd, ih ht, eq_comm (a := ri)]

theorem rowsOf_covers {c : Fin 23} {is : List ℕ} {rs : List Row}
    (h : rowsOf c is = some rs) (i : ℕ) (hi : i ∈ is) :
    ∃ r, decode c i = some r := by
  induction is generalizing rs with
  | nil => simp at hi
  | cons j js ih =>
    cases hd : decode c j with
    | none => simp [rowsOf, hd] at h
    | some r =>
      cases ht : rowsOf c js with
      | none => simp [rowsOf, hd, ht] at h
      | some rs' =>
        rcases List.mem_cons.mp hi with rfl | hi
        · exact ⟨r, hd⟩
        · exact ih ht hi

theorem rows_dimension {sup : ℕ} {c : Fin 23} {rs : List Row} (hb : sup < 2 ^ 1771)
    (h : rowsOf c (bitIndices 1771 sup) = some rs) :
    rankRows rs = finrank ℚ (spanS sup) := by
  simp only [rankRows_eq (fun r hr => by
    obtain ⟨i, _, hi⟩ := (rowsOf_spec h r).mp hr
    exact (decode_spec hi).1)]
  have hv : ∀ v ∈ spanS sup, ∑ p, v p = 3 * v c := by
    intro v hm
    induction hm using Submodule.span_induction with
    | mem v hm =>
      obtain ⟨i, hi, rfl⟩ := hm
      obtain ⟨r, hr⟩ := rowsOf_covers h i ((mem_bitIndices (by decide) hb).mpr hi)
      exact (decode_spec hr).2.2
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, Finset.sum_add_distrib, hx, hy, mul_add]
    | smul a x _ hx =>
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx]
      ring
  rw [← dropped_dim _ _ hv, spanS, Submodule.map_span, spanRows]
  suffices he : {v : V | ∃ r ∈ rs, v = r.vec} =
      (drop c) '' {v : V | ∃ i, sup.testBit i = true ∧ v = tvQ i} by
    rw [he]
  ext v
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨i, hi, hd⟩ := (rowsOf_spec h r).mp hr
    exact ⟨tvQ i, ⟨i, (mem_bitIndices (by decide) hb).mp hi, rfl⟩, (decode_spec hd).2.1⟩
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    have hi' := (mem_bitIndices (by decide) hb).mpr hi
    obtain ⟨r, hd⟩ := rowsOf_covers h i hi'
    exact ⟨r, (rowsOf_spec h r).mpr ⟨i, hi', hd⟩, (decode_spec hd).2.1⟩

theorem nodeCheck_sound {n : ℕ} (hC : HasCentre (densSupG n))
    (h : nodeCheck n = true) :
    finrank ℚ (spanS (densSupG n)) = dimF n := by
  have hb : densSupG n < 2 ^ 1771 := by
    obtain ⟨_, _, hc⟩ := hC
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    cases he : (densSupG n).testBit i with
    | false => rfl
    | true => exact (not_lt_of_ge hi) (hc i he).1 |>.elim
  unfold nodeCheck at h
  split at h
  · rename_i hc
    split at h
    · contradiction
    · rename_i rs hr
      rw [← rows_dimension hb hr]
      exact Nat.beq_eq.mp h
  · contradiction

end IntMul.Kappa.R8.Bit.Oppbank.RankCheck

namespace IntMul.Kappa.R8.Bit.Oppbank.RankCheck

open Matrix Module Submodule Pnd SupG Cent CentStarBit

theorem triple_order : ∀ i : Fin 1771, ptsL i.val 0 < ptsL i.val 1 ∧
    ptsL i.val 1 < ptsL i.val 2 ∧ ptsL i.val 2 < 23 := by decide +kernel

theorem decode_exists {i : ℕ} (hi : i < 1771) {c : Fin 23}
    (hm : (triL i).testBit c.val = true) :
    ∃ r, decode c i = some r := by
  have h := triple_order ⟨i, hi⟩
  dsimp only at h
  simp only [triL, Nat.shiftLeft_eq', Nat.lor_eq, Nat.one_shiftLeft,
    Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hm
  unfold decode
  rw [dif_pos h]
  rcases hm with (hm | hm) | hm
  · have ha : c = ⟨ptsL i 0, by omega⟩ := Fin.ext hm.symm
    simp [ha]
  · have hb : c = ⟨ptsL i 1, by omega⟩ := Fin.ext hm.symm
    simp [hb, ne_of_gt h.1]
  · have hd : c = ⟨ptsL i 2, h.2.2⟩ := Fin.ext hm.symm
    simp [hd, ne_of_gt (h.1.trans h.2.1), ne_of_gt h.2.1]

theorem rowsOf_exists {c : Fin 23} {is : List ℕ}
    (h : ∀ i ∈ is, ∃ r, decode c i = some r) : ∃ rs, rowsOf c is = some rs := by
  induction is with
  | nil => exact ⟨[], rfl⟩
  | cons i is ih =>
    obtain ⟨r, hr⟩ := h i (by simp)
    obtain ⟨rs, hrs⟩ := ih (fun j hj => h j (by simp [hj]))
    exact ⟨r :: rs, by simp [rowsOf, hr, hrs]⟩

theorem star_mp {sup i : ℕ} {c : Fin 23} (hi : i < 1771)
    (ho : centredStar sup c.val = true) (hm : sup.testBit i = true) :
    (triL i).testBit c.val = true := by
  have he := centredStar_eq ho
  rw [Nat.land_eq] at he
  conv at hm => lhs; rw [← he]
  rw [Nat.testBit_land, Bool.and_eq_true] at hm
  rw [← starC_bit c.isLt ⟨i,hi⟩]
  exact hm.2

theorem span_eq_sum {sup : ℕ} {c : Fin 23} {rs : List Row} (hb : sup < 2 ^ 1771)
    (h : rowsOf c (bitIndices 1771 sup) = some rs) :
    ∀ v ∈ spanS sup, ∑ p, v p = 3 * v c := by
  intro v hm
  induction hm using Submodule.span_induction with
  | mem v hm =>
    obtain ⟨i, hi, rfl⟩ := hm
    obtain ⟨r, hr⟩ := rowsOf_covers h i ((mem_bitIndices (by decide) hb).mpr hi)
    exact (decode_spec hr).2.2
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, Finset.sum_add_distrib, hx, hy, mul_add]
  | smul a x _ hx =>
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx]
    ring

theorem absent_coord {sup : ℕ} {c p : Fin 23} (hpc : p ≠ c)
    (hp : p ∉ active sup c) (hb : sup < 2 ^ 1771) :
    ∀ v ∈ spanS sup, v p = 0 := by
  have hmask : sup &&& starC p.val = 0 := by
    by_contra! hne
    exact hp (by simp [active, hpc, hne])
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, hi, rfl⟩ := hv
    have hlt : i < 1771 := by
      by_contra! hge
      have hf := Nat.testBit_eq_false_of_lt
        (hb.trans_le (Nat.pow_le_pow_right (by decide) hge))
      rw [hf] at hi
      contradiction
    have ht := congrArg (Nat.testBit · i) hmask
    rw [Nat.testBit_land, hi, Bool.true_and, starC_bit p.isLt ⟨i,hlt⟩] at ht
    simp [tvQ, ht]
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => simp [hx]

theorem active_upper {sup : ℕ} {c : Fin 23} (hb : sup < 2 ^ 1771)
    (hs : ∀ v ∈ spanS sup, ∑ p, v p = 3 * v c) :
    finrank ℚ (spanS sup) ≤ (active sup c).length := by
  let t := (active sup c).toFinset
  let f : spanS sup →ₗ[ℚ] (↥t → ℚ) :=
    LinearMap.pi (fun p : ↥t => (LinearMap.proj p.val).comp (spanS sup).subtype)
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hz : ∀ p ≠ c, (v : V) p = 0 := by
      intro p hpc
      by_cases hm : p ∈ active sup c
      · let pp : ↥t := ⟨p, List.mem_toFinset.mpr hm⟩
        exact congrFun hv pp
      · exact absent_coord hpc hm hb v v.property
    have hsum : (∑ p, (v : V) p) = (v : V) c := by
      apply Finset.sum_eq_single c
      · intro p _ hpc
        exact hz p hpc
      · simp
    have hc := hs v v.property
    rw [hsum] at hc
    have hcv : (v : V) c = 0 := by linarith
    apply Subtype.ext
    funext p
    by_cases hp : p = c
    · simpa [hp] using hcv
    · exact hz p hp
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hdim
  have hnd : (active sup c).Nodup := (List.nodup_finRange 23).filter _
  change _ ≤ (active sup c).toFinset.card at hdim
  simpa only [List.toFinset_card_of_nodup hnd] using hdim

theorem mark_index {sup i : ℕ} (h : sup < 2 ^ 1771) (hi : sup.testBit i = true) : i < 1771 := by
  by_contra! hge
  have hf := Nat.testBit_eq_false_of_lt (h.trans_le (Nat.pow_le_pow_right (by decide) hge))
  rw [hf] at hi
  contradiction

theorem supported_rows {sup : ℕ} {c : Fin 23} (hb : sup < 2 ^ 1771)
    (hc : centredStar sup c.val = true) :
    ∃ rs, rowsOf c (bitIndices 1771 sup) = some rs := by
  apply rowsOf_exists
  intro i hi
  have ht := (mem_bitIndices (by decide) hb).mp hi
  have hilt := mark_index hb ht
  exact decode_exists hilt (star_mp hilt hc ht)

theorem supported_pair {i : ℕ} {c : Fin 23} (hi : i < 1771)
    (hc : (triL i).testBit c.val = true) :
    ∃ a b : Fin 23, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ drop c (tvQ i) = unit a + unit b := by
  have ho := triple_order ⟨i, hi⟩
  dsimp only at ho
  let a : Fin 23 := ⟨ptsL i 0, by omega⟩
  let b : Fin 23 := ⟨ptsL i 1, by omega⟩
  let d : Fin 23 := ⟨ptsL i 2, ho.2.2⟩
  have hab : a ≠ b := fun h => (ne_of_lt ho.1) (congrArg Fin.val h)
  have had : a ≠ d := fun h => (ne_of_lt (ho.1.trans ho.2.1)) (congrArg Fin.val h)
  have hbd : b ≠ d := fun h => (ne_of_lt ho.2.1) (congrArg Fin.val h)
  have hv : tvQ i = unit a + unit b + unit d := triple_vec rfl rfl rfl hab had hbd
  simp only [triL, Nat.shiftLeft_eq', Nat.lor_eq, Nat.one_shiftLeft,
    Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hc
  rcases hc with (hc | hc) | hc
  · have he : c = a := Fin.ext hc.symm
    exact ⟨b, d, hbd, he ▸ hab.symm, he ▸ had.symm, by
      simp [hv, he, drop_unit, hab.symm, had.symm]⟩
  · have he : c = b := Fin.ext hc.symm
    exact ⟨a, d, had, he ▸ hab, he ▸ hbd.symm, by
      simp [hv, he, drop_unit, hab, hbd.symm]⟩
  · have he : c = d := Fin.ext hc.symm
    exact ⟨a, b, hab, he ▸ had, he ▸ hbd, by simp [hv, he, drop_unit, had, hbd]⟩

theorem unit_pair_coord {a b p : Fin 23} (hne : a ≠ b) :
    (unit a + unit b) p = (if p = a ∨ p = b then 1 else 0) := by
  by_cases ha : p = a
  · subst p
    simp [unit, hne, Pi.single_eq_of_ne]
  by_cases hb : p = b
  · subst p
    simp [unit, hne.symm, Pi.single_eq_of_ne]
  · simp [unit, ha, hb, Pi.single_eq_of_ne]

theorem pair_mem_of_overlap {sup : ℕ} {c a p : Fin 23} (hb : sup < 2^1771)
    (hcent : centredStar sup c.val = true) (hac : a ≠ c) (hpc : p ≠ c) (hap : a ≠ p)
    (h : (sup &&& starC a.val &&& starC p.val) ≠ 0) :
    unit a + unit p ∈ (spanS sup).map (drop c) := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
  simp only [Nat.testBit_land, Bool.and_eq_true] at hi
  obtain ⟨⟨hi, ha⟩, hp⟩ := hi
  have hlt := mark_index hb hi
  have hac' : tvQ i a = 1 := by
    rw [starC_bit a.isLt ⟨i,hlt⟩] at ha
    simp [tvQ, ha]
  have hpc' : tvQ i p = 1 := by
    rw [starC_bit p.isLt ⟨i,hlt⟩] at hp
    simp [tvQ, hp]
  obtain ⟨x,y,hxy,_,_,hv⟩ := supported_pair hlt (star_mp hlt hcent hi)
  have hh : unit x + unit y = unit a + unit p := by
    have hx := congrFun hv a
    have hy := congrFun hv p
    rw [drop_apply, if_neg hac, hac', unit_pair_coord hxy] at hx
    rw [drop_apply, if_neg hpc, hpc', unit_pair_coord hxy] at hy
    have ex : a = x ∨ a = y := by by_contra! h; simp [h] at hx
    have ey : p = x ∨ p = y := by by_contra! h; simp [h] at hy
    rcases ex with rfl | rfl <;> rcases ey with rfl | rfl
    · exact (hap rfl).elim
    · rfl
    · ac_rfl
    · exact (hap rfl).elim
  exact Submodule.mem_map.mpr ⟨tvQ i, Submodule.subset_span ⟨i,hi,rfl⟩, hv.trans hh⟩

theorem active_ne_c {sup : ℕ} {c p : Fin 23} (hp : p ∈ active sup c) : p ≠ c := by
  have h := (List.mem_filter.mp hp).2
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  exact h.1

theorem hub_lower {sup : ℕ} {c a : Fin 23} (hb : sup < 2^1771)
    (hcent : centredStar sup c.val = true) (hs : ∀ v ∈ spanS sup, ∑ p, v p = 3 * v c)
    (ha : hub sup (active sup c) = some a) :
    (active sup c).length ≤ finrank ℚ (spanS sup) := by
  unfold hub at ha
  have hac := active_ne_c (List.mem_of_find?_eq_some ha)
  have htest := List.find?_some ha
  simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at htest
  have hnon : sup &&& starC a.val ≠ sup := htest.1
  have hex : ∃ i, sup.testBit i = true ∧ (starC a.val).testBit i = false := by
    by_contra! hh
    apply hnon
    apply Nat.eq_of_testBit_eq
    intro i
    cases he : sup.testBit i with
    | false => simp [he]
    | true =>
      have ht : (starC a.val).testBit i = true := by cases h : (starC a.val).testBit i <;> simp_all
      simp [he, ht]
  let W := (spanS sup).map (drop c)
  have hspoke : ∀ p ∈ active sup c, a ≠ p → unit a + unit p ∈ W := by
    intro p hp hne
    exact pair_mem_of_overlap hb hcent hac (active_ne_c hp) hne
      ((htest.2 p hp).resolve_left (Ne.symm hne))
  obtain ⟨i, hi, hn⟩ := hex
  have hit := mark_index hb hi
  obtain ⟨p,q,hpq,hpc,hqc,hvec⟩ := supported_pair hit (star_mp hit hcent hi)
  have hmem : tvQ i ∈ spanS sup := Submodule.subset_span ⟨i,hi,rfl⟩
  have hpqmem : unit p + unit q ∈ W := Submodule.mem_map.mpr ⟨tvQ i, hmem, hvec⟩
  have hpactive : p ∈ active sup c := by
    by_contra hout
    have z := absent_coord hpc hout hb _ hmem
    have hp := congrFun hvec p
    rw [drop_apply, if_neg hpc, z, unit_pair_coord hpq] at hp
    simp at hp
  have hqactive : q ∈ active sup c := by
    by_contra hout
    have z := absent_coord hqc hout hb _ hmem
    have hq := congrFun hvec q
    rw [drop_apply, if_neg hqc, z, unit_pair_coord hpq] at hq
    simp at hq
  have hz : tvQ i a = 0 := by
    rw [starC_bit a.isLt ⟨i,hit⟩] at hn
    simp [tvQ, hn]
  have hna : a ≠ p ∧ a ≠ q := by
    have hh := congrFun hvec a
    rw [drop_apply, if_neg hac, hz, unit_pair_coord hpq] at hh
    constructor
    · intro he
      simp [he] at hh
    · intro he
      simp [he] at hh
  have hunit : unit a ∈ W := by
    have step := W.smul_mem (1/2 : ℚ)
      (W.sub_mem (W.add_mem (hspoke p hpactive hna.1) (hspoke q hqactive hna.2)) hpqmem)
    convert step using 1 <;> module
  have hup : ∀ p ∈ active sup c, unit p ∈ W := by
    intro p hp
    rcases eq_or_ne a p with rfl | hn
    · exact hunit
    · simpa only [add_sub_cancel_left] using W.sub_mem (hspoke p hp hn) hunit
  let T := (active sup c).toFinset
  let ys : ↥T → V := fun p => unit p.val
  have hli : LinearIndependent ℚ ys := by
    have basis := (Pi.basisFun ℚ (Fin 23)).linearIndependent.comp (fun p : ↥T => p.val)
      Subtype.val_injective
    simpa [ys, Function.comp_def, unit, Pi.basisFun_apply] using basis
  have hle : Submodule.span ℚ (Set.range ys) ≤ W :=
    (Submodule.span_le.mpr (by rintro _ ⟨p,rfl⟩; exact hup p.val (List.mem_toFinset.mp p.property)))
  have hh := Submodule.finrank_mono hle
  have hnd : (active sup c).Nodup := (List.nodup_finRange 23).filter _
  rw [finrank_span_eq_card hli, Fintype.card_coe] at hh
  change (active sup c).toFinset.card ≤ finrank ℚ ((spanS sup).map (drop c)) at hh
  rwa [List.toFinset_card_of_nodup hnd, dropped_dim _ _ hs] at hh

theorem hubTest_sound {n : ℕ} (h : hubTest n (densSupG n) = true) :
    nodeCheck n = true := by
  unfold hubTest at h
  split at h
  · rename_i hc
    dsimp only at h
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨⟨⟨hb,hcent⟩,hcard⟩,a,ha⟩ := h
    have hbnd : densSupG n < 2^1771 := of_decide_eq_true hb
    have hd := eq_of_beq hcard
    let c : Fin 23 := ⟨centF n, hc⟩
    obtain ⟨rs, hrs⟩ := supported_rows (c := c) hbnd hcent
    have hs := span_eq_sum hbnd hrs
    have h1 := active_upper hbnd hs
    have h2 := hub_lower hbnd hcent hs ha
    unfold nodeCheck
    rw [dif_pos hc, hrs, Nat.beq_eq]
    exact (rows_dimension hbnd hrs).trans ((le_antisymm h1 h2).trans hd)
  · contradiction

theorem leafPart_pow {sup i : ℕ} {p : Fin 23} (h : (leafPart sup p).testBit i = true) :
    sup &&& starC p.val = 2 ^ i := by
  unfold leafPart at h
  dsimp only at h
  split at h
  · rename_i ht
    simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at ht
    obtain ⟨k,hk⟩ := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo ht.1).mp ht.2
    rw [hk, Nat.testBit_two_pow, decide_eq_true_eq] at h
    rwa [h] at hk
  · simp at h

theorem fold_cover {sup i : ℕ} {ps : List (Fin 23)}
    (h : (ps.foldr (fun p r => leafPart sup p ||| r) 0).testBit i = true) :
    ∃ p ∈ ps, (leafPart sup p).testBit i = true := by
  induction ps with
  | nil => simp at h
  | cons p ps ih =>
    simp only [List.foldr_cons, Nat.testBit_lor, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨p, by simp, h⟩
    · obtain ⟨q,hq,ht⟩ := ih h
      exact ⟨q, by simp [hq], ht⟩

theorem leaf_coord {sup i : ℕ} (hb : sup < 2 ^ 1771) (hcov : leafCover sup = sup)
    (hi : sup.testBit i = true) :
    ∃ p : Fin 23, tvQ i p = 1 ∧ ∀ j, sup.testBit j = true → j ≠ i → tvQ j p = 0 := by
  obtain ⟨p, _, hpart⟩ := fold_cover (show (leafCover sup).testBit i = true by rwa [hcov])
  have hpower := leafPart_pow hpart
  refine ⟨p, ?_, ?_⟩
  · have hlt := mark_index hb hi
    have ht := congrArg (Nat.testBit · i) hpower
    simp only [Nat.testBit_land, hi, Bool.true_and, Nat.testBit_two_pow_self,
      starC_bit p.isLt ⟨i,hlt⟩] at ht
    simp [tvQ, ht]
  · intro j hj hji
    have hlt := mark_index hb hj
    have ht := congrArg (Nat.testBit · j) hpower
    simp only [Nat.testBit_land, hj, Bool.true_and, Nat.testBit_two_pow_of_ne (Ne.symm hji),
      starC_bit p.isLt ⟨j,hlt⟩] at ht
    simp [tvQ, ht]

theorem leaf_dimension {sup : ℕ} (hb : sup < 2 ^ 1771) (hcover : leafCover sup = sup)
    (hnd : (bitIndices 1771 sup).Nodup) :
    finrank ℚ (spanS sup) = (bitIndices 1771 sup).length := by
  let T := (bitIndices 1771 sup).toFinset
  let y : ↥T → V := fun i => tvQ i.val
  have hbits : ∀ i : ↥T, sup.testBit i.val = true := fun i =>
    (mem_bitIndices (by decide) hb).mp (List.mem_toFinset.mp i.property)
  have hli : LinearIndependent ℚ y := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    obtain ⟨p,h1,h0⟩ := leaf_coord hb hcover (hbits j)
    have hz := congrFun hg p
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hz
    rw [Finset.sum_eq_single j] at hz
    · simpa [y, h1] using hz
    · intro i _ hn
      have hne : i.val ≠ j.val := fun h => hn (Subtype.ext h)
      simp [y, h0 i.val (hbits i) hne]
    · simp
  have hspan : spanS sup = span ℚ (Set.range y) := by
    unfold spanS
    congr 1
    ext v
    constructor
    · rintro ⟨i, hi, rfl⟩
      let ii : ↥T := ⟨i, List.mem_toFinset.mpr ((mem_bitIndices (by decide) hb).mpr hi)⟩
      exact ⟨ii,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,hbits i,rfl⟩
  rw [hspan, finrank_span_eq_card hli, Fintype.card_coe]
  exact List.toFinset_card_of_nodup hnd

theorem leafTest_sound {n : ℕ} (h : leafTest n (densSupG n) = true) :
    nodeCheck n = true := by
  unfold leafTest at h
  split at h
  · rename_i hc
    dsimp only at h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hbnd,hcent⟩,hcover⟩,hlen,hnd⟩ := h
    let c : Fin 23 := ⟨centF n, hc⟩
    obtain ⟨rs, hrs⟩ := supported_rows (c := c) hbnd hcent
    unfold nodeCheck
    rw [dif_pos hc, hrs, Nat.beq_eq, rows_dimension hbnd hrs]
    exact (leaf_dimension hbnd hcover hnd).trans hlen
  · contradiction

end IntMul.Kappa.R8.Bit.Oppbank.RankCheck

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck in
private theorem checked_nodeFast_sound {n : ℕ} (h : nodeFast n = true) : nodeCheck n = true := by
  simp only [nodeFast, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact hubTest_sound h
  · exact leafTest_sound h
  · exact h

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

set_option maxHeartbeats 0
set_option Elab.async false

private theorem checked22528 : pass nodeFast 22528 128 = true := by decide +kernel

private theorem checked22656 : pass nodeFast 22656 128 = true := by decide +kernel

private theorem checked22784 : pass nodeFast 22784 128 = true := by decide +kernel

private theorem checked22912 : pass nodeFast 22912 128 = true := by decide +kernel

private theorem checked23040 : pass nodeFast 23040 128 = true := by decide +kernel

private theorem checked23168 : pass nodeFast 23168 128 = true := by decide +kernel

private theorem checked23296 : pass nodeFast 23296 128 = true := by decide +kernel

private theorem checked23424 : pass nodeFast 23424 128 = true := by decide +kernel

private theorem checked23552 : pass nodeFast 23552 128 = true := by decide +kernel

private theorem checked23680 : pass nodeFast 23680 128 = true := by decide +kernel

private theorem checked23808 : pass nodeFast 23808 128 = true := by decide +kernel

private theorem checked23936 : pass nodeFast 23936 128 = true := by decide +kernel

private theorem checked24064 : pass nodeFast 24064 128 = true := by decide +kernel

private theorem checked24192 : pass nodeFast 24192 128 = true := by decide +kernel

private theorem checked24320 : pass nodeFast 24320 128 = true := by decide +kernel

private theorem checked24448 : pass nodeFast 24448 128 = true := by decide +kernel


private theorem in_checked_range {a w n : ℕ} (h : pass nodeFast a w = true)
    (hlo : a ≤ n) (hhi : n < a + w) : nodeCheck n = true := by
  have hm : n - a ∈ List.range w := List.mem_range.mpr (by omega)
  have hh := List.all_eq_true.mp h _ hm
  exact checked_nodeFast_sound (by simpa only [Nat.add_sub_of_le hlo] using hh)

theorem solution : ∀ n : ℕ, 22528 ≤ n → n < 24576 → nodeCheck n = true := by
  intro n hlo hhi

  by_cases h22528 : n < 22656
  · exact in_checked_range checked22528 (by omega) (by omega)

  by_cases h22656 : n < 22784
  · exact in_checked_range checked22656 (by omega) (by omega)

  by_cases h22784 : n < 22912
  · exact in_checked_range checked22784 (by omega) (by omega)

  by_cases h22912 : n < 23040
  · exact in_checked_range checked22912 (by omega) (by omega)

  by_cases h23040 : n < 23168
  · exact in_checked_range checked23040 (by omega) (by omega)

  by_cases h23168 : n < 23296
  · exact in_checked_range checked23168 (by omega) (by omega)

  by_cases h23296 : n < 23424
  · exact in_checked_range checked23296 (by omega) (by omega)

  by_cases h23424 : n < 23552
  · exact in_checked_range checked23424 (by omega) (by omega)

  by_cases h23552 : n < 23680
  · exact in_checked_range checked23552 (by omega) (by omega)

  by_cases h23680 : n < 23808
  · exact in_checked_range checked23680 (by omega) (by omega)

  by_cases h23808 : n < 23936
  · exact in_checked_range checked23808 (by omega) (by omega)

  by_cases h23936 : n < 24064
  · exact in_checked_range checked23936 (by omega) (by omega)

  by_cases h24064 : n < 24192
  · exact in_checked_range checked24064 (by omega) (by omega)

  by_cases h24192 : n < 24320
  · exact in_checked_range checked24192 (by omega) (by omega)

  by_cases h24320 : n < 24448
  · exact in_checked_range checked24320 (by omega) (by omega)

  exact in_checked_range checked24448 (by omega) (by omega)
