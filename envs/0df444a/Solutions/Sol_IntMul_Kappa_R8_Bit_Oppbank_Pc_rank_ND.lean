-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T06:52:33.910909+00:00
-- url     : https://prove2.me/submissions/b4e353f8-e217-4bc6-98f2-610cdd4f8548
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck

import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock00000
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock02048
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock04096
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock06144
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock08192
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock10240
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock12288
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock14336
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock16384
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock18432
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock20480
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock22528
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock24576
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock26624
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock28672
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock30720
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock32768
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock34816
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock36864
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock38912
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock40960
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock43008
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock45056
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock47104
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock49152
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock51200
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock53248
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock55296
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock57344
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock59392
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock61440
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

open IntMul.Kappa.R8.Bit.Oppbank IntMul.Kappa.R8.Bit.Oppbank.Pnd IntMul.Kappa.R8.Bit.Oppbank.SupG IntMul.Kappa.R8.Bit.Oppbank.RankCheck Matrix in
theorem solution {n : ℕ} (hn : 1773 + n < codeBound)
    (hC : HasCentre (densSupG n)) :
    (Pc (1773 + n)).rank = dimF n := by
  have hn' : n < 62478 := by
    rw [codeBound_eq, nNodes_eq] at hn
    omega
  have htable : nodeCheck n = true := by
    by_cases h2048 : n < 2048
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock00000 n (by omega) h2048
    by_cases h4096 : n < 4096
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock02048 n (by omega) h4096
    by_cases h6144 : n < 6144
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock04096 n (by omega) h6144
    by_cases h8192 : n < 8192
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock06144 n (by omega) h8192
    by_cases h10240 : n < 10240
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock08192 n (by omega) h10240
    by_cases h12288 : n < 12288
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock10240 n (by omega) h12288
    by_cases h14336 : n < 14336
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock12288 n (by omega) h14336
    by_cases h16384 : n < 16384
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock14336 n (by omega) h16384
    by_cases h18432 : n < 18432
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock16384 n (by omega) h18432
    by_cases h20480 : n < 20480
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock18432 n (by omega) h20480
    by_cases h22528 : n < 22528
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock20480 n (by omega) h22528
    by_cases h24576 : n < 24576
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock22528 n (by omega) h24576
    by_cases h26624 : n < 26624
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock24576 n (by omega) h26624
    by_cases h28672 : n < 28672
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock26624 n (by omega) h28672
    by_cases h30720 : n < 30720
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock28672 n (by omega) h30720
    by_cases h32768 : n < 32768
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock30720 n (by omega) h32768
    by_cases h34816 : n < 34816
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock32768 n (by omega) h34816
    by_cases h36864 : n < 36864
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock34816 n (by omega) h36864
    by_cases h38912 : n < 38912
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock36864 n (by omega) h38912
    by_cases h40960 : n < 40960
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock38912 n (by omega) h40960
    by_cases h43008 : n < 43008
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock40960 n (by omega) h43008
    by_cases h45056 : n < 45056
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock43008 n (by omega) h45056
    by_cases h47104 : n < 47104
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock45056 n (by omega) h47104
    by_cases h49152 : n < 49152
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock47104 n (by omega) h49152
    by_cases h51200 : n < 51200
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock49152 n (by omega) h51200
    by_cases h53248 : n < 53248
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock51200 n (by omega) h53248
    by_cases h55296 : n < 55296
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock53248 n (by omega) h55296
    by_cases h57344 : n < 57344
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock55296 n (by omega) h57344
    by_cases h59392 : n < 59392
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock57344 n (by omega) h59392
    by_cases h61440 : n < 61440
    · exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock59392 n (by omega) h61440
    exact IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock61440 n (by omega) hn'
  rw [Pc_of_ND n hn]
  unfold PndD Pnd
  rw [dif_pos hC]
  unfold prjM Matrix.rank
  rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix', Submodule.range_projection]
  exact nodeCheck_sound hC htable
