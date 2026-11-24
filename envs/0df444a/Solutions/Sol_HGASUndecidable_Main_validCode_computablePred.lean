-- Prove2me | solution 1 for HGASUndecidable.Main.validCode_computablePred
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:12:11.521288+00:00
-- url     : https://prove2.me/submissions/3fc0e170-f78f-4cc2-89d9-eb78d03d44d1

import Definitions.Def_HGASUndecidable_Main_PaddingCodes

open Encodable Denumerable Primrec

/-! ## Primitive recursive gcd -/

theorem Primrec.nat_gcd' : Primrec₂ Nat.gcd := by
  show Primrec fun p : ℕ × ℕ => Nat.gcd p.1 p.2
  have hdvd : PrimrecRel fun (k m : ℕ) => m % k = 0 :=
    Primrec.eq.comp (nat_mod.comp snd fst) (const 0)
  have hR : PrimrecRel fun (k : ℕ) (pg : (ℕ × ℕ) × ℕ) =>
      ¬(pg.1.1 % k = 0 ∧ pg.1.2 % k = 0) ∨ pg.2 % k = 0 :=
    PrimrecPred.or
      (PrimrecPred.not (PrimrecPred.and (hdvd.comp fst (fst.comp (fst.comp snd)))
        (hdvd.comp fst (snd.comp (fst.comp snd)))))
      (hdvd.comp fst (snd.comp snd))
  have hR' := PrimrecRel.forall_mem_list hR
  have hall' : PrimrecPred fun pg : (ℕ × ℕ) × ℕ => ∀ k ∈ List.range (Nat.succ (pg.1.1 + pg.1.2)),
      ¬(pg.1.1 % k = 0 ∧ pg.1.2 % k = 0) ∨ pg.2 % k = 0 := hR'.comp (g := fun pg => pg)
    (list_range.comp (Primrec.succ.comp (nat_add.comp (fst.comp fst) (snd.comp fst)))) Primrec.id
  have hall : PrimrecPred fun pg : (ℕ × ℕ) × ℕ => ∀ k < Nat.succ (pg.1.1 + pg.1.2),
      ¬(pg.1.1 % k = 0 ∧ pg.1.2 % k = 0) ∨ pg.2 % k = 0 :=
    hall'.of_eq fun pg => by simp only [List.mem_range]
  have hgraph : PrimrecRel fun (p : ℕ × ℕ) (g : ℕ) =>
      p.1 % g = 0 ∧ p.2 % g = 0 ∧
        ∀ k < Nat.succ (p.1 + p.2), ¬(p.1 % k = 0 ∧ p.2 % k = 0) ∨ g % k = 0 :=
    PrimrecPred.and (hdvd.comp snd (fst.comp fst))
      (PrimrecPred.and (hdvd.comp snd (snd.comp fst)) hall)
  have hle : ∀ a b : ℕ, Nat.gcd a b ≤ a + b := by
    intro a b
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · exact (Nat.gcd_le_left b ha).trans (Nat.le_add_right _ _)
  refine Primrec.of_graph ⟨fun p => p.1 + p.2, nat_add.comp fst snd, fun p => ?_⟩
    (PrimrecRel.of_eq hgraph ?_)
  · simpa using hle p.1 p.2
  · rintro ⟨a, b⟩ g
    simp only
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hg1 : g ∣ a := Nat.dvd_of_mod_eq_zero h1
      have hg2 : g ∣ b := Nat.dvd_of_mod_eq_zero h2
      have hlt : Nat.gcd a b < Nat.succ (a + b) := Nat.lt_succ_of_le (hle a b)
      rcases h3 _ hlt with h | h
      · exact absurd ⟨Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left a b),
          Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right a b)⟩ h
      · exact Nat.dvd_antisymm (Nat.dvd_of_mod_eq_zero h) (Nat.dvd_gcd hg1 hg2)
    · rintro rfl
      refine ⟨Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left a b),
        Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right a b), fun k _ => ?_⟩
      by_cases h : a % k = 0 ∧ b % k = 0
      · exact Or.inr (Nat.mod_eq_zero_of_dvd
          (Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h.1) (Nat.dvd_of_mod_eq_zero h.2)))
      · exact Or.inl h

/-! ## Primitive recursive arithmetic on `ℚ` (Mathlib's `Denumerable ℚ` coding) -/

namespace RatPrimrec

/-- The encoding of `ℚ` from `Mathlib.Data.Rat.Encodable`. -/
def rawEncode (q : ℚ) : ℕ := @Encodable.encode ℚ Rat.instEncodable q

theorem rawEncode_eq (q : ℚ) : rawEncode q = Nat.pair (Equiv.intEquivNat q.num) q.den := rfl

theorem intEquivNat_ofNat (m : ℕ) : Equiv.intEquivNat (Int.ofNat m) = Nat.bit false m := rfl

theorem intEquivNat_negSucc (m : ℕ) : Equiv.intEquivNat (Int.negSucc m) = Nat.bit true m := rfl

theorem intEquivNat_natCast (m : ℕ) : Equiv.intEquivNat (m : ℤ) = Nat.bit false m := rfl

/-- Positive part of the integer with code `a`. -/
def posOf (a : ℕ) : ℕ := cond a.bodd 0 a.div2

/-- Negative part of the integer with code `a`. -/
def negOf (a : ℕ) : ℕ := cond a.bodd (a.div2 + 1) 0

theorem posOf_code (z : ℤ) : posOf (Equiv.intEquivNat z) = z.toNat := by
  cases z with
  | ofNat m =>
    rw [intEquivNat_ofNat]
    simp [posOf, Nat.bodd_bit, Nat.div2_bit]
  | negSucc m => simp [posOf, intEquivNat_negSucc]

theorem negOf_code (z : ℤ) : negOf (Equiv.intEquivNat z) = (-z).toNat := by
  cases z with
  | ofNat m =>
    rw [intEquivNat_ofNat]
    simp only [negOf, Nat.bodd_bit, cond_false]
    try simp only [Int.ofNat_eq_natCast]
    omega
  | negSucc m => simp [negOf, intEquivNat_negSucc]

theorem natAbs_code (z : ℤ) :
    z.natAbs = posOf (Equiv.intEquivNat z) + negOf (Equiv.intEquivNat z) := by
  rw [posOf_code, negOf_code]; omega

theorem primrec_posOf : Primrec posOf := cond nat_bodd (const 0) nat_div2

theorem primrec_negOf : Primrec negOf := cond nat_bodd (Primrec.succ.comp nat_div2) (const 0)

/-- The image of `rawEncode`. -/
def MemR (y : ℕ) : Prop :=
  0 < y.unpair.2 ∧ Nat.gcd (posOf y.unpair.1 + negOf y.unpair.1) y.unpair.2 = 1

instance : DecidablePred MemR := fun y => by unfold MemR; infer_instance

theorem memR_iff (y : ℕ) : y ∈ Set.range rawEncode ↔ MemR y := by
  constructor
  · rintro ⟨q, rfl⟩
    rw [rawEncode_eq]
    simp only [MemR, Nat.unpair_pair, ← natAbs_code]
    exact ⟨q.den_pos, q.reduced⟩
  · rintro ⟨hd, hc⟩
    have hcode : Equiv.intEquivNat (Equiv.intEquivNat.symm y.unpair.1) = y.unpair.1 := by simp
    refine ⟨⟨Equiv.intEquivNat.symm y.unpair.1, y.unpair.2, by omega, ?_⟩, ?_⟩
    · show Nat.gcd _ _ = 1
      rw [natAbs_code, hcode]; exact hc
    · show Nat.pair (Equiv.intEquivNat (Equiv.intEquivNat.symm y.unpair.1)) y.unpair.2 = y
      rw [hcode]; exact Nat.pair_unpair y

theorem primrec_memR : PrimrecPred MemR :=
  PrimrecPred.and (nat_lt.comp (const 0) (snd.comp unpair))
    (Primrec.eq.comp (Primrec.nat_gcd'.comp
      (nat_add.comp (primrec_posOf.comp (fst.comp unpair)) (primrec_negOf.comp (fst.comp unpair)))
      (snd.comp unpair)) (const 1))

/-- Number of codes of rationals below `y`. -/
def cntR (y : ℕ) : ℕ := ((List.range y).filter fun x => decide (MemR x)).length

theorem primrec_cntR : Primrec cntR :=
  list_length.comp ((listFilter primrec_memR).comp list_range)

theorem cntR_le (y : ℕ) : cntR y ≤ y :=
  (List.length_filter_le _ _).trans (by simp)

/-- The `Denumerable ℚ` code of `q` counts the raw codes below the raw code of `q`. -/
theorem encode_eq_cntR (q : ℚ) :
    @Encodable.encode ℚ Denumerable.toEncodable q = cntR (rawEncode q) := by
  change List.countP _ (List.range (rawEncode q)) = _
  rw [List.countP_eq_length_filter]
  unfold cntR
  congr 1
  apply List.filter_congr
  intro x _
  exact decide_eq_decide.mpr (memR_iff x)

theorem ofNat_spec (n y : ℕ) :
    rawEncode (Denumerable.ofNat ℚ n) = y ↔ MemR y ∧ cntR y = n := by
  constructor
  · rintro rfl
    refine ⟨(memR_iff _).1 ⟨_, rfl⟩, ?_⟩
    rw [← encode_eq_cntR, Denumerable.encode_ofNat]
  · rintro ⟨hm, hc⟩
    obtain ⟨q, rfl⟩ := (memR_iff y).2 hm
    rw [← encode_eq_cntR] at hc
    rw [← hc, Denumerable.ofNat_encode]

theorem memR_pair_one (a : ℕ) : MemR (Nat.pair a 1) := by
  simp [MemR, Nat.unpair_pair]

theorem ofNat_le (n : ℕ) : rawEncode (Denumerable.ofNat ℚ n) ≤ Nat.pair n 1 := by
  by_contra hlt
  rw [not_le] at hlt
  have hy := (ofNat_spec n _).1 rfl
  have hsub : ((List.range (n+1)).map fun a => Nat.pair a 1) ⊆
      (List.range (rawEncode (Denumerable.ofNat ℚ n))).filter fun x => decide (MemR x) := by
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    refine ⟨lt_of_le_of_lt ?_ hlt, memR_pair_one a⟩
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ha) with h | h
    · exact (Nat.pair_lt_pair_left 1 h).le
    · rw [h]
  have hnd : ((List.range (n+1)).map fun a => Nat.pair a 1).Nodup := by
    refine List.nodup_range.map ?_
    intro a b h
    exact (Nat.pair_eq_pair.mp h).1
  have hlen := (hnd.subperm hsub).length_le
  simp only [List.length_map, List.length_range] at hlen
  have h2 := hy.2
  unfold cntR at h2
  omega

theorem primrec_ofNat_raw : Primrec fun n : ℕ => rawEncode (Denumerable.ofNat ℚ n) := by
  refine Primrec.of_graph ⟨fun n => Nat.pair n 1, Primrec₂.natPair.comp Primrec.id (const 1),
    fun n => by simpa using ofNat_le n⟩ ?_
  exact PrimrecRel.of_eq (r := fun n y => MemR y ∧ cntR y = n)
    (PrimrecPred.and (primrec_memR.comp snd) (Primrec.eq.comp (primrec_cntR.comp snd) fst))
    fun n y => (ofNat_spec n y).symm

/-- Mathlib's raw `ℚ` encoding is primitive recursive with respect to the `Primcodable ℚ`
structure. -/
theorem primrec_rawEncode : Primrec rawEncode :=
  Primrec.ofNat_iff.2 primrec_ofNat_raw

theorem _root_.Primrec.rat_den : Primrec Rat.den :=
  (snd.comp (unpair.comp primrec_rawEncode)).of_eq fun q => by
    rw [rawEncode_eq, Nat.unpair_pair]

theorem _root_.Primrec.rat_num : Primrec Rat.num :=
  Primrec.encode_iff.1 <| (fst.comp (unpair.comp primrec_rawEncode)).of_eq fun q => by
    rw [rawEncode_eq, Nat.unpair_pair]; rfl

/-- Sign-split representation `(q.num⁺, q.num⁻, q.den)`. -/
def triple (q : ℚ) : ℕ × ℕ × ℕ := (q.num.toNat, (-q.num).toNat, q.den)

theorem primrec_triple : Primrec triple := by
  refine (Primrec.pair (primrec_posOf.comp (fst.comp (unpair.comp primrec_rawEncode)))
    (Primrec.pair (primrec_negOf.comp (fst.comp (unpair.comp primrec_rawEncode)))
      (snd.comp (unpair.comp primrec_rawEncode)))).of_eq fun q => ?_
  simp only [rawEncode_eq, Nat.unpair_pair, posOf_code, negOf_code, triple]

/-- The rational `(p - n) / d`. -/
def ofSigned (x : ℕ × ℕ × ℕ) : ℚ := ((x.1 : ℚ) - x.2.1) / x.2.2

theorem ofSigned_triple (q : ℚ) : ofSigned (triple q) = q := by
  simp only [ofSigned, triple]
  have h1 : ((q.num.toNat : ℚ) - ((-q.num).toNat : ℚ)) = (q.num : ℚ) := by
    have := Int.toNat_sub_toNat_neg q.num
    exact_mod_cast this
  rw [h1]; exact Rat.num_div_den q

/-- Cross-multiplication test for `ofSigned x = ofSigned y` (when `y.2.2 > 0`). -/
def SameRel (x y : ℕ × ℕ × ℕ) : Prop :=
  (x.2.2 = 0 ∧ y.1 = y.2.1) ∨
    (0 < x.2.2 ∧ x.1 * y.2.2 + y.2.1 * x.2.2 = y.1 * x.2.2 + x.2.1 * y.2.2)

instance : DecidableRel SameRel := fun x y => by unfold SameRel; infer_instance

theorem ofSigned_eq_iff (x y : ℕ × ℕ × ℕ) (hy : 0 < y.2.2) :
    ofSigned x = ofSigned y ↔ SameRel x y := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨p, n, d⟩ := y
  simp only [ofSigned, SameRel] at *
  have hd : (d : ℚ) ≠ 0 := by positivity
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp only [Nat.cast_zero, div_zero, lt_irrefl, false_and, or_false, true_and]
    rw [eq_comm, div_eq_zero_iff, or_iff_left hd, sub_eq_zero, Nat.cast_inj]
  · have hc' : (c : ℚ) ≠ 0 := by positivity
    rw [div_eq_div_iff hc' hd]
    simp only [hc.ne', false_and, false_or, hc, true_and]
    constructor
    · intro h
      have h' : (a : ℚ) * d + n * c = p * c + b * d := by linear_combination h
      exact_mod_cast h'
    · intro h
      have h' : (a : ℚ) * d + n * c = p * c + b * d := by exact_mod_cast h
      linear_combination h'

theorem primrec_sameRel : PrimrecRel SameRel :=
  PrimrecPred.or
    (PrimrecPred.and (Primrec.eq.comp (snd.comp (snd.comp fst)) (const 0))
      (Primrec.eq.comp (fst.comp snd) (fst.comp (snd.comp snd))))
    (PrimrecPred.and (nat_lt.comp (const 0) (snd.comp (snd.comp fst)))
      (Primrec.eq.comp
        (nat_add.comp (nat_mul.comp (fst.comp fst) (snd.comp (snd.comp snd)))
          (nat_mul.comp (fst.comp (snd.comp snd)) (snd.comp (snd.comp fst))))
        (nat_add.comp (nat_mul.comp (fst.comp snd) (snd.comp (snd.comp fst)))
          (nat_mul.comp (fst.comp (snd.comp fst)) (snd.comp (snd.comp snd))))))

theorem pair_le_sq (a b : ℕ) : Nat.pair a b ≤ (a + b + 1) ^ 2 := by
  unfold Nat.pair
  split_ifs <;> nlinarith

theorem code_le (z : ℤ) : Equiv.intEquivNat z ≤ 2 * z.natAbs + 1 := by
  cases z with
  | ofNat m => rw [intEquivNat_ofNat, Nat.bit_val]; simp
  | negSucc m => rw [intEquivNat_negSucc, Nat.bit_val]; simp

theorem ofSigned_bounds (x : ℕ × ℕ × ℕ) :
    (ofSigned x).num.natAbs ≤ x.1 + x.2.1 ∧ (ofSigned x).den ≤ x.2.2 + 1 := by
  obtain ⟨a, b, c⟩ := x
  simp only [ofSigned]
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  · have hq : ((a : ℚ) - b) / c = Rat.divInt ((a : ℤ) - b) (c : ℤ) := by
      rw [← Rat.intCast_div_eq_divInt]; push_cast; rfl
    rw [hq]
    have hc0 : (c : ℤ) ≠ 0 := by omega
    constructor
    · by_cases hz : (a : ℤ) - b = 0
      · rw [hz]; simp
      · have h1 := Rat.num_dvd ((a : ℤ) - b) hc0
        have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hz) (Int.natAbs_dvd_natAbs.mpr h1)
        omega
    · have h1 := Rat.den_dvd ((a : ℤ) - b) (c : ℤ)
      have h2 := Int.le_of_dvd (by omega) h1
      omega

theorem encode_ofSigned_le (x : ℕ × ℕ × ℕ) :
    @Encodable.encode ℚ Denumerable.toEncodable (ofSigned x) ≤
      (2 * (x.1 + x.2.1) + x.2.2 + 3) ^ 2 := by
  rw [encode_eq_cntR]
  refine (cntR_le _).trans ?_
  rw [rawEncode_eq]
  refine (pair_le_sq _ _).trans (Nat.pow_le_pow_left ?_ 2)
  have h1 := code_le (ofSigned x).num
  have h2 := ofSigned_bounds x
  omega

theorem primrec_ofSigned : Primrec ofSigned := by
  refine Primrec.encode_iff.1 (Primrec.of_graph ⟨fun x => (2 * (x.1 + x.2.1) + x.2.2 + 3) ^ 2,
    ?_, fun x => by simpa using encode_ofSigned_le x⟩ ?_)
  · exact (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp
      (nat_add.comp (nat_add.comp (nat_mul.comp (const 2) (nat_add.comp fst (fst.comp snd)))
        (snd.comp snd)) (const 3)) (const 2)
  · refine PrimrecRel.of_eq (r := fun x k => SameRel x (triple (Denumerable.ofNat ℚ k)))
      (primrec_sameRel.comp fst (primrec_triple.comp ((Primrec.ofNat ℚ).comp snd))) ?_
    intro x k
    rw [← ofSigned_eq_iff _ _ (Rat.den_pos _), ofSigned_triple]
    constructor
    · intro h; rw [h]; exact Denumerable.encode_ofNat k
    · intro h; rw [← h]; exact (Denumerable.ofNat_encode _).symm

def addT (x y : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (x.1 * y.2.2 + y.1 * x.2.2, x.2.1 * y.2.2 + y.2.1 * x.2.2, x.2.2 * y.2.2)

def mulT (x y : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (x.1 * y.1 + x.2.1 * y.2.1, x.1 * y.2.1 + x.2.1 * y.1, x.2.2 * y.2.2)

def negT (x : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (x.2.1, x.1, x.2.2)

theorem primrec_addT : Primrec₂ addT :=
  Primrec.pair
    (nat_add.comp (nat_mul.comp (fst.comp fst) (snd.comp (snd.comp snd)))
      (nat_mul.comp (fst.comp snd) (snd.comp (snd.comp fst))))
    (Primrec.pair
      (nat_add.comp (nat_mul.comp (fst.comp (snd.comp fst)) (snd.comp (snd.comp snd)))
        (nat_mul.comp (fst.comp (snd.comp snd)) (snd.comp (snd.comp fst))))
      (nat_mul.comp (snd.comp (snd.comp fst)) (snd.comp (snd.comp snd))))

theorem primrec_mulT : Primrec₂ mulT :=
  Primrec.pair
    (nat_add.comp (nat_mul.comp (fst.comp fst) (fst.comp snd))
      (nat_mul.comp (fst.comp (snd.comp fst)) (fst.comp (snd.comp snd))))
    (Primrec.pair
      (nat_add.comp (nat_mul.comp (fst.comp fst) (fst.comp (snd.comp snd)))
        (nat_mul.comp (fst.comp (snd.comp fst)) (fst.comp snd)))
      (nat_mul.comp (snd.comp (snd.comp fst)) (snd.comp (snd.comp snd))))

theorem primrec_negT : Primrec negT :=
  Primrec.pair (fst.comp snd) (Primrec.pair fst (snd.comp snd))

theorem add_eq (q r : ℚ) : q + r = ofSigned (addT (triple q) (triple r)) := by
  conv_lhs => rw [← ofSigned_triple q, ← ofSigned_triple r]
  have hq : (q.den : ℚ) ≠ 0 := by have := q.den_pos; positivity
  have hr : (r.den : ℚ) ≠ 0 := by have := r.den_pos; positivity
  simp only [ofSigned, addT, triple]
  push_cast
  field_simp
  ring

theorem mul_eq (q r : ℚ) : q * r = ofSigned (mulT (triple q) (triple r)) := by
  conv_lhs => rw [← ofSigned_triple q, ← ofSigned_triple r]
  simp only [ofSigned, mulT, triple]
  push_cast
  rw [div_mul_div_comm]
  congr 1
  ring

theorem neg_eq (q : ℚ) : -q = ofSigned (negT (triple q)) := by
  conv_lhs => rw [← ofSigned_triple q]
  simp only [ofSigned, negT, triple]
  rw [← neg_div, neg_sub]

theorem _root_.Primrec.rat_add : Primrec₂ ((· + ·) : ℚ → ℚ → ℚ) :=
  Primrec₂.of_eq (primrec_ofSigned.comp₂ (primrec_addT.comp₂
    (primrec_triple.comp₂ Primrec₂.left) (primrec_triple.comp₂ Primrec₂.right)))
    fun q r => (add_eq q r).symm

theorem _root_.Primrec.rat_mul : Primrec₂ ((· * ·) : ℚ → ℚ → ℚ) :=
  Primrec₂.of_eq (primrec_ofSigned.comp₂ (primrec_mulT.comp₂
    (primrec_triple.comp₂ Primrec₂.left) (primrec_triple.comp₂ Primrec₂.right)))
    fun q r => (mul_eq q r).symm

theorem _root_.Primrec.rat_neg : Primrec (fun q : ℚ => -q) :=
  (primrec_ofSigned.comp (primrec_negT.comp primrec_triple)).of_eq fun q => (neg_eq q).symm

theorem _root_.Primrec.rat_sub : Primrec₂ ((· - ·) : ℚ → ℚ → ℚ) :=
  Primrec₂.of_eq (Primrec.rat_add.comp₂ Primrec₂.left (Primrec.rat_neg.comp₂ Primrec₂.right))
    fun q r => (sub_eq_add_neg q r).symm

theorem _root_.Primrec.rat_list_sum : Primrec (List.sum : List ℚ → ℚ) :=
  (list_foldr Primrec.id (const 0)
    (Primrec.rat_add.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq fun l => by
      show List.foldr (fun b s => b + s) 0 l = l.sum
      induction l with
      | nil => rfl
      | cons a l ih => simp only [List.foldr_cons, List.sum_cons, ih]

end RatPrimrec

theorem Primrec.nat_list_sum' : Primrec (List.sum : List ℕ → ℕ) :=
  (list_foldr Primrec.id (const 0)
    (nat_add.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq fun l => by
      show List.foldr (fun b s => b + s) 0 l = l.sum
      induction l with
      | nil => rfl
      | cons a l ih => simp only [List.foldr_cons, List.sum_cons, ih]

/-! ## The code-validity checker -/

namespace HGASUndecidable.Main.ValidCodeAux

open MvPolynomial

/-- The exponent vector encoded by a list (missing entries are `0`). -/
noncomputable def expOf (n : ℕ) (l : List ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j : Fin n => l[j.val]?.getD 0)

/-- Total coefficient of the monomial `e` in coordinate `i`. -/
def coeffSum (L : List (ℕ × List ℕ × ℚ)) (i : ℕ) (e : List ℕ) : ℚ :=
  (L.map fun t => if t.1 = i ∧ t.2.1 = e then t.2.2 else 0).sum

/-- Finite reformulation of `ValidCode`. -/
def V (c : RawFieldCode) : Prop :=
  1 ≤ c.1 ∧ 1 ≤ c.2.1 ∧ (∀ t ∈ c.2.2, t.1 < c.1 ∧ t.2.1.length = c.1) ∧
    ∀ t ∈ c.2.2, t.2.1.sum = c.2.1 ∨ coeffSum c.2.2 t.1 t.2.1 = 0

theorem coeff_listSum (n i : ℕ) (L : List (ℕ × List ℕ × ℚ)) (m : Fin n →₀ ℕ) :
    ((L.map fun t => if t.1 = i then
        (MvPolynomial.monomial (expOf n t.2.1) t.2.2 : MvPolynomial (Fin n) ℚ) else 0).sum).coeff m =
      (L.map fun t => if t.1 = i ∧ expOf n t.2.1 = m then t.2.2 else 0).sum := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons, MvPolynomial.coeff_add, ih]
    congr 1
    by_cases h1 : t.1 = i <;> by_cases h2 : expOf n t.2.1 = m <;>
      simp [h1, h2, MvPolynomial.coeff_monomial]

theorem codePolys_coeff (c : RawFieldCode) (i : Fin c.1) (m : Fin c.1 →₀ ℕ) :
    (codePolys c i).coeff m =
      (c.2.2.map fun t => if t.1 = i.val ∧ expOf c.1 t.2.1 = m then t.2.2 else 0).sum :=
  coeff_listSum c.1 i.val c.2.2 m

theorem expOf_inj {n : ℕ} {l l' : List ℕ} (hl : l.length = n) (hl' : l'.length = n) :
    expOf n l = expOf n l' ↔ l = l' := by
  constructor
  · intro h
    apply List.ext_getElem (hl.trans hl'.symm)
    intro j h1 h2
    have := DFunLike.congr_fun h ⟨j, hl ▸ h1⟩
    simpa [expOf, Finsupp.coe_equivFunOnFinite_symm, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2] using this
  · rintro rfl; rfl

theorem expOf_deg {n : ℕ} {l : List ℕ} (hl : l.length = n) :
    (expOf n l).sum (fun _ a => a) = l.sum := by
  subst hl
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp [expOf]

theorem coeff_at (c : RawFieldCode) (H3 : ∀ t ∈ c.2.2, t.1 < c.1 ∧ t.2.1.length = c.1)
    (t : ℕ × List ℕ × ℚ) (ht : t ∈ c.2.2) :
    (codePolys c ⟨t.1, (H3 t ht).1⟩).coeff (expOf c.1 t.2.1) = coeffSum c.2.2 t.1 t.2.1 := by
  rw [codePolys_coeff]
  unfold coeffSum
  congr 1
  apply List.map_congr_left
  intro s hs
  have h : (s.1 = t.1 ∧ expOf c.1 s.2.1 = expOf c.1 t.2.1) ↔ (s.1 = t.1 ∧ s.2.1 = t.2.1) := by
    rw [expOf_inj (H3 s hs).2 (H3 t ht).2]
  exact if_congr h rfl rfl

theorem validCode_iff (c : RawFieldCode) : ValidCode c ↔ V c := by
  unfold ValidCode V
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun t ht => ?_⟩
    by_cases hs : t.2.1.sum = c.2.1
    · exact Or.inl hs
    · right
      rw [← coeff_at c h3 t ht]
      by_contra hne
      apply hs
      have hm : expOf c.1 t.2.1 ∈ (codePolys c ⟨t.1, (h3 t ht).1⟩).support :=
        MvPolynomial.mem_support_iff.mpr hne
      have := h4 _ _ hm
      rwa [expOf_deg (h3 t ht).2] at this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun i m hm => ?_⟩
    have hne := MvPolynomial.mem_support_iff.mp hm
    rw [codePolys_coeff] at hne
    obtain ⟨x, hx, hx0⟩ := List.exists_mem_ne_zero_of_sum_ne_zero hne
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    have hcond : t.1 = i.val ∧ expOf c.1 t.2.1 = m := by
      by_contra hc
      exact hx0 (if_neg hc)
    obtain ⟨hti, rfl⟩ := hcond
    have hi : i = ⟨t.1, (h3 t ht).1⟩ := Fin.ext hti.symm
    subst hi
    rcases h4 t ht with hsum | hzero
    · rw [expOf_deg (h3 t ht).2]; exact hsum
    · exact absurd ((coeff_at c h3 t ht).trans hzero) (MvPolynomial.mem_support_iff.mp hm)

theorem primrec_coeffSum :
    Primrec₂ fun (L : List (ℕ × List ℕ × ℚ)) (p : ℕ × List ℕ) => coeffSum L p.1 p.2 := by
  have hc : PrimrecPred fun (a : (List (ℕ × List ℕ × ℚ) × (ℕ × List ℕ)) × (ℕ × List ℕ × ℚ)) =>
      a.2.1 = a.1.2.1 ∧ a.2.2.1 = a.1.2.2 :=
    PrimrecPred.and (Primrec.eq.comp (fst.comp snd) (fst.comp (snd.comp fst)))
      (Primrec.eq.comp (fst.comp (snd.comp snd)) (snd.comp (snd.comp fst)))
  exact Primrec.rat_list_sum.comp (list_map fst (Primrec.ite hc (snd.comp (snd.comp snd)) (const (0 : ℚ))).to₂)

theorem primrec_V : PrimrecPred V := by
  have hR3 : PrimrecRel fun (t : ℕ × List ℕ × ℚ) (c : RawFieldCode) =>
      t.1 < c.1 ∧ t.2.1.length = c.1 :=
    PrimrecPred.and (nat_lt.comp (fst.comp fst) (fst.comp snd))
      (Primrec.eq.comp (list_length.comp (fst.comp (snd.comp fst))) (fst.comp snd))
  have hR4 : PrimrecRel fun (t : ℕ × List ℕ × ℚ) (c : RawFieldCode) =>
      t.2.1.sum = c.2.1 ∨ coeffSum c.2.2 t.1 t.2.1 = 0 :=
    PrimrecPred.or
      (Primrec.eq.comp (Primrec.nat_list_sum'.comp (fst.comp (snd.comp fst)))
        (fst.comp (snd.comp snd)))
      (Primrec.eq.comp (primrec_coeffSum.comp (snd.comp (snd.comp snd))
        (Primrec.pair (fst.comp fst) (fst.comp (snd.comp fst)))) (const 0))
  exact PrimrecPred.and (nat_le.comp (const 1) fst)
    (PrimrecPred.and (nat_le.comp (const 1) (fst.comp snd))
      (PrimrecPred.and ((PrimrecRel.forall_mem_list hR3).comp (snd.comp snd) Primrec.id)
        ((PrimrecRel.forall_mem_list hR4).comp (snd.comp snd) Primrec.id)))

end HGASUndecidable.Main.ValidCodeAux

theorem solution :
    ComputablePred HGASUndecidable.Main.ValidCode :=
  ComputablePred.of_eq (PrimrecPred.computablePred HGASUndecidable.Main.ValidCodeAux.primrec_V)
    fun c => (HGASUndecidable.Main.ValidCodeAux.validCode_iff c).symm
