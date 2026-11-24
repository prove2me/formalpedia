-- Prove2me | solution 1 for HGASUndecidable.Main.guardedPaddingMap_computable
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T19:41:15.00991+00:00
-- url     : https://prove2.me/submissions/fe637bb8-57c1-475d-87e8-d8ca858a97bc

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

/-! ## Mathlib's raw `Encodable ℚ` coding as a `Primcodable` structure -/

theorem subtype_decode_val {P : ℕ → Prop} [DecidablePred P] (v : ℕ) (s : {d : ℕ // P d})
    (h : Encodable.decode v = some s) : s.val = v := by
  change Encodable.decodeSubtype v = some s at h
  simp only [Encodable.decodeSubtype, Encodable.decode_nat, Option.bind_some] at h
  split_ifs at h with hp
  · cases h; rfl

/-- Raw decoding only succeeds on raw codes. -/
theorem raw_decode_spec (n : ℕ) (q : ℚ) :
    @Encodable.decode ℚ Rat.instEncodable n = some q → rawEncode q = n := by
  intro h
  simp only [Encodable.decode_ofEquiv, Encodable.decode_sigma_val,
    Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
  obtain ⟨⟨z, ⟨dv, ⟨hpos, hcop⟩⟩⟩, ⟨z', hz, a, ha, he⟩, rfl⟩ := h
  have hd := subtype_decode_val _ _ ha
  have h12 := Sigma.mk.inj_iff.mp he
  have h1 : z' = z := h12.1
  subst h1
  have h2 : a = ⟨dv, ⟨hpos, hcop⟩⟩ := eq_of_heq h12.2
  subst h2
  have hz' : Equiv.intEquivNat z' = (Nat.unpair n).1 := by
    obtain ⟨b, hb, hbz⟩ := hz
    simp only [Encodable.decode_nat, Option.some.injEq] at hb
    rw [← hbz, ← hb]; simp
  change Nat.pair (Equiv.intEquivNat z') dv = n
  rw [hz']
  simp only at hd
  rw [hd]; exact Nat.pair_unpair n

theorem raw_decode_eq (n : ℕ) :
    @Encodable.decode ℚ Rat.instEncodable n =
      if MemR n then some (Denumerable.ofNat ℚ (cntR n)) else none := by
  by_cases hm : MemR n
  · rw [if_pos hm]
    obtain ⟨q, rfl⟩ := (memR_iff n).2 hm
    rw [← encode_eq_cntR, Denumerable.ofNat_encode]
    exact @Encodable.encodek ℚ Rat.instEncodable q
  · rw [if_neg hm]
    cases hq : @Encodable.decode ℚ Rat.instEncodable n with
    | none => rfl
    | some q => exact absurd ((memR_iff n).1 ⟨q, raw_decode_spec n q hq⟩) hm

/-- `ℚ` with Mathlib's raw `Encodable` instance. -/
def RQ : Type := ℚ

instance : Encodable RQ := Rat.instEncodable

instance : Primcodable RQ :=
  ⟨(Primrec.nat_iff.1 (Primrec.ite primrec_memR Primrec.succ (const 0))).of_eq fun n => by
    show _ = @Encodable.encode (Option ℚ) (@Option.encodable ℚ Rat.instEncodable)
      (@Encodable.decode ℚ Rat.instEncodable n)
    rw [raw_decode_eq]
    split_ifs with h
    · show n.succ = (rawEncode (Denumerable.ofNat ℚ (cntR n))).succ
      rw [(ofNat_spec _ _).2 ⟨h, rfl⟩]
    · rfl⟩

def toRQ (q : ℚ) : RQ := q

def ofRQ (q : RQ) : ℚ := q

theorem primrec_toRQ : Primrec toRQ :=
  (Primrec.encode_iff (f := toRQ)).1 (primrec_rawEncode.of_eq fun _ => rfl)

theorem primrec_ofRQ : Primrec ofRQ :=
  (Primrec.encode_iff (f := ofRQ)).1 ((primrec_cntR.comp (Primrec.encode (α := RQ))).of_eq
    fun q => (encode_eq_cntR (ofRQ q)).symm)

end RatPrimrec

/-! ## Field codes: Mathlib's raw `Encodable` coding vs. the `Primcodable` coding -/

namespace HGASUndecidable.Main.CodeBridge

open RatPrimrec

/-- Field codes whose rational leaves use the raw coding. -/
abbrev RawFieldCodeR := ℕ × ℕ × List (ℕ × List ℕ × RQ)

def tFromR (t : ℕ × List ℕ × RQ) : ℕ × List ℕ × ℚ := (t.1, t.2.1, ofRQ t.2.2)

def tToR (t : ℕ × List ℕ × ℚ) : ℕ × List ℕ × RQ := (t.1, t.2.1, toRQ t.2.2)

def fromR (c : RawFieldCodeR) : RawFieldCode := (c.1, c.2.1, c.2.2.map tFromR)

def toR (c : RawFieldCode) : RawFieldCodeR := (c.1, c.2.1, c.2.2.map tToR)

theorem primrec_tFromR : Primrec tFromR :=
  Primrec.pair fst (Primrec.pair (fst.comp snd) (primrec_ofRQ.comp (snd.comp snd)))

theorem primrec_tToR : Primrec tToR :=
  Primrec.pair fst (Primrec.pair (fst.comp snd) (primrec_toRQ.comp (snd.comp snd)))

theorem primrec_fromR : Primrec fromR :=
  Primrec.pair fst (Primrec.pair (fst.comp snd)
    (list_map (snd.comp snd) (primrec_tFromR.comp snd).to₂))

theorem primrec_toR : Primrec toR :=
  Primrec.pair fst (Primrec.pair (fst.comp snd)
    (list_map (snd.comp snd) (primrec_tToR.comp snd).to₂))

theorem map_tFromR (L : List (ℕ × List ℕ × RQ)) :
    L.map tFromR = (L : List (ℕ × List ℕ × ℚ)) := by
  induction L with
  | nil => rfl
  | cons t L ih => rw [List.map_cons, ih]; rfl

theorem map_tToR (L : List (ℕ × List ℕ × ℚ)) :
    L.map tToR = (L : List (ℕ × List ℕ × RQ)) := by
  induction L with
  | nil => rfl
  | cons t L ih => rw [List.map_cons, ih]; rfl

theorem option_map_fromR (x : Option RawFieldCodeR) :
    x.map fromR = (x : Option RawFieldCode) := by
  cases x with
  | none => rfl
  | some c =>
    show some (c.1, c.2.1, c.2.2.map tFromR) = some c
    rw [map_tFromR]; rfl

/-- `decodeField` (which uses Mathlib's raw `Encodable ℚ`) is primitive recursive. -/
theorem primrec_decodeField : Primrec decodeField :=
  (option_map (Primrec.decode (α := RawFieldCodeR)) (primrec_fromR.comp snd).to₂).of_eq
    fun _ => (option_map_fromR _).trans rfl

/-- The raw `Encodable` code of a field code is primitive recursive. -/
theorem primrec_encodeField :
    Primrec fun c : RawFieldCode => @Encodable.encode RawFieldCode
      (@Encodable.Prod.encodable _ _ _ (@Encodable.Prod.encodable _ _ _
        (@List.encodable _ (@Encodable.Prod.encodable _ _ _
          (@Encodable.Prod.encodable _ _ _ Rat.instEncodable))))) c :=
  (Primrec.encode.comp primrec_toR).of_eq fun c => by
    show Encodable.encode (c.1, c.2.1, c.2.2.map tToR) = _
    rw [map_tToR]; rfl

end HGASUndecidable.Main.CodeBridge

open HGASUndecidable.Main HGASUndecidable.Main.CodeBridge

theorem solution
    (n₀ k₀ n j : ℕ) [DecidablePred HGASUndecidable.Main.ValidCode]
    (hn : Nat.choose (n₀+k₀-1) k₀ ≤ n) (f : ℕ → ℕ)
    (hv : ComputablePred HGASUndecidable.Main.ValidCode)
    (hp : Computable (HGASUndecidable.Main.paddingCode hn j)) (hf : Computable f) :
    Computable (HGASUndecidable.Main.guardedPaddingMap n₀ k₀ n j hn f) := by
  have hV : Computable fun c : RawFieldCode => decide (ValidCode c) := hv.decide
  have hA : Computable fun c : RawFieldCode =>
      decide (ValidCode c ∧ c.1 = n₀ ∧ c.2.1 = 2*k₀+1) := by
    have h2 : Primrec fun c : RawFieldCode => decide (c.1 = n₀ ∧ c.2.1 = 2*k₀+1) :=
      (PrimrecPred.and (Primrec.eq.comp fst (const n₀))
        (Primrec.eq.comp (fst.comp snd) (const (2*k₀+1)))).decide
    exact (Primrec.and.to_comp.comp hV h2.to_comp).of_eq fun c => by simp [Bool.decide_and]
  have hB : Computable fun q : RawFieldCode =>
      decide (ValidCode q ∧ q.1 = Nat.choose (n₀+k₀-1) k₀ ∧ q.2.1 = 3) := by
    have h2 : Primrec fun q : RawFieldCode =>
        decide (q.1 = Nat.choose (n₀+k₀-1) k₀ ∧ q.2.1 = 3) :=
      (PrimrecPred.and (Primrec.eq.comp fst (const _))
        (Primrec.eq.comp (fst.comp snd) (const 3))).decide
    exact (Primrec.and.to_comp.comp hV h2.to_comp).of_eq fun c => by simp [Bool.decide_and]
  have hDec : Computable decodeField := primrec_decodeField.to_comp
  have hEnc := primrec_encodeField.to_comp
  have hInner : Computable fun q : RawFieldCode =>
      if ValidCode q ∧ q.1 = Nat.choose (n₀+k₀-1) k₀ ∧ q.2.1 = 3 then
        some (paddingCode hn j q.2.2) else none :=
    (Computable.cond hB (Computable.option_some.comp
      (hp.comp (Computable.snd.comp Computable.snd))) (Computable.const none)).of_eq
      fun q => by simp only [Bool.cond_decide]
  have hG : Computable fun c : RawFieldCode =>
      if ValidCode c ∧ c.1 = n₀ ∧ c.2.1 = 2*k₀+1 then
        (decodeField (f (Encodable.encode c))).bind fun q =>
          if ValidCode q ∧ q.1 = Nat.choose (n₀+k₀-1) k₀ ∧ q.2.1 = 3 then
            some (paddingCode hn j q.2.2) else none
      else none :=
    (Computable.cond hA (Computable.option_bind (hDec.comp (hf.comp hEnc))
      (hInner.comp Computable.snd).to₂) (Computable.const none)).of_eq
      fun c => by simp only [Bool.cond_decide]
  exact (Computable.option_getD (Computable.option_bind hDec (hG.comp Computable.snd).to₂)
    (Computable.const _)).of_eq fun e => rfl
