-- Prove2me | solution 1 for NadlerCLS.circ_eval_polyTime
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:05:53.194576+00:00
-- url     : https://prove2.me/submissions/815b89a5-ae8c-4f78-8a2c-3b599116b71d

import Mathlib
import Definitions.Def_BuhaiPapers_Background_PolyTime_Rat
import Definitions.Def_BuhaiPapers_Background_PolyTime_Lists
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_NadlerCLS_Circ
import Definitions.Def_NadlerCLS_l1

set_option autoImplicit false
open Turing.MultiTapeTM

namespace NadlerCLS.CircEval


def rNat (w : List Bool) : ℕ × List Bool :=
  let k := w.idxOf false
  (ofBits ((w.drop (k + 1)).take k), w.drop (k + 1 + k))

theorem rNat_poly : ComputableInPolyTime rNat encBits (encPair encNat encBits) := by
  unfold rNat
  fun_prop

@[fun_prop] theorem rNat_poly' {α : Type} {input : α ↪ List Bool} {f : α → List Bool}
    (hf : ComputableInPolyTime f input encBits) :
    ComputableInPolyTime (fun a => rNat (f a)) input (encPair encNat encBits) := rNat_poly.comp hf

def rInt (w : List Bool) : ℤ × List Bool :=
  let p := rNat w.tail
  (if w.headD false then -(p.1 : ℤ) else (p.1 : ℤ), p.2)

theorem rInt_poly : ComputableInPolyTime rInt encBits (encPair encIntBin encBits) := by
  unfold rInt
  fun_prop

@[fun_prop] theorem rInt_poly' {α : Type} {input : α ↪ List Bool} {f : α → List Bool}
    (hf : ComputableInPolyTime f input encBits) :
    ComputableInPolyTime (fun a => rInt (f a)) input (encPair encIntBin encBits) := rInt_poly.comp hf

def rRat (w : List Bool) : ℚ × List Bool :=
  let p := rInt w
  let q := rNat p.2
  ((p.1 : ℚ) / (q.1 : ℚ), q.2)

theorem rRat_poly : ComputableInPolyTime rRat encBits (encPair Encoding.encRat encBits) := by
  unfold rRat
  fun_prop



@[fun_prop] theorem getD_bin {γ α : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
    {l : γ → List α} {i : γ → ℕ} (d : α)
    (hl : ComputableInPolyTime l encIn (encList encA)) (hi : ComputableInPolyTime i encIn encNat) :
    ComputableInPolyTime (fun x => (l x).getD (i x) d) encIn encA :=
  ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listGetD_binary (encA := encA) d hl.tidy hi.tidy)

abbrev Gt := ℕ × ℕ × ℕ × ℚ
abbrev encG : Gt ↪ List Bool := encPair encNat (encPair encNat (encPair encNat Encoding.encRat))

def capv (K : ℕ) (v : ℚ) : ℚ := if |v| ≤ 2 ^ K ∧ (v.den : ℚ) ≤ 2 ^ K then v else 0

def raw (xs prior : List ℚ) (g : Gt) : ℚ :=
  if g.1 = 0 then xs.getD g.2.1 0 else if g.1 = 1 then g.2.2.2
  else if g.1 = 2 then prior.getD g.2.1 0 + prior.getD g.2.2.1 0
  else if g.1 = 3 then prior.getD g.2.1 0 - prior.getD g.2.2.1 0
  else if g.1 = 4 then prior.getD g.2.1 0 * prior.getD g.2.2.1 0
  else if g.1 = 5 then min (prior.getD g.2.1 0) (prior.getD g.2.2.1 0)
  else if g.1 = 6 then max (prior.getD g.2.1 0) (prior.getD g.2.2.1 0)
  else if g.1 = 7 then (if prior.getD g.2.2.1 0 < prior.getD g.2.1 0 then 1 else 0)
  else 0

def estep (par : ℕ × List ℚ) (prior : List ℚ) (g : Gt) : List ℚ :=
  prior ++ [capv par.1 (raw par.2 prior g)]

theorem capv_poly : ComputableInPolyTime (fun p : ℕ × ℚ => capv p.1 p.2)
    (encPair encUnary Encoding.encRat) Encoding.encRat := by
  unfold capv
  fun_prop

theorem raw_poly : ComputableInPolyTime (fun p : (List ℚ × List ℚ) × Gt => raw p.1.1 p.1.2 p.2)
    (encPair (encPair (encList Encoding.encRat) (encList Encoding.encRat)) encG) Encoding.encRat := by
  unfold raw
  fun_prop



def rItems {α : Type} (rd : List Bool → α × List Bool) (k : ℕ) (w : List Bool) :
    List α × List Bool :=
  (w.take (min w.length k)).foldl (fun st _ => (st.1 ++ [(rd st.2).1], (rd st.2).2)) ([], w)

theorem poly_aux (c d m L : ℕ) (hL : L ≤ m) :
    2 * (L * (2 * (c * (m + 1) ^ d) + 1)) + 1 + m ≤ (4 * c + 4) * (m + 1) ^ (d + 1) := by
  have h1 : 1 ≤ (m + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have h2 : L * (2 * (c * (m + 1) ^ d) + 1) ≤ (m + 1) * (2 * (c * (m + 1) ^ d) + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : (m + 1) * (2 * (c * (m + 1) ^ d) + 1) = 2 * (c * (m + 1) ^ (d + 1)) + (m + 1) := by
    rw [pow_succ]; ring
  have h4 : m + 1 ≤ (m + 1) ^ (d + 1) := by
    calc m + 1 = (m + 1) * 1 := by ring
      _ ≤ (m + 1) * (m + 1) ^ d := Nat.mul_le_mul_left _ h1
      _ = (m + 1) ^ (d + 1) := by rw [pow_succ]; ring
  have h5 : (4 * c + 4) * (m + 1) ^ (d + 1) = 4 * (c * (m + 1) ^ (d + 1)) + 4 * (m + 1) ^ (d + 1) := by
    ring
  omega

theorem rItems_poly {α : Type} {encA : α ↪ List Bool} (rd : List Bool → α × List Bool)
    (hrd : ComputableInPolyTime rd encBits (encPair encA encBits))
    (hsuf : ∀ w, (rd w).2.length ≤ w.length) :
    ComputableInPolyTime (fun p : ℕ × List Bool => rItems rd p.1 p.2)
      (encPair encNat encBits) (encPair (encList encA) encBits) := by
  obtain ⟨c, d, hcd⟩ := hrd.polyBounded_length.exists_le
  have hlist : ComputableInPolyTime (fun p : ℕ × List Bool => p.2.take (min p.2.length p.1))
      (encPair encNat encBits) encBits := by
    have hm : ComputableInPolyTime (fun p : ℕ × List Bool => min p.2.length p.1)
        (encPair encNat encBits) encUnary :=
      ComputableInPolyTime.binary_min_unary' (by fun_prop) (by fun_prop)
    exact ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.bitsTakeWithInput (by fun_prop : ComputableInPolyTime
        (fun p : ℕ × List Bool => p.2) (encPair encNat encBits) encBits).tidy hm.tidy)
  have hstep : ComputableInPolyTime
      (fun p : (List α × List Bool) × Bool => (p.1.1 ++ [(rd p.1.2).1], (rd p.1.2).2))
      (encPair (encPair (encList encA) encBits) encBool) (encPair (encList encA) encBits) := by
    have h1 : ComputableInPolyTime (fun p : (List α × List Bool) × Bool => rd p.1.2)
        (encPair (encPair (encList encA) encBits) encBool) (encPair encA encBits) :=
      hrd.comp (by fun_prop)
    fun_prop
  have := (ComputableTidilyInPolyTime.foldl_spec (encA := encBool) (encL := encBits)
    (encB := encPair (encList encA) encBits)
    (list := fun p : ℕ × List Bool => p.2.take (min p.2.length p.1))
    (init := fun p : ℕ × List Bool => (([] : List α), p.2))
    (step := fun st (_ : Bool) => (st.1 ++ [(rd st.2).1], (rd st.2).2))
    hlist.tidy (by fun_prop : ComputableInPolyTime (fun p : ℕ × List Bool => (([] : List α), p.2))
      (encPair encNat encBits) (encPair (encList encA) encBits)).tidy hstep.tidy
    (fun x consumed st => st.2.length ≤ x.2.length ∧
      (encList encA st.1).length ≤ consumed.length * (2 * (c * (x.2.length + 1) ^ d) + 1))
    (by intro x; simp)
    ?_ (size := fun x => (4 * c + 4) * ((encPair encNat encBits x).length + 1) ^ (d + 1))
    (PolyBounded.of_forall_le (4 * c + 4) (d + 1) (fun _ => le_rfl)) ?_).1
  · exact ComputableInPolyTime.of_tidy this
  · intro x consumed st v _ ⟨h1, h2⟩
    refine ⟨(hsuf _).trans h1, ?_⟩
    have hb := hcd st.2
    have hle : (encA (rd st.2).1).length ≤ (encPair encA encBits (rd st.2)).length :=
      length_le_encPair_left _ _ _
    have hmono : c * (st.2.length + 1) ^ d ≤ c * (x.2.length + 1) ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    simp only [encBits_apply] at hb
    simp only [length_encList, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.length_append, List.length_cons, List.length_nil] at h2 ⊢
    nlinarith
  · intro x consumed st hpre ⟨h1, h2⟩
    have hc : consumed.length ≤ x.2.length := by
      have := hpre.length_le
      simp only [List.length_take] at this
      omega
    have hx : x.2.length ≤ (encPair encNat encBits x).length := by
      simp
    rw [length_encPair]
    simp only [encBits_apply]
    have := poly_aux c d (encPair encNat encBits x).length consumed.length (hc.trans hx)
    have hm : 2 * (consumed.length * (2 * (c * (x.2.length + 1) ^ d) + 1)) ≤
        2 * (consumed.length * (2 * (c * ((encPair encNat encBits x).length + 1) ^ d) + 1)) := by
      gcongr
    omega


/-! ### Gate reader -/

def rGate (w : List Bool) : Gt × List Bool :=
  let p := rNat w
  if p.1 = 1 then ((1, 0, 0, (rRat p.2).1), (rRat p.2).2)
  else if p.1 = 0 then ((0, (rNat p.2).1, 0, 0), (rNat p.2).2)
  else ((p.1, (rNat p.2).1, (rNat (rNat p.2).2).1, 0), (rNat (rNat p.2).2).2)

theorem rRat_poly' : ComputableInPolyTime rRat encBits (encPair Encoding.encRat encBits) := rRat_poly

@[fun_prop] theorem rRat_poly'' {α : Type} {input : α ↪ List Bool} {f : α → List Bool}
    (hf : ComputableInPolyTime f input encBits) :
    ComputableInPolyTime (fun a => rRat (f a)) input (encPair Encoding.encRat encBits) :=
  rRat_poly.comp hf

theorem rGate_poly : ComputableInPolyTime rGate encBits (encPair encG encBits) := by
  unfold rGate
  fun_prop

theorem rNat_suf (w : List Bool) : (rNat w).2.length ≤ w.length := by
  simp [rNat]

theorem rInt_suf (w : List Bool) : (rInt w).2.length ≤ w.length := by
  have := rNat_suf w.tail
  simp only [rInt, List.length_tail] at this ⊢
  omega

theorem rRat_suf (w : List Bool) : (rRat w).2.length ≤ w.length :=
  (rNat_suf _).trans (rInt_suf w)

theorem rGate_suf (w : List Bool) : (rGate w).2.length ≤ w.length := by
  unfold rGate
  have h1 := rNat_suf w
  have h2 := rNat_suf (rNat w).2
  have h3 := rNat_suf (rNat (rNat w).2).2
  have h4 := rRat_suf (rNat w).2
  dsimp only
  split_ifs <;> simp only <;> omega

/-- Read a mission-coded list: a count, then that many items (at most the remaining length). -/
def rList {α : Type} (rd : List Bool → α × List Bool) (w : List Bool) : List α × List Bool :=
  rItems rd (rNat w).1 (rNat w).2

theorem rList_poly {α : Type} {encA : α ↪ List Bool} (rd : List Bool → α × List Bool)
    (hrd : ComputableInPolyTime rd encBits (encPair encA encBits))
    (hsuf : ∀ w, (rd w).2.length ≤ w.length) :
    ComputableInPolyTime (rList rd) encBits (encPair (encList encA) encBits) :=
  (rItems_poly rd hrd hsuf).comp rNat_poly

/-- Budgeted evaluation of all gates. -/
def evalAll (K : ℕ) (xs : List ℚ) (gs : List Gt) : List ℚ := gs.foldl (estep (K, xs)) []

theorem size_le_of_le (n K : ℕ) (h : n ≤ 2 ^ K) : n.size ≤ K + 1 := by
  rw [Nat.size_le]
  calc n ≤ 2 ^ K := h
    _ < 2 ^ (K + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem encRat_len (q : ℚ) :
    (Encoding.encRat q).length = 2 * (q.num.natAbs.size + 1) + 1 + q.den.size := by
  have h1 : ∀ n : ℕ, (Encoding.encNat n).length = n.size := fun n => Nat.size_eq_bits_len n
  have h2 : ∀ z : ℤ, (Encoding.encInt z).length = z.natAbs.size + 1 := fun z => by
    show (decide (z < 0) :: Encoding.encNat z.natAbs).length = _
    simp [h1]
  simp [Encoding.encRat, Encoding.encPair, Encoding.frame, h1, h2]
  ring

theorem capv_len (K : ℕ) (v : ℚ) : (Encoding.encRat (capv K v)).length ≤ 5 * K + 6 := by
  unfold capv
  split_ifs with h
  · rw [encRat_len]
    obtain ⟨h1, h2⟩ := h
    have hd : v.den ≤ 2 ^ K := by exact_mod_cast h2
    have hn : (v.num.natAbs : ℚ) ≤ 2 ^ K * 2 ^ K := by
      have e : (v.num.natAbs : ℚ) = |v| * v.den := by
        rw [Nat.cast_natAbs, Int.cast_abs, ← Rat.mul_den_eq_num, abs_mul]
        simp
      rw [e]
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have hn' : v.num.natAbs ≤ 2 ^ (K + K) := by
      rw [pow_add]; exact_mod_cast hn
    have := size_le_of_le _ _ hn'
    have := size_le_of_le _ _ hd
    omega
  · rw [encRat_len]
    simp

@[fun_prop] theorem capv_poly' {α : Type} {input : α ↪ List Bool} {f : α → ℕ} {g : α → ℚ}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input Encoding.encRat) :
    ComputableInPolyTime (fun a => capv (f a) (g a)) input Encoding.encRat := by
  have := capv_poly.comp (hf.prod hg)
  exact this

@[fun_prop] theorem raw_poly' {α : Type} {input : α ↪ List Bool} {f g : α → List ℚ} {h : α → Gt}
    (hf : ComputableInPolyTime f input (encList Encoding.encRat))
    (hg : ComputableInPolyTime g input (encList Encoding.encRat))
    (hh : ComputableInPolyTime h input encG) :
    ComputableInPolyTime (fun a => raw (f a) (g a) (h a)) input Encoding.encRat := by
  have := raw_poly.comp ((hf.prod hg).prod hh)
  exact this

theorem evalAll_poly : ComputableInPolyTime (fun p : (ℕ × List ℚ) × List Gt => evalAll p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary (encList Encoding.encRat)) (encList encG))
    (encList Encoding.encRat) := by
  have hstep : ComputableInPolyTime
      (fun q : ((ℕ × List ℚ) × List ℚ) × Gt => estep q.1.1 q.1.2 q.2)
      (encPair (encPair (encPair encUnary (encList Encoding.encRat)) (encList Encoding.encRat)) encG)
      (encList Encoding.encRat) := by
    unfold estep
    fun_prop
  refine ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.foldlWith_of_bounded_growth
    (par := fun p : (ℕ × List ℚ) × List Gt => p.1) (list := fun p => p.2)
    (init := fun _ => ([] : List ℚ)) (step := estep) (encA := encG) (encL := encList encG)
    (encP := encPair encUnary (encList Encoding.encRat))
    (by fun_prop : ComputableInPolyTime (fun p : (ℕ × List ℚ) × List Gt => p.1)
      (encPair (encPair encUnary (encList Encoding.encRat)) (encList encG))
      (encPair encUnary (encList Encoding.encRat))).tidy
    (by fun_prop : ComputableInPolyTime (fun p : (ℕ × List ℚ) × List Gt => p.2)
      (encPair (encPair encUnary (encList Encoding.encRat)) (encList encG)) (encList encG)).tidy
    (ComputableInPolyTime.const _).tidy hstep.tidy
    (growth := fun p => 10 * p.1.1 + 13) ?_ ?_)
  · refine PolyBounded.of_forall_le 13 1 (fun p => ?_)
    have : p.1.1 ≤ (encPair (encPair encUnary (encList Encoding.encRat)) (encList encG) p).length := by
      rw [length_encPair, length_encPair]
      show p.1.1 ≤ 2 * (2 * (List.replicate p.1.1 true).length + 1 + _) + 1 + _
      simp only [List.length_replicate]
      omega
    simp only [pow_one]
    omega
  · intro p st g _
    unfold estep
    have := capv_len p.1.1 (raw p.1.2 st g)
    simp only [length_encList, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    omega

/-- Mission printer for a list of rationals. -/
def printL (l : List ℚ) : List Bool :=
  NetworkEquilibriumCLS.LinearNash.encList NetworkEquilibriumCLS.LinearNash.encRat l

theorem pNat_poly : ComputableInPolyTime (fun n : ℕ => NetworkEquilibriumCLS.LinearNash.encNat n)
    encNat encBits := by
  unfold NetworkEquilibriumCLS.LinearNash.encNat
  fun_prop

@[fun_prop] theorem pNat_poly' {α : Type} {input : α ↪ List Bool} {f : α → ℕ}
    (hf : ComputableInPolyTime f input encNat) :
    ComputableInPolyTime (fun a => NetworkEquilibriumCLS.LinearNash.encNat (f a)) input encBits :=
  pNat_poly.comp hf

theorem pInt_poly : ComputableInPolyTime (fun z : ℤ => NetworkEquilibriumCLS.LinearNash.encInt z)
    encIntBin encBits := by
  unfold NetworkEquilibriumCLS.LinearNash.encInt
  fun_prop

@[fun_prop] theorem pInt_poly' {α : Type} {input : α ↪ List Bool} {f : α → ℤ}
    (hf : ComputableInPolyTime f input encIntBin) :
    ComputableInPolyTime (fun a => NetworkEquilibriumCLS.LinearNash.encInt (f a)) input encBits :=
  pInt_poly.comp hf

theorem pRat_poly : ComputableInPolyTime (fun q : ℚ => NetworkEquilibriumCLS.LinearNash.encRat q)
    Encoding.encRat encBits := by
  unfold NetworkEquilibriumCLS.LinearNash.encRat
  fun_prop

theorem printL_poly : ComputableInPolyTime printL (encList Encoding.encRat) encBits := by
  have : ComputableInPolyTime (fun l : List ℚ => (l.flatMap NetworkEquilibriumCLS.LinearNash.encRat))
      (encList Encoding.encRat) encBits := by
    have h1 : ComputableInPolyTime (fun p : List ℚ × ℚ => NetworkEquilibriumCLS.LinearNash.encRat p.2)
        (encPair (encList Encoding.encRat) Encoding.encRat) (encList encBool) :=
      (bits_encList_polyTime encBool).1.comp (pRat_poly.comp (by fun_prop))
    have h2 := ComputableTidilyInPolyTime.flatMapWithInput
      (f := fun (_ : List ℚ) (q : ℚ) => NetworkEquilibriumCLS.LinearNash.encRat q)
      (list := fun l : List ℚ => l) (encIn := encList Encoding.encRat) (encA := Encoding.encRat)
      (by fun_prop : ComputableInPolyTime (fun l : List ℚ => l) (encList Encoding.encRat)
        (encList Encoding.encRat)).tidy h1.tidy
    exact (bits_encList_polyTime encBool).2.comp (ComputableInPolyTime.of_tidy h2)
  unfold printL NetworkEquilibriumCLS.LinearNash.encList
  fun_prop

/-- The evaluator. -/
def E (w : List Bool) : List Bool :=
  let pg := rList rGate w
  let po := rList rNat pg.2
  let px := rList rRat po.2
  let vals := evalAll (w.length ^ 3) px.1 pg.1
  printL (po.1.map (fun o => vals.getD o 0))

@[fun_prop] theorem evalAll_poly' {α : Type} {input : α ↪ List Bool} {f : α → ℕ} {g : α → List ℚ}
    {h : α → List Gt}
    (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input (encList Encoding.encRat))
    (hh : ComputableInPolyTime h input (encList encG)) :
    ComputableInPolyTime (fun a => evalAll (f a) (g a) (h a)) input (encList Encoding.encRat) := by
  have := evalAll_poly.comp ((hf.prod hg).prod hh)
  exact this

@[fun_prop] theorem printL_poly' {α : Type} {input : α ↪ List Bool} {f : α → List ℚ}
    (hf : ComputableInPolyTime f input (encList Encoding.encRat)) :
    ComputableInPolyTime (fun a => printL (f a)) input encBits :=
  printL_poly.comp hf

theorem rGates_poly : ComputableInPolyTime (rList rGate) encBits (encPair (encList encG) encBits) :=
  rList_poly rGate rGate_poly rGate_suf

theorem rNats_poly : ComputableInPolyTime (rList rNat) encBits (encPair (encList encNat) encBits) :=
  rList_poly rNat rNat_poly rNat_suf

theorem rRats_poly : ComputableInPolyTime (rList rRat) encBits
    (encPair (encList Encoding.encRat) encBits) :=
  rList_poly rRat rRat_poly rRat_suf

@[fun_prop] theorem rGates_poly' {α : Type} {input : α ↪ List Bool} {f : α → List Bool}
    (hf : ComputableInPolyTime f input encBits) :
    ComputableInPolyTime (fun a => rList rGate (f a)) input (encPair (encList encG) encBits) :=
  rGates_poly.comp hf

@[fun_prop] theorem rNats_poly' {α : Type} {input : α ↪ List Bool} {f : α → List Bool}
    (hf : ComputableInPolyTime f input encBits) :
    ComputableInPolyTime (fun a => rList rNat (f a)) input (encPair (encList encNat) encBits) :=
  rNats_poly.comp hf

@[fun_prop] theorem rRats_poly' {α : Type} {input : α ↪ List Bool} {f : α → List Bool}
    (hf : ComputableInPolyTime f input encBits) :
    ComputableInPolyTime (fun a => rList rRat (f a)) input (encPair (encList Encoding.encRat) encBits) :=
  rRats_poly.comp hf

theorem E_poly : ComputableInPolyTime E encBits encBits := by
  unfold E
  fun_prop

open NetworkEquilibriumCLS.LinearNash hiding encNat encInt encRat encList

local notation "mNat" => NetworkEquilibriumCLS.LinearNash.encNat
local notation "mInt" => NetworkEquilibriumCLS.LinearNash.encInt
local notation "mRat" => NetworkEquilibriumCLS.LinearNash.encRat
local notation "mList" => NetworkEquilibriumCLS.LinearNash.encList

/-! ### Correctness of the readers -/

theorem ofBits_bits (n : ℕ) : ofBits n.bits = n := by
  induction n using Nat.binaryRec with
  | zero => simp [ofBits]
  | bit b n ih =>
    by_cases h : n = 0 ∧ b = false
    · obtain ⟨rfl, rfl⟩ := h
      simp [ofBits]
    · rw [Nat.bits_append_bit _ _ (fun hn => by simp_all)]
      simp only [ofBits, List.foldr_cons] at ih ⊢
      rw [ih]

theorem rNat_enc (n : ℕ) (rest : List Bool) : rNat (mNat n ++ rest) = (n, rest) := by
  have hk : (mNat n ++ rest).idxOf false = n.bits.length := by
    simp only [NetworkEquilibriumCLS.LinearNash.encNat, List.append_assoc, List.cons_append]
    rw [List.idxOf_append_of_notMem (by simp)]
    simp
  simp only [rNat, hk]
  have hd : (mNat n ++ rest).drop (n.bits.length + 1) = n.bits ++ rest := by
    simp [NetworkEquilibriumCLS.LinearNash.encNat, List.drop_append]
  refine Prod.ext ?_ ?_
  · simp only
    rw [hd, List.take_left' rfl, ofBits_bits]
  · simp only
    rw [← List.drop_drop, hd, List.drop_left' rfl]

theorem rInt_enc (z : ℤ) (rest : List Bool) : rInt (mInt z ++ rest) = (z, rest) := by
  simp only [rInt, NetworkEquilibriumCLS.LinearNash.encInt, List.cons_append, List.tail_cons, List.headD_cons, rNat_enc]
  refine Prod.ext ?_ rfl
  by_cases h : z < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (not_lt.mp h)]

theorem rRat_enc (q : ℚ) (rest : List Bool) : rRat (mRat q ++ rest) = (q, rest) := by
  simp only [rRat, NetworkEquilibriumCLS.LinearNash.encRat, List.append_assoc, rInt_enc, rNat_enc]
  refine Prod.ext ?_ rfl
  exact Rat.num_div_den q

/-- The tuple form of a gate. -/
def repr : ArithmeticGate → Gt
  | .input i => (0, i, 0, 0)
  | .constant r => (1, 0, 0, r)
  | .add a b => (2, a, b, 0)
  | .sub a b => (3, a, b, 0)
  | .mul a b => (4, a, b, 0)
  | .minimum a b => (5, a, b, 0)
  | .maximum a b => (6, a, b, 0)
  | .test a b => (7, a, b, 0)

theorem rGate_enc (g : ArithmeticGate) (rest : List Bool) :
    rGate (gateCode g ++ rest) = (repr g, rest) := by
  cases g <;> simp [gateCode, rGate, repr, rNat_enc, rRat_enc, List.append_assoc]

theorem rItems_enc {α β : Type} (rd : List Bool → α × List Bool) (code : β → List Bool)
    (rp : β → α) (hrd : ∀ b rest, rd (code b ++ rest) = (rp b, rest)) (xs : List β)
    (rest : List Bool) (hlen : xs.length ≤ (xs.flatMap code ++ rest).length) :
    rItems rd xs.length (xs.flatMap code ++ rest) = (xs.map rp, rest) := by
  have key : ∀ (ys : List β) (L : List Bool) (acc : List α), L.length = ys.length →
      L.foldl (fun st _ => (st.1 ++ [(rd st.2).1], (rd st.2).2)) (acc, ys.flatMap code ++ rest) =
        (acc ++ ys.map rp, rest) := by
    intro ys
    induction ys with
    | nil => intro L acc hL; simp_all
    | cons y ys ih =>
      intro L acc hL
      cases L with
      | nil => simp at hL
      | cons b L =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hL
        simp only [List.foldl_cons, List.flatMap_cons, List.append_assoc, hrd, List.map_cons]
        rw [ih L _ hL]
        simp
  unfold rItems
  rw [key]
  · simp
  · simp only [List.length_take]
    omega

theorem rList_enc {α β : Type} (rd : List Bool → α × List Bool) (code : β → List Bool)
    (rp : β → α) (hrd : ∀ b rest, rd (code b ++ rest) = (rp b, rest))
    (hne : ∀ b, code b ≠ []) (xs : List β) (rest : List Bool) :
    rList rd (mList code xs ++ rest) = (xs.map rp, rest) := by
  unfold rList
  simp only [NetworkEquilibriumCLS.LinearNash.encList, List.append_assoc, rNat_enc]
  apply rItems_enc rd code rp hrd
  have : xs.length ≤ (xs.flatMap code).length := by
    rw [List.length_flatMap]
    induction xs with
    | nil => simp
    | cons y ys ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have := List.length_pos_iff.mpr (hne y)
      omega
  simp only [List.length_append]
  omega

theorem encNat_ne (n : ℕ) : mNat n ≠ [] := by simp [NetworkEquilibriumCLS.LinearNash.encNat]

theorem gateCode_ne (g : ArithmeticGate) : gateCode g ≠ [] := by
  cases g <;> simp [gateCode, NetworkEquilibriumCLS.LinearNash.encNat]

theorem encRat_ne (q : ℚ) : mRat q ≠ [] := by simp [NetworkEquilibriumCLS.LinearNash.encRat, NetworkEquilibriumCLS.LinearNash.encInt]

/-- Rational gate evaluation, mirroring `gateEval`. -/
def gevQ (xs prior : List ℚ) : ArithmeticGate → ℚ
  | .input i => xs.getD i 0
  | .constant r => r
  | .add a b => prior.getD a 0 + prior.getD b 0
  | .sub a b => prior.getD a 0 - prior.getD b 0
  | .mul a b => prior.getD a 0 * prior.getD b 0
  | .minimum a b => min (prior.getD a 0) (prior.getD b 0)
  | .maximum a b => max (prior.getD a 0) (prior.getD b 0)
  | .test a b => if prior.getD b 0 < prior.getD a 0 then 1 else 0

def vq (xs : List ℚ) (gs : List ArithmeticGate) : List ℚ :=
  gs.foldl (fun prior g => prior ++ [gevQ xs prior g]) []

def cq (gs : List ArithmeticGate) : List (Bool × ℕ) :=
  gs.foldl (fun prior g => prior ++ [gateComplexity prior g]) []

theorem vq_snoc (xs : List ℚ) (gs : List ArithmeticGate) (g : ArithmeticGate) :
    vq xs (gs ++ [g]) = vq xs gs ++ [gevQ xs (vq xs gs) g] := by
  simp [vq, List.foldl_append]

theorem cq_snoc (gs : List ArithmeticGate) (g : ArithmeticGate) :
    cq (gs ++ [g]) = cq gs ++ [gateComplexity (cq gs) g] := by
  simp [cq, List.foldl_append]

theorem vq_length (xs : List ℚ) (gs : List ArithmeticGate) : (vq xs gs).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => simp [vq_snoc, ih]

theorem cq_length (gs : List ArithmeticGate) : (cq gs).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => simp [cq_snoc, ih]

theorem getD_snoc {α : Type} (l : List α) (x d : α) (a : ℕ) :
    (l ++ [x]).getD a d = if a < l.length then l.getD a d else if a = l.length then x else d := by
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ h1]
  · subst h2; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem getD_ge {α : Type} (l : List α) (d : α) (a : ℕ) (h : l.length ≤ a) : l.getD a d = d :=
  List.getD_eq_default _ _ h

/-! ### The size predicate -/

/-- `PP Q W v e`: `v * Q^e` is an integer and `|v| ≤ 2^(e W)`. -/
def PP (Q W : ℕ) (v : ℚ) (e : ℕ) : Prop := (∃ z : ℤ, v * (Q : ℚ) ^ e = z) ∧ |v| ≤ 2 ^ (e * W)

section PPlemmas
variable {Q W : ℕ}

theorem PP_mono {v : ℚ} {e e' : ℕ} (h : PP Q W v e) (he : e ≤ e') : PP Q W v e' := by
  obtain ⟨⟨z, hz⟩, hb⟩ := h
  refine ⟨⟨z * (Q : ℤ) ^ (e' - e), ?_⟩, hb.trans ?_⟩
  · have : (Q : ℚ) ^ e' = (Q : ℚ) ^ e * (Q : ℚ) ^ (e' - e) := by
      rw [← pow_add]; congr 1; omega
    rw [this, ← mul_assoc, hz]; push_cast; ring
  · exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right _ he)

theorem PP_zero (e : ℕ) : PP Q W 0 e := ⟨⟨0, by simp⟩, by simp⟩

theorem PP_one (e : ℕ) : PP Q W 1 e :=
  ⟨⟨(Q : ℤ) ^ e, by simp⟩, by simp; exact one_le_pow₀ (by norm_num)⟩

theorem PP_add (hW : 1 ≤ W) {u v : ℚ} {e : ℕ} (hu : PP Q W u e) (hv : PP Q W v e) :
    PP Q W (u + v) (e + 1) := by
  obtain ⟨⟨z1, h1⟩, b1⟩ := hu
  obtain ⟨⟨z2, h2⟩, b2⟩ := hv
  refine ⟨⟨(z1 + z2) * Q, ?_⟩, ?_⟩
  · rw [pow_succ]; push_cast; rw [← h1, ← h2]; ring
  · calc |u + v| ≤ |u| + |v| := abs_add_le u v
      _ ≤ 2 ^ (e * W) + 2 ^ (e * W) := add_le_add b1 b2
      _ = 2 ^ (e * W) * 2 := by ring
      _ ≤ 2 ^ (e * W) * 2 ^ W := by
        gcongr; calc (2 : ℚ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ W := pow_le_pow_right₀ (by norm_num) hW
      _ = 2 ^ ((e + 1) * W) := by rw [← pow_add]; congr 1; ring

theorem PP_neg {v : ℚ} {e : ℕ} (hv : PP Q W v e) : PP Q W (-v) e := by
  obtain ⟨⟨z, h⟩, b⟩ := hv
  exact ⟨⟨-z, by push_cast; rw [← h]; ring⟩, by rwa [abs_neg]⟩

theorem PP_sub (hW : 1 ≤ W) {u v : ℚ} {e : ℕ} (hu : PP Q W u e) (hv : PP Q W v e) :
    PP Q W (u - v) (e + 1) := by
  rw [sub_eq_add_neg]; exact PP_add hW hu (PP_neg hv)

theorem PP_mul {u v : ℚ} {e1 e2 : ℕ} (hu : PP Q W u e1) (hv : PP Q W v e2) :
    PP Q W (u * v) (e1 + e2) := by
  obtain ⟨⟨z1, h1⟩, b1⟩ := hu
  obtain ⟨⟨z2, h2⟩, b2⟩ := hv
  refine ⟨⟨z1 * z2, ?_⟩, ?_⟩
  · push_cast; rw [← h1, ← h2, pow_add]; ring
  · rw [abs_mul, add_mul, pow_add]
    exact mul_le_mul b1 b2 (abs_nonneg _) (by positivity)

theorem PP_min {u v : ℚ} {e : ℕ} (hu : PP Q W u e) (hv : PP Q W v e) : PP Q W (min u v) e := by
  rcases min_choice u v with h | h <;> rw [h] <;> assumption

theorem PP_max {u v : ℚ} {e : ℕ} (hu : PP Q W u e) (hv : PP Q W v e) : PP Q W (max u v) e := by
  rcases max_choice u v with h | h <;> rw [h] <;> assumption

end PPlemmas

theorem getD_mem_or_zero (l : List ℚ) (i : ℕ) : l.getD i 0 ∈ l ∨ l.getD i 0 = 0 := by
  by_cases h : i < l.length
  · left; rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
  · right; exact List.getD_eq_default _ _ (by omega)

theorem pow_mul_le (ta M j : ℕ) (h : ta ≤ M) : 2 ^ ta * j ≤ 2 ^ M * j :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) h)

theorem gate_step {Q W : ℕ} (hW : 1 ≤ W) (xs : List ℚ) (hx : ∀ r ∈ xs, PP Q W r 1)
    (c : List (Bool × ℕ)) (p : List ℚ) (j : ℕ)
    (hp : ∀ a, PP Q W (p.getD a 0) (2 ^ (c.getD a (false, 0)).2 * j))
    (hf : ∀ a, (c.getD a (false, 0)).1 = false → PP Q W (p.getD a 0) 1)
    (g : ArithmeticGate) (hg : ∀ r, g = .constant r → PP Q W r 1) :
    PP Q W (gevQ xs p g) (2 ^ (gateComplexity c g).2 * (j + 1)) ∧
      ((gateComplexity c g).1 = false → PP Q W (gevQ xs p g) 1) := by
  have hpos : ∀ t : ℕ, 1 ≤ 2 ^ t := fun t => Nat.one_le_two_pow
  -- binary gates with max depth
  have hbin : ∀ (a b : ℕ) (v : ℚ), (PP Q W (p.getD a 0) (2 ^ max (c.getD a (false, 0)).2
      (c.getD b (false, 0)).2 * j) → PP Q W (p.getD b 0) (2 ^ max (c.getD a (false, 0)).2
      (c.getD b (false, 0)).2 * j) → PP Q W v (2 ^ max (c.getD a (false, 0)).2
      (c.getD b (false, 0)).2 * j + 1)) →
      PP Q W v (2 ^ max (c.getD a (false, 0)).2 (c.getD b (false, 0)).2 * (j + 1)) := by
    intro a b v h
    refine PP_mono (h (PP_mono (hp a) (pow_mul_le _ _ _ (le_max_left _ _)))
      (PP_mono (hp b) (pow_mul_le _ _ _ (le_max_right _ _)))) ?_
    have := hpos (max (c.getD a (false, 0)).2 (c.getD b (false, 0)).2)
    rw [Nat.mul_succ]; omega
  cases g with
  | input i =>
    refine ⟨?_, fun h => by simp [gateComplexity] at h⟩
    simp only [gevQ, gateComplexity, pow_zero, one_mul]
    rcases getD_mem_or_zero xs i with h | h
    · exact PP_mono (hx _ h) (by omega)
    · rw [h]; exact PP_zero _
  | constant r =>
    have := hg r rfl
    refine ⟨?_, fun _ => this⟩
    simp only [gevQ, gateComplexity, pow_zero, one_mul]
    exact PP_mono this (by omega)
  | add a b =>
    refine ⟨?_, fun h => by simp [gateComplexity] at h⟩
    simp only [gevQ, gateComplexity, ← List.getD_eq_getElem?_getD]
    exact hbin a b _ (fun h1 h2 => PP_add hW h1 h2)
  | sub a b =>
    refine ⟨?_, fun h => by simp [gateComplexity] at h⟩
    simp only [gevQ, gateComplexity, ← List.getD_eq_getElem?_getD]
    exact hbin a b _ (fun h1 h2 => PP_sub hW h1 h2)
  | minimum a b =>
    refine ⟨?_, fun h => by simp [gateComplexity] at h⟩
    simp only [gevQ, gateComplexity, ← List.getD_eq_getElem?_getD]
    exact hbin a b _ (fun h1 h2 => PP_mono (PP_min h1 h2) (by omega))
  | maximum a b =>
    refine ⟨?_, fun h => by simp [gateComplexity] at h⟩
    simp only [gevQ, gateComplexity, ← List.getD_eq_getElem?_getD]
    exact hbin a b _ (fun h1 h2 => PP_mono (PP_max h1 h2) (by omega))
  | test a b =>
    refine ⟨?_, fun h => by simp [gateComplexity] at h⟩
    simp only [gevQ]
    split_ifs
    · exact PP_one _
    · exact PP_zero _
  | mul a b =>
    refine ⟨?_, fun h => by simp [gateComplexity] at h⟩
    simp only [gevQ, gateComplexity, ← List.getD_eq_getElem?_getD]
    have ha := hp a
    have hb := hp b
    have hM := hpos (max (c.getD a (false, 0)).2 (c.getD b (false, 0)).2)
    have h1 := pow_mul_le (c.getD a (false, 0)).2 (max (c.getD a (false, 0)).2
      (c.getD b (false, 0)).2) j (le_max_left _ _)
    have h2 := pow_mul_le (c.getD b (false, 0)).2 (max (c.getD a (false, 0)).2
      (c.getD b (false, 0)).2) j (le_max_right _ _)
    by_cases hfl : ((c.getD a (false, 0)).1 && (c.getD b (false, 0)).1) = true
    · rw [if_pos hfl]
      refine PP_mono (PP_mul ha hb) ?_
      rw [pow_succ]
      nlinarith
    · rw [if_neg hfl, Nat.add_zero]
      simp only [Bool.and_eq_true, not_and_or, Bool.not_eq_true] at hfl
      rcases hfl with hfa | hfb
      · refine PP_mono (PP_mul (hf a hfa) hb) ?_
        rw [Nat.mul_succ]; omega
      · refine PP_mono (PP_mul ha (hf b hfb)) ?_
        rw [Nat.mul_succ]; omega

theorem bound {Q W : ℕ} (hW : 1 ≤ W) (xs : List ℚ) (hx : ∀ r ∈ xs, PP Q W r 1) :
    ∀ gs : List ArithmeticGate, (∀ r, ArithmeticGate.constant r ∈ gs → PP Q W r 1) →
      (∀ a, PP Q W ((vq xs gs).getD a 0) (2 ^ ((cq gs).getD a (false, 0)).2 * gs.length)) ∧
      (∀ a, ((cq gs).getD a (false, 0)).1 = false → PP Q W ((vq xs gs).getD a 0) 1) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro _; simp [vq, cq, PP_zero]
  | append_singleton gs g ih =>
    intro hc
    obtain ⟨ih1, ih2⟩ := ih (fun r hr => hc r (List.mem_append_left _ hr))
    have hst := gate_step hW xs hx (cq gs) (vq xs gs) gs.length ih1 ih2 g
      (fun r hr => hc r (by simp [hr]))
    simp only [vq_snoc, cq_snoc, List.length_append, List.length_singleton]
    constructor
    · intro a
      rw [getD_snoc, getD_snoc, vq_length, cq_length]
      split_ifs with h1 h2
      · exact PP_mono (ih1 a) (Nat.mul_le_mul_left _ (by omega))
      · exact hst.1
      · exact PP_zero _
    · intro a
      rw [getD_snoc, getD_snoc, vq_length, cq_length]
      split_ifs with h1 h2
      · exact ih2 a
      · exact hst.2
      · intro _; exact PP_zero _


/-! ### The budget does not change the gates of small depth -/


def vc (K : ℕ) (xs : List ℚ) (gs : List ArithmeticGate) : List ℚ :=
  gs.foldl (fun prior g => prior ++ [capv K (gevQ xs prior g)]) []

theorem vc_snoc (K : ℕ) (xs : List ℚ) (gs : List ArithmeticGate) (g : ArithmeticGate) :
    vc K xs (gs ++ [g]) = vc K xs gs ++ [capv K (gevQ xs (vc K xs gs) g)] := by
  simp [vc, List.foldl_append]

theorem vc_length (K : ℕ) (xs : List ℚ) (gs : List ArithmeticGate) :
    (vc K xs gs).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => simp [vc_snoc, ih]

theorem gev_congr (xs : List ℚ) (c : List (Bool × ℕ)) (p1 p2 : List ℚ) (S : ℕ)
    (g : ArithmeticGate) (hS : 2 ^ (gateComplexity c g).2 ≤ S)
    (h : ∀ a, 2 ^ (c.getD a (false, 0)).2 ≤ S → p1.getD a 0 = p2.getD a 0) :
    gevQ xs p1 g = gevQ xs p2 g := by
  have hle : ∀ t t' : ℕ, t ≤ t' → 2 ^ t' ≤ S → 2 ^ t ≤ S := fun t t' ht h' =>
    (Nat.pow_le_pow_right (by norm_num) ht).trans h'
  cases g with
  | input i => rfl
  | constant r => rfl
  | add a b =>
    simp only [gateComplexity, ← List.getD_eq_getElem?_getD] at hS
    simp only [gevQ]
    rw [h a (hle _ _ (le_max_left _ _) hS), h b (hle _ _ (le_max_right _ _) hS)]
  | sub a b =>
    simp only [gateComplexity, ← List.getD_eq_getElem?_getD] at hS
    simp only [gevQ]
    rw [h a (hle _ _ (le_max_left _ _) hS), h b (hle _ _ (le_max_right _ _) hS)]
  | minimum a b =>
    simp only [gateComplexity, ← List.getD_eq_getElem?_getD] at hS
    simp only [gevQ]
    rw [h a (hle _ _ (le_max_left _ _) hS), h b (hle _ _ (le_max_right _ _) hS)]
  | maximum a b =>
    simp only [gateComplexity, ← List.getD_eq_getElem?_getD] at hS
    simp only [gevQ]
    rw [h a (hle _ _ (le_max_left _ _) hS), h b (hle _ _ (le_max_right _ _) hS)]
  | test a b =>
    simp only [gateComplexity, ← List.getD_eq_getElem?_getD] at hS
    simp only [gevQ]
    rw [h a (hle _ _ (le_max_left _ _) hS), h b (hle _ _ (le_max_right _ _) hS)]
  | mul a b =>
    simp only [gateComplexity, ← List.getD_eq_getElem?_getD] at hS
    simp only [gevQ]
    rw [h a (hle _ _ ((le_max_left _ _).trans (Nat.le_add_right _ _)) hS),
      h b (hle _ _ ((le_max_right _ _).trans (Nat.le_add_right _ _)) hS)]

theorem budget (K S : ℕ) (xs : List ℚ) : ∀ gs : List ArithmeticGate,
    (∀ a < gs.length, 2 ^ ((cq gs).getD a (false, 0)).2 ≤ S →
      |(vq xs gs).getD a 0| ≤ 2 ^ K ∧ (((vq xs gs).getD a 0).den : ℚ) ≤ 2 ^ K) →
    ∀ a, 2 ^ ((cq gs).getD a (false, 0)).2 ≤ S → (vc K xs gs).getD a 0 = (vq xs gs).getD a 0 := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro _ a _; simp [vc, vq]
  | append_singleton gs g ih =>
    intro hfit
    have hfit' : ∀ a < gs.length, 2 ^ ((cq gs).getD a (false, 0)).2 ≤ S →
        |(vq xs gs).getD a 0| ≤ 2 ^ K ∧ (((vq xs gs).getD a 0).den : ℚ) ≤ 2 ^ K := by
      intro a ha hS
      have := hfit a (by simp; omega)
      simp only [vq_snoc, cq_snoc, getD_snoc, vq_length, cq_length, if_pos ha] at this
      exact this hS
    have ih' := ih hfit'
    intro a hS
    simp only [vc_snoc, vq_snoc, cq_snoc, getD_snoc, vq_length, cq_length, vc_length] at hS ⊢
    split_ifs at hS ⊢ with h1 h2
    · exact ih' a hS
    · have hj := hfit gs.length (by simp)
      simp only [vq_snoc, cq_snoc, getD_snoc, vq_length, cq_length, lt_irrefl, if_false,
        if_true] at hj
      have hfj := hj hS
      rw [gev_congr xs (cq gs) (vc K xs gs) (vq xs gs) S g hS ih']
      unfold capv
      rw [if_pos hfj]
    · rfl

section Final

/-! ### Real values and the rational fold -/

theorem getD_cast (l : List ℚ) (i : ℕ) :
    ((l.map (fun q : ℚ => (q : ℝ)))[i]?).getD 0 = ((l.getD i 0 : ℚ) : ℝ) := by
  rw [List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[i]? <;> simp

theorem gateEval_cast (xs prior : List ℚ) (g : ArithmeticGate) :
    gateEval (xs.map (fun q : ℚ => (q : ℝ))) (prior.map (fun q : ℚ => (q : ℝ))) g =
      ((gevQ xs prior g : ℚ) : ℝ) := by
  cases g with
  | input i => simp only [gateEval, gevQ, getD_cast]
  | constant r => rfl
  | add a b => simp only [gateEval, gevQ, getD_cast]; push_cast; rfl
  | sub a b => simp only [gateEval, gevQ, getD_cast]; push_cast; rfl
  | mul a b => simp only [gateEval, gevQ, getD_cast]; push_cast; rfl
  | minimum a b => simp only [gateEval, gevQ, getD_cast, Rat.cast_min]
  | maximum a b => simp only [gateEval, gevQ, getD_cast, Rat.cast_max]
  | test a b =>
    simp only [gateEval, gevQ, getD_cast, Rat.cast_lt]
    split_ifs <;> simp

theorem values_cast (xs : List ℚ) (gs : List ArithmeticGate) :
    gs.foldl (fun prior g => prior ++ [gateEval (xs.map (fun q : ℚ => (q : ℝ))) prior g]) [] =
      (vq xs gs).map (fun q : ℚ => (q : ℝ)) := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [List.foldl_append, ih, vq_snoc]
    simp [gateEval_cast]

theorem raw_repr (xs prior : List ℚ) (g : ArithmeticGate) : raw xs prior (repr g) = gevQ xs prior g := by
  cases g <;> simp [raw, repr, gevQ]

theorem evalAll_eq (K : ℕ) (xs : List ℚ) (gs : List ArithmeticGate) :
    evalAll K xs (gs.map repr) = vc K xs gs := by
  unfold evalAll vc
  rw [List.foldl_map]
  congr 1
  funext prior g
  simp [estep, raw_repr]

/-! ### Sizes -/

theorem mNat_len (n : ℕ) : (mNat n).length = 2 * n.size + 1 := by
  simp [NetworkEquilibriumCLS.LinearNash.encNat, Nat.size_eq_bits_len]
  ring

theorem mRat_len (r : ℚ) :
    (mRat r).length = 2 * r.num.natAbs.size + 2 * r.den.size + 3 := by
  simp [NetworkEquilibriumCLS.LinearNash.encRat, NetworkEquilibriumCLS.LinearNash.encInt, mNat_len]
  ring

theorem den_lt_len (r : ℚ) : r.den < 2 ^ (mRat r).length := by
  calc r.den < 2 ^ r.den.size := Nat.lt_size_self _
    _ ≤ 2 ^ (mRat r).length := Nat.pow_le_pow_right (by norm_num) (by rw [mRat_len]; omega)

theorem abs_le_len (r : ℚ) : |r| ≤ 2 ^ (mRat r).length := by
  have h1 : |r| ≤ (r.num.natAbs : ℚ) := by
    have e : (r.num.natAbs : ℚ) = |r| * r.den := by
      rw [Nat.cast_natAbs, Int.cast_abs, ← Rat.mul_den_eq_num, abs_mul]
      simp
    rw [e]
    have : (1 : ℚ) ≤ r.den := by exact_mod_cast r.den_pos
    nlinarith [abs_nonneg r]
  have h2 : r.num.natAbs < 2 ^ (mRat r).length := by
    calc r.num.natAbs < 2 ^ r.num.natAbs.size := Nat.lt_size_self _
      _ ≤ 2 ^ (mRat r).length := Nat.pow_le_pow_right (by norm_num) (by rw [mRat_len]; omega)
  have h3 : (r.num.natAbs : ℚ) ≤ 2 ^ (mRat r).length := by exact_mod_cast h2.le
  linarith

theorem prod_den_le (l : List ℚ) :
    (l.map (fun r => r.den)).prod ≤ 2 ^ ((l.map (fun r => (mRat r).length)).sum) := by
  induction l with
  | nil => simp
  | cons r l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add]
    exact Nat.mul_le_mul (den_lt_len r).le ih

def constOf : ArithmeticGate → List ℚ
  | .constant r => [r]
  | _ => []

def consts (gs : List ArithmeticGate) : List ℚ := gs.flatMap constOf

theorem mem_consts {gs : List ArithmeticGate} {r : ℚ} (h : ArithmeticGate.constant r ∈ gs) :
    r ∈ consts gs := by
  unfold consts
  rw [List.mem_flatMap]
  exact ⟨_, h, by simp [constOf]⟩

theorem consts_sum (gs : List ArithmeticGate) :
    ((consts gs).map (fun r => (mRat r).length)).sum ≤ (gs.flatMap gateCode).length := by
  induction gs with
  | nil => simp [consts]
  | cons g gs ih =>
    simp only [consts, List.flatMap_cons, List.map_append, List.sum_append,
      List.length_append] at ih ⊢
    have : ((constOf g).map (fun r => (mRat r).length)).sum ≤ (gateCode g).length := by
      cases g <;> simp [constOf, gateCode]
    omega

theorem xs_sum (xs : List ℚ) :
    (xs.map (fun r => (mRat r).length)).sum ≤ (mList mRat xs).length := by
  simp [NetworkEquilibriumCLS.LinearNash.encList, List.length_flatMap]

theorem length_le_flatMap {β : Type} (code : β → List Bool) (hne : ∀ b, code b ≠ [])
    (xs : List β) : xs.length ≤ (xs.flatMap code).length := by
  rw [List.length_flatMap]
  induction xs with
  | nil => simp
  | cons y ys ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have := List.length_pos_iff.mpr (hne y)
    omega

theorem den_le_of_PP {Q W : ℕ} (hQ : 1 ≤ Q) {v : ℚ} {e : ℕ} (h : PP Q W v e) :
    v.den ≤ Q ^ e := by
  obtain ⟨⟨z, hz⟩, _⟩ := h
  have hm : (0 : ℤ) < (Q : ℤ) ^ e := by positivity
  have hv : v = Rat.divInt z ((Q : ℤ) ^ e) := by
    rw [Rat.divInt_eq_div, ← hz]
    push_cast
    field_simp
  have hd := Rat.den_dvd z ((Q : ℤ) ^ e)
  rw [← hv] at hd
  have := Int.le_of_dvd hm hd
  exact_mod_cast this

/-! ### Assembly -/

theorem ofFn_getD {outs : ℕ} (l : List ℕ) (hl : l.length = outs) (f : ℕ → ℚ) :
    List.ofFn (fun j : Fin outs => f (l.getD j 0)) = l.map f := by
  subst hl
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem E_spec (C : Circ) (ins outs : ℕ) (hC : C.Valid ins outs) (x : Fin ins → ℚ) :
    ∃ q : Fin outs → ℚ, E (encCirc C ++ encVector x) = encVector q ∧
      ∀ j, (q j : ℝ) = C.eval (rpt x) j := by
  set xsL := List.ofFn x with hxsL
  set w := encCirc C ++ encVector x with hw
  set n := w.length with hn
  set K := n ^ 3 with hK
  set L := C.gates.length with hL
  set S := (mList gateCode C.gates).length with hS
  -- parsing
  have hE : E w = printL (C.outputs.map (fun o => (vc K xsL C.gates).getD o 0)) := by
    have h1 : rList rGate w = (C.gates.map repr, mList mNat C.outputs ++ encVector x) := by
      rw [hw, encCirc, List.append_assoc]
      exact rList_enc rGate gateCode repr rGate_enc gateCode_ne _ _
    have h2 : rList rNat (mList mNat C.outputs ++ encVector x) = (C.outputs, encVector x) := by
      have := rList_enc rNat mNat id rNat_enc encNat_ne C.outputs (encVector x)
      simpa using this
    have h3 : rList rRat (encVector x) = (xsL, []) := by
      have := rList_enc rRat mRat id rRat_enc encRat_ne xsL []
      simpa [encVector] using this
    simp only [E, h1, h2, h3, ← hn, ← hK, evalAll_eq]
  -- sizes
  have hnS : S + (mList mRat xsL).length ≤ n := by
    have hv : encVector x = mList mRat xsL := rfl
    rw [hn, hw, encCirc, hv]
    simp only [List.length_append]
    omega
  have hLS : L ≤ (C.gates.flatMap gateCode).length := length_le_flatMap gateCode gateCode_ne _
  have hSflat : (mNat L).length + (C.gates.flatMap gateCode).length = S := by
    rw [hS, hL]; simp [NetworkEquilibriumCLS.LinearNash.encList]
  have hn1 : 1 ≤ n := by
    have := mNat_len L
    omega
  set R := consts C.gates ++ xsL with hR
  have hsumR : (R.map (fun r => (mRat r).length)).sum ≤ n := by
    have := consts_sum C.gates
    have := xs_sum xsL
    simp only [hR, List.map_append, List.sum_append]
    omega
  set Q := (R.map (fun r => r.den)).prod with hQ
  have hQ1 : 1 ≤ Q := by
    show 0 < Q
    apply List.prod_pos
    intro a ha
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp ha
    exact r.den_pos
  have hQn : Q ≤ 2 ^ n :=
    (prod_den_le R).trans (Nat.pow_le_pow_right (by norm_num) hsumR)
  have hPR : ∀ r ∈ R, PP Q n r 1 := by
    intro r hr
    constructor
    · have hd : r.den ∣ Q := List.dvd_prod (List.mem_map.mpr ⟨r, hr, rfl⟩)
      obtain ⟨k, hk⟩ := hd
      refine ⟨r.num * k, ?_⟩
      rw [pow_one, hk]
      push_cast
      rw [← mul_assoc, Rat.mul_den_eq_num]
    · have hle : (mRat r).length ≤ n := by
        exact (List.le_sum_of_mem (List.mem_map.mpr ⟨r, hr, rfl⟩)).trans hsumR
      calc |r| ≤ 2 ^ (mRat r).length := abs_le_len r
        _ ≤ 2 ^ (1 * n) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hbd := (bound hn1 xsL (fun r hr => hPR r (List.mem_append_right _ hr)) C.gates
    (fun r hr => hPR r (List.mem_append_left _ (mem_consts hr)))).1
  have hfit : ∀ a < C.gates.length, 2 ^ ((cq C.gates).getD a (false, 0)).2 ≤ S →
      |(vq xsL C.gates).getD a 0| ≤ 2 ^ K ∧ (((vq xsL C.gates).getD a 0).den : ℚ) ≤ 2 ^ K := by
    intro a _ ha
    have hP := hbd a
    have he : 2 ^ ((cq C.gates).getD a (false, 0)).2 * C.gates.length ≤ n * n :=
      Nat.mul_le_mul (by omega) (by omega)
    constructor
    · calc |(vq xsL C.gates).getD a 0|
          ≤ 2 ^ (2 ^ ((cq C.gates).getD a (false, 0)).2 * C.gates.length * n) := hP.2
        _ ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) (by
            rw [hK]; calc _ ≤ n * n * n := Nat.mul_le_mul_right _ he
              _ = n ^ 3 := by ring)
    · have hden := den_le_of_PP hQ1 hP
      have : ((vq xsL C.gates).getD a 0).den ≤ 2 ^ K := by
        calc _ ≤ Q ^ (2 ^ ((cq C.gates).getD a (false, 0)).2 * C.gates.length) := hden
          _ ≤ (2 ^ n) ^ (2 ^ ((cq C.gates).getD a (false, 0)).2 * C.gates.length) :=
            Nat.pow_le_pow_left hQn _
          _ = 2 ^ (n * (2 ^ ((cq C.gates).getD a (false, 0)).2 * C.gates.length)) := by
            rw [← pow_mul]
          _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by
            rw [hK]; calc _ ≤ n * (n * n) := Nat.mul_le_mul_left _ he
              _ = n ^ 3 := by ring)
      exact_mod_cast this
  have hout : ∀ o ∈ C.outputs, (vc K xsL C.gates).getD o 0 = (vq xsL C.gates).getD o 0 := by
    intro o ho
    apply budget K S xsL C.gates hfit
    have := (hC.2.2 o ho).2
    simpa [Circ.complexities, cq, List.getD_eq_getElem?_getD] using this
  refine ⟨fun j => (vq xsL C.gates).getD (C.outputs.getD j 0) 0, ?_, ?_⟩
  · rw [hE, encVector, ofFn_getD C.outputs hC.2.1 (fun o => (vq xsL C.gates).getD o 0),
      List.map_congr_left hout]
    rfl
  · intro j
    have hrpt : List.ofFn (rpt x) = xsL.map (fun q : ℚ => (q : ℝ)) := by
      rw [hxsL, List.map_ofFn]; rfl
    simp only [Circ.eval, Circ.values, hrpt, values_cast, getD_cast, List.getD_eq_getElem?_getD]

end Final
end NadlerCLS.CircEval

open NadlerCLS NetworkEquilibriumCLS.LinearNash in
theorem solution :
    ∃ E : List Bool → List Bool,
      Turing.MultiTapeTM.ComputableInPolyTime E Turing.MultiTapeTM.encBits
        Turing.MultiTapeTM.encBits ∧
      ∀ (C : Circ) (ins outs : ℕ), C.Valid ins outs → ∀ x : Fin ins → ℚ,
        ∃ q : Fin outs → ℚ, E (encCirc C ++ encVector x) = encVector q ∧
          ∀ j, (q j : ℝ) = C.eval (rpt x) j :=
  ⟨NadlerCLS.CircEval.E, NadlerCLS.CircEval.E_poly, NadlerCLS.CircEval.E_spec⟩
