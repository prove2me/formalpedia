-- Prove2me | solution 1 for IntMul.Kappa.R6.Leaf.fineNeed6_all
-- status  : ACCEPTED   (prove)
-- author  : @Ethan
-- created : 2026-10-21T05:24:49.997987+00:00
-- url     : https://prove2.me/submissions/4770b4b3-550f-402c-9361-c500a9951bbd

import Definitions.Def_IntMul_Kappa_R6_Defs70
import Theorems.Thm_NLogN_KFUU_R6Fine_fineE_runs
import Theorems.Thm_NLogN_KFUU_R6Fine_coreF_runs
import Theorems.Thm_NLogN_KFUU_R6Fine_coreB_runs
import Theorems.Thm_NLogN_KFUU_R6Fine_cTot_le
import Theorems.Thm_AModel_getElem_pull
import Theorems.Thm_AModel_decode_encode

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 20000

namespace AModel
lemma encode_decode {sh : Shape} {m : ℕ} (h : m < vol sh) : encode sh (decode sh m) = m := by
  induction sh generalizing m with
  | nil => simp at h; subst h; rfl
  | cons q sh ih =>
    simp only [vol_cons] at h
    have hV : 0 < vol sh := Nat.pos_of_ne_zero (by rintro h'; simp [h'] at h)
    have hq : m / vol sh < q := (Nat.div_lt_iff_lt_mul hV).2 h
    simp only [decode, encode, List.headD_cons, List.tail_cons, Nat.mod_eq_of_lt hq,
      ih (Nat.mod_lt m hV)]
    exact Nat.div_add_mod' m (vol sh)
end AModel

namespace IntMul.HvdH.RefPf
open IntMul.HvdH IntMul.HvdH.Ref

section lists
variable {α : Type*}

lemma flatten_getD_uniform (n : ℕ) (d : α) : ∀ (rows : List (List α)),
    (∀ row ∈ rows, row.length = n) → ∀ c < rows.length, ∀ a < n,
    rows.flatten.getD (c * n + a) d = (rows.getD c []).getD a d
  | [], _, c, hc, _, _ => by simp at hc
  | row :: rows, h, c, hc, a, ha => by
    have hrow : row.length = n := h row (by simp)
    rcases c with _ | c
    · simp only [List.flatten_cons, zero_mul, zero_add, List.getD_cons_zero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD]
    · simp only [List.flatten_cons, List.getD_cons_succ]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hrow]; nlinarith),
        ← List.getD_eq_getElem?_getD, hrow]
      have : (c + 1) * n + a - n = c * n + a := by rw [add_mul, one_mul]; omega
      rw [this]
      exact flatten_getD_uniform n d rows (fun r hr => h r (by simp [hr])) c
        (by simp at hc; omega) a ha

lemma transposeL_length [Inhabited α] (n m : ℕ) (L : List α) : (transposeL n m L).length = m * n := by
  simp [transposeL]

lemma transposeL_getD [Inhabited α] (n m : ℕ) (L : List α) (q : ℕ) (hq : q < m * n) :
    (transposeL n m L).getD q default = L.getD ((q % n) * m + q / n) default := by
  rw [List.getD_eq_getElem _ _ (by rw [transposeL_length]; exact hq)]
  simp [transposeL]

end lists

end IntMul.HvdH.RefPf


namespace NLogN.KFB
open IntMul RS AModel KIL KFD Complex
theorem getD_gflat (zs : List GI) (J : ℕ) :
    (gflat zs).getD J 0 = if J % 2 = 0 then (zs.getD (J / 2) 0).1 else (zs.getD (J / 2) 0).2 := by
  induction zs generalizing J with
  | nil => simp
  | cons z zs ih =>
    rcases J with _ | _ | J
    · simp
    · simp
    · rw [gflat_cons, List.getD_cons_succ, List.getD_cons_succ, ih,
        show (J + 1 + 1) / 2 = J / 2 + 1 by omega, List.getD_cons_succ,
        show (J + 1 + 1) % 2 = J % 2 by omega]
end NLogN.KFB

namespace NLogN.KFUU
open IntMul KIL KFB KFC KFT KFU AModel AModelL12
theorem zsz_le_size' (n : ℕ) : zsz (n : ℤ) ≤ Nat.size n :=
  zsz_le_of_lt (by simpa using Nat.lt_size_self n)
end NLogN.KFUU

namespace NLogN.KFUU.R6Fine

open IntMul AModel NLogN.KFB IntMul.Kappa.R6

/-! ## Generic pull facts -/

theorem getD_pull_enc {α : Type*} {S B : Shape} (g : List ℕ → List ℕ) (d : α) (xs : List α)
    {b : List ℕ} (hb : Valid B b) :
    (pull S B g d xs).getD (encode B b) d = xs.getD (encode S (g b)) d := by
  rw [List.getD_eq_getElem _ _ (by simpa using encode_lt hb), getElem_pull, decode_encode hb]

theorem ext_enc {α : Type*} {B : Shape} {X Y : List α} (d : α) (hX : X.length = vol B)
    (hY : Y.length = vol B) (h : ∀ b, Valid B b → X.getD (encode B b) d = Y.getD (encode B b) d) :
    X = Y := by
  apply List.ext_getElem (by rw [hX, hY])
  intro j h1 h2
  have hj : j < vol B := by rwa [hX] at h1
  have := h _ (valid_decode hj)
  rw [encode_decode hj, List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
  exact this

theorem valid5 {s0 s1 s2 s3 s4 : ℕ} {b : List ℕ} (h : Valid [s0, s1, s2, s3, s4] b) :
    ∃ b0 b1 b2 b3 b4, b = [b0, b1, b2, b3, b4] ∧ b0 < s0 ∧ b1 < s1 ∧ b2 < s2 ∧ b3 < s3 ∧
      b4 < s4 := by
  rcases h with _ | ⟨h0, h⟩
  rcases h with _ | ⟨h1, h⟩
  rcases h with _ | ⟨h2, h⟩
  rcases h with _ | ⟨h3, h⟩
  rcases h with _ | ⟨h4, h⟩
  rcases h with _ | _
  exact ⟨_, _, _, _, _, rfl, h0, h1, h2, h3, h4⟩

theorem enc4 (s0 s1 s2 s3 b0 b1 b2 b3 : ℕ) :
    encode [s0, s1, s2, s3] [b0, b1, b2, b3] = ((b0 * s1 + b1) * s2 + b2) * s3 + b3 := by
  simp [encode, vol]; ring

theorem enc5 (s0 s1 s2 s3 s4 b0 b1 b2 b3 b4 : ℕ) :
    encode [s0, s1, s2, s3, s4] [b0, b1, b2, b3, b4] =
      (((b0 * s1 + b1) * s2 + b2) * s3 + b3) * s4 + b4 := by
  simp [encode, vol]; ring

/-! ## The stage maps -/

/-! ## The first stages -/

/-! ## The blockwise transpose -/

theorem length_blkT (m k a : ℕ) (zs : List GI) : (blkT m k a zs).length = a * (m * k) := by
  unfold blkT
  rw [List.length_flatMap]
  simp only [IntMul.HvdH.RefPf.transposeL_length, List.map_const', List.length_range,
    List.sum_replicate, smul_eq_mul]
  ring

theorem getD_blkT (m k a : ℕ) (zs : List GI) {i r l : ℕ} (hi : i < a) (hr : r < k) (hl : l < m) :
    (blkT m k a zs).getD (i * (m * k) + (r * m + l)) 0 = zs.getD (i * (m * k) + (l * k + r)) 0 := by
  have hq : r * m + l < m * k := by
    have : (r + 1) * m ≤ k * m := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at this; rw [Nat.mul_comm m k]; omega
  unfold blkT
  rw [List.flatMap_def]
  have hrows : ∀ row ∈ (List.range a).map (fun i => IntMul.HvdH.Ref.transposeL m k
      ((zs.drop (i * (m * k))).take (m * k))), row.length = m * k := by
    intro row hrow
    simp only [List.mem_map] at hrow
    obtain ⟨_, _, rfl⟩ := hrow
    rw [IntMul.HvdH.RefPf.transposeL_length, Nat.mul_comm]
  rw [IntMul.HvdH.RefPf.flatten_getD_uniform (m * k) 0 _ hrows i (by simpa using hi) _ hq]
  have hrow : ((List.range a).map (fun i => IntMul.HvdH.Ref.transposeL m k
      ((zs.drop (i * (m * k))).take (m * k)))).getD i [] =
      IntMul.HvdH.Ref.transposeL m k ((zs.drop (i * (m * k))).take (m * k)) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp
  rw [hrow]
  have ht := IntMul.HvdH.RefPf.transposeL_getD m k ((zs.drop (i * (m * k))).take (m * k)) _
    (by rw [Nat.mul_comm k m]; exact hq)
  have e1 : (r * m + l) % m = l := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
  have e2 : (r * m + l) / m = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hl, zero_add]
  rw [e1, e2] at ht
  have hlk : l * k + r < m * k := by
    have : (l + 1) * k ≤ m * k := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at this; omega
  have hd : ((zs.drop (i * (m * k))).take (m * k)).getD (l * k + r) (default : GI) =
      zs.getD (i * (m * k) + (l * k + r)) default := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, if_pos hlk]
  exact ht.trans hd

theorem getD_gflat2 (zs : List GI) (q c : ℕ) (hc : c < 2) :
    (gflat zs).getD (q * 2 + c) 0 = if c = 0 then (zs.getD q 0).1 else (zs.getD q 0).2 := by
  rw [getD_gflat]
  have e1 : (q * 2 + c) % 2 = c := by omega
  have e2 : (q * 2 + c) / 2 = q := by omega
  rw [e1, e2]

theorem gflat_len (zs : List GI) : (gflat zs).length = 2 * zs.length := by
  induction zs with
  | nil => rfl
  | cons z zs ih => rw [gflat_cons]; simp only [List.length_cons, ih]; ring

theorem stF_end (a N y : ℕ) (zs : List GI) :
    stF a N y 1 N (gflat zs) = gflat (blkT N y a zs) := by
  apply ext_enc (B := [a, 1, y, N, 2]) (0 : ℤ) (by simp)
    (by rw [gflat_len, length_blkT]; simp only [vol, List.prod_cons, List.prod_nil]; ring)
  intro b hb
  obtain ⟨i, h, r, l, c, rfl, hi, hh, hr, hl, hc⟩ := valid5 hb
  obtain rfl : h = 0 := by omega
  unfold stF
  rw [getD_pull_enc _ _ _ hb]
  simp only [gF, List.getD_cons_zero, List.getD_cons_succ]
  rw [enc4, enc5]
  have e1 : ((i * N + (0 * N + l)) * y + r) * 2 + c = (i * (N * y) + (l * y + r)) * 2 + c := by ring
  have e2 : (((i * 1 + 0) * y + r) * N + l) * 2 + c = (i * (N * y) + (r * N + l)) * 2 + c := by ring
  rw [e1, e2, getD_gflat2 _ _ _ hc, getD_gflat2 _ _ _ hc, getD_blkT N y a zs hi hr hl]

theorem stB_end (a N y : ℕ) (zs : List GI) :
    stB a N y N 1 (gflat zs) = gflat (blkT y N a zs) := by
  apply ext_enc (B := [a, N, y, 1, 2]) (0 : ℤ) (by simp)
    (by rw [gflat_len, length_blkT]; simp only [vol, List.prod_cons, List.prod_nil]; ring)
  intro b hb
  obtain ⟨i, h, r, l, c, rfl, hi, hh, hr, hl, hc⟩ := valid5 hb
  obtain rfl : l = 0 := by omega
  unfold stB
  rw [getD_pull_enc _ _ _ hb]
  simp only [gB, List.getD_cons_zero, List.getD_cons_succ]
  rw [enc4, enc5]
  have e1 : ((i * y + r) * N + (h * 1 + 0)) * 2 + c = (i * (y * N) + (r * N + h)) * 2 + c := by ring
  have e2 : (((i * N + h) * y + r) * 1 + 0) * 2 + c = (i * (y * N) + (h * y + r)) * 2 + c := by ring
  rw [e1, e2, getD_gflat2 _ _ _ hc, getD_gflat2 _ _ _ hc, getD_blkT y N a zs hi hh hr]



open IntMul KIL KFB KFC KFT KFU AModel AModelL12 NLogN.KFUU IntMul.Kappa.R6

/-! ## Arithmetic -/

theorem size_two_mul_le (V : ℕ) : Nat.size (2 * V) ≤ Nat.size V + 1 := by
  rw [Nat.size_le]
  have := Nat.lt_size_self V
  rw [pow_succ]; omega

/-! ## One exposure on the managed state -/

section Gen

variable {P : ℕ} {I : List Sym} {iprog : Fin P → IStmt HS P}

theorem gflat_len' (zs : List GI) {a f y : ℕ} (h : zs.length = a * (2 ^ f * y)) :
    (gflat zs).length = vol [a, 2 ^ f, y, 2] := by
  rw [gflat_len, h]; simp only [vol, List.prod_cons, List.prod_nil]; ring

theorem gflat_len'' (zs : List GI) {a f y : ℕ} (h : zs.length = a * (2 ^ f * y)) :
    (gflat zs).length = vol [a, y, 2 ^ f, 2] := by
  rw [gflat_len, h]; simp only [vol, List.prod_cons, List.prod_nil]; ring

/-- The facts shared by both directions. -/
theorem fine_facts (w f a y : ℕ) (hy : 1 ≤ y) :
    2 ≤ Nat.size (a * 2 ^ f * y) + 2 ∧
    zsz ((2 * (a * 2 ^ f * y) : ℕ) : ℤ) ≤ Nat.size (a * 2 ^ f * y) + 2 ∧
    zsz (w : ℤ) ≤ Nat.size (a * 2 ^ f * y) + w + f + 4 ∧
    zsz (f : ℤ) ≤ Nat.size (a * 2 ^ f * y) + w + f + 4 ∧
    zsz (a : ℤ) ≤ Nat.size (a * 2 ^ f * y) + w + f + 4 := by
  have haV : a ≤ a * 2 ^ f * y := by
    have : a * 1 * 1 ≤ a * 2 ^ f * y := Nat.mul_le_mul (Nat.mul_le_mul_left _ Nat.one_le_two_pow) hy
    simpa using this
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · have := zsz_le_size' (2 * (a * 2 ^ f * y)); have := size_two_mul_le (a * 2 ^ f * y); omega
  · have := KFC.zsz_nat_le w; omega
  · have := KFC.zsz_nat_le f; omega
  · have := zsz_le_size' a; have := Nat.size_le_size haV; omega

set_option maxHeartbeats 8000000 in
theorem fineRun_F (w f a y : ℕ) (s : IState HS) (F : Fin HS → List ℤ) (zs : List GI) (l : List ℤ)
    (hF : ∀ j, j ≠ 0 → j ≠ dP → F j = []) (hd : F dP = descFine w f a y)
    (h0 : F 0 = gflat zs ++ l) (hy : 1 ≤ y) (hlen : zs.length = a * (2 ^ f * y)) (hgb : GB w zs) :
    IRuns I iprog (fineE coreF) (encK s F)
      (encK s (Function.update F 0 (gflat (blkT (2 ^ f) y a zs) ++ l)))
      (cCore w f (a * 2 ^ f * y) (Nat.size (a * 2 ^ f * y) + 2) +
        6 * cU (Nat.size (a * 2 ^ f * y) + w + f + 4) + 26) := by
  obtain ⟨hZ2, hVZ, zw, zf, za⟩ := fine_facts w f a y hy
  set t := encK s F with ht
  have hdP : t.G dP = .int (w : ℤ) :: .int (f : ℤ) :: .int (a : ℤ) :: (.int (y : ℤ) :: s.G dP) := by
    simp [t, hd, descFine, ints]
  have ht0 : t.G 0 = ints (gflat zs) ++ (ints l ++ s.G 0) := by
    simp [t, h0, ints]
  set X0 := ints (gflat (blkT (2 ^ f) y a zs)) ++ (ints l ++ s.G 0) with hX0
  have H := fineE_runs (I := I) (iprog := iprog) coreF w f a (Nat.size (a * 2 ^ f * y) + w + f + 4) t
    (.int (y : ℤ) :: s.G dP) hdP zw zf za X0
    (cCore w f (a * 2 ^ f * y) (Nat.size (a * 2 ^ f * y) + 2)) ?_ ?_
  · refine H.mono' ?_ le_rfl
    refine IState.ext' (fun j => ?_) rfl rfl
    by_cases e : j = 0
    · subst e; simp [t, X0, ints]
    · simp [t, e]
  · intro ha
    have Hc := coreF_runs (I := I) (iprog := iprog) a f y w (Nat.size (a * 2 ^ f * y) + 2) ha hy hZ2 hVZ
      (gflat zs) (gflat_len' zs hlen) hgb.bnd
      ((((t.upd dP (.int (y : ℤ) :: s.G dP)).upd rW (.int (w : ℤ) :: t.G rW)).upd
        rU (.int (f : ℤ) :: t.G rU)).upd rCZ (.int (a : ℤ) :: t.G rCZ))
      (ints l ++ s.G 0) (s.G dP) (t.G rCZ) (t.G rU)
      (by simp +decide [ht0]) (by simp +decide) (by simp +decide) (by simp +decide)
    rw [stF_end] at Hc
    exact Hc
  · intro ha
    subst ha
    have hz : zs = [] := List.eq_nil_of_length_eq_zero (by rw [hlen]; simp)
    subst hz
    simp [X0, ht0, blkT, gflat]

set_option maxHeartbeats 8000000 in
theorem fineRun_B (w f a y : ℕ) (s : IState HS) (F : Fin HS → List ℤ) (zs : List GI) (l : List ℤ)
    (hF : ∀ j, j ≠ 0 → j ≠ dP → F j = []) (hd : F dP = descFine w f a y)
    (h0 : F 0 = gflat zs ++ l) (hy : 1 ≤ y) (hlen : zs.length = a * (2 ^ f * y)) (hgb : GB w zs) :
    IRuns I iprog (fineE coreB) (encK s F)
      (encK s (Function.update F 0 (gflat (blkT y (2 ^ f) a zs) ++ l)))
      (cCore w f (a * 2 ^ f * y) (Nat.size (a * 2 ^ f * y) + 2) +
        6 * cU (Nat.size (a * 2 ^ f * y) + w + f + 4) + 26) := by
  obtain ⟨hZ2, hVZ, zw, zf, za⟩ := fine_facts w f a y hy
  set t := encK s F with ht
  have hdP : t.G dP = .int (w : ℤ) :: .int (f : ℤ) :: .int (a : ℤ) :: (.int (y : ℤ) :: s.G dP) := by
    simp [t, hd, descFine, ints]
  have ht0 : t.G 0 = ints (gflat zs) ++ (ints l ++ s.G 0) := by
    simp [t, h0, ints]
  set X0 := ints (gflat (blkT y (2 ^ f) a zs)) ++ (ints l ++ s.G 0) with hX0
  have H := fineE_runs (I := I) (iprog := iprog) coreB w f a (Nat.size (a * 2 ^ f * y) + w + f + 4) t
    (.int (y : ℤ) :: s.G dP) hdP zw zf za X0
    (cCore w f (a * 2 ^ f * y) (Nat.size (a * 2 ^ f * y) + 2)) ?_ ?_
  · refine H.mono' ?_ le_rfl
    refine IState.ext' (fun j => ?_) rfl rfl
    by_cases e : j = 0
    · subst e; simp [t, X0, ints]
    · simp [t, e]
  · intro ha
    have Hc := coreB_runs (I := I) (iprog := iprog) a f y w (Nat.size (a * 2 ^ f * y) + 2) ha hy hZ2 hVZ
      (gflat zs) (gflat_len'' zs hlen) hgb.bnd
      ((((t.upd dP (.int (y : ℤ) :: s.G dP)).upd rW (.int (w : ℤ) :: t.G rW)).upd
        rU (.int (f : ℤ) :: t.G rU)).upd rCZ (.int (a : ℤ) :: t.G rCZ))
      (ints l ++ s.G 0) (s.G dP) (t.G rCZ) (t.G rU)
      (by simp +decide [ht0]) (by simp +decide) (by simp +decide) (by simp +decide)
    rw [stB_end] at Hc
    exact Hc
  · intro ha
    subst ha
    have hz : zs = [] := List.eq_nil_of_length_eq_zero (by rw [hlen]; simp)
    subst hz
    simp [X0, ht0, blkT, gflat]

end Gen

/-! ## `FineNeed6` -/

theorem cTot_real (w f a y : ℕ) :
    ((cCore w f (a * 2 ^ f * y) (Nat.size (a * 2 ^ f * y) + 2) +
        6 * cU (Nat.size (a * 2 ^ f * y) + w + f + 4) + 26 + 2 : ℕ) : ℝ) ≤
      (C0fine : ℝ) * cFine w f a y := by
  have h := cTot_le w f (a * 2 ^ f * y)
  unfold cTot at h
  calc ((cCore w f (a * 2 ^ f * y) (Nat.size (a * 2 ^ f * y) + 2) +
        6 * cU (Nat.size (a * 2 ^ f * y) + w + f + 4) + 26 + 2 : ℕ) : ℝ)
      ≤ ((C0fine * ((w + 1) * (a * 2 ^ f * y + 1) * (f + 1) +
          (Nat.size (a * 2 ^ f * y) + w + f + 4) ^ 2) : ℕ) : ℝ) := by exact_mod_cast h
    _ = (C0fine : ℝ) * cFine w f a y := by
      unfold cFine
      generalize Nat.size (a * 2 ^ f * y) = S
      generalize a * 2 ^ f * y = V
      generalize C0fine = K
      push_cast
      ring

theorem fineU6 (tab : Fin 1 → IStmt HS 1) : FineU6 tab := by
  refine ⟨2, fineU, 0, 1, dP, (C0fine : ℝ), by decide, Nat.cast_nonneg _, ?_⟩
  intro E ext idx hidx Isym w f a y s F zs l hF hd h0 hy hlen hgb
  have e0 : IL.kTableP tab ext (idx 0) = fineE coreF := by rw [hidx 0]; simp [fineU]
  have e1 : IL.kTableP tab ext (idx 1) = fineE coreB := by rw [hidx 1]; simp [fineU]
  refine ⟨⟨_, ?_, cTot_real w f a y⟩, ⟨_, ?_, cTot_real w f a y⟩⟩
  · apply IRuns.call
    rw [e0]
    exact fineRun_F w f a y s F zs l hF hd h0 hy hlen hgb
  · apply IRuns.call
    rw [e1]
    exact fineRun_B w f a y s F zs l hF hd h0 hy hlen hgb

/-- **`FineNeed6`** for every parameter record. -/
theorem fineNeed6_all : ∀ P : Prm, P.Ok → FineNeed6 P :=
  fun _ _ tab _ _ => fineU6 tab

end NLogN.KFUU.R6Fine

open IntMul.Kappa.R6
open NLogN.KFUU.R6Fine

theorem solution (P : Prm) (hP : P.Ok) : FineNeed6 P :=
  fineNeed6_all P hP
