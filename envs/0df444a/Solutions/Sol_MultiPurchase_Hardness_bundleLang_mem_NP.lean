-- Prove2me | solution 1 for MultiPurchase.Hardness.bundleLang_mem_NP
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T03:53:37.555729+00:00
-- url     : https://prove2.me/submissions/7f51591e-0d9f-4f4b-84cb-a16936a4fb92
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model
import Definitions.Def_MultiPurchase_Hardness_Checker
import Theorems.Thm_MultiPurchase_Hardness_shape_filter_polytime
import Theorems.Thm_MultiPurchase_Hardness_canon_filter_polytime
import Theorems.Thm_MultiPurchase_Hardness_rev_check_polytime
import Theorems.Thm_CookPvsNP_mem_P_of_polyReducible
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp

set_option autoImplicit false

open CookPvsNP ProjSchedTW.Complexity MultiPurchase.Hardness


namespace MPHNP

/-! ## Encodings -/

lemma encInts_nil : encInts [] = [] := rfl

lemma encInts_cons (a : ℤ) (l : List ℤ) : encInts (a :: l) = encInt a ++ encInts l := by
  simp [encInts]

lemma encInts_append (l₁ l₂ : List ℤ) : encInts (l₁ ++ l₂) = encInts l₁ ++ encInts l₂ := by
  simp [encInts]

lemma encInt_natCast (k : ℕ) : encInt (k : ℤ) = encNat k := by
  simp [encInt]

def ratInts (q : ℚ) : List ℤ := [q.num, (q.den : ℤ)]

lemma encRat_eq (q : ℚ) : encRat q = encInts (ratInts q) := by
  simp [encRat, ratInts, encInts, encInt_natCast]

lemma encRats_eq (qs : List ℚ) : encRats qs = encInts (qs.flatMap ratInts) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [encRats, List.flatMap_cons] at ih ⊢
    rw [encInts_append, ← encRat_eq, ← ih]

def v2List (I : Instance) : List ℚ :=
  (List.finRange I.n).flatMap fun i =>
    ((List.finRange I.n).filter (fun j => i < j)).map fun j => I.V2 i j

def qsOf (I : Instance) (κ : ℚ) : List ℚ :=
  List.ofFn I.r ++ List.ofFn I.V1 ++ v2List I ++ [I.v0, κ]

def codeInts (I : Instance) (κ : ℚ) : List ℤ :=
  (I.n : ℤ) :: (qsOf I κ).flatMap ratInts

lemma code_eq (I : Instance) (κ : ℚ) : code I κ = encInts (codeInts I κ) := by
  simp only [code, codeInts, qsOf, encInts_cons, encInt_natCast, List.flatMap_append,
    encInts_append, encRats_eq, v2List]
  simp [encRat_eq, List.append_assoc, ratInts, encInts]

/-! ## Indexing into `l.flatMap ratInts` -/

lemma flat_length (l : List ℚ) : (l.flatMap ratInts).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons q l ih => simp [List.flatMap_cons, ratInts, ih]; ring

lemma flat_getD (l : List ℚ) : ∀ t, t < l.length →
    (l.flatMap ratInts).getD (2 * t) 0 = (l.getD t 0).num ∧
    (l.flatMap ratInts).getD (2 * t + 1) 0 = ((l.getD t 0).den : ℤ) := by
  induction l with
  | nil => intro t ht; simp at ht
  | cons q l ih =>
    intro t ht
    cases t with
    | zero => simp [List.flatMap_cons, ratInts]
    | succ t =>
      have ht' : t < l.length := by simpa using ht
      obtain ⟨h1, h2⟩ := ih t ht'
      have e1 : 2 * (t + 1) = (2 * t) + 1 + 1 := by ring
      have e2 : 2 * (t + 1) + 1 = (2 * t + 1) + 1 + 1 := by ring
      simp only [List.flatMap_cons, ratInts, e1, e2, List.cons_append, List.nil_append,
        List.getD_cons_succ, List.getD_cons_succ] at h1 h2 ⊢
      exact ⟨h1, h2⟩

lemma chk_of_flat (z : ℤ) (l : List ℚ) (t : ℕ) (ht : t < l.length) :
    chkNum (z :: l.flatMap ratInts) t = (l.getD t 0).num ∧
    chkDen (z :: l.flatMap ratInts) t = ((l.getD t 0).den : ℤ) ∧
    chkRat (z :: l.flatMap ratInts) t = l.getD t 0 := by
  obtain ⟨h1, h2⟩ := flat_getD l t ht
  have a1 : chkNum (z :: l.flatMap ratInts) t = (l.getD t 0).num := by
    simp only [chkNum, List.getD_cons_succ]; exact h1
  have a2 : chkDen (z :: l.flatMap ratInts) t = ((l.getD t 0).den : ℤ) := by
    have : 2 * t + 2 = (2 * t + 1) + 1 := by ring
    simp only [chkDen, this, List.getD_cons_succ]; exact h2
  refine ⟨a1, a2, ?_⟩
  simp only [chkRat, a1, a2]
  push_cast
  exact Rat.num_div_den _

end MPHNP


namespace MPHNP

/-! ## The row-by-row order of pairs -/

def base (n i : ℕ) : ℕ := i * n - i * (i + 1) / 2

lemma tri_succ (m : ℕ) : (m + 1) * (m + 2) / 2 = m * (m + 1) / 2 + (m + 1) := by
  have : (m + 1) * (m + 2) = m * (m + 1) + 2 * (m + 1) := by ring
  rw [this, Nat.add_mul_div_left _ _ (by norm_num)]

lemma base_succ (n m : ℕ) (hm : m < n) : base n (m + 1) = base n m + (n - 1 - m) := by
  unfold base
  have h1 : (m + 1) * n = m * n + n := by ring
  have h2 := tri_succ m
  have h3 : m * (m + 1) / 2 ≤ m * n :=
    le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul_left _ hm)
  rw [show m + 1 + 1 = m + 2 by ring, h1, h2]
  omega

lemma base_self (n : ℕ) : base n n = n * (n - 1) / 2 := by
  unfold base
  cases n with
  | zero => simp
  | succ k =>
    have h2 := tri_succ k
    have h4 : (k + 1) * (k + 1) = k * (k + 1) + (k + 1) := by ring
    have h5 : k * (k + 1) / 2 * 2 = k * (k + 1) :=
      Nat.div_two_mul_two_of_even (Nat.even_mul_succ_self k)
    rw [show k + 1 + 1 = k + 2 by ring, h2, h4, Nat.add_sub_cancel, mul_comm (k + 1) k]
    omega

lemma flat_ranges (n : ℕ) : ∀ m, m ≤ n →
    (List.range m).flatMap (fun i => List.range' (base n i) (n - 1 - i)) =
      List.range' 0 (base n m) := by
  intro m
  induction m with
  | zero => intro _; simp [base]
  | succ m ih =>
    intro hm
    rw [List.range_succ, List.flatMap_append, ih (by omega), base_succ n m (by omega)]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have := @List.range'_append_1 0 (base n m) (n - 1 - m)
    simpa using this

lemma map_range'_shift (a b : ℕ) : ∀ k s, a ≤ s →
    (List.range' s k).map (fun j => b + (j - a)) = List.range' (b + (s - a)) k := by
  intro k
  induction k with
  | zero => intro s _; simp
  | succ k ih =>
    intro s hs
    rw [List.range'_succ, List.map_cons, ih (s + 1) (by omega), List.range'_succ]
    congr 2
    omega

lemma finRange_map_val (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

lemma filter_range_gt (n i : ℕ) (hi : i < n) :
    (List.range n).filter (fun j => decide (i < j)) = List.range' (i + 1) (n - 1 - i) := by
  have e : List.range n = List.range' 0 (i + 1) ++ List.range' (i + 1) (n - 1 - i) := by
    rw [List.range_eq_range']
    have := @List.range'_append_1 0 (i + 1) (n - 1 - i)
    simp only [Nat.zero_add] at this
    rw [this]
    congr 1
    omega
  rw [e, List.filter_append]
  have h1 : (List.range' 0 (i + 1)).filter (fun j => decide (i < j)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    rw [List.mem_range'_1] at ha
    simp
    omega
  have h2 : (List.range' (i + 1) (n - 1 - i)).filter (fun j => decide (i < j)) =
      List.range' (i + 1) (n - 1 - i) := by
    rw [List.filter_eq_self]
    intro a ha
    rw [List.mem_range'_1] at ha
    simp
    omega
  rw [h1, h2, List.nil_append]

lemma inner_idx (n : ℕ) (i : Fin n) :
    ((List.finRange n).filter (fun j => decide (i < j))).map
        (fun j : Fin n => pairIdx n (i : ℕ) (j : ℕ)) =
      List.range' (base n i) (n - 1 - i) := by
  have e1 : ((List.finRange n).filter (fun j => decide (i < j))).map
        (fun j : Fin n => pairIdx n (i : ℕ) (j : ℕ)) =
      ((List.range n).filter (fun j => decide ((i : ℕ) < j))).map
        (fun j => base n i + (j - (i + 1))) := by
    rw [← finRange_map_val, List.filter_map, List.map_map]
    have hf : (List.finRange n).filter (fun j => decide (i < j)) =
        (List.finRange n).filter ((fun j => decide ((i : ℕ) < j)) ∘ Fin.val) := by
      congr 1
    rw [hf]
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply, pairIdx, base]
    omega
  rw [e1, filter_range_gt n i i.isLt, map_range'_shift (i + 1) (base n i) _ _ le_rfl]
  simp

def pairsL (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter (fun j => decide (i < j))).map fun j => (i, j)

lemma pairsL_idx (n : ℕ) :
    (pairsL n).map (fun e : Fin n × Fin n => pairIdx n (e.1 : ℕ) (e.2 : ℕ)) =
      List.range (n * (n - 1) / 2) := by
  unfold pairsL
  rw [List.map_flatMap]
  have e : ∀ i : Fin n,
      (((List.finRange n).filter (fun j => decide (i < j))).map fun j => (i, j)).map
        (fun e : Fin n × Fin n => pairIdx n (e.1 : ℕ) (e.2 : ℕ)) =
        List.range' (base n i) (n - 1 - i) := by
    intro i
    rw [List.map_map]
    exact inner_idx n i
  simp only [e]
  have e2 : (List.finRange n).flatMap (fun i : Fin n => List.range' (base n i) (n - 1 - i)) =
      (List.range n).flatMap (fun i => List.range' (base n i) (n - 1 - i)) := by
    rw [← finRange_map_val, List.flatMap_map]
  rw [e2, flat_ranges n n le_rfl, base_self, List.range_eq_range']

lemma pairsL_length (n : ℕ) : (pairsL n).length = n * (n - 1) / 2 := by
  have := congrArg List.length (pairsL_idx n)
  simpa using this

lemma pairsL_mem (n : ℕ) (i j : Fin n) (h : i < j) : (i, j) ∈ pairsL n := by
  simp [pairsL, List.mem_flatMap, List.mem_filter, h]

lemma pairsL_lt (n : ℕ) (e : Fin n × Fin n) (h : e ∈ pairsL n) : e.1 < e.2 := by
  simp only [pairsL, List.mem_flatMap, List.mem_map, List.mem_filter] at h
  obtain ⟨i, _, j, ⟨_, hij⟩, rfl⟩ := h
  simpa using hij

lemma pairIdx_eq (n : ℕ) (i j : Fin n) (h : i < j) :
    ∃ p, ∃ hp : p < (pairsL n).length, (pairsL n)[p] = (i, j) ∧ pairIdx n i j = p := by
  obtain ⟨p, hp, hpe⟩ := List.getElem_of_mem (pairsL_mem n i j h)
  refine ⟨p, hp, hpe, ?_⟩
  have h1 := congrArg (fun l => l[p]?) (pairsL_idx n)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hp, hpe, Option.map_some] at h1
  rw [List.getElem?_range (by rw [← pairsL_length]; exact hp)] at h1
  simpa using h1

lemma pairIdx_lt (n : ℕ) (i j : Fin n) (h : i < j) : pairIdx n i j < n * (n - 1) / 2 := by
  obtain ⟨p, hp, _, he⟩ := pairIdx_eq n i j h
  rw [he, ← pairsL_length]; exact hp

lemma getD_map_pairs {α : Type} (n : ℕ) (f : Fin n × Fin n → α) (dflt : α) (i j : Fin n)
    (h : i < j) : ((pairsL n).map f).getD (pairIdx n i j) dflt = f (i, j) := by
  obtain ⟨p, hp, hpe, he⟩ := pairIdx_eq n i j h
  rw [he, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hp, hpe]
  rfl

lemma v2List_eq (I : Instance) : v2List I = (pairsL I.n).map (fun e => I.V2 e.1 e.2) := by
  unfold v2List pairsL
  rw [List.map_flatMap]
  congr 1
  funext i
  rw [List.map_map]
  rfl

end MPHNP


namespace MPHNP

/-! ## Lookups in `qsOf` -/

lemma v2List_length (I : Instance) : (v2List I).length = I.n * (I.n - 1) / 2 := by
  rw [v2List_eq, List.length_map, pairsL_length]

lemma qs_length (I : Instance) (κ : ℚ) : (qsOf I κ).length = numRats I.n := by
  simp [qsOf, v2List_length, numRats]
  ring

lemma getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (d : α) (t : ℕ) (h : t < n) :
    (List.ofFn f).getD t d = f ⟨t, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

lemma qs_r (I : Instance) (κ : ℚ) (i : Fin I.n) : (qsOf I κ).getD i 0 = I.r i := by
  unfold qsOf
  rw [List.append_assoc, List.append_assoc, List.getD_append _ _ _ _ (by simp)]
  exact getD_ofFn _ _ _ i.isLt

lemma qs_V1 (I : Instance) (κ : ℚ) (i : Fin I.n) : (qsOf I κ).getD (I.n + i) 0 = I.V1 i := by
  unfold qsOf
  rw [List.append_assoc, List.append_assoc, List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ (by simp)]
  exact getD_ofFn _ _ _ i.isLt

lemma qs_V2 (I : Instance) (κ : ℚ) (p : ℕ) (hp : p < I.n * (I.n - 1) / 2) :
    (qsOf I κ).getD (2 * I.n + p) 0 = (v2List I).getD p 0 := by
  unfold qsOf
  rw [List.getD_append _ _ _ _ (by simp [v2List_length]; omega)]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_append, List.length_ofFn]
  rw [show 2 * I.n + p - (I.n + I.n) = p by omega]

lemma qs_v0 (I : Instance) (κ : ℚ) : (qsOf I κ).getD (numRats I.n - 2) 0 = I.v0 := by
  unfold qsOf
  rw [List.getD_append_right _ _ _ _ (by simp [v2List_length, numRats]; omega)]
  simp only [List.length_append, List.length_ofFn, v2List_length, numRats]
  rw [show 2 * I.n + I.n * (I.n - 1) / 2 + 2 - 2 - (I.n + I.n + I.n * (I.n - 1) / 2) = 0 by omega]
  simp

lemma qs_kappa (I : Instance) (κ : ℚ) : (qsOf I κ).getD (numRats I.n - 1) 0 = κ := by
  unfold qsOf
  rw [List.getD_append_right _ _ _ _ (by simp [v2List_length, numRats]; omega)]
  simp only [List.length_append, List.length_ofFn, v2List_length, numRats]
  rw [show 2 * I.n + I.n * (I.n - 1) / 2 + 2 - 1 - (I.n + I.n + I.n * (I.n - 1) / 2) = 1 by omega]
  simp

lemma v2_mem_pos (I : Instance) (hI : I.WellFormed) (q : ℚ) (hq : q ∈ v2List I) : 0 ≤ q := by
  rw [v2List_eq, List.mem_map] at hq
  obtain ⟨e, he, rfl⟩ := hq
  exact hI.2.2.1 _ _ (pairsL_lt _ e he)

lemma qs_V2_pair (I : Instance) (κ : ℚ) (i j : Fin I.n) (h : i < j) :
    (qsOf I κ).getD (2 * I.n + pairIdx I.n i j) 0 = I.V2 i j := by
  rw [qs_V2 I κ _ (pairIdx_lt _ _ _ h), v2List_eq]
  exact getD_map_pairs I.n (fun e => I.V2 e.1 e.2) 0 i j h

/-! ## Facts about `codeInts` -/

lemma code_c0 (I : Instance) (κ : ℚ) : (codeInts I κ).getD 0 0 = (I.n : ℤ) := by
  simp [codeInts]

lemma code_n (I : Instance) (κ : ℚ) : ((codeInts I κ).getD 0 0).toNat = I.n := by
  simp [codeInts]

lemma code_length (I : Instance) (κ : ℚ) : (codeInts I κ).length = 2 * numRats I.n + 1 := by
  simp only [codeInts, List.length_cons, flat_length, qs_length]

lemma code_chk (I : Instance) (κ : ℚ) (t : ℕ) (ht : t < numRats I.n) :
    chkNum (codeInts I κ) t = ((qsOf I κ).getD t 0).num ∧
    chkDen (codeInts I κ) t = (((qsOf I κ).getD t 0).den : ℤ) ∧
    chkRat (codeInts I κ) t = (qsOf I κ).getD t 0 :=
  chk_of_flat _ _ t (by rw [qs_length]; exact ht)

def cert {n : ℕ} (C : Finset (Fin n)) : List Bool := List.ofFn fun i => decide (i ∈ C)

lemma cert_getD {n : ℕ} (C : Finset (Fin n)) (i : Fin n) :
    (cert C).getD i false = decide (i ∈ C) := getD_ofFn _ _ _ i.isLt

lemma canon_code (I : Instance) (κ : ℚ) : CanonOK (codeInts I κ) := by
  intro t ht
  rw [code_n] at ht
  obtain ⟨h1, h2, _⟩ := code_chk I κ t ht
  rw [h1, h2]
  refine ⟨by exact_mod_cast ((qsOf I κ).getD t 0).den_pos, ?_⟩
  have := ((qsOf I κ).getD t 0).reduced
  simpa [Int.gcd] using this

lemma shape_code (I : Instance) (κ : ℚ) (hI : I.WellFormed) (C : Finset (Fin I.n)) :
    ShapeOK (codeInts I κ) (cert C) := by
  have hn := code_n I κ
  refine ⟨by rw [code_c0]; positivity, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hn, code_length]
  · rw [hn]; simp [cert]
  · intro i hi
    rw [hn] at hi
    rw [(code_chk I κ i (by unfold numRats; omega)).1]
    have := qs_r I κ ⟨i, hi⟩
    simp only at this
    rw [this]
    exact Rat.num_pos.mpr (hI.1 _)
  · intro t h1 h2
    rw [hn] at h1 h2
    rw [(code_chk I κ t (by omega)).1]
    apply Rat.num_nonneg.mpr
    by_cases h3 : t < 2 * I.n
    · have := qs_V1 I κ ⟨t - I.n, by omega⟩
      simp only at this
      rw [show t = I.n + (t - I.n) by omega, this]
      exact hI.2.1 _
    · have hp : t - 2 * I.n < I.n * (I.n - 1) / 2 := by unfold numRats at h2; omega
      have := qs_V2 I κ (t - 2 * I.n) hp
      rw [show t = 2 * I.n + (t - 2 * I.n) by omega, this]
      apply v2_mem_pos I hI
      rw [List.getD_eq_getElem _ _ (by rw [v2List_length]; exact hp)]
      exact List.getElem_mem _
  · rw [hn, (code_chk I κ _ (by unfold numRats; omega)).1, qs_v0]
    exact Rat.num_pos.mpr hI.2.2.2

end MPHNP


namespace MPHNP

/-! ## The revenue condition on a code -/

lemma sum_ite_C {n : ℕ} (C : Finset (Fin n)) (g : Fin n → ℚ) :
    ∑ i : Fin n, (if i ∈ C then g i else 0) = ∑ i ∈ C, g i := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma sum_ite_C2 {n : ℕ} (C : Finset (Fin n)) (F G : Fin n → Fin n → ℚ)
    (hFG : ∀ i j, i < j → F i j = G i j) :
    ∑ i : Fin n, ∑ j : Fin n, (if (i : ℕ) < j ∧ i ∈ C ∧ j ∈ C then F i j else 0) =
      ∑ i ∈ C, ∑ j ∈ C.filter (fun j => i < j), G i j := by
  rw [← sum_ite_C C (fun i => ∑ j ∈ C.filter (fun j => i < j), G i j)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ C
  · simp only [hi, if_true]
    rw [Finset.sum_filter, ← sum_ite_C C (fun j => if i < j then G i j else 0)]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ C
    · by_cases hij : i < j
      · simp [hj, hij, Fin.lt_def.mp hij, hFG i j hij]
      · have : ¬ (i : ℕ) < j := fun h => hij (Fin.lt_def.mpr h)
        simp [hj, hij, this]
    · simp [hj]
  · simp [hi]

lemma rev_code (I : Instance) (κ : ℚ) (hI : I.WellFormed) (C : Finset (Fin I.n)) :
    RevOK (codeInts I κ) (cert C) ↔ κ ≤ I.R2 C := by
  have hr : ∀ i : Fin I.n, chkRat (codeInts I κ) i = I.r i := fun i => by
    rw [(code_chk I κ i (by unfold numRats; omega)).2.2, qs_r]
  have hV1 : ∀ i : Fin I.n, chkRat (codeInts I κ) (I.n + i) = I.V1 i := fun i => by
    rw [(code_chk I κ _ (by unfold numRats; omega)).2.2, qs_V1]
  have hV2 : ∀ i j : Fin I.n, i < j →
      chkRat (codeInts I κ) (2 * I.n + pairIdx I.n i j) = I.V2 i j := fun i j h => by
    have := pairIdx_lt I.n i j h
    rw [(code_chk I κ _ (by unfold numRats; omega)).2.2, qs_V2_pair I κ i j h]
  have hv0 : chkRat (codeInts I κ) (numRats I.n - 2) = I.v0 := by
    rw [(code_chk I κ _ (by unfold numRats; omega)).2.2, qs_v0]
  have hk : chkRat (codeInts I κ) (numRats I.n - 1) = κ := by
    rw [(code_chk I κ _ (by unfold numRats; omega)).2.2, qs_kappa]
  have hd : ∀ i : Fin I.n, (cert C).getD i false = decide (i ∈ C) := cert_getD C
  unfold RevOK
  simp only [code_n, hv0, hk, Finset.sum_range, hd, hr, hV1, decide_eq_true_eq]
  rw [sum_ite_C C (fun i => I.V1 i), sum_ite_C C (fun i => I.r i * I.V1 i),
    sum_ite_C2 C _ (fun i j => I.V2 i j) hV2,
    sum_ite_C2 C _ (fun i j => (I.r i + I.r j) * I.V2 i j)
      (fun i j h => by rw [hV2 i j h])]
  have hD : 0 < I.v0 + ∑ i ∈ C, I.V1 i + ∑ i ∈ C, ∑ j ∈ C.filter (fun j => i < j), I.V2 i j := by
    apply add_pos_of_pos_of_nonneg
    · exact add_pos_of_pos_of_nonneg hI.2.2.2 (Finset.sum_nonneg fun i _ => hI.2.1 i)
    · apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro j hj
      exact hI.2.2.1 i j (Finset.mem_filter.mp hj).2
  unfold Instance.R2
  rw [le_div_iff₀ hD]

/-! ## Decoding a checked code -/

def decI (c : List ℤ) : Instance where
  n := (c.getD 0 0).toNat
  r := fun i => chkRat c i
  V1 := fun i => chkRat c ((c.getD 0 0).toNat + i)
  V2 := fun i j => chkRat c (2 * (c.getD 0 0).toNat + pairIdx (c.getD 0 0).toNat i j)
  v0 := chkRat c (numRats (c.getD 0 0).toNat - 2)

def decK (c : List ℤ) : ℚ := chkRat c (numRats (c.getD 0 0).toNat - 1)

lemma decI_n (c : List ℤ) : (decI c).n = (c.getD 0 0).toNat := rfl

lemma range_split (n M : ℕ) :
    List.range (2 * n + M + 2) =
      List.range' 0 n ++ List.range' n n ++ List.range' (2 * n) M ++
        List.range' (2 * n + M) 2 := by
  rw [List.range_eq_range']
  have a1 := @List.range'_append_1 0 n n
  have a2 := @List.range'_append_1 0 (n + n) M
  have a3 := @List.range'_append_1 0 (n + n + M) 2
  simp only [Nat.zero_add] at a1 a2 a3
  rw [show 2 * n = n + n by ring, a1, a2, a3]

lemma qs_dec (c : List ℤ) :
    qsOf (decI c) (decK c) = (List.range (numRats (c.getD 0 0).toNat)).map (chkRat c) := by
  have e1 : List.ofFn (decI c).r = (List.range' 0 (c.getD 0 0).toNat).map (chkRat c) := by
    show List.ofFn (fun i : Fin (c.getD 0 0).toNat => chkRat c i) = _
    rw [List.ofFn_eq_map, ← List.range_eq_range', ← finRange_map_val, List.map_map]
    rfl
  have e2 : List.ofFn (decI c).V1 =
      (List.range' (c.getD 0 0).toNat (c.getD 0 0).toNat).map (chkRat c) := by
    show List.ofFn (fun i : Fin (c.getD 0 0).toNat => chkRat c ((c.getD 0 0).toNat + i)) = _
    rw [List.ofFn_eq_map, List.range'_eq_map_range, ← finRange_map_val, List.map_map,
      List.map_map]
    rfl
  have e3 : v2List (decI c) = (List.range' (2 * (c.getD 0 0).toNat)
      ((c.getD 0 0).toNat * ((c.getD 0 0).toNat - 1) / 2)).map (chkRat c) := by
    rw [v2List_eq]
    show (pairsL (c.getD 0 0).toNat).map (fun e => chkRat c (2 * (c.getD 0 0).toNat +
      pairIdx (c.getD 0 0).toNat e.1 e.2)) = _
    rw [List.range'_eq_map_range, ← pairsL_idx, List.map_map, List.map_map]
    rfl
  have e4 : [(decI c).v0, decK c] = (List.range' (2 * (c.getD 0 0).toNat +
      (c.getD 0 0).toNat * ((c.getD 0 0).toNat - 1) / 2) 2).map (chkRat c) := by
    simp only [decI, decK, numRats, List.range'_succ, List.range'_zero, List.map_cons,
      List.map_nil]
    congr 2 <;> omega
  unfold qsOf
  rw [e1, e2, e3, e4, numRats, range_split]
  simp only [List.map_append]

lemma ext_getD' (l₁ l₂ : List ℤ) (hl : l₁.length = l₂.length)
    (h : ∀ k < l₁.length, l₁.getD k 0 = l₂.getD k 0) : l₁ = l₂ := by
  apply List.ext_getElem hl
  intro k h1 h2
  have := h k h1
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

lemma recon (c : List ℤ) (N : ℕ) (hlen : c.length = 2 * N + 1)
    (hcan : ∀ t < N, 0 < chkDen c t ∧ Int.gcd (chkNum c t) (chkDen c t) = 1) :
    c = c.getD 0 0 :: ((List.range N).map (chkRat c)).flatMap ratInts := by
  have hL : ((List.range N).map (chkRat c)).length = N := by simp
  apply ext_getD'
  · rw [List.length_cons, flat_length, hL, hlen]
  · intro k hk
    cases k with
    | zero => simp
    | succ m =>
      rw [List.getD_cons_succ]
      obtain ⟨t, ht⟩ : ∃ t, m = 2 * t ∨ m = 2 * t + 1 := ⟨m / 2, by omega⟩
      have htN : t < N := by omega
      have hg : ((List.range N).map (chkRat c)).getD t 0 = chkRat c t := by
        rw [List.getD_eq_getElem _ _ (by rw [hL]; exact htN)]
        simp
      obtain ⟨hd, hg1⟩ := hcan t htN
      have hcop : Nat.Coprime (chkNum c t).natAbs (chkDen c t).natAbs := hg1
      rcases ht with rfl | rfl
      · rw [(flat_getD _ t (by rw [hL]; exact htN)).1, hg]
        unfold chkRat
        rw [Rat.num_div_eq_of_coprime hd hcop]
        rfl
      · rw [(flat_getD _ t (by rw [hL]; exact htN)).2, hg]
        unfold chkRat
        rw [Rat.den_div_eq_of_coprime hd hcop]
        rfl

lemma dec_code (c : List ℤ) (d : List Bool) (hS : ShapeOK c d) (hC : CanonOK c) :
    c = codeInts (decI c) (decK c) := by
  unfold codeInts
  rw [qs_dec, decI_n, Int.toNat_of_nonneg hS.1]
  exact recon c _ hS.2.1 hC

lemma dec_wf (c : List ℤ) (d : List Bool) (hS : ShapeOK c d) (hC : CanonOK c) :
    (decI c).WellFormed := by
  obtain ⟨_, _, _, hpos, hnn, hv0⟩ := hS
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have hi := i.isLt
    simp only [decI_n] at hi
    have h1 := hpos i hi
    have h2 := (hC i (by unfold numRats; omega)).1
    show 0 < chkRat c i
    unfold chkRat
    exact div_pos (by exact_mod_cast h1) (by exact_mod_cast h2)
  · intro i
    have hi := i.isLt
    simp only [decI_n] at hi
    have h1 := hnn ((c.getD 0 0).toNat + i) (by omega) (by unfold numRats; omega)
    have h2 := (hC ((c.getD 0 0).toNat + i) (by unfold numRats; omega)).1
    show 0 ≤ chkRat c _
    unfold chkRat
    exact div_nonneg (by exact_mod_cast h1) (by exact_mod_cast h2.le)
  · intro i j hij
    have hp := pairIdx_lt _ i j hij
    simp only [decI_n] at hp
    have h1 := hnn (2 * (c.getD 0 0).toNat + pairIdx (c.getD 0 0).toNat i j) (by omega)
      (by unfold numRats; omega)
    have h2 := (hC (2 * (c.getD 0 0).toNat + pairIdx (c.getD 0 0).toNat i j)
      (by unfold numRats; omega)).1
    show 0 ≤ chkRat c _
    unfold chkRat
    exact div_nonneg (by exact_mod_cast h1) (by exact_mod_cast h2.le)
  · have h2 := (hC (numRats (c.getD 0 0).toNat - 2) (by unfold numRats; omega)).1
    show 0 < chkRat c _
    unfold chkRat
    exact div_pos (by exact_mod_cast hv0) (by exact_mod_cast h2)

lemma dec_cert (c : List ℤ) (d : List Bool) (hS : ShapeOK c d) :
    d = cert (Finset.univ.filter fun i : Fin (decI c).n => d.getD i false = true) := by
  have hlen := hS.2.2.1
  apply List.ext_getElem
  · simp [cert, hlen, decI_n]
  · intro k h1 h2
    simp only [cert, List.getElem_ofFn, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [List.getD_eq_getElem _ _ h1]
    simp

/-! ## Injectivity of the checker encoding -/

lemma split_at {α : Type} (x : α) : ∀ (l₁ l₂ r₁ r₂ : List α), x ∉ l₁ → x ∉ l₂ →
    l₁ ++ x :: r₁ = l₂ ++ x :: r₂ → l₁ = l₂ ∧ r₁ = r₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ r₁ r₂ _ h₂ h
    cases l₂ with
    | nil => simpa using h
    | cons b l₂ =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) h₂
  | cons a l₁ ih =>
    intro l₂ r₁ r₂ h₁ h₂ h
    cases l₂ with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) h₁
    | cons b l₂ =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨e1, e2⟩ := ih l₂ r₁ r₂ (fun hm => h₁ (List.mem_cons_of_mem _ hm))
        (fun hm => h₂ (List.mem_cons_of_mem _ hm)) h
      exact ⟨by rw [e1], e2⟩

def dig (b : Bool) : BSym := if b then BSym.one else BSym.zero

lemma dig_inj : Function.Injective dig := by
  intro a b h; cases a <;> cases b <;> simp_all [dig]

lemma sep_not_mem_dig (L : List Bool) : BSym.sep ∉ L.map dig := by
  simp only [List.mem_map, not_exists, not_and]
  intro b _ h; cases b <;> simp [dig] at h

lemma minus_not_mem_dig (L : List Bool) : BSym.minus ∉ L.map dig := by
  simp only [List.mem_map, not_exists, not_and]
  intro b _ h; cases b <;> simp [dig] at h

lemma bits_inj {a b : ℕ} (h : a.bits = b.bits) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_eq_inth, Nat.testBit_eq_inth, h]

lemma encNat_eq (k : ℕ) : encNat k = (Nat.bits k).map dig ++ [BSym.sep] := rfl

lemma encNat_app (a b : ℕ) (s t : List BSym) (h : encNat a ++ s = encNat b ++ t) :
    a = b ∧ s = t := by
  rw [encNat_eq, encNat_eq] at h
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h
  obtain ⟨e1, e2⟩ := split_at BSym.sep _ _ _ _ (sep_not_mem_dig _) (sep_not_mem_dig _) h
  exact ⟨bits_inj (List.map_injective_iff.mpr dig_inj e1), e2⟩

lemma encNat_head (k : ℕ) (s : List BSym) : ∃ x l, encNat k ++ s = x :: l ∧ x ≠ BSym.minus := by
  rw [encNat_eq]
  cases hb : Nat.bits k with
  | nil => exact ⟨BSym.sep, s, by simp, by decide⟩
  | cons b L => exact ⟨dig b, L.map dig ++ [BSym.sep] ++ s, rfl, by cases b <;> simp [dig]⟩

lemma encInt_app (a b : ℤ) (s t : List BSym) (h : encInt a ++ s = encInt b ++ t) :
    a = b ∧ s = t := by
  unfold encInt at h
  by_cases ha : a < 0 <;> by_cases hb : b < 0
  · simp only [ha, hb, if_true, List.cons_append, List.nil_append, List.append_assoc,
      List.cons.injEq, true_and] at h
    obtain ⟨e1, e2⟩ := encNat_app _ _ _ _ h
    exact ⟨by omega, e2⟩
  · simp only [ha, hb, if_true, if_false, List.cons_append, List.nil_append,
      List.append_assoc] at h
    obtain ⟨x, l, hx, hne⟩ := encNat_head b.natAbs t
    rw [hx] at h
    exact absurd (List.cons.inj h).1.symm hne
  · simp only [ha, hb, if_true, if_false, List.cons_append, List.nil_append,
      List.append_assoc] at h
    obtain ⟨x, l, hx, hne⟩ := encNat_head a.natAbs s
    rw [hx] at h
    exact absurd (List.cons.inj h).1 hne
  · simp only [ha, hb, if_false, List.nil_append] at h
    obtain ⟨e1, e2⟩ := encNat_app _ _ _ _ h
    exact ⟨by omega, e2⟩

lemma encInt_ne_nil (a : ℤ) : encInt a ≠ [] := by
  simp [encInt, encNat]

lemma encInts_inj : ∀ (c c' : List ℤ), encInts c = encInts c' → c = c' := by
  intro c
  induction c with
  | nil =>
    intro c' h
    cases c' with
    | nil => rfl
    | cons b l =>
      rw [encInts_cons, encInts_nil] at h
      exact absurd h.symm (by simp [encInt_ne_nil])
  | cons a l ih =>
    intro c' h
    cases c' with
    | nil =>
      rw [encInts_cons, encInts_nil] at h
      exact absurd h (by simp [encInt_ne_nil])
    | cons b l' =>
      rw [encInts_cons, encInts_cons] at h
      obtain ⟨e1, e2⟩ := encInt_app _ _ _ _ h
      rw [e1, ih l' e2]

lemma chkWord_inj (c c' : List ℤ) (d d' : List Bool) (h : chkWord c d = chkWord c' d') :
    c = c' ∧ d = d' := by
  unfold chkWord at h
  have hn : ∀ (w : List BSym), (none : Option (BSym ⊕ Bool)) ∉ w.map (some ∘ Sum.inl) := by
    intro w; simp
  obtain ⟨e1, e2⟩ := split_at _ _ _ _ _ (hn _) (hn _) h
  have i1 : Function.Injective (some ∘ Sum.inl : BSym → Option (BSym ⊕ Bool)) := by
    intro x y hxy; simpa using hxy
  have i2 : Function.Injective (some ∘ Sum.inr : Bool → Option (BSym ⊕ Bool)) := by
    intro x y hxy; simpa using hxy
  exact ⟨encInts_inj _ _ (List.map_injective_iff.mpr i1 e1), List.map_injective_iff.mpr i2 e2⟩

lemma chkWord_ne_nil (c : List ℤ) (d : List Bool) : chkWord c d ≠ [] := by
  simp [chkWord]

end MPHNP


namespace MPHNP

/-! ## The language of nonempty words is in P -/

inductive NQ | q0 | acc | rej
  deriving DecidableEq

instance : Fintype NQ where
  elems := {NQ.q0, NQ.acc, NQ.rej}
  complete := by intro x; cases x <;> simp

def neTM (Γ : Type) : TM Γ where
  Q := NQ
  q₀ := NQ.q0
  qaccept := NQ.acc
  qreject := NQ.rej
  accept_ne_reject := by decide
  δ := fun q s => match q with
    | NQ.q0 => ((if s.isSome then NQ.acc else NQ.rej), s, Move.right)
    | q => (q, s, Move.right)

lemma neTM_run (Γ : Type) (w : List Γ) (n : ℕ) :
    ((neTM Γ).run (n + 1) ((neTM Γ).init w)).state = if w = [] then NQ.rej else NQ.acc := by
  have h1 : ((neTM Γ).step ((neTM Γ).init w)).state = if w = [] then NQ.rej else NQ.acc := by
    cases w <;> simp [TM.step, TM.init, TM.IsHalting, neTM]
  have hfix : ∀ c : Cfg Γ (neTM Γ).Q, (c.state = NQ.acc ∨ c.state = NQ.rej) →
      (neTM Γ).step c = c := by
    intro c hc
    have : (neTM Γ).IsHalting c := hc
    unfold TM.step; rw [if_pos this]
  have hst : ∀ m, ((neTM Γ).run (m + 1) ((neTM Γ).init w)).state =
      if w = [] then NQ.rej else NQ.acc := by
    intro m
    induction m with
    | zero => simpa [TM.run] using h1
    | succ m ih =>
      have h2 : (neTM Γ).run (m + 1 + 1) ((neTM Γ).init w) =
          (neTM Γ).step ((neTM Γ).run (m + 1) ((neTM Γ).init w)) := by
        simp only [TM.run]; rw [Function.iterate_succ_apply']
      rw [h2]
      have hh : ((neTM Γ).run (m + 1) ((neTM Γ).init w)).state = NQ.acc ∨
          ((neTM Γ).run (m + 1) ((neTM Γ).init w)).state = NQ.rej := by
        rw [ih]; split_ifs <;> first | exact Or.inr rfl | exact Or.inl rfl
      exact (congrArg Cfg.state (hfix _ hh)).trans ih
  exact hst n

theorem neLang_mem_P (Γ : Type) [Fintype Γ] : {w : List Γ | w ≠ []} ∈ P Γ := by
  have e : ∀ w : List Γ, w.map (⇑(Function.Embedding.refl Γ)) = w := fun w => List.map_id w
  refine ⟨Γ, inferInstance, Function.Embedding.refl Γ, neTM Γ, 1, ?_, ?_⟩
  · intro w
    obtain ⟨m, hm⟩ : ∃ m, w.length ^ 1 + 1 = m + 1 := ⟨w.length, by simp⟩
    have := neTM_run Γ w m
    rw [e]
    unfold TM.HaltsWithin TM.IsHalting
    rw [hm]
    show _ = NQ.acc ∨ _ = NQ.rej
    rw [this]
    split_ifs <;> first | exact Or.inr rfl | exact Or.inl rfl
  · intro w
    rw [e]
    constructor
    · intro hw
      refine ⟨1, ?_⟩
      have := neTM_run Γ w 0
      rw [if_neg hw] at this
      exact this
    · rintro ⟨n, hn⟩ rfl
      cases n with
      | zero => exact absurd hn (by simp [TM.run, TM.init, neTM])
      | succ n =>
        have := neTM_run Γ ([] : List Γ) n
        rw [if_pos rfl] at this
        have h2 : NQ.rej = NQ.acc := this.symm.trans hn
        exact absurd h2 (by decide)

/-! ## The checking relation -/

def Rchk (w : List BSym) (y : List Bool) : Prop :=
  ∃ c, w = encInts c ∧ ShapeOK c y ∧ CanonOK c ∧ RevOK c y

lemma checkLang_iff (u : List (Option (BSym ⊕ Bool))) :
    u ∈ checkLang Rchk ↔ ∃ c d, u = chkWord c d ∧ ShapeOK c d ∧ CanonOK c ∧ RevOK c d := by
  constructor
  · rintro ⟨w, y, ⟨c, rfl, h1, h2, h3⟩, rfl⟩
    exact ⟨c, y, rfl, h1, h2, h3⟩
  · rintro ⟨c, d, rfl, h1, h2, h3⟩
    exact ⟨encInts c, d, ⟨c, rfl, h1, h2, h3⟩, rfl⟩

open Classical in
lemma checkLang_mem_P : checkLang Rchk ∈ P (Option (BSym ⊕ Bool)) := by
  obtain ⟨gC, hgC, hgC0, hgCs⟩ := canon_filter_polytime
  obtain ⟨gR, hgR, hgR0, hgRs⟩ := rev_check_polytime
  have hS := shape_filter_polytime
  have hf := polyTimeComputable_comp _ _ (polyTimeComputable_comp _ _ hS hgC) hgR
  refine mem_P_of_polyReducible _ {w | w ≠ []} ⟨_, hf, ?_⟩ (neLang_mem_P _)
  intro u
  simp only [Set.mem_setOf_eq, Function.comp_apply]
  rw [checkLang_iff]
  by_cases hs : ∃ c d, u = chkWord c d ∧ ShapeOK c d
  · rw [if_pos hs]
    obtain ⟨c, d, rfl, hsh⟩ := hs
    rw [hgCs c d hsh]
    by_cases hc : CanonOK c
    · rw [if_pos hc, hgRs c d hsh hc]
      constructor
      · rintro ⟨c', d', he, _, _, hr⟩
        obtain ⟨rfl, rfl⟩ := chkWord_inj _ _ _ _ he
        exact hr
      · intro hr
        exact ⟨c, d, rfl, hsh, hc, hr⟩
    · rw [if_neg hc, hgR0]
      simp only [ne_eq, not_true_eq_false, iff_false]
      rintro ⟨c', d', he, _, hc', _⟩
      obtain ⟨rfl, rfl⟩ := chkWord_inj _ _ _ _ he
      exact hc hc'
  · rw [if_neg hs, hgC0, hgR0]
    simp only [ne_eq, not_true_eq_false, iff_false]
    rintro ⟨c, d, rfl, hsh, _, _⟩
    exact hs ⟨c, d, rfl, hsh⟩

/-! ## Certificate length -/

lemma encRats_len (l : List ℚ) : l.length ≤ (encRats l).length := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [encRats, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have : 1 ≤ (encRat q).length := by simp [encRat, encNat]; omega
    omega

lemma cert_len_le (I : Instance) (κ : ℚ) (C : Finset (Fin I.n)) :
    (cert C).length ≤ (code I κ).length := by
  have h := encRats_len (List.ofFn I.r)
  simp only [List.length_ofFn] at h
  simp only [cert, List.length_ofFn, code, List.length_append]
  omega

end MPHNP

open MPHNP in
theorem solution : bundleLang ∈ NP BSym := by
  refine ⟨Bool, inferInstance, ⟨true⟩, Rchk, 1, checkLang_mem_P, ?_⟩
  intro w
  constructor
  · rintro ⟨I, κ, ⟨hI, C, hC⟩, rfl⟩
    refine ⟨cert C, ?_, codeInts I κ, code_eq I κ, shape_code I κ hI C, canon_code I κ,
      (rev_code I κ hI C).mpr hC⟩
    rw [pow_one]
    exact cert_len_le I κ C
  · rintro ⟨y, _, c, rfl, hS, hC, hR⟩
    have hc := dec_code c y hS hC
    have hwf := dec_wf c y hS hC
    have hy := dec_cert c y hS
    refine ⟨decI c, decK c,
      ⟨hwf, Finset.univ.filter (fun i : Fin (decI c).n => y.getD i false = true), ?_⟩, ?_⟩
    · rw [← rev_code (decI c) (decK c) hwf, ← hy, ← hc]
      exact hR
    · rw [code_eq, ← hc]

