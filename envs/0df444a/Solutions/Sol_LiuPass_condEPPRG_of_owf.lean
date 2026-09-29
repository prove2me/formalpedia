-- Prove2me | solution 1 for LiuPass.condEPPRG_of_owf
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T09:54:21.909327+00:00
-- url     : https://prove2.me/submissions/7025b893-3469-4a66-8bfc-f6c7ac1283b0

import Mathlib
import Definitions.Def_LiuPass_crypto

/-! Disproof of 6f075af9 `LiuPass.condEPPRG_of_owf`.

The counterexample machine `lpM`: a string `true :: x` is a program that halts at once with output
`x`, and no other string halts. `pair` is defined so that every structure field holds. `pair (1^n) x = []` for
every non-all-ones `x` (the inverter is blind), `pair [false] w = true :: w` (identity), and `sim`, `padProg` and a
length program are hard-wired. `univ_prog` is vacuous: `evaln k` rejects inputs `≥ k`, and `2^m` distinct
`encode`d strings cannot all lie below a polynomial `T m`. So `id` is a one-way function on `lpM`. Every
polynomial-time function outputs at most `|input| + O(1)` bits, and `K^t x = |x| + 1` exactly.

On `lpM` one-way functions exist, but a conditionally secure EP-PRG must stretch `n` bits to
`n + γ log n` bits. Every polynomial-time function stretches by at most a constant, so none exists. -/

set_option autoImplicit false

open scoped Classical

/-! A concrete `LiuPass.UMachine` in which every string `true :: x` is a program that halts at
once with output `x`, and nothing else halts. -/

def lpM_tailOut : List Bool → List Bool
  | true :: x => x
  | _ => []

def lpM_simOut : List Bool → List Bool
  | false :: x => x
  | _ => []

def lpM_binRep : ℕ → List Bool
  | 0 => []
  | (n + 1) => lpM_binRep ((n + 1) / 2) ++ [decide ((n + 1) % 2 = 1)]
decreasing_by omega

def lpM_cnt (l : List Bool) : ℕ := (l.takeWhile (fun b => b)).length

def lpM_gen (a b : List Bool) : List Bool :=
  if b.all (fun c => c) then (if b = [] then [] else false :: lpM_tailOut a)
  else (match a with
    | true :: _ => []
    | _ => a ++ b)

def lpM_pair : List Bool → List Bool → List Bool
  | [], b => lpM_gen [] b
  | true :: x, b => lpM_gen (true :: x) b
  | [false], b => true :: b
  | false :: true :: rest, b =>
      true :: (b.take (lpM_cnt rest) ++
        lpM_tailOut (lpM_pair (rest.drop (lpM_cnt rest + 1)) (b.drop (lpM_cnt rest))))
  | [false, false], b => true :: lpM_simOut b
  | [false, false, false], b => true :: lpM_binRep (b.length + 1)
  | false :: false :: false :: c :: d, b => lpM_gen (false :: false :: false :: c :: d) b
  | false :: false :: true :: d, b => lpM_gen (false :: false :: true :: d) b
termination_by a => a.length
decreasing_by simp; omega

def lpM_run (P : List Bool) (s : ℕ) : Option (List Bool) :=
  if s = 0 then none else
    match P with
    | true :: x => some x
    | _ => none

theorem lpM_run_eq_some (P x : List Bool) (s : ℕ) :
    lpM_run P s = some x ↔ s ≠ 0 ∧ P = true :: x := by
  unfold lpM_run
  by_cases hs : s = 0
  · simp [hs]
  · simp only [hs, if_false, ne_eq, not_false_eq_true, true_and]
    match P with
    | [] => simp
    | true :: y => simp
    | false :: y => simp

theorem lpM_run_true (x : List Bool) (s : ℕ) (hs : s ≠ 0) : lpM_run (true :: x) s = some x :=
  (lpM_run_eq_some _ _ _).2 ⟨hs, rfl⟩

theorem lpM_tailOut_len (l : List Bool) : (lpM_tailOut l).length ≤ l.length := by
  match l with
  | [] => simp [lpM_tailOut]
  | true :: x => simp [lpM_tailOut]
  | false :: x => simp [lpM_tailOut]

theorem lpM_simOut_len (l : List Bool) : (lpM_simOut l).length ≤ l.length := by
  match l with
  | [] => simp [lpM_simOut]
  | true :: x => simp [lpM_simOut]
  | false :: x => simp [lpM_simOut]

theorem lpM_binRep_len (n : ℕ) : (lpM_binRep n).length ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [lpM_binRep]
    | m + 1 =>
      rw [lpM_binRep]
      have := ih ((m + 1) / 2) (by omega)
      simp
      omega

theorem lpM_bitsToNat_snoc (l : List Bool) (c : Bool) :
    LiuPass.bitsToNat (l ++ [c]) = 2 * LiuPass.bitsToNat l + (if c then 1 else 0) := by
  unfold LiuPass.bitsToNat
  rw [List.foldl_append]
  simp

theorem lpM_bitsToNat_binRep (n : ℕ) : LiuPass.bitsToNat (lpM_binRep n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [lpM_binRep, LiuPass.bitsToNat]
    | m + 1 =>
      rw [lpM_binRep, lpM_bitsToNat_snoc, ih ((m + 1) / 2) (by omega)]
      by_cases h : (m + 1) % 2 = 1
      · simp [h]; omega
      · simp [h]; omega

theorem lpM_gen_len (a b : List Bool) : (lpM_gen a b).length ≤ a.length + b.length + 1 := by
  unfold lpM_gen
  split_ifs
  · simp
  · have := lpM_tailOut_len a
    simp; omega
  · match a with
    | [] => simp
    | true :: x => simp
    | false :: x => simp

theorem lpM_pair_len (a b : List Bool) : (lpM_pair a b).length ≤ a.length + b.length + 2 := by
  induction a, b using lpM_pair.induct with
  | case1 b => have := lpM_gen_len [] b; rw [lpM_pair]; simp at this ⊢; omega
  | case2 x b => have := lpM_gen_len (true :: x) b; rw [lpM_pair]; simp at this ⊢; omega
  | case3 b => rw [lpM_pair]; simp; omega
  | case4 rest b ih =>
      rw [lpM_pair]
      have h1 := lpM_tailOut_len (lpM_pair (rest.drop (lpM_cnt rest + 1)) (b.drop (lpM_cnt rest)))
      simp only [List.length_cons, List.length_append, List.length_take, List.length_drop] at ih h1 ⊢
      omega
  | case5 b => rw [lpM_pair]; have := lpM_simOut_len b; simp; omega
  | case6 b => rw [lpM_pair]; have := lpM_binRep_len (b.length + 1); simp; omega
  | case7 c d b =>
      have := lpM_gen_len (false :: false :: false :: c :: d) b; rw [lpM_pair]; simp at this ⊢; omega
  | case8 d b =>
      have := lpM_gen_len (false :: false :: true :: d) b; rw [lpM_pair]; simp at this ⊢; omega

theorem lpM_all_rep (t : ℕ) : (List.replicate t true).all (fun c => c) = true := by
  simp

theorem lpM_simOut_gen_false (y : List Bool) (t : ℕ) :
    lpM_simOut (lpM_gen (false :: y) (List.replicate t true)) = [] := by
  unfold lpM_gen
  rw [if_pos (lpM_all_rep t)]
  split_ifs <;> simp [lpM_simOut, lpM_tailOut]

theorem lpM_simOut_pair (Pi : List Bool) (t : ℕ) :
    lpM_simOut (lpM_pair Pi (LiuPass.unary t)) = (lpM_run Pi t).getD [] := by
  unfold LiuPass.unary
  match Pi with
  | [] =>
      rw [lpM_pair]; unfold lpM_gen; rw [if_pos (lpM_all_rep t)]
      by_cases ht : t = 0
      · subst ht; simp [lpM_simOut, lpM_run]
      · rw [if_neg (by simpa using ht)]; simp [lpM_simOut, lpM_tailOut, lpM_run]
  | true :: x =>
      rw [lpM_pair]; unfold lpM_gen; rw [if_pos (lpM_all_rep t)]
      by_cases ht : t = 0
      · subst ht; simp [lpM_simOut, lpM_run]
      · rw [if_neg (by simpa using ht)]; simp [lpM_simOut, lpM_tailOut, lpM_run, ht]
  | [false] => rw [lpM_pair]; simp [lpM_simOut, lpM_run]
  | false :: true :: rest => rw [lpM_pair]; simp [lpM_simOut, lpM_run]
  | [false, false] => rw [lpM_pair]; simp [lpM_simOut, lpM_run]
  | [false, false, false] => rw [lpM_pair]; simp [lpM_simOut, lpM_run]
  | false :: false :: false :: c :: d =>
      rw [lpM_pair, lpM_simOut_gen_false]; simp [lpM_run]
  | false :: false :: true :: d =>
      rw [lpM_pair, lpM_simOut_gen_false]; simp [lpM_run]

def lpM_padProg (Q : List Bool) (k : ℕ) : List Bool :=
  false :: true :: (List.replicate k true ++ false :: Q)

theorem lpM_cnt_pad (Q : List Bool) (k : ℕ) :
    lpM_cnt (List.replicate k true ++ false :: Q) = k := by
  unfold lpM_cnt
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ]

theorem lpM_drop_pad (Q : List Bool) (k : ℕ) :
    (List.replicate k true ++ false :: Q).drop (k + 1) = Q := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ]; simpa using ih

theorem lpM_pair_pad (Q : List Bool) (k : ℕ) (w : List Bool) :
    lpM_pair (lpM_padProg Q k) w =
      true :: (w.take k ++ lpM_tailOut (lpM_pair Q (w.drop k))) := by
  unfold lpM_padProg
  rw [lpM_pair, lpM_cnt_pad, lpM_drop_pad]

/-- evaluation with polynomial fuel never accepts inputs of size beyond the fuel -/
theorem lpM_two_pow_le (F : List Bool → List Bool) (T : ℕ → ℕ)
    (h : LiuPass.CodeComputableInTime F T) (m : ℕ) : 2 ^ m ≤ T m := by
  obtain ⟨c, hc⟩ := h
  have hlt : ∀ v : Fin m → Bool, Encodable.encode (List.ofFn v) < T m := by
    intro v
    have := hc (List.ofFn v)
    rw [List.length_ofFn] at this
    exact Nat.Partrec.Code.evaln_bound (by rw [this]; exact Option.mem_some_iff.mpr rfl)
  have hcard := Finset.card_le_card_of_injOn (fun v : Fin m → Bool => Encodable.encode (List.ofFn v))
    (s := Finset.univ) (t := Finset.range (T m))
    (fun v _ => by simpa using hlt v)
    (fun a _ b _ hab => by
      have := Encodable.encode_injective hab
      exact List.ofFn_injective this)
  simpa using hcard

theorem lpM_growth (C k : ℕ) : ∃ N : ℕ, ∀ n ≥ N, (C : ℝ) * (n : ℝ) ^ k + C < 2 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt k (r := (2 : ℝ)) one_lt_two
  have hpos : (0 : ℝ) < 1 / (2 * C + 1) := by positivity
  have hev := h.eventually (gt_mem_nhds hpos)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨max N 1, fun n hn => ?_⟩
  have h1 := hN n (le_trans (le_max_left _ _) hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hpow1 : (1 : ℝ) ≤ (n : ℝ) ^ k := one_le_pow₀ hn1
  have h2pos : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_lt_div_iff₀ h2pos (by positivity)] at h1
  have hC : (0 : ℝ) ≤ C := by positivity
  nlinarith

theorem lpM_univ_vacuous (F : List Bool → List Bool) (T : ℕ → ℕ) (hT : LiuPass.IsPoly T)
    (h : LiuPass.CodeComputableInTime F T) : False := by
  obtain ⟨k, c, hk⟩ := hT
  obtain ⟨N, hN⟩ := lpM_growth c k
  have h1 := lpM_two_pow_le F T h N
  have h2 := hk N
  have h3 := hN N le_rfl
  have : ((2 : ℕ) ^ N : ℝ) ≤ (c : ℝ) * (N : ℝ) ^ k + c := by exact_mod_cast le_trans h1 h2
  push_cast at this
  linarith

def lpM : LiuPass.UMachine where
  run := lpM_run
  run_mono := by
    intro Pi t t' x htt' h
    rw [lpM_run_eq_some] at h ⊢
    exact ⟨by omega, h.2⟩
  pair := lpM_pair
  pairOverhead := 2
  pair_length_le := lpM_pair_len
  idProg := [false]
  run_idProg := by
    intro w t ht
    rw [lpM_pair]
    exact lpM_run_true w t (by omega)
  sim := [false, false]
  simTime := fun n => n + 1
  simTime_poly := ⟨1, 1, fun n => by simp⟩
  run_sim := by
    intro Pi t
    rw [lpM_pair, lpM_run_true _ _ (by omega), lpM_simOut_pair]
  padProg := lpM_padProg
  padOverhead := 1
  run_padProg := by
    intro Pi k t w y h
    rw [lpM_run_eq_some] at h
    rw [lpM_pair_pad, h.2]
    simp only [lpM_tailOut]
    exact lpM_run_true _ _ (by omega)
  univ_prog := by
    intro F T hT h
    exact (lpM_univ_vacuous F T hT h).elim

/-! ### `id` is one-way on `lpM`: the inverter's input `pair (1^n) x` is blind. -/

theorem lpM_pair_unary_blind (n : ℕ) (x : List Bool) (hx : x.length = n) :
    x = LiuPass.unary n ∨ lpM_pair (LiuPass.unary n) x = [] := by
  by_cases hall : x.all (fun c => c) = true
  · left
    unfold LiuPass.unary
    rw [List.eq_replicate_iff]
    refine ⟨hx, fun b hb => ?_⟩
    rw [List.all_eq_true] at hall
    simpa using hall b hb
  · right
    match n, hx with
    | 0, hx =>
        exfalso; apply hall
        rw [List.length_eq_zero_iff] at hx; subst hx; simp
    | m + 1, _ =>
        unfold LiuPass.unary
        rw [List.replicate_succ, lpM_pair]
        unfold lpM_gen
        rw [if_neg hall]

theorem lpM_prUnif₂_le (n m : ℕ) (P : List Bool → List Bool → Prop) (c : ℕ)
    (h : (Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      P (List.ofFn v.1) (List.ofFn v.2)).card ≤ c * 2 ^ m) :
    LiuPass.prUnif₂ n m P ≤ c * (1 / 2) ^ n := by
  unfold LiuPass.prUnif₂
  rw [div_le_iff₀ (by positivity)]
  have h' : ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      P (List.ofFn v.1) (List.ofFn v.2)).card : ℝ) ≤ c * 2 ^ m := by exact_mod_cast h
  calc _ ≤ (c : ℝ) * 2 ^ m := h'
    _ = c * (1 / 2) ^ n * 2 ^ (n + m) := by
        rw [pow_add, one_div_pow]
        field_simp

theorem lpM_card_fst_fixed (n m : ℕ) (x₀ : List Bool) :
    (Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) => List.ofFn v.1 = x₀).card
      ≤ 2 ^ m := by
  have := Finset.card_le_card_of_injOn (fun v : (Fin n → Bool) × (Fin m → Bool) => v.2)
    (s := Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) => List.ofFn v.1 = x₀)
    (t := Finset.univ) (fun _ _ => by simp)
    (fun a ha b hb hab => by
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
      exact Prod.ext (List.ofFn_injective (ha.trans hb.symm)) hab)
  simpa using this

theorem lpM_card_fst_fun (n m : ℕ) (g : List Bool → List Bool) :
    (Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      List.ofFn v.1 = g (List.ofFn v.2)).card ≤ 2 ^ m := by
  have := Finset.card_le_card_of_injOn (fun v : (Fin n → Bool) × (Fin m → Bool) => v.2)
    (s := Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      List.ofFn v.1 = g (List.ofFn v.2))
    (t := Finset.univ) (fun _ _ => by simp)
    (fun a ha b hb hab => by
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
      have hab' : a.2 = b.2 := hab
      rw [hab'] at ha
      exact Prod.ext (List.ofFn_injective (ha.trans hb.symm)) hab)
  simpa using this

theorem lpM_negl_two : LiuPass.Negligible (fun n => (2 : ℝ) * (1 / 2) ^ n) := by
  intro k
  obtain ⟨N, hN⟩ := lpM_growth 2 k
  refine ⟨max N 1, fun n hn => ?_⟩
  have h1 := hN n (le_trans (le_max_left _ _) hn)
  have hpk : (0 : ℝ) < (n : ℝ) ^ k := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
    positivity
  show (2 : ℝ) * (1 / 2) ^ n ≤ 1 / (n : ℝ) ^ k
  rw [one_div_pow, mul_one_div, div_le_div_iff₀ (by positivity) hpk]
  push_cast at h1
  linarith

/-- a success event that forces `x = x₀` or `x = g r` has probability at most `2 · 2^-n` -/
theorem lpM_prUnif₂_two (n m : ℕ) (P : List Bool → List Bool → Prop) (x₀ : List Bool)
    (g : List Bool → List Bool) (h : ∀ x r, x.length = n → P x r → x = x₀ ∨ x = g r) :
    LiuPass.prUnif₂ n m P ≤ 2 * (1 / 2) ^ n := by
  have := lpM_prUnif₂_le n m P 2 (by
    calc _ ≤ ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
            List.ofFn v.1 = x₀) ∪
          (Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
            List.ofFn v.1 = g (List.ofFn v.2))).card := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hv ⊢
          exact h _ _ (by simp) hv
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ 2 ^ m + 2 ^ m := Nat.add_le_add (lpM_card_fst_fixed _ _ _) (lpM_card_fst_fun _ _ g)
      _ = 2 * 2 ^ m := by ring)
  simpa using this

/-- an event holding for every `x ≠ x₀` (with no random tape) has probability `≥ 1 - 2^-n` -/
theorem lpM_prUnif₂_ge (n : ℕ) (P : List Bool → List Bool → Prop) (x₀ : List Bool)
    (h : ∀ x : List Bool, x.length = n → x ≠ x₀ → P x []) :
    1 - (1 / 2 : ℝ) ^ n ≤ LiuPass.prUnif₂ n 0 P := by
  unfold LiuPass.prUnif₂
  have hcompl : (Finset.univ.filter fun v : (Fin n → Bool) × (Fin 0 → Bool) =>
      ¬ P (List.ofFn v.1) (List.ofFn v.2)).card ≤ 1 := by
    calc _ ≤ (Finset.univ.filter fun v : (Fin n → Bool) × (Fin 0 → Bool) =>
            List.ofFn v.1 = x₀).card := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          by_contra hne
          apply hv
          have h2 : List.ofFn v.2 = [] := by rw [List.ofFn_eq_nil_iff]
          rw [h2]
          exact h _ (by simp) hne
      _ ≤ 2 ^ 0 := lpM_card_fst_fixed _ _ _
      _ = 1 := rfl
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ((Fin n → Bool) × (Fin 0 → Bool))))
    (fun v : (Fin n → Bool) × (Fin 0 → Bool) => P (List.ofFn v.1) (List.ofFn v.2))
  have hcard : (Finset.univ : Finset ((Fin n → Bool) × (Fin 0 → Bool))).card = 2 ^ n := by
    simp
  rw [hcard] at htot
  have hsR : (2 : ℝ) ^ n - 1 ≤ ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin 0 → Bool) =>
      P (List.ofFn v.1) (List.ofFn v.2)).card : ℝ) := by
    have : 2 ^ n ≤ (Finset.univ.filter fun v : (Fin n → Bool) × (Fin 0 → Bool) =>
      P (List.ofFn v.1) (List.ofFn v.2)).card + 1 := by omega
    have : ((2 ^ n : ℕ) : ℝ) ≤ ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin 0 → Bool) =>
      P (List.ofFn v.1) (List.ofFn v.2)).card : ℝ) + 1 := by exact_mod_cast this
    push_cast at this
    linarith
  rw [Nat.add_zero, le_div_iff₀ (by positivity), sub_mul, one_div_pow,
    div_mul_cancel₀ _ (by positivity)]
  linarith

theorem lpM_owf_id : LiuPass.IsOWF lpM id := by
  refine ⟨⟨fun _ => 1, ⟨0, 1, fun n => by simp⟩, [false], fun w => ?_⟩, fun A => ?_⟩
  · show lpM_run (lpM_pair [false] w) 1 = some w
    rw [lpM_pair]; exact lpM_run_true w 1 (by norm_num)
  · refine ⟨fun n => (2 : ℝ) * (1 / 2) ^ n, lpM_negl_two, fun n => ?_⟩
    unfold LiuPass.invSucc
    apply lpM_prUnif₂_two n (A.tape n) _ (LiuPass.unary n) (fun r => A.out r [])
    intro x r hxl hx
    rcases lpM_pair_unary_blind n x hxl with h | h
    · exact Or.inl h
    · right
      have h' : lpM.pair (LiuPass.unary n) x = [] := h
      simp only [id] at hx
      rw [h'] at hx
      exact hx.symm

/-! ### Every polynomial-time function on `lpM` stretches by at most a constant. -/

theorem lpM_ptc_len (G : List Bool → List Bool) (hG : LiuPass.PolyTimeComputable lpM G) :
    ∃ C : ℕ, ∀ w : List Bool, (G w).length ≤ w.length + C := by
  obtain ⟨T, _, Pi, hPi⟩ := hG
  refine ⟨Pi.length + 1, fun w => ?_⟩
  have h := hPi w
  have h' : lpM_run (lpM_pair Pi w) (T w.length) = some (G w) := h
  rw [lpM_run_eq_some] at h'
  have hl := lpM_pair_len Pi w
  rw [h'.2] at hl
  simp at hl
  omega

theorem lpM_no_condEPPRG (gamma : ℕ) (hgamma : 1 < gamma) (mu : ℕ → ℝ)
    (G : List Bool → List Bool) : ¬ LiuPass.IsCondEPPRG lpM gamma mu G := by
  intro hG
  obtain ⟨C, hC⟩ := lpM_ptc_len G hG.1
  have hlen := hG.2.1 (2 ^ (C + 1)) (List.replicate (2 ^ (C + 1)) false) (by simp)
  have h1 := hC (List.replicate (2 ^ (C + 1)) false)
  rw [hlen, Nat.log_pow (by norm_num)] at h1
  simp at h1
  nlinarith

/-! ### `K^t` on `lpM` is `|x| + 1`, and a length heuristic computes it. -/

theorem lpM_Kt (t : ℕ → ℕ) (x : List Bool) (ht : 0 < t x.length) :
    LiuPass.Kt lpM t x = x.length + 1 := by
  unfold LiuPass.Kt
  have hset : {l : ℕ | ∃ Pi : List Bool, Pi.length = l ∧ lpM.run Pi (t x.length) = some x} =
      {x.length + 1} := by
    ext l
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨Pi, hl, hr⟩
      have hr' : lpM_run Pi (t x.length) = some x := hr
      rw [lpM_run_eq_some] at hr'
      rw [← hl, hr'.2]; simp
    · intro hl
      refine ⟨true :: x, by simp [hl], ?_⟩
      exact lpM_run_true x _ (by omega)
  rw [hset, csInf_singleton]

def lpM_H : LiuPass.PPT lpM where
  tape := fun _ => 0
  out := fun r w => lpM_binRep ((lpM_pair r w).length + 1)
  tape_poly := ⟨0, 0, fun n => by simp⟩
  out_poly := ⟨fun _ => 1, ⟨0, 1, fun n => by simp⟩, [false, false, false], fun r w => by
    show lpM_run (lpM_pair [false, false, false] (lpM_pair r w)) 1 = _
    rw [lpM_pair]
    exact lpM_run_true _ _ (by norm_num)⟩

theorem lpM_heur_lb (t : ℕ → ℕ) (ht : ∀ n, 0 < t n) (n : ℕ) :
    1 - (1 / 2 : ℝ) ^ n ≤ LiuPass.heurSucc lpM (LiuPass.Kt lpM t) lpM_H n := by
  unfold LiuPass.heurSucc
  apply lpM_prUnif₂_ge n _ (LiuPass.unary n)
  intro x hxl hne
  rw [lpM_Kt t _ (ht _)]
  have hall : ¬ x.all (fun c => c) = true := by
    intro hall
    apply hne
    unfold LiuPass.unary
    rw [List.eq_replicate_iff]
    refine ⟨hxl, fun b hb => ?_⟩
    rw [List.all_eq_true] at hall
    simpa using hall b hb
  show LiuPass.bitsToNat (lpM_binRep ((lpM_pair [] x).length + 1)) = _
  rw [lpM_bitsToNat_binRep, lpM_pair]
  unfold lpM_gen
  rw [if_neg hall]
  simp

theorem lpM_not_mildlyHoA (t : ℕ → ℕ) (ht : ∀ n, 0 < t n) :
    ¬ LiuPass.MildlyHoA lpM (LiuPass.Kt lpM t) := by
  rintro ⟨p, ⟨k, c, hpk⟩, hppos, hH⟩
  obtain ⟨n₀, hn₀⟩ := hH lpM_H
  obtain ⟨N, hN⟩ := lpM_growth c k
  set n := max n₀ N with hn
  have h1 := hn₀ n (le_max_left _ _)
  have h2 := lpM_heur_lb t ht n
  have h3 := hN n (le_max_right _ _)
  have hp : ((p n : ℕ) : ℝ) ≤ (c : ℝ) * (n : ℝ) ^ k + c := by exact_mod_cast hpk n
  have hppos' : (0 : ℝ) < p n := by exact_mod_cast hppos n
  have h4 : (1 / 2 : ℝ) ^ n ≤ 1 / (p n : ℝ) := by
    rw [one_div_pow]
    apply one_div_le_one_div_of_le hppos'
    linarith
  linarith

open LiuPass in
theorem solution : ¬ (∀ (U : UMachine) (hf : ∃ f : BitStr → BitStr, IsOWF U f),
    ∃ t₀ : ℕ → ℕ, IsPoly t₀ ∧ ∀ gamma delta : ℕ, 1 < gamma → 1 < delta →
      ∃ G : BitStr → BitStr,
        IsCondEPPRG U gamma (fun n => 1 / (n : ℝ) ^ delta) G ∧
        ComputesInTime U (fun n => (gamma + delta) * t₀ n) G) := by
  intro H
  obtain ⟨t₀, _, h⟩ := H lpM ⟨id, lpM_owf_id⟩
  obtain ⟨G, hG, _⟩ := h 2 2 (by norm_num) (by norm_num)
  exact lpM_no_condEPPRG 2 (by norm_num) _ G hG
