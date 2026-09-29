-- Prove2me | solution 1 for LiuPass.weakOWF_of_HoA_Kt
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T11:05:22.032974+00:00
-- url     : https://prove2.me/submissions/93d47767-268a-46ac-ac67-652b10a5e537

import Mathlib
import Definitions.Def_LiuPass_crypto

/-! Disproof of 69e7c2e5 `LiuPass.weakOWF_of_HoA_Kt`.

The counterexample machines `lpX pt`. `UMachine`'s `univ_prog` is vacuous, because `evaln k` rejects inputs `≥ k`
and `2^m` distinct `encode`d strings cannot all lie below a polynomial `T m`. So a concrete machine can be built.
In `lpX pt` the programs that halt are exactly the literals `false :: x` (output `x`). `pair` hard-wires identity,
`sim`, `padProg`, and an inverter program `INV Q`. The inverter reads a tagged view and returns (by choice) a
preimage under the function that `Q` computes. `pair (1^n) y` is the tagged string `tagWrap n y`.

In `lpX true` a coin-free inverter sees the tagged image directly, so it inverts every polynomial-time `f` with
probability 1 and no weak one-way function exists. A heuristic sees `x` only if its first coin is `true`, if
`x` starts with the tag bits `[true,false]`, or if `x` is all ones. Otherwise its view is `[]` and its output is
a constant. Meanwhile `K^t x = |x| + 1` exactly (for `t = 1`), so the heuristic succeeds with probability at most
`1/2 + 1/4 + 2^-n < 7/8`. That makes `K^t` `1/8`-hard on average. -/

set_option autoImplicit false

open scoped Classical

/-! ### Generic facts: polynomial growth, vacuity of `univ_prog`, prefix counting -/

theorem lpX_growth (C k : ℕ) : ∃ N : ℕ, ∀ n ≥ N, (C : ℝ) * (n : ℝ) ^ k + C < 2 ^ n := by
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

theorem lpX_two_pow_le (F : List Bool → List Bool) (T : ℕ → ℕ)
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

theorem lpX_univ_vacuous (F : List Bool → List Bool) (T : ℕ → ℕ) (hT : LiuPass.IsPoly T)
    (h : LiuPass.CodeComputableInTime F T) : False := by
  obtain ⟨k, c, hk⟩ := hT
  obtain ⟨N, hN⟩ := lpX_growth c k
  have h1 := lpX_two_pow_le F T h N
  have h2 := hk N
  have h3 := hN N le_rfl
  have : ((2 : ℕ) ^ N : ℝ) ≤ (c : ℝ) * (N : ℝ) ^ k + c := by exact_mod_cast le_trans h1 h2
  push_cast at this
  linarith

theorem lpX_exists_v (n : ℕ) (x : List Bool) (hx : x.length = n) :
    ∃ v : Fin n → Bool, List.ofFn v = x := by
  subst hx
  exact ⟨x.get, List.ofFn_get x⟩

/-- at most `2^(m-k)` strings of length `m` start with a given length-`k` prefix -/
theorem lpX_card_prefix (m : ℕ) (pre : List Bool) :
    (Finset.univ.filter fun v : Fin m → Bool => (List.ofFn v).take pre.length = pre).card
      ≤ 2 ^ (m - pre.length) := by
  have := Finset.card_le_card_of_injOn (fun v : Fin m → Bool => List.ofFn v)
    (s := Finset.univ.filter fun v : Fin m → Bool => (List.ofFn v).take pre.length = pre)
    (t := (Finset.univ : Finset (Fin (m - pre.length) → Bool)).image
      (fun u => pre ++ List.ofFn u))
    (fun v hv => by
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
      obtain ⟨u, hu⟩ := lpX_exists_v (m - pre.length) ((List.ofFn v).drop pre.length)
        (by simp)
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      refine ⟨u, ?_⟩
      rw [hu]
      conv_rhs => rw [← List.take_append_drop pre.length (List.ofFn v)]
      rw [hv])
    (fun a _ b _ hab => List.ofFn_injective hab)
  calc _ ≤ _ := this
    _ ≤ (Finset.univ : Finset (Fin (m - pre.length) → Bool)).card := Finset.card_image_le
    _ = 2 ^ (m - pre.length) := by simp

/-! ### The machine family `lpX pt` -/

def lpX_runOut : List Bool → List Bool
  | false :: x => x
  | _ => []

def lpX_run (P : List Bool) (s : ℕ) : Option (List Bool) :=
  if s = 0 then none else
    match P with
    | false :: x => some x
    | _ => none

def lpX_tagWrap (m : ℕ) (b : List Bool) : List Bool :=
  true :: false :: (List.replicate m true ++ false :: b)

def lpX_simOut : List Bool → List Bool
  | true :: true :: x => x
  | _ => []

def lpX_isTag (b : List Bool) : Prop := ∃ m : ℕ, 1 ≤ m ∧ ∃ y : List Bool, b = lpX_tagWrap m y

def lpX_cnt (l : List Bool) : ℕ := (l.takeWhile (fun b => b)).length

/-- does `x'` (with its image `y`) explain the inverter's view `z`? -/
def lpX_invEq (pt : Bool) (x' y z : List Bool) : Prop :=
  if pt then lpX_tagWrap x'.length y = z else lpX_tagWrap 1 (lpX_tagWrap x'.length y) = z

noncomputable def lpX_gen (pt : Bool) (a b : List Bool) : List Bool :=
  if a ≠ [] ∧ a.all (fun c => c) = true then lpX_tagWrap a.length b
  else if b.all (fun c => c) = true then (if b = [] then [] else true :: true :: lpX_runOut a)
  else if pt = true ∧ a = [] ∧ lpX_isTag b then b
  else []

noncomputable def lpX_pair (pt : Bool) : List Bool → List Bool → List Bool
  | [], b => lpX_gen pt [] b
  | false :: x, b => lpX_gen pt (false :: x) b
  | [true], b => lpX_gen pt [true] b
  | true :: true :: x, b => lpX_gen pt (true :: true :: x) b
  | [true, false], b => lpX_gen pt [true, false] b
  | [true, false, false], b => false :: b
  | [true, false, true], b => false :: lpX_simOut b
  | true :: false :: false :: false :: x, b => lpX_gen pt (true :: false :: false :: false :: x) b
  | true :: false :: false :: true :: rest, b =>
      false :: (b.take (lpX_cnt rest) ++
        lpX_runOut (lpX_pair pt (rest.drop (lpX_cnt rest + 1)) (b.drop (lpX_cnt rest))))
  | true :: false :: true :: false :: x, b => lpX_gen pt (true :: false :: true :: false :: x) b
  | true :: false :: true :: true :: Q, b =>
      false :: (if h : ∃ x' : List Bool, 1 ≤ x'.length ∧
          lpX_invEq pt x' (lpX_runOut (lpX_pair pt Q x')) b then Classical.choose h else [])
termination_by a => a.length
decreasing_by all_goals (simp; try omega)

theorem lpX_run_eq_some (P x : List Bool) (s : ℕ) :
    lpX_run P s = some x ↔ s ≠ 0 ∧ P = false :: x := by
  unfold lpX_run
  by_cases hs : s = 0
  · simp [hs]
  · simp only [hs, if_false, ne_eq, not_false_eq_true, true_and]
    match P with
    | [] => simp
    | true :: y => simp
    | false :: y => simp

theorem lpX_run_false (x : List Bool) (s : ℕ) (hs : s ≠ 0) : lpX_run (false :: x) s = some x :=
  (lpX_run_eq_some _ _ _).2 ⟨hs, rfl⟩

theorem lpX_runOut_len (l : List Bool) : (lpX_runOut l).length ≤ l.length := by
  match l with
  | [] => simp [lpX_runOut]
  | true :: x => simp [lpX_runOut]
  | false :: x => simp [lpX_runOut]

theorem lpX_simOut_len (l : List Bool) : (lpX_simOut l).length ≤ l.length := by
  match l with
  | [] => simp [lpX_simOut]
  | [true] => simp [lpX_simOut]
  | true :: true :: x => simp [lpX_simOut]; omega
  | true :: false :: x => simp [lpX_simOut]
  | false :: x => simp [lpX_simOut]

theorem lpX_tagWrap_len (m : ℕ) (b : List Bool) :
    (lpX_tagWrap m b).length = m + b.length + 3 := by
  simp [lpX_tagWrap]; omega

theorem lpX_invEq_len (pt : Bool) (x' y z : List Bool) (h : lpX_invEq pt x' y z) :
    x'.length ≤ z.length := by
  unfold lpX_invEq at h
  split_ifs at h
  · rw [← h, lpX_tagWrap_len]; omega
  · rw [← h, lpX_tagWrap_len, lpX_tagWrap_len]; omega

theorem lpX_gen_len (pt : Bool) (a b : List Bool) :
    (lpX_gen pt a b).length ≤ a.length + b.length + 3 := by
  unfold lpX_gen
  split_ifs
  · rw [lpX_tagWrap_len]
  · simp
  · have := lpX_runOut_len a
    simp; omega
  · omega
  · simp

theorem lpX_pair_len (pt : Bool) (a b : List Bool) :
    (lpX_pair pt a b).length ≤ a.length + b.length + 3 := by
  induction a, b using lpX_pair.induct with
  | case1 b => have := lpX_gen_len pt [] b; rw [lpX_pair]; exact this
  | case2 x b => have := lpX_gen_len pt (false :: x) b; rw [lpX_pair]; exact this
  | case3 b => have := lpX_gen_len pt [true] b; rw [lpX_pair]; exact this
  | case4 x b => have := lpX_gen_len pt (true :: true :: x) b; rw [lpX_pair]; exact this
  | case5 b => have := lpX_gen_len pt [true, false] b; rw [lpX_pair]; exact this
  | case6 b => rw [lpX_pair]; simp; omega
  | case7 b => rw [lpX_pair]; have := lpX_simOut_len b; simp; omega
  | case8 x b =>
      have := lpX_gen_len pt (true :: false :: false :: false :: x) b; rw [lpX_pair]; exact this
  | case9 rest b ih =>
      rw [lpX_pair]
      have h1 := lpX_runOut_len
        (lpX_pair pt (rest.drop (lpX_cnt rest + 1)) (b.drop (lpX_cnt rest)))
      simp only [List.length_cons, List.length_append, List.length_take, List.length_drop] at ih h1 ⊢
      omega
  | case10 x b =>
      have := lpX_gen_len pt (true :: false :: true :: false :: x) b; rw [lpX_pair]; exact this
  | case11 Q b ih =>
      rw [lpX_pair]
      split_ifs with h
      · have := lpX_invEq_len pt _ _ _ (Classical.choose_spec h).2
        simp; omega
      · simp

theorem lpX_all_rep (t : ℕ) : (List.replicate t true).all (fun c => c) = true := by
  simp

theorem lpX_simOut_gen (pt : Bool) (a : List Bool) (t : ℕ) :
    lpX_simOut (lpX_gen pt a (List.replicate t true)) = (lpX_run a t).getD [] := by
  unfold lpX_gen
  by_cases ha : a ≠ [] ∧ a.all (fun c => c) = true
  · rw [if_pos ha]
    simp only [lpX_tagWrap, lpX_simOut]
    obtain ⟨hne, hall⟩ := ha
    match a, hne, hall with
    | true :: y, _, _ => simp [lpX_run]
    | false :: y, _, hall => simp at hall
  · rw [if_neg ha, if_pos (lpX_all_rep t)]
    by_cases ht : t = 0
    · subst ht; simp [lpX_simOut, lpX_run]
    · rw [if_neg (by simpa using ht)]
      simp only [lpX_simOut]
      unfold lpX_run
      rw [if_neg ht]
      match a with
      | [] => simp [lpX_runOut]
      | true :: y => simp [lpX_runOut]
      | false :: y => simp [lpX_runOut]

theorem lpX_simOut_pair (pt : Bool) (Pi : List Bool) (t : ℕ) :
    lpX_simOut (lpX_pair pt Pi (LiuPass.unary t)) = (lpX_run Pi t).getD [] := by
  unfold LiuPass.unary
  match Pi with
  | [] => rw [lpX_pair, lpX_simOut_gen]
  | false :: x => rw [lpX_pair, lpX_simOut_gen]
  | [true] => rw [lpX_pair, lpX_simOut_gen]
  | true :: true :: x => rw [lpX_pair, lpX_simOut_gen]
  | [true, false] => rw [lpX_pair, lpX_simOut_gen]
  | [true, false, false] => rw [lpX_pair]; simp [lpX_simOut, lpX_run]
  | [true, false, true] => rw [lpX_pair]; simp [lpX_simOut, lpX_run]
  | true :: false :: false :: false :: x => rw [lpX_pair, lpX_simOut_gen]
  | true :: false :: false :: true :: rest => rw [lpX_pair]; simp [lpX_simOut, lpX_run]
  | true :: false :: true :: false :: x => rw [lpX_pair, lpX_simOut_gen]
  | true :: false :: true :: true :: Q => rw [lpX_pair]; simp [lpX_simOut, lpX_run]

def lpX_padProg (Q : List Bool) (k : ℕ) : List Bool :=
  true :: false :: false :: true :: (List.replicate k true ++ false :: Q)

theorem lpX_cnt_pad (Q : List Bool) (k : ℕ) :
    lpX_cnt (List.replicate k true ++ false :: Q) = k := by
  unfold lpX_cnt
  induction k with
  | zero => simp
  | succ k _ => simp [List.replicate_succ]

theorem lpX_drop_pad (Q : List Bool) (k : ℕ) :
    (List.replicate k true ++ false :: Q).drop (k + 1) = Q := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ]; simpa using ih

theorem lpX_pair_pad (pt : Bool) (Q : List Bool) (k : ℕ) (w : List Bool) :
    lpX_pair pt (lpX_padProg Q k) w =
      false :: (w.take k ++ lpX_runOut (lpX_pair pt Q (w.drop k))) := by
  unfold lpX_padProg
  rw [lpX_pair, lpX_cnt_pad, lpX_drop_pad]

noncomputable def lpX (pt : Bool) : LiuPass.UMachine where
  run := lpX_run
  run_mono := by
    intro Pi t t' x htt' h
    rw [lpX_run_eq_some] at h ⊢
    exact ⟨by omega, h.2⟩
  pair := lpX_pair pt
  pairOverhead := 3
  pair_length_le := lpX_pair_len pt
  idProg := [true, false, false]
  run_idProg := by
    intro w t ht
    rw [lpX_pair]
    exact lpX_run_false w t (by omega)
  sim := [true, false, true]
  simTime := fun n => n + 1
  simTime_poly := ⟨1, 1, fun n => by simp⟩
  run_sim := by
    intro Pi t
    rw [lpX_pair, lpX_run_false _ _ (by omega), lpX_simOut_pair]
  padProg := lpX_padProg
  padOverhead := 1
  run_padProg := by
    intro Pi k t w y h
    rw [lpX_run_eq_some] at h
    rw [lpX_pair_pad, h.2]
    simp only [lpX_runOut]
    exact lpX_run_false _ _ (by omega)
  univ_prog := by
    intro F T hT h
    exact (lpX_univ_vacuous F T hT h).elim

/-! ### Shared facts about `lpX` -/

theorem lpX_pair_unary (pt : Bool) (n : ℕ) (hn : 1 ≤ n) (b : List Bool) :
    (lpX pt).pair (LiuPass.unary n) b = lpX_tagWrap n b := by
  show lpX_pair pt (List.replicate n true) b = _
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hg : lpX_gen pt (List.replicate (m + 1) true) b = lpX_tagWrap (m + 1) b := by
    unfold lpX_gen
    rw [if_pos ⟨by simp, by simp⟩]
    simp
  match m with
  | 0 => rw [show List.replicate (0 + 1) true = [true] from rfl, lpX_pair]; exact hg
  | j + 1 =>
      rw [show List.replicate (j + 1 + 1) true = true :: true :: List.replicate j true from rfl,
        lpX_pair]
      exact hg

theorem lpX_tagWrap_inj (m m' : ℕ) (y y' : List Bool)
    (h : lpX_tagWrap m y = lpX_tagWrap m' y') : m = m' ∧ y = y' := by
  unfold lpX_tagWrap at h
  simp only [List.cons.injEq, true_and] at h
  induction m generalizing m' with
  | zero =>
      match m' with
      | 0 => simpa using h
      | _ + 1 => simp [List.replicate_succ] at h
  | succ k ih =>
      match m' with
      | 0 => simp [List.replicate_succ] at h
      | k' + 1 =>
          simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
          have := ih k' h
          exact ⟨by omega, this.2⟩

theorem lpX_tagWrap_not_all (m : ℕ) (b : List Bool) :
    ¬ (lpX_tagWrap m b).all (fun c => c) = true := by
  simp [lpX_tagWrap]

/-- computed functions are read off the literal program -/
theorem lpX_ptc_out (pt : Bool) (g : List Bool → List Bool)
    (hg : LiuPass.PolyTimeComputable (lpX pt) g) :
    ∃ Pi : List Bool, ∀ x, lpX_pair pt Pi x = false :: g x := by
  obtain ⟨T, _, Pi, hPi⟩ := hg
  refine ⟨Pi, fun x => ?_⟩
  have h : lpX_run (lpX_pair pt Pi x) (T x.length) = some (g x) := hPi x
  rw [lpX_run_eq_some] at h
  exact h.2

theorem lpX_ppt_out (pt : Bool) (A : LiuPass.PPT (lpX pt)) :
    ∃ Pi : List Bool, ∀ r w, lpX_pair pt Pi (lpX_pair pt r w) = false :: A.out r w := by
  obtain ⟨T, _, Pi, hPi⟩ := A.out_poly
  refine ⟨Pi, fun r w => ?_⟩
  have h : lpX_run (lpX_pair pt Pi (lpX_pair pt r w)) (T (r.length + w.length)) =
      some (A.out r w) := hPi r w
  rw [lpX_run_eq_some] at h
  exact h.2

/-- the inverter program for a function computed by `Pi` -/
noncomputable def lpX_INV (pt : Bool) (Pi : List Bool) (tp : ℕ) : LiuPass.PPT (lpX pt) where
  tape := fun _ => tp
  out := fun r w => lpX_runOut (lpX_pair pt (true :: false :: true :: true :: Pi) (lpX_pair pt r w))
  tape_poly := ⟨0, tp, fun n => by simp⟩
  out_poly := ⟨fun _ => 1, ⟨0, 1, fun n => by simp⟩, true :: false :: true :: true :: Pi,
    fun r w => by
      show lpX_run (lpX_pair pt (true :: false :: true :: true :: Pi) (lpX_pair pt r w)) 1 =
        some (lpX_runOut (lpX_pair pt (true :: false :: true :: true :: Pi) (lpX_pair pt r w)))
      obtain ⟨X, hX⟩ : ∃ X, lpX_pair pt (true :: false :: true :: true :: Pi) (lpX_pair pt r w) =
          false :: X := ⟨_, by rw [lpX_pair]⟩
      rw [hX]
      exact lpX_run_false X 1 (by norm_num)⟩

/-- the inverter finds a genuine preimage whenever its view is explained by some `x` -/
theorem lpX_INV_correct (pt : Bool) (Pi : List Bool) (g : List Bool → List Bool)
    (hPi : ∀ x, lpX_pair pt Pi x = false :: g x) (z x : List Bool) (hx : 1 ≤ x.length)
    (hz : lpX_invEq pt x (g x) z) :
    g (lpX_runOut (lpX_pair pt (true :: false :: true :: true :: Pi) z)) = g x := by
  have hro : ∀ x', lpX_runOut (lpX_pair pt Pi x') = g x' := fun x' => by rw [hPi]; rfl
  rw [lpX_pair]
  have hex : ∃ x' : List Bool, 1 ≤ x'.length ∧
      lpX_invEq pt x' (lpX_runOut (lpX_pair pt Pi x')) z := ⟨x, hx, by rw [hro]; exact hz⟩
  have key : ∀ x'' : List Bool, (1 ≤ x''.length ∧
      lpX_invEq pt x'' (lpX_runOut (lpX_pair pt Pi x'')) z) → g x'' = g x := by
    rintro x'' ⟨_, h2⟩
    rw [hro] at h2
    unfold lpX_invEq at h2 hz
    cases pt with
    | true =>
        simp only [if_true] at h2 hz
        rw [← hz] at h2
        exact (lpX_tagWrap_inj _ _ _ _ h2).2
    | false =>
        simp only [Bool.false_eq_true, if_false] at h2 hz
        rw [← hz] at h2
        have := (lpX_tagWrap_inj _ _ _ _ h2).2
        exact (lpX_tagWrap_inj _ _ _ _ this).2
  rw [dif_pos hex]
  exact key _ (Classical.choose_spec hex)

/-! ### Probability bounds -/

theorem lpX_prUnif₂_ub (n m : ℕ) (P : List Bool → List Bool → Prop) (c : ℝ) (N : ℕ)
    (h : (Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      P (List.ofFn v.1) (List.ofFn v.2)).card ≤ N) (hN : (N : ℝ) ≤ c * 2 ^ (n + m)) :
    LiuPass.prUnif₂ n m P ≤ c := by
  unfold LiuPass.prUnif₂
  rw [div_le_iff₀ (by positivity)]
  have : (((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      P (List.ofFn v.1) (List.ofFn v.2)).card : ℕ) : ℝ) ≤ N := by exact_mod_cast h
  linarith

theorem lpX_card_prefixR (m : ℕ) (pre : List Bool) :
    ((Finset.univ.filter fun v : Fin m → Bool => (List.ofFn v).take pre.length = pre).card : ℝ)
      ≤ 2 ^ m / 2 ^ pre.length := by
  by_cases hm : pre.length ≤ m
  · have h := lpX_card_prefix m pre
    have h' : ((Finset.univ.filter fun v : Fin m → Bool =>
        (List.ofFn v).take pre.length = pre).card : ℝ) ≤ ((2 ^ (m - pre.length) : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [le_div_iff₀ (by positivity)]
    calc _ ≤ ((2 ^ (m - pre.length) : ℕ) : ℝ) * 2 ^ pre.length :=
          mul_le_mul_of_nonneg_right h' (by positivity)
      _ = 2 ^ m := by
          push_cast
          rw [← pow_add, Nat.sub_add_cancel hm]
  · have hempty : (Finset.univ.filter fun v : Fin m → Bool =>
        (List.ofFn v).take pre.length = pre) = ∅ := by
      apply Finset.filter_false_of_mem
      intro v _ hv
      have := congrArg List.length hv
      simp at this
      omega
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-- pairs whose second component starts with `pre` -/
theorem lpX_card_snd_prefix (n m : ℕ) (pre : List Bool) :
    ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      (List.ofFn v.2).take pre.length = pre).card : ℝ) ≤ 2 ^ n * (2 ^ m / 2 ^ pre.length) := by
  have h := Finset.card_le_card_of_injOn (fun v : (Fin n → Bool) × (Fin m → Bool) => v)
    (s := Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      (List.ofFn v.2).take pre.length = pre)
    (t := (Finset.univ : Finset (Fin n → Bool)) ×ˢ
      (Finset.univ.filter fun u : Fin m → Bool => (List.ofFn u).take pre.length = pre))
    (fun v hv => by
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
      simp only [Finset.coe_product, Finset.coe_univ, Finset.coe_filter, Finset.mem_univ,
        true_and, Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq]
      exact hv)
    (fun a _ b _ hab => hab)
  rw [Finset.card_product] at h
  have h2 := lpX_card_prefixR m pre
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  have h' : ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      (List.ofFn v.2).take pre.length = pre).card : ℝ) ≤ (2 ^ n : ℝ) *
      ((Finset.univ.filter fun u : Fin m → Bool =>
        (List.ofFn u).take pre.length = pre).card : ℝ) := by exact_mod_cast h
  calc _ ≤ _ := h'
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- pairs whose first component starts with `pre` -/
theorem lpX_card_fst_prefix (n m : ℕ) (pre : List Bool) :
    ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      (List.ofFn v.1).take pre.length = pre).card : ℝ) ≤ (2 ^ n / 2 ^ pre.length) * 2 ^ m := by
  have h := Finset.card_le_card_of_injOn (fun v : (Fin n → Bool) × (Fin m → Bool) => v)
    (s := Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      (List.ofFn v.1).take pre.length = pre)
    (t := (Finset.univ.filter fun u : Fin n → Bool => (List.ofFn u).take pre.length = pre) ×ˢ
      (Finset.univ : Finset (Fin m → Bool)))
    (fun v hv => by
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
      simp only [Finset.coe_product, Finset.coe_univ, Finset.coe_filter, Finset.mem_univ,
        true_and, Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq, and_true]
      exact hv)
    (fun a _ b _ hab => hab)
  rw [Finset.card_product] at h
  have h2 := lpX_card_prefixR n pre
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  have h' : ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      (List.ofFn v.1).take pre.length = pre).card : ℝ) ≤
      ((Finset.univ.filter fun u : Fin n → Bool =>
        (List.ofFn u).take pre.length = pre).card : ℝ) * (2 ^ m : ℝ) := by exact_mod_cast h
  calc _ ≤ _ := h'
    _ ≤ _ := mul_le_mul_of_nonneg_right h2 (by positivity)

theorem lpX_card_fst_fixed (n m : ℕ) (x₀ : List Bool) :
    (Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) => List.ofFn v.1 = x₀).card
      ≤ 2 ^ m := by
  have := Finset.card_le_card_of_injOn (fun v : (Fin n → Bool) × (Fin m → Bool) => v.2)
    (s := Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) => List.ofFn v.1 = x₀)
    (t := Finset.univ) (fun _ _ => by simp)
    (fun a ha b hb hab => by
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
      exact Prod.ext (List.ofFn_injective (ha.trans hb.symm)) hab)
  simpa using this

/-! ### Generic probability bounds for predicates -/

theorem lpX_prUnif₂_coin_or_fixed (n m : ℕ) (P : List Bool → List Bool → Prop) (c : List Bool)
    (h : ∀ x r : List Bool, x.length = n → r.length = m → P x r →
      r.take [true].length = [true] ∨ x = c) :
    LiuPass.prUnif₂ n m P ≤ 1 / 2 + (1 / 2) ^ n := by
  unfold LiuPass.prUnif₂
  rw [div_le_iff₀ (by positivity)]
  have hsub : (Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      P (List.ofFn v.1) (List.ofFn v.2)) ⊆
      (Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
        (List.ofFn v.2).take [true].length = [true]) ∪
      (Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) => List.ofFn v.1 = c) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hv ⊢
    exact h _ _ (by simp) (by simp) hv
  have hc := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hc' : ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      P (List.ofFn v.1) (List.ofFn v.2)).card : ℝ) ≤
      ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
        (List.ofFn v.2).take [true].length = [true]).card : ℝ) +
      ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
        List.ofFn v.1 = c).card : ℝ) := by exact_mod_cast hc
  have h1 : ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      (List.ofFn v.2).take [true].length = [true]).card : ℝ) ≤ 1 / 2 * 2 ^ (n + m) := by
    calc _ ≤ _ := lpX_card_snd_prefix n m [true]
      _ = _ := by simp only [List.length_singleton, pow_one, pow_add]; ring
  have h2 : ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      List.ofFn v.1 = c).card : ℝ) ≤ (1 / 2) ^ n * 2 ^ (n + m) := by
    calc _ ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast lpX_card_fst_fixed n m c
      _ = _ := by push_cast; rw [pow_add, one_div_pow]; field_simp
  linarith

theorem lpX_prUnif₂_coin_or_fixed_or_tag (n m : ℕ) (P : List Bool → List Bool → Prop)
    (c : List Bool)
    (h : ∀ x r : List Bool, x.length = n → r.length = m → P x r →
      r.take [true].length = [true] ∨ x = c ∨ x.take [true, false].length = [true, false]) :
    LiuPass.prUnif₂ n m P ≤ 1 / 2 + (1 / 2) ^ n + 1 / 4 := by
  unfold LiuPass.prUnif₂
  rw [div_le_iff₀ (by positivity)]
  have hsub : (Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      P (List.ofFn v.1) (List.ofFn v.2)) ⊆
      ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
        (List.ofFn v.2).take [true].length = [true]) ∪
      (Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) => List.ofFn v.1 = c)) ∪
      (Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
        (List.ofFn v.1).take [true, false].length = [true, false]) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hv ⊢
    rcases h _ _ (by simp) (by simp) hv with h' | h' | h'
    · exact Or.inl (Or.inl h')
    · exact Or.inl (Or.inr h')
    · exact Or.inr h'
  have hc := le_trans (Finset.card_le_card hsub)
    (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hc' : ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      P (List.ofFn v.1) (List.ofFn v.2)).card : ℝ) ≤
      ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
        (List.ofFn v.2).take [true].length = [true]).card : ℝ) +
      ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
        List.ofFn v.1 = c).card : ℝ) +
      ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
        (List.ofFn v.1).take [true, false].length = [true, false]).card : ℝ) := by
    exact_mod_cast hc
  have h1 : ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      (List.ofFn v.2).take [true].length = [true]).card : ℝ) ≤ 1 / 2 * 2 ^ (n + m) := by
    calc _ ≤ _ := lpX_card_snd_prefix n m [true]
      _ = _ := by simp only [List.length_singleton, pow_one, pow_add]; ring
  have h2 : ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      List.ofFn v.1 = c).card : ℝ) ≤ (1 / 2) ^ n * 2 ^ (n + m) := by
    calc _ ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast lpX_card_fst_fixed n m c
      _ = _ := by push_cast; rw [pow_add, one_div_pow]; field_simp
  have h3 : ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      (List.ofFn v.1).take [true, false].length = [true, false]).card : ℝ) ≤
      1 / 4 * 2 ^ (n + m) := by
    calc _ ≤ _ := lpX_card_fst_prefix n m [true, false]
      _ = _ := by simp only [List.length_cons, List.length_nil, pow_add]; ring
  linarith

theorem lpX_prUnif₂_ge_half (n : ℕ) (P : List Bool → List Bool → Prop)
    (h : ∀ x : List Bool, x.length = n → P x [true]) : 1 / 2 ≤ LiuPass.prUnif₂ n 1 P := by
  unfold LiuPass.prUnif₂
  rw [le_div_iff₀ (by positivity)]
  have hsub : ((Finset.univ : Finset (Fin n → Bool)).image
      (fun v1 => (v1, (fun _ => true : Fin 1 → Bool)))) ⊆
      (Finset.univ.filter fun v : (Fin n → Bool) × (Fin 1 → Bool) =>
        P (List.ofFn v.1) (List.ofFn v.2)) := by
    intro v hv
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨v1, rfl⟩ := hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h _ (by simp)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun a b hab => (Prod.ext_iff.mp hab).1)] at hc
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hc
  have hc' : ((2 ^ n : ℕ) : ℝ) ≤ ((Finset.univ.filter fun v : (Fin n → Bool) × (Fin 1 → Bool) =>
      P (List.ofFn v.1) (List.ofFn v.2)).card : ℝ) := by exact_mod_cast hc
  push_cast at hc'
  rw [pow_add]
  linarith

theorem lpX_prUnif₂_one (n : ℕ) (P : List Bool → List Bool → Prop)
    (h : ∀ x : List Bool, x.length = n → P x []) : 1 ≤ LiuPass.prUnif₂ n 0 P := by
  unfold LiuPass.prUnif₂
  rw [le_div_iff₀ (by positivity)]
  have hfull : (Finset.univ.filter fun v : (Fin n → Bool) × (Fin 0 → Bool) =>
      P (List.ofFn v.1) (List.ofFn v.2)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro v _
    have h2 : List.ofFn v.2 = [] := by rw [List.ofFn_eq_nil_iff]
    rw [h2]
    exact h _ (by simp)
  rw [hfull]
  simp

/-! ### `lpX true`: a coin-free inverter sees the tagged image, a heuristic is blind -/

theorem lpV_Kt (t : ℕ → ℕ) (x : List Bool) (ht : 0 < t x.length) :
    LiuPass.Kt (lpX true) t x = x.length + 1 := by
  unfold LiuPass.Kt
  have hset : {l : ℕ | ∃ Pi : List Bool, Pi.length = l ∧ (lpX true).run Pi (t x.length) = some x} =
      {x.length + 1} := by
    ext l
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨Pi, hl, hr⟩
      have hr' : lpX_run Pi (t x.length) = some x := hr
      rw [lpX_run_eq_some] at hr'
      rw [← hl, hr'.2]; simp
    · intro hl
      refine ⟨false :: x, by simp [hl], ?_⟩
      exact lpX_run_false x _ (by omega)
  rw [hset, csInf_singleton]

theorem lpV_blind (r x : List Bool) (hr : ¬ r.take [true].length = [true])
    (hx : ¬ x.all (fun c => c) = true)
    (htag : ¬ x.take [true, false].length = [true, false]) : lpX_pair true r x = [] := by
  have hnt : ¬ lpX_isTag x := by
    rintro ⟨m, _, y, rfl⟩
    apply htag
    simp [lpX_tagWrap]
  match r with
  | [] => rw [lpX_pair]; unfold lpX_gen; simp [hx, hnt]
  | false :: y => rw [lpX_pair]; unfold lpX_gen; simp [hx]
  | true :: y => simp at hr

theorem lpV_HoA : LiuPass.HoA (lpX true) (fun n => 1 / (((fun _ => 8) n : ℕ) : ℝ))
    (LiuPass.Kt (lpX true) (fun _ => 1)) := by
  intro H
  obtain ⟨Pi, hPi⟩ := lpX_ppt_out true H
  set c := lpX_runOut (lpX_pair true Pi []) with hc
  refine ⟨LiuPass.bitsToNat c + 4, fun n hn => ?_⟩
  unfold LiuPass.heurSucc
  have hb := lpX_prUnif₂_coin_or_fixed_or_tag n (H.tape n)
    (fun x r => LiuPass.bitsToNat (H.out r x) = LiuPass.Kt (lpX true) (fun _ => 1) x)
    (LiuPass.unary n)
    (fun x r hx _ hs => by
      by_cases hr : r.take [true].length = [true]
      · exact Or.inl hr
      by_cases hall : x.all (fun c => c) = true
      · right; left
        unfold LiuPass.unary
        rw [List.eq_replicate_iff]
        refine ⟨hx, fun b hb => ?_⟩
        rw [List.all_eq_true] at hall
        simpa using hall b hb
      by_cases htag : x.take [true, false].length = [true, false]
      · exact Or.inr (Or.inr htag)
      exfalso
      have h0 := lpV_blind r x hr hall htag
      have h1 := hPi r x
      rw [h0] at h1
      have hout : H.out r x = c := by rw [hc, h1]; rfl
      rw [hout, lpV_Kt _ _ (by norm_num), hx] at hs
      omega)
  have hpow : (1 / 2 : ℝ) ^ n ≤ 1 / 16 := by
    calc (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ 4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 16 := by norm_num
  have : (1 : ℝ) / ((8 : ℕ) : ℝ) = 1 / 8 := by norm_num
  show _ < 1 - 1 / ((8 : ℕ) : ℝ)
  rw [this]
  linarith

theorem lpV_no_weakOWF (f : List Bool → List Bool) : ¬ LiuPass.IsWeakOWF (lpX true) f := by
  rintro ⟨q, _, hqpos, hptc, hA⟩
  obtain ⟨Pi, hPi⟩ := lpX_ptc_out true f hptc
  obtain ⟨n₀, hn₀⟩ := hA (lpX_INV true Pi 0)
  set n := max n₀ 1
  have hn : 1 ≤ n := le_max_right _ _
  have h1 := hn₀ n (le_max_left _ _)
  have h2 : 1 ≤ LiuPass.invSucc (lpX true) f (lpX_INV true Pi 0) n := by
    unfold LiuPass.invSucc
    apply lpX_prUnif₂_one n
    intro x hx
    rw [lpX_pair_unary true n hn]
    show f (lpX_runOut (lpX_pair true (true :: false :: true :: true :: Pi)
      (lpX_pair true [] (lpX_tagWrap n (f x))))) = _
    have hw : lpX_pair true [] (lpX_tagWrap n (f x)) = lpX_tagWrap n (f x) := by
      rw [lpX_pair]; unfold lpX_gen
      rw [if_neg (by simp), if_neg (lpX_tagWrap_not_all n (f x)),
        if_pos ⟨rfl, rfl, n, hn, f x, rfl⟩]
    rw [hw]
    apply lpX_INV_correct true Pi f hPi _ _ (by omega)
    unfold lpX_invEq
    simp [hx]
  have hq : (0 : ℝ) < 1 / (q n : ℝ) := by
    have : (0 : ℝ) < q n := by exact_mod_cast hqpos n
    positivity
  linarith

open LiuPass in
theorem solution : ¬ (∀ (U : UMachine) (t p : ℕ → ℕ) (ht : IsPoly t) (htpos : ∀ n, 0 < t n)
    (hp : IsPoly p) (hppos : ∀ n, 0 < p n) (hhard : HoA U (fun n => 1 / (p n : ℝ)) (Kt U t)),
    ∃ f : BitStr → BitStr, IsWeakOWF U f) := by
  intro H
  obtain ⟨f, hf⟩ := H (lpX true) (fun _ => 1) (fun _ => 8) ⟨0, 1, fun n => by simp⟩
    (fun _ => one_pos) ⟨0, 8, fun n => by simp⟩ (fun _ => by norm_num) lpV_HoA
  exact lpV_no_weakOWF f hf
