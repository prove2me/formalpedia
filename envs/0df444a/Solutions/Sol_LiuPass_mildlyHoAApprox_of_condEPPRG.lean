-- Prove2me | solution 1 for LiuPass.mildlyHoAApprox_of_condEPPRG
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T15:27:27.312859+00:00
-- url     : https://prove2.me/submissions/cd12eef6-981e-4a74-ab45-f5d7aed15d74

import Mathlib
import Definitions.Def_LiuPass_crypto

set_option autoImplicit false

open scoped Classical

def lpM_G (gamma : ℕ) (s : List Bool) : List Bool :=
  s ++ List.replicate (gamma * Nat.log 2 s.length) false

def lpM_cnt (l : List Bool) : ℕ := (l.takeWhile (fun b => b)).length

theorem lpM_cnt_le (l : List Bool) : lpM_cnt l ≤ l.length := by
  unfold lpM_cnt
  induction l with
  | nil => simp
  | cons b bs ih =>
    cases b <;> simp [List.takeWhile]
    omega

def lpM_genOut (rest : List Bool) : List Bool :=
  let k := lpM_cnt rest
  let u := rest.drop (k + 1)
  let p := u.take k
  let r1 := u.drop k
  let gamma := lpM_cnt r1
  let seed := r1.drop (gamma + 1)
  p ++ lpM_G gamma seed

def lpM_progOut : List Bool → Option (List Bool)
  | true :: x => some x
  | false :: false :: false :: false :: rest => some (lpM_genOut rest)
  | _ => none

def lpM_run (P : List Bool) (s : ℕ) : Option (List Bool) :=
  if s = 0 then none else lpM_progOut P

noncomputable def lpM_ktVal (x : List Bool) : ℕ :=
  sInf {l : ℕ | ∃ Pi : List Bool, Pi.length = l ∧ lpM_progOut Pi = some x}

theorem lpM_ktVal_le (x : List Bool) : lpM_ktVal x ≤ x.length + 1 := by
  unfold lpM_ktVal
  exact Nat.sInf_le ⟨true :: x, by simp, rfl⟩

def lpM_binRep : ℕ → List Bool
  | 0 => []
  | (n + 1) => lpM_binRep ((n + 1) / 2) ++ [decide ((n + 1) % 2 = 1)]
decreasing_by omega

def lpM_prepend (q : List Bool) : List Bool → List Bool
  | true :: x => true :: (q ++ x)
  | false :: false :: false :: false :: rest =>
      let k := lpM_cnt rest
      let u := rest.drop (k + 1)
      false :: false :: false :: false ::
        (List.replicate (q.length + k) true ++ false :: (q ++ u))
  | _ => []

def lpM_simProg : List Bool → List Bool
  | false :: true :: x => true :: x
  | false :: false :: true :: rest => false :: false :: false :: false :: rest
  | _ => [true]

def lpM_gen (a b : List Bool) : List Bool :=
  if b.all (fun c => c) then
    if b = [] then []
    else match a with
      | true :: x => false :: true :: x
      | false :: false :: false :: false :: rest => false :: false :: true :: rest
      | _ => []
  else match a with
    | true :: _ => []
    | _ => a ++ b

noncomputable def lpM_pair : List Bool → List Bool → List Bool
  | [], b => lpM_gen [] b
  | true :: x, b => lpM_gen (true :: x) b
  | [false], b => true :: b
  | false :: true :: rest, b =>
      lpM_prepend (b.take (lpM_cnt rest))
        (lpM_pair (rest.drop (lpM_cnt rest + 1)) (b.drop (lpM_cnt rest)))
  | [false, false], b => lpM_simProg b
  | [false, false, false], b => true :: lpM_binRep (lpM_ktVal b)
  | false :: false :: false :: false :: rest, b =>
      lpM_gen (false :: false :: false :: false :: rest) b
  | false :: false :: false :: true :: d, b =>
      lpM_gen (false :: false :: false :: true :: d) b
  | false :: false :: true :: d, b =>
      false :: false :: false :: false :: false ::
        (List.replicate (lpM_cnt d) true ++ false :: b)
termination_by a => a.length
decreasing_by simp; omega

theorem lpM_run_true (x : List Bool) (s : ℕ) (hs : s ≠ 0) : lpM_run (true :: x) s = some x := by
  simp [lpM_run, hs, lpM_progOut]

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

theorem lpM_prepend_len (q P : List Bool) :
    (lpM_prepend q P).length ≤ 2 * q.length + P.length + 1 := by
  match P with
  | [] => simp [lpM_prepend]
  | true :: x => simp [lpM_prepend]; omega
  | [false] => simp [lpM_prepend]
  | false :: true :: _ => simp [lpM_prepend]
  | [false, false] => simp [lpM_prepend]
  | false :: false :: true :: _ => simp [lpM_prepend]
  | [false, false, false] => simp [lpM_prepend]
  | false :: false :: false :: true :: _ => simp [lpM_prepend]
  | false :: false :: false :: false :: rest =>
    have hcnt := lpM_cnt_le rest
    simp [lpM_prepend]
    omega

theorem lpM_simProg_len (b : List Bool) : (lpM_simProg b).length ≤ b.length + 1 := by
  match b with
  | false :: true :: x => simp [lpM_simProg]
  | false :: false :: true :: rest => simp [lpM_simProg]
  | [] => simp [lpM_simProg]
  | true :: _ => simp [lpM_simProg]
  | [false] => simp [lpM_simProg]
  | [false, false] => simp [lpM_simProg]
  | false :: false :: false :: _ => simp [lpM_simProg]

theorem lpM_gen_len (a b : List Bool) : (lpM_gen a b).length ≤ a.length + b.length + 1 := by
  unfold lpM_gen
  split_ifs
  · simp
  · match a with
    | true :: x => simp
    | false :: false :: false :: false :: rest => simp; omega
    | [] => simp
    | [false] => simp
    | false :: true :: _ => simp
    | [false, false] => simp
    | false :: false :: true :: _ => simp
    | [false, false, false] => simp
    | false :: false :: false :: true :: _ => simp
  · match a with
    | [] => simp
    | true :: x => simp
    | false :: x => simp

theorem lpM_pair_len (a b : List Bool) : (lpM_pair a b).length ≤ a.length + b.length + 3 := by
  induction a, b using lpM_pair.induct with
  | case1 b => have := lpM_gen_len [] b; rw [lpM_pair]; simp at this ⊢; omega
  | case2 x b => have := lpM_gen_len (true :: x) b; rw [lpM_pair]; simp at this ⊢; omega
  | case3 b => rw [lpM_pair]; simp; omega
  | case4 rest b ih =>
      rw [lpM_pair]
      have h1 := lpM_prepend_len (b.take (lpM_cnt rest))
        (lpM_pair (rest.drop (lpM_cnt rest + 1)) (b.drop (lpM_cnt rest)))
      have hcnt := lpM_cnt_le rest
      simp only [List.length_cons, List.length_take, List.length_drop] at ih h1 ⊢
      omega
  | case5 b => rw [lpM_pair]; have := lpM_simProg_len b; simp; omega
  | case6 b =>
      rw [lpM_pair]
      have h1 := lpM_binRep_len (lpM_ktVal b)
      have h2 := lpM_ktVal_le b
      simp; omega
  | case7 rest b =>
      have := lpM_gen_len (false :: false :: false :: false :: rest) b
      rw [lpM_pair]; simp at this ⊢; omega
  | case8 d b =>
      have := lpM_gen_len (false :: false :: false :: true :: d) b
      rw [lpM_pair]; simp at this ⊢; omega
  | case9 d b =>
      rw [lpM_pair]
      have hcnt := lpM_cnt_le d
      simp; omega

theorem lpM_all_rep (t : ℕ) : (List.replicate t true).all (fun c => c) = true := by
  simp

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

theorem lpM_progOut_prepend (q P y : List Bool) (h : lpM_progOut P = some y) :
    lpM_progOut (lpM_prepend q P) = some (q ++ y) := by
  match P with
  | true :: x =>
      simp only [lpM_progOut, Option.some.injEq] at h
      subst h
      simp [lpM_prepend, lpM_progOut]
  | false :: false :: false :: false :: rest =>
      simp only [lpM_progOut, Option.some.injEq] at h
      subst h
      simp only [lpM_prepend, lpM_progOut, Option.some.injEq, lpM_genOut]
      rw [lpM_cnt_pad, lpM_drop_pad]
      have htake : (q ++ rest.drop (lpM_cnt rest + 1)).take (q.length + lpM_cnt rest) =
          q ++ (rest.drop (lpM_cnt rest + 1)).take (lpM_cnt rest) := by
        rw [List.take_append]; simp
      have hdrop : (q ++ rest.drop (lpM_cnt rest + 1)).drop (q.length + lpM_cnt rest) =
          (rest.drop (lpM_cnt rest + 1)).drop (lpM_cnt rest) := by
        rw [List.drop_append]; simp
      rw [htake, hdrop, List.append_assoc]
  | [] => simp [lpM_progOut] at h
  | [false] => simp [lpM_progOut] at h
  | false :: true :: _ => simp [lpM_progOut] at h
  | [false, false] => simp [lpM_progOut] at h
  | false :: false :: true :: _ => simp [lpM_progOut] at h
  | [false, false, false] => simp [lpM_progOut] at h
  | false :: false :: false :: true :: _ => simp [lpM_progOut] at h

theorem lpM_simProg_prepend_default (q P : List Bool) :
    lpM_simProg (lpM_prepend q P) = [true] := by
  match P with
  | true :: x => simp [lpM_prepend, lpM_simProg]
  | false :: false :: false :: false :: rest => simp [lpM_prepend, lpM_simProg]
  | [] => simp [lpM_prepend, lpM_simProg]
  | [false] => simp [lpM_prepend, lpM_simProg]
  | false :: true :: _ => simp [lpM_prepend, lpM_simProg]
  | [false, false] => simp [lpM_prepend, lpM_simProg]
  | false :: false :: true :: _ => simp [lpM_prepend, lpM_simProg]
  | [false, false, false] => simp [lpM_prepend, lpM_simProg]
  | false :: false :: false :: true :: _ => simp [lpM_prepend, lpM_simProg]

theorem lpM_simProg_unary (t : ℕ) : lpM_simProg (LiuPass.unary t) = [true] := by
  unfold LiuPass.unary
  cases t with
  | zero => simp [lpM_simProg]
  | succ m => simp [List.replicate_succ, lpM_simProg]

theorem lpM_run_sim_pair (Pi : List Bool) (t : ℕ) (s : ℕ) (hs : s ≠ 0) :
    lpM_run (lpM_simProg (lpM_pair Pi (LiuPass.unary t))) s =
      some ((lpM_run Pi t).getD []) := by
  simp only [lpM_run, hs, if_false]
  match Pi with
  | [] =>
      rw [lpM_pair]; unfold lpM_gen LiuPass.unary
      rw [if_pos (lpM_all_rep t)]
      split_ifs <;> simp [lpM_simProg, lpM_progOut]
  | true :: x =>
      rw [lpM_pair]; unfold lpM_gen LiuPass.unary
      rw [if_pos (lpM_all_rep t)]
      by_cases ht : t = 0
      · subst ht; simp [lpM_simProg, lpM_progOut]
      · rw [if_neg (by simpa using ht)]; simp [lpM_simProg, lpM_progOut, ht]
  | [false] => rw [lpM_pair]; simp [lpM_simProg, lpM_progOut]
  | false :: true :: rest =>
      rw [lpM_pair, lpM_simProg_prepend_default]; simp [lpM_progOut]
  | [false, false] =>
      rw [lpM_pair, lpM_simProg_unary]; simp [lpM_simProg, lpM_progOut]
  | [false, false, false] => rw [lpM_pair]; simp [lpM_simProg, lpM_progOut]
  | false :: false :: false :: false :: rest =>
      rw [lpM_pair]; unfold lpM_gen LiuPass.unary
      rw [if_pos (lpM_all_rep t)]
      by_cases ht : t = 0
      · subst ht; simp [lpM_simProg, lpM_progOut]
      · rw [if_neg (by simpa using ht)]; simp [lpM_simProg, lpM_progOut, ht]
  | false :: false :: false :: true :: d =>
      rw [lpM_pair]; unfold lpM_gen LiuPass.unary
      rw [if_pos (lpM_all_rep t)]
      split_ifs <;> simp [lpM_simProg, lpM_progOut]
  | false :: false :: true :: d =>
      rw [lpM_pair]; simp [lpM_simProg, lpM_progOut]

def lpM_padProg (Q : List Bool) (k : ℕ) : List Bool :=
  false :: true :: (List.replicate k true ++ false :: Q)

theorem lpM_pair_pad (Q : List Bool) (k : ℕ) (w : List Bool) :
    lpM_pair (lpM_padProg Q k) w =
      lpM_prepend (w.take k) (lpM_pair Q (w.drop k)) := by
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

noncomputable def lpM : LiuPass.UMachine where
  run := lpM_run
  run_mono := by
    intro Pi t t' x htt' h
    unfold lpM_run at h ⊢
    by_cases ht : t = 0
    · simp [ht] at h
    · have ht' : t' ≠ 0 := by omega
      simpa [ht, ht'] using h
  pair := lpM_pair
  pairOverhead := 3
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
    rw [lpM_pair]
    exact lpM_run_sim_pair Pi t _ (by omega)
  padProg := lpM_padProg
  padOverhead := 1
  run_padProg := by
    intro Pi k t w y h
    unfold lpM_run at h ⊢
    by_cases ht : t = 0
    · simp [ht] at h
    · rw [if_neg ht] at h
      rw [if_neg (by omega), lpM_pair_pad]
      exact lpM_progOut_prepend (w.take k) _ y h
  univ_prog := by
    intro F T hT h
    exact (lpM_univ_vacuous F T hT h).elim

/-! ### Rate-1 efficiency and conditional EP-PRG security of `lpM_G gamma` on `lpM`. -/

def lpM_genProg (gamma : ℕ) : List Bool :=
  false :: false :: true :: List.replicate gamma true

theorem lpM_cnt_rep (gamma : ℕ) : lpM_cnt (List.replicate gamma true) = gamma := by
  unfold lpM_cnt
  simp

theorem lpM_run_genProg (gamma : ℕ) (w : List Bool) (s : ℕ) (hs : s ≠ 0) :
    lpM.run (lpM.pair (lpM_genProg gamma) w) s = some (lpM_G gamma w) := by
  show lpM_run (lpM_pair (lpM_genProg gamma) w) s = some (lpM_G gamma w)
  unfold lpM_genProg
  rw [lpM_pair, lpM_cnt_rep]
  simp only [lpM_run, hs, if_false, lpM_progOut, lpM_genOut]
  have h0 : lpM_cnt (false :: (List.replicate gamma true ++ false :: w)) = 0 := by
    simp [lpM_cnt]
  rw [h0]
  simp only [Nat.zero_add, List.drop_succ_cons, List.drop_zero, List.take_zero, List.nil_append]
  rw [lpM_cnt_pad, lpM_drop_pad]

theorem lpM_rate1_G (gamma : ℕ) : LiuPass.Rate1Efficient lpM (lpM_G gamma) := by
  refine ⟨0, 1, le_rfl, zero_lt_one, lpM_genProg gamma, fun w => ?_⟩
  exact lpM_run_genProg gamma w _ (Nat.succ_ne_zero _)

theorem lpM_ptc_G (gamma : ℕ) : LiuPass.PolyTimeComputable lpM (lpM_G gamma) := by
  refine ⟨fun _ => 1, ⟨0, 1, fun n => by simp⟩, lpM_genProg gamma, fun w => ?_⟩
  exact lpM_run_genProg gamma w 1 (by omega)

theorem lpM_G_inj (gamma n : ℕ) {s₁ s₂ : List Bool} (h₁ : s₁.length = n) (h₂ : s₂.length = n)
    (heq : lpM_G gamma s₁ = lpM_G gamma s₂) : s₁ = s₂ := by
  have ht := congrArg (List.take n) heq
  unfold lpM_G at ht
  rwa [List.take_left' h₁, List.take_left' h₂] at ht

theorem lpM_prUnif_true (n : ℕ) : LiuPass.prUnif n (fun _ => True) = 1 := by
  unfold LiuPass.prUnif
  simp

theorem lpM_condOutProb_G (gamma n : ℕ) (v : Fin n → Bool) :
    LiuPass.condOutProb n (fun _ => True) (lpM_G gamma) (lpM_G gamma (List.ofFn v)) =
      (1 : ℝ) / 2 ^ n := by
  unfold LiuPass.condOutProb
  rw [lpM_prUnif_true, div_one]
  unfold LiuPass.prUnif
  rw [show (1 : ℝ) / 2 ^ n = ((({v} : Finset (Fin n → Bool)).card : ℝ)) / 2 ^ n by simp]
  congr 3
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => List.ofFn_injective (lpM_G_inj gamma n (by simp) (by simp) h),
    fun h => by rw [h]⟩

theorem lpM_condOutEntropy_G (gamma n : ℕ) :
    LiuPass.condOutEntropy n (fun _ => True) (lpM_G gamma) = n := by
  unfold LiuPass.condOutEntropy
  rw [Finset.sum_image (by
    intro a _ b _ hab
    exact List.ofFn_injective (lpM_G_inj gamma n (by simp) (by simp) hab))]
  have hterm : ∀ v : Fin n → Bool,
      -(LiuPass.condOutProb n (fun _ => True) (lpM_G gamma) (lpM_G gamma (List.ofFn v))) *
        Real.logb 2 (LiuPass.condOutProb n (fun _ => True) (lpM_G gamma)
          (lpM_G gamma (List.ofFn v))) = (n : ℝ) / 2 ^ n := by
    intro v
    rw [lpM_condOutProb_G]
    have hlog2 : Real.logb 2 2 = 1 := by
      unfold Real.logb
      exact div_self (ne_of_gt (Real.log_pos one_lt_two))
    have hlog : Real.logb 2 ((1 : ℝ) / 2 ^ n) = -(n : ℝ) := by
      rw [one_div, Real.logb_inv, Real.logb_pow, hlog2, mul_one]
    rw [hlog]
    ring
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact mul_div_cancel₀ _ (by positivity)

theorem lpM_pair_unary_blind (n m : ℕ) (hn : 1 ≤ n) (x : List Bool) (hx : x.length = m) :
    x = LiuPass.unary m ∨ lpM_pair (LiuPass.unary n) x = [] := by
  by_cases hall : x.all (fun c => c) = true
  · left
    unfold LiuPass.unary
    rw [List.eq_replicate_iff]
    refine ⟨hx, fun b hb => ?_⟩
    rw [List.all_eq_true] at hall
    simpa using hall b hb
  · right
    cases n with
    | zero => omega
    | succ k =>
        unfold LiuPass.unary
        rw [List.replicate_succ, lpM_pair]
        unfold lpM_gen
        rw [if_neg hall]

theorem lpM_G_not_all_true (gamma n : ℕ) (hgamma : 1 < gamma) (hn : 2 ≤ n)
    (s : List Bool) (hs : s.length = n) :
    (lpM_G gamma s).all (fun c => c) = false := by
  unfold lpM_G
  rw [List.all_eq_false]
  refine ⟨false, ?_, by simp⟩
  apply List.mem_append_right
  apply List.mem_replicate.mpr
  refine ⟨?_, rfl⟩
  have hlog : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le one_lt_two (by omega)
  rw [hs]
  exact Nat.mul_ne_zero (by omega) (by omega)

theorem lpM_pair_unary_G (gamma n : ℕ) (hgamma : 1 < gamma) (hn : 2 ≤ n)
    (s : List Bool) (hs : s.length = n) :
    lpM.pair (LiuPass.unary n) (lpM_G gamma s) = [] := by
  show lpM_pair (LiuPass.unary n) (lpM_G gamma s) = []
  have hall : ¬ (lpM_G gamma s).all (fun c => c) = true := by
    rw [lpM_G_not_all_true gamma n hgamma hn s hs]; decide
  cases n with
  | zero => omega
  | succ k =>
      unfold LiuPass.unary
      rw [List.replicate_succ, lpM_pair]
      unfold lpM_gen
      rw [if_neg hall]

theorem lpM_prUnif₂_snd (n t : ℕ) (R : List Bool → Prop) :
    LiuPass.prUnif₂ n t (fun _ r => R r) = LiuPass.prUnif t R := by
  unfold LiuPass.prUnif₂ LiuPass.prUnif
  have hcard : (Finset.univ.filter fun v : (Fin n → Bool) × (Fin t → Bool) =>
      R (List.ofFn v.2)).card = 2 ^ n * (Finset.univ.filter fun r : Fin t → Bool =>
        R (List.ofFn r)).card := by
    have heq : (Finset.univ.filter fun v : (Fin n → Bool) × (Fin t → Bool) => R (List.ofFn v.2)) =
        (Finset.univ : Finset (Fin n → Bool)) ×ˢ
          (Finset.univ.filter fun r : Fin t → Bool => R (List.ofFn r)) := by
      ext ⟨v1, v2⟩
      simp
    rw [heq, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  rw [hcard, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add,
    mul_div_mul_left _ _ (by positivity)]

theorem lpM_distCondOne_G (gamma : ℕ) (hgamma : 1 < gamma) (D : LiuPass.PPT lpM)
    (n : ℕ) (hn : 2 ≤ n) :
    LiuPass.distCondOne lpM D n (fun _ => True) (lpM_G gamma) =
      LiuPass.prUnif (D.tape n) (fun r => LiuPass.bitsToNat (D.out r []) = 1) := by
  unfold LiuPass.distCondOne
  rw [lpM_prUnif_true, div_one, ← lpM_prUnif₂_snd n (D.tape n)]
  unfold LiuPass.prUnif₂
  congr 3
  ext ⟨v1, v2⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [lpM_pair_unary_G gamma n hgamma hn (List.ofFn v1) (by simp)]

theorem lpM_card_fst_fixed (n m : ℕ) (x₀ : List Bool) :
    (Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) => List.ofFn v.1 = x₀).card
      ≤ 2 ^ m := by
  have := Finset.card_le_card_of_injOn (fun v : (Fin n → Bool) × (Fin m → Bool) => v.2)
    (s := Finset.univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) => List.ofFn v.1 = x₀)
    (t := Finset.univ) (fun _ _ => by simp)
    (fun a ha b hb hab => by
      simp only [Finset.coe_filter, Finset.mem_univ, true_and] at ha hb
      exact Prod.ext (List.ofFn_injective (ha.trans hb.symm)) hab)
  simpa using this

theorem lpM_prUnif₂_diff (m t : ℕ) (P Q : List Bool → List Bool → Prop) (y₀ : List Bool)
    (hPQ : ∀ y r, y.length = m → y ≠ y₀ → (P y r ↔ Q y r)) :
    |LiuPass.prUnif₂ m t P - LiuPass.prUnif₂ m t Q| ≤ (1 / 2 : ℝ) ^ m := by
  unfold LiuPass.prUnif₂
  set A := Finset.univ.filter fun v : (Fin m → Bool) × (Fin t → Bool) =>
    P (List.ofFn v.1) (List.ofFn v.2)
  set B := Finset.univ.filter fun v : (Fin m → Bool) × (Fin t → Bool) =>
    Q (List.ofFn v.1) (List.ofFn v.2)
  set C := Finset.univ.filter fun v : (Fin m → Bool) × (Fin t → Bool) =>
    List.ofFn v.1 = y₀
  have hsubAB : A \ B ⊆ C := by
    intro v hv
    simp only [A, B, C, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    by_contra hne
    exact hv.2 ((hPQ (List.ofFn v.1) (List.ofFn v.2) (by simp) hne).mp hv.1)
  have hsubBA : B \ A ⊆ C := by
    intro v hv
    simp only [A, B, C, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    by_contra hne
    exact hv.2 ((hPQ (List.ofFn v.1) (List.ofFn v.2) (by simp) hne).mpr hv.1)
  have hC : C.card ≤ 2 ^ t := lpM_card_fst_fixed m t y₀
  have h1 : A.card ≤ B.card + 2 ^ t := by
    have := Finset.card_le_card hsubAB
    have hsd := Finset.card_sdiff_add_card_inter A B
    have hin : (A ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
    omega
  have h2 : B.card ≤ A.card + 2 ^ t := by
    have := Finset.card_le_card hsubBA
    have hsd := Finset.card_sdiff_add_card_inter B A
    have hin : (B ∩ A).card ≤ A.card := Finset.card_le_card Finset.inter_subset_right
    omega
  have h1R : (A.card : ℝ) ≤ (B.card : ℝ) + (2 : ℝ) ^ t := by exact_mod_cast h1
  have h2R : (B.card : ℝ) ≤ (A.card : ℝ) + (2 : ℝ) ^ t := by exact_mod_cast h2
  have hdiff : |(A.card : ℝ) - (B.card : ℝ)| ≤ (2 : ℝ) ^ t :=
    abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (m + t) := by positivity
  rw [← sub_div, abs_div, abs_of_pos h2pos, div_le_iff₀ h2pos]
  calc |(A.card : ℝ) - (B.card : ℝ)| ≤ (2 : ℝ) ^ t := hdiff
    _ = (1 / 2 : ℝ) ^ m * (2 : ℝ) ^ (m + t) := by
        rw [pow_add, one_div_pow]
        field_simp

theorem lpM_distUnifOne_diff (D : LiuPass.PPT lpM) (n m : ℕ) (hn : 1 ≤ n) :
    |LiuPass.prUnif (D.tape n) (fun r => LiuPass.bitsToNat (D.out r []) = 1) -
      LiuPass.distUnifOne lpM D n m| ≤ (1 / 2 : ℝ) ^ m := by
  rw [← lpM_prUnif₂_snd m (D.tape n)]
  unfold LiuPass.distUnifOne
  apply lpM_prUnif₂_diff m (D.tape n) _ _ (LiuPass.unary m)
  intro y r hyl hne
  rcases lpM_pair_unary_blind n m hn y hyl with h | h
  · exact (hne h).elim
  · have h' : lpM.pair (LiuPass.unary n) y = [] := h
    rw [h']

theorem lpM_condEPPRG (gamma : ℕ) (hgamma : 1 < gamma) :
    LiuPass.IsCondEPPRG lpM gamma (fun n => 1 / (n : ℝ) ^ 2) (lpM_G gamma) := by
  refine ⟨lpM_ptc_G gamma, fun n s hs => by simp [lpM_G, hs],
    fun _ _ => True, 0, fun n => by rw [lpM_prUnif_true]; exact zero_lt_one,
    fun D => ?_, 0, fun n _ => ?_⟩
  · obtain ⟨N, hN⟩ := lpM_growth 1 2
    refine ⟨max N 2, fun n hn => ?_⟩
    have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    rw [lpM_distCondOne_G gamma hgamma D n hn2]
    have hd := lpM_distUnifOne_diff D n (n + gamma * Nat.log 2 n) (by omega)
    have hpow : (1 / 2 : ℝ) ^ (n + gamma * Nat.log 2 n) ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by positivity) (by norm_num) (Nat.le_add_right _ _)
    have h1 := hN n hnN
    push_cast at h1
    have hnR : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have hlt : (1 / 2 : ℝ) ^ n < 1 / (n : ℝ) ^ 2 := by
      rw [one_div_pow, one_div_lt_one_div (by positivity) hnR]
      linarith
    linarith
  · rw [lpM_condOutEntropy_G]
    simp

theorem lpM_hG : ∀ gamma : ℕ, 1 < gamma → ∃ G : LiuPass.BitStr → LiuPass.BitStr,
    LiuPass.Rate1Efficient lpM G ∧
      LiuPass.IsCondEPPRG lpM gamma (fun n => 1 / (n : ℝ) ^ 2) G :=
  fun gamma hgamma => ⟨lpM_G gamma, lpM_rate1_G gamma, lpM_condEPPRG gamma hgamma⟩

/-! ### `K^t` on `lpM` is `lpM_ktVal`, and `lpM_H` computes it on all `x ≠ 1^n`. -/

theorem lpM_Kt (t : ℕ → ℕ) (x : List Bool) (ht : 0 < t x.length) :
    LiuPass.Kt lpM t x = lpM_ktVal x := by
  unfold LiuPass.Kt lpM_ktVal
  congr 1
  ext l
  have hne : t x.length ≠ 0 := by omega
  simp [lpM, lpM_run, hne]

noncomputable def lpM_H : LiuPass.PPT lpM where
  tape := fun _ => 0
  out := fun r w => lpM_binRep (lpM_ktVal (lpM_pair r w))
  tape_poly := ⟨0, 0, fun n => by simp⟩
  out_poly := ⟨fun _ => 1, ⟨0, 1, fun n => by simp⟩, [false, false, false], fun r w => by
    show lpM_run (lpM_pair [false, false, false] (lpM_pair r w)) 1 = _
    rw [lpM_pair]
    exact lpM_run_true _ _ (by norm_num)⟩

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

theorem lpM_heurApprox_lb (t : ℕ → ℕ) (beta : ℕ → ℕ) (n : ℕ) (ht : 0 < t n) :
    1 - (1 / 2 : ℝ) ^ n ≤
      LiuPass.heurApproxSucc lpM (LiuPass.Kt lpM t) beta lpM_H n := by
  unfold LiuPass.heurApproxSucc
  apply lpM_prUnif₂_ge n _ (LiuPass.unary n)
  intro x hxl hne
  have ht' : 0 < t x.length := by rwa [hxl]
  rw [lpM_Kt t x ht']
  have hall : ¬ x.all (fun c => c) = true := by
    intro hall
    apply hne
    unfold LiuPass.unary
    rw [List.eq_replicate_iff]
    refine ⟨hxl, fun b hb => ?_⟩
    rw [List.all_eq_true] at hall
    simpa using hall b hb
  show |(LiuPass.bitsToNat (lpM_binRep (lpM_ktVal (lpM_pair [] x))) : ℤ) -
    (lpM_ktVal x : ℤ)| ≤ (beta x.length : ℤ)
  rw [lpM_bitsToNat_binRep, lpM_pair]
  unfold lpM_gen
  rw [if_neg hall]
  simp

theorem lpM_not_mildlyHoAApprox (t : ℕ → ℕ) (beta : ℕ → ℕ) (ht : ∀ n ≥ 1, 0 < t n) :
    ¬ LiuPass.MildlyHoAApprox lpM beta (LiuPass.Kt lpM t) := by
  rintro ⟨p, ⟨k, c, hpk⟩, hppos, hH⟩
  obtain ⟨n₀, hn₀⟩ := hH lpM_H
  obtain ⟨N, hN⟩ := lpM_growth c k
  set n := max (max n₀ N) 1
  have hn₀' : n₀ ≤ n := le_trans (le_max_left _ _) (le_max_left _ _)
  have hN' : N ≤ n := le_trans (le_max_right _ _) (le_max_left _ _)
  have hn1 : 1 ≤ n := le_max_right _ _
  have h1 := hn₀ n hn₀'
  have h2 := lpM_heurApprox_lb t beta n (ht n hn1)
  have h3 := hN n hN'
  have hp : ((p n : ℕ) : ℝ) ≤ (c : ℝ) * (n : ℝ) ^ k + c := by exact_mod_cast hpk n
  have hppos' : (0 : ℝ) < p n := by exact_mod_cast hppos n
  have h4 : (1 / 2 : ℝ) ^ n ≤ 1 / (p n : ℝ) := by
    rw [one_div_pow]
    apply one_div_le_one_div_of_le hppos'
    linarith
  linarith

open LiuPass in
theorem solution : ¬ (∀ (U : UMachine)
    (hG : ∀ gamma : ℕ, 1 < gamma → ∃ G : BitStr → BitStr,
      Rate1Efficient U G ∧ IsCondEPPRG U gamma (fun n => 1 / (n : ℝ) ^ 2) G)
    (d : ℕ) (hd : 0 < d) (eps : ℝ) (heps : 0 < eps) (t : ℕ → ℕ) (ht : IsPoly t)
    (htlb : ∀ n : ℕ, (1 + eps) * (n : ℝ) ≤ (t n : ℝ)),
    MildlyHoAApprox U (fun n => d * Nat.log 2 n) (Kt U t)) := by
  intro H
  have h := H lpM lpM_hG 1 zero_lt_one 1 zero_lt_one (fun n => 2 * n)
    ⟨1, 2, fun n => by simp⟩ (fun n => by push_cast; linarith)
  exact lpM_not_mildlyHoAApprox (fun n => 2 * n) (fun n => 1 * Nat.log 2 n)
    (fun n hn => by omega) h
