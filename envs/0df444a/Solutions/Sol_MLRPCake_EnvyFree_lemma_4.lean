-- Prove2me | solution 1 for MLRPCake.EnvyFree.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:56:46.695812+00:00
-- url     : https://prove2.me/submissions/dcf4486d-3355-4508-a12d-2ed753dbc4bc

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Theorems.Thm_MLRPCake_EnvyFree_proposition_1
import Theorems.Thm_MLRPCake_EnvyFree_lemma_2

open MLRPCake.EnvyFree MeasureTheory

namespace MLRPLemma4Aux

lemma cut_le_one {n : ℕ} (f : Fin n → ℝ → ℝ) (k : ℕ) (ℓ τ : ℝ) : cut f k ℓ τ ≤ 1 := by
  unfold cut
  split_ifs with h
  · obtain ⟨y, hy, hy2⟩ := h
    exact le_trans (csInf_le ⟨ℓ, fun z hz => hz.1.1⟩ ⟨hy, hy2⟩) hy.2
  · exact le_rfl

lemma cut_ge {n : ℕ} (f : Fin n → ℝ → ℝ) (k : ℕ) (ℓ τ : ℝ) (hℓ : ℓ ≤ 1) : ℓ ≤ cut f k ℓ τ := by
  unfold cut
  split_ifs with h
  · obtain ⟨y, hy, hy2⟩ := h
    exact le_csInf ⟨y, hy, hy2⟩ (fun z hz => hz.1.1)
  · exact hℓ

lemma cut_one {n : ℕ} (f : Fin n → ℝ → ℝ) (k : ℕ) (τ : ℝ) : cut f k 1 τ = 1 :=
  le_antisymm (cut_le_one f k 1 τ) (cut_ge f k 1 τ le_rfl)

lemma cut_zero {n : ℕ} (f : Fin n → ℝ → ℝ) (k : ℕ) (ℓ : ℝ) (hℓ : ℓ ≤ 1) : cut f k ℓ 0 = ℓ := by
  apply le_antisymm _ (cut_ge f k ℓ 0 hℓ)
  have hmem : ℓ ∈ {y | y ∈ Set.Icc ℓ 1 ∧ val f k ℓ y = 0} := ⟨⟨le_rfl, hℓ⟩, by simp [val]⟩
  unfold cut
  rw [if_pos ⟨ℓ, hmem.1, hmem.2⟩]
  exact csInf_le ⟨ℓ, fun z hz => hz.1.1⟩ hmem

lemma rd_mem {n : ℕ} (f : Fin n → ℝ → ℝ) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    ∀ k, rd f k x ∈ Set.Icc (0:ℝ) 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [rd]
    | 1, _ => simpa [rd] using hx
    | k + 2, ih =>
      simp only [rd]
      have h1 := ih (k + 1) (by omega)
      exact ⟨le_trans h1.1 (cut_ge f k _ _ h1.2), cut_le_one f k _ _⟩

lemma eval_eq_val {n : ℕ} (f : Fin n → ℝ → ℝ) (k : ℕ) (a b : ℝ) (hab : a ≤ b) :
    eval f k a b = val f k a b := by
  unfold eval val
  rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

lemma rd_zero {n : ℕ} (f : Fin n → ℝ → ℝ) : ∀ k, rd f k 0 = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [rd]
    | 1, _ => simp [rd]
    | k + 2, ih =>
      simp only [rd]
      rw [ih k (by omega), ih (k + 1) (by omega), eval_eq_val f k 0 0 le_rfl]
      simp only [val, intervalIntegral.integral_same]
      exact cut_zero f k 0 zero_le_one

lemma rd_one {n : ℕ} (f : Fin n → ℝ → ℝ) : ∀ k, 1 ≤ k → rd f k 1 = 1 := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp [rd]
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      show cut f m (rd f (m + 1) 1) _ = 1
      rw [ih (by omega)]
      exact cut_one f m _

lemma rd_sticky {n : ℕ} (f : Fin n → ℝ → ℝ) (x : ℝ) :
    ∀ m k, 1 ≤ k → rd f k x = 1 → rd f (k + m) x = 1 := by
  intro m
  induction m with
  | zero => intro k _ h; simpa using h
  | succ m ih =>
    intro k hk h
    have := ih k hk h
    obtain ⟨j, hj⟩ : ∃ j, k + m = j + 1 := ⟨k + m - 1, by omega⟩
    rw [hj] at this
    have e : k + (m + 1) = j + 2 := by omega
    rw [e]
    show cut f j (rd f (j + 1) x) _ = 1
    rw [this]
    exact cut_one f j _


end MLRPLemma4Aux

open MLRPLemma4Aux

theorem solution : ∃ c : ℕ, ∀ (n : ℕ) (f : Fin n → ℝ → ℝ) (lam δ : ℝ), 1 ≤ n → IsInstance f →
    1 ≤ lam → QueriesLipschitz f lam → 0 < δ → δ < 1 →
    ∃ T : ℕ, bsStops f δ T ∧ (∀ k < T, ¬ bsStops f δ k) ∧
      (T : ℝ) ≤ c * ((n : ℝ) + Real.logb 2 lam + Real.logb 2 (1 / δ) + 1) ^ c ∧
      IsRipple f δ (bsOutput f δ T) := by
  refine ⟨3, ?_⟩
  intro n f lam δ hn hf hlam hL hδ0 hδ1
  have hlam0 : 0 < lam := by linarith
  set Λ : ℝ := lam ^ (2 * (n - 1)) with hΛ
  have hΛpos : 0 < Λ := by positivity
  -- RD_n is Λ-Lipschitz on [0,1]
  have hLip : ∀ x x' : ℝ, x ∈ Set.Icc (0:ℝ) 1 → x' ∈ Set.Icc (0:ℝ) 1 →
      |rd f n x' - rd f n x| ≤ Λ * |x' - x| := by
    rcases Nat.lt_or_ge n 2 with h | h
    · have hn1 : n = 1 := by omega
      intro x x' _ _
      have : Λ = 1 := by rw [hΛ, hn1]; simp
      rw [this, one_mul]
      subst hn1
      simp [rd]
    · exact MLRPCake.EnvyFree.proposition_1 n f lam h hf hlam hL
  have hrd0 : rd f n 0 = 0 := rd_zero f n
  have hrd1 : rd f n 1 = 1 := rd_one f n hn
  -- the BinSearch invariant
  let Inv : ℕ → Prop := fun k =>
    (bsIter f δ k).1 ∈ Set.Icc (0:ℝ) 1 ∧ (bsIter f δ k).2 ∈ Set.Icc (0:ℝ) 1 ∧
    (bsIter f δ k).2 - (bsIter f δ k).1 = (1 / 2 : ℝ) ^ k ∧
    rd f n (bsIter f δ k).1 < 1 - δ ∧ rd f n (bsIter f δ k).2 = 1
  have hInv : ∀ k, (∀ j < k, ¬ bsStops f δ j) → Inv k := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [bsIter, hrd0, hrd1] <;> linarith
    | succ k ih =>
      intro hns
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih (fun j hj => hns j (by omega))
      have hk := hns k (by omega)
      unfold bsStops at hk
      have hmid : bsMid f δ k = ((bsIter f δ k).1 + (bsIter f δ k).2) / 2 := rfl
      set ℓ := (bsIter f δ k).1 with hℓ
      set r := (bsIter f δ k).2 with hr
      have hmin : bsMid f δ k ∈ Set.Icc (0:ℝ) 1 := by
        rw [hmid]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      have hle1 : rd f n (bsMid f δ k) ≤ 1 := (rd_mem f _ hmin n).2
      have hstep : bsIter f δ (k + 1) =
          if rd f n (bsMid f δ k) < 1 - δ then (bsMid f δ k, r)
          else if rd f n (bsMid f δ k) = 1 then (ℓ, bsMid f δ k) else (ℓ, r) := rfl
      by_cases hA : rd f n (bsMid f δ k) < 1 - δ
      · rw [if_pos hA] at hstep
        show Inv (k + 1)
        simp only [Inv]
        rw [hstep]
        refine ⟨hmin, h2, ?_, hA, h5⟩
        simp only
        rw [hmid, pow_succ]; linarith
      · have hB : rd f n (bsMid f δ k) = 1 := by
          by_contra hB
          exact hk ⟨by linarith, lt_of_le_of_ne hle1 hB⟩
        rw [if_neg hA, if_pos hB] at hstep
        show Inv (k + 1)
        simp only [Inv]
        rw [hstep]
        refine ⟨h1, hmin, ?_, h4, hB⟩
        simp only
        rw [hmid, pow_succ]; linarith
  -- the invariant forces δ < Λ / 2^k
  have hbound : ∀ k, Inv k → δ < Λ * (1 / 2 : ℝ) ^ k := by
    intro k ⟨h1, h2, h3, h4, h5⟩
    have := hLip _ _ h1 h2
    rw [h5, h3, abs_of_pos (by positivity : (0:ℝ) < (1/2) ^ k)] at this
    have := le_abs_self (1 - rd f n (bsIter f δ k).1)
    linarith
  -- logarithmic iteration count
  set L := Real.logb 2 lam with hLdef
  set E := Real.logb 2 (1 / δ) with hEdef
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) hlam
  have hE0 : 0 ≤ E := Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hδ0]; linarith)
  set A : ℝ := 2 * ((n : ℝ) - 1) * L + E with hA
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hA0 : 0 ≤ A := by
    have : 0 ≤ 2 * ((n : ℝ) - 1) * L := by
      apply mul_nonneg _ hL0; linarith
    linarith
  have hlogA : Real.logb 2 (Λ / δ) = A := by
    rw [Real.logb_div hΛpos.ne' hδ0.ne', hΛ, Real.logb_pow, hA, hEdef, one_div, Real.logb_inv]
    push_cast [Nat.cast_sub hn]
    ring
  set K := ⌈A⌉₊ with hK
  have hKpow : Λ / δ ≤ (2:ℝ) ^ K := by
    have e1 : (2:ℝ) ^ A = Λ / δ := by
      rw [← hlogA]; exact Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
    rw [← e1, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil A)
  have hex : ∃ j, bsStops f δ j := by
    by_contra hno
    push Not at hno
    have := hbound K (hInv K (fun j _ => hno j))
    have h2K : (0:ℝ) < 2 ^ K := by positivity
    rw [one_div, inv_pow, ← div_eq_mul_inv, lt_div_iff₀ h2K] at this
    rw [div_le_iff₀ hδ0] at hKpow
    linarith
  classical
  let T := Nat.find hex
  have hT : bsStops f δ T := Nat.find_spec hex
  have hTmin : ∀ k < T, ¬ bsStops f δ k := fun k hk => Nat.find_min hex hk
  have hTK : T ≤ K := by
    by_contra hc
    push Not at hc
    have := hbound K (hInv K (fun j hj => hTmin j (by omega)))
    have h2K : (0:ℝ) < 2 ^ K := by positivity
    rw [one_div, inv_pow, ← div_eq_mul_inv, lt_div_iff₀ h2K] at this
    rw [div_le_iff₀ hδ0] at hKpow
    linarith
  refine ⟨T, hT, hTmin, ?_, ?_⟩
  · -- the polynomial bound with c = 3
    have hKA : (K : ℝ) ≤ A + 1 := (Nat.ceil_lt_add_one hA0).le
    have hTA : (T : ℝ) ≤ A + 1 := le_trans (by exact_mod_cast hTK) hKA
    set S : ℝ := (n : ℝ) + L + E + 1 with hS
    have hS1 : 1 ≤ S := by linarith
    have h1 : 2 * ((n : ℝ) - 1) * L ≤ 2 * (S * S) := by
      have ha : (n : ℝ) - 1 ≤ S := by linarith
      have hb : L ≤ S := by linarith
      have := mul_le_mul ha hb hL0 (by linarith)
      linarith
    have h2 : S * S ≤ S ^ 3 := by
      have : S ^ 3 = S * S * S := by ring
      rw [this]; nlinarith
    have h3 : E + 1 ≤ S ^ 3 := by nlinarith
    push_cast
    nlinarith
  · -- the output is a δ-ripple division
    obtain ⟨h1, h2, h3, h4, h5⟩ := hInv T hTmin
    have hmid : bsMid f δ T = ((bsIter f δ T).1 + (bsIter f δ T).2) / 2 := rfl
    have hpos : (0:ℝ) < (1/2) ^ T := by positivity
    have hmo : bsMid f δ T ∈ Set.Ioo (0:ℝ) 1 := by
      rw [hmid]; constructor <;> linarith [h1.1, h2.2]
    have hstop := hT
    unfold bsStops at hstop
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hn1 : n = 1 := by omega
      subst hn1
      refine ⟨by simp [bsOutput, rd], ?_, ?_, ?_, ?_⟩
      · intro k hk
        have : k = 0 := by omega
        subst this
        simp [bsOutput, rd]; exact hmo.1.le
      · simp [bsOutput, rd]; exact hmo.2.le
      · simpa [bsOutput, rd] using hstop.1
      · intro i hi; omega
    · set y := rd f n (bsMid f δ T) with hy
      have hy0 : 0 < 1 - y := by linarith [hstop.2]
      have hy1 : 1 - y < 1 := by linarith [hstop.1]
      have hR := (MLRPCake.EnvyFree.lemma_2 n f lam (1 - y) hn2 hf hlam hL hy0 hy1).2
        (bsMid f δ T) hmo (by rw [← hy]; ring)
      obtain ⟨r1, r2, r3, _, r5⟩ := hR
      exact ⟨r1, r2, r3, by simpa [bsOutput, ← hy] using hstop.1, r5⟩
