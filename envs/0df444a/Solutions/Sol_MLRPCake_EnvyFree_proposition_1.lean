-- Prove2me | solution 1 for MLRPCake.EnvyFree.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:52:44.286201+00:00
-- url     : https://prove2.me/submissions/a886dda0-54f3-42fc-956b-ee84652e276e

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model

open MLRPCake.EnvyFree MeasureTheory

namespace MLRPProp1Aux

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

lemma eval_nonneg {n : ℕ} (f : Fin n → ℝ → ℝ) (hf : IsInstance f) (k : ℕ) (hk : k < n)
    (a b : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) : 0 ≤ eval f k a b := by
  unfold eval
  apply setIntegral_nonneg measurableSet_Icc
  intro t ht
  simp only [dens, hk, dite_true]
  exact (hf ⟨k, hk⟩).1 t ⟨le_trans ha.1 ht.1, le_trans ht.2 hb.2⟩

end MLRPProp1Aux

open MLRPProp1Aux

theorem solution (n : ℕ) (f : Fin n → ℝ → ℝ) (lam : ℝ) (hn : 2 ≤ n) (hf : IsInstance f)
    (hlam : 1 ≤ lam) (hL : QueriesLipschitz f lam) :
    ∀ x x' : ℝ, x ∈ Set.Icc (0:ℝ) 1 → x' ∈ Set.Icc (0:ℝ) 1 →
      |rd f n x' - rd f n x| ≤ lam ^ (2 * (n - 1)) * |x' - x| := by
  intro x x' hx hx'
  have hlam0 : 0 ≤ lam := by linarith
  have hd : 0 ≤ |x' - x| := abs_nonneg _
  let P : ℕ → Prop := fun k => |rd f k x' - rd f k x| ≤ lam ^ (2 * (k - 1)) * |x' - x|
  have hP0 : P 0 := by
    show |rd f 0 x' - rd f 0 x| ≤ _
    simp only [rd, sub_self, abs_zero]; positivity
  have hP1 : P 1 := by
    show |rd f 1 x' - rd f 1 x| ≤ _
    simp [rd]
  have step : ∀ k, k + 2 ≤ n → P k → P (k + 1) → P (k + 2) := by
    intro k hk hPk hPk1
    have hkn : k < n := by omega
    have hA := rd_mem f x hx
    have hA' := rd_mem f x' hx'
    obtain ⟨hev, hcut⟩ := hL ⟨k, hkn⟩
    -- eval part
    have hE : |eval f k (rd f k x') (rd f (k + 1) x') - eval f k (rd f k x) (rd f (k + 1) x)| ≤
        lam ^ (2 * k + 1) * |x' - x| := by
      have := hev (rd f k x) (rd f (k + 1) x) (rd f k x') (rd f (k + 1) x')
        (hA k) (hA (k + 1)) (hA' k) (hA' (k + 1))
      refine le_trans this ?_
      have hm : max |rd f k x' - rd f k x| |rd f (k + 1) x' - rd f (k + 1) x| ≤
          lam ^ (2 * k) * |x' - x| := by
        apply max_le
        · refine le_trans hPk ?_
          gcongr
          · omega
        · have : 2 * (k + 1 - 1) = 2 * k := by omega
          simpa [P, this] using hPk1
      calc lam * max _ _ ≤ lam * (lam ^ (2 * k) * |x' - x|) := by gcongr
        _ = lam ^ (2 * k + 1) * |x' - x| := by ring
    -- cut part
    show |rd f (k + 2) x' - rd f (k + 2) x| ≤ lam ^ (2 * (k + 2 - 1)) * |x' - x|
    simp only [rd]
    have hc := hcut (rd f (k + 1) x) (eval f k (rd f k x) (rd f (k + 1) x))
      (rd f (k + 1) x') (eval f k (rd f k x') (rd f (k + 1) x'))
      (hA (k + 1)) (hA' (k + 1))
      (eval_nonneg f hf k hkn _ _ (hA k) (hA (k + 1)))
      (eval_nonneg f hf k hkn _ _ (hA' k) (hA' (k + 1)))
    refine le_trans hc ?_
    have hm : max |rd f (k + 1) x' - rd f (k + 1) x|
        |eval f k (rd f k x') (rd f (k + 1) x') - eval f k (rd f k x) (rd f (k + 1) x)| ≤
        lam ^ (2 * k + 1) * |x' - x| := by
      apply max_le
      · have : 2 * (k + 1 - 1) = 2 * k := by omega
        have h2 : |rd f (k + 1) x' - rd f (k + 1) x| ≤ lam ^ (2 * k) * |x' - x| := by
          simpa [P, this] using hPk1
        refine le_trans h2 ?_
        gcongr
        omega
      · exact hE
    have e : 2 * (k + 2 - 1) = 2 * k + 1 + 1 := by omega
    rw [e]
    calc lam * max _ _ ≤ lam * (lam ^ (2 * k + 1) * |x' - x|) := by gcongr
      _ = lam ^ (2 * k + 1 + 1) * |x' - x| := by ring
  have hall : ∀ k, k + 1 ≤ n → P k ∧ P (k + 1) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨hP0, hP1⟩
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2⟩ := ih (by omega)
      exact ⟨h2, step k (by omega) h1 h2⟩
  have := (hall (n - 1) (by omega)).2
  have e : n - 1 + 1 = n := by omega
  rw [e] at this
  exact this
