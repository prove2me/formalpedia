-- Prove2me | solution 1 for MomentSearch.opt_le_of_peak
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T00:47:22.191859+00:00
-- url     : https://prove2.me/submissions/ed8081d8-7b49-42d4-a525-21c5ce4d6787

import Mathlib
import Definitions.Def_MomentSearch_OPT

open MomentSearch

private theorem binary_search_of_capacity (d a b : ℕ) (hab : a ≤ b) (size : b+1-a ≤ 2^d) :
    ∃ T : SearchTree a b, ∀ t : ℕ, a ≤ t → t ≤ b → queries T t ≤ d := by
  induction d generalizing a b with
  | zero =>
      simp only [pow_zero] at size
      have h : b = a := by omega
      subst b
      exact ⟨SearchTree.leaf a,by simp [queries]⟩
  | succ d ih =>
      by_cases e : a = b
      · subst b
        exact ⟨SearchTree.leaf a,by simp [queries]⟩
      have hab' : a < b := lt_of_le_of_ne hab e
      let v := a+(b-a)/2
      have hav : a ≤ v := by omega
      have hvb : v ≤ b := by omega
      have leftSize (hv : a < v) : (v-1)+1-a ≤ 2^d := by
        rw [pow_succ] at size
        dsimp [v] at *
        omega
      have rightSize (hv : v < b) : b+1-(v+1) ≤ 2^d := by
        rw [pow_succ] at size
        dsimp [v] at *
        omega
      have L (hv : a < v) := ih a (v-1) (by omega) (leftSize hv)
      have R (hv : v < b) := ih (v+1) b (by omega) (rightSize hv)
      choose left hleft using L
      choose right hright using R
      refine ⟨.node v hav hvb hab' left right,?_⟩
      intro t hat htb
      rcases lt_trichotomy t v with h | rfl | h
      · have hv : a < v := hat.trans_lt h
        have dep := hleft hv t hat (by omega)
        simp only [queries,if_neg h.ne,if_pos h,dif_pos hv]
        omega
      · simp [queries]
      · have hv : v < b := h.trans_le htb
        have dep := hright hv t (by omega) htb
        simp only [queries,if_neg h.ne.symm,if_neg (not_lt_of_gt h),dif_pos hv]
        omega

theorem solution {n : ℕ} (hn : 2 ≤ n) (p : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n))
    (m : Fin n) (γ : ℝ) (hγ : 1 - γ ≤ p m) :
    OPT p ≤ 1 + γ * (Nat.clog 2 n : ℝ) ∧
    (γ ≤ 1 / (4 * Real.logb 2 n) → OPT p ≤ 3 / 2) := by
  classical
  let d := Nat.clog 2 n
  have cap : n ≤ 2^d := Nat.le_pow_clog (by norm_num) n
  have mv : (m:ℕ) ≤ n-1 := by have h := m.isLt; omega
  have hab : 0 < n-1 := by omega
  have lex (hm : 0 < (m:ℕ)) := binary_search_of_capacity d 0 ((m:ℕ)-1) (Nat.zero_le _)
    (by omega)
  have rex (hm : (m:ℕ) < n-1) := binary_search_of_capacity d ((m:ℕ)+1) (n-1)
    (by omega) (by omega)
  choose l hl using lex
  choose r hr using rex
  let S : Strategy n := .node m (Nat.zero_le _) mv hab l r
  have qm : queries S m = 1 := by simp [S,queries]
  have q (t : Fin n) : queries S t ≤ 1+d := by
    have ht := t.isLt
    rcases lt_trichotomy (t:ℕ) (m:ℕ) with h | h | h
    · have hm : 0 < (m:ℕ) := by omega
      have hq := hl hm t (Nat.zero_le _) (by omega)
      simp only [S,queries,if_neg h.ne,if_pos h,dif_pos hm]
      omega
    · rw [h,qm]; omega
    · have hm : (m:ℕ) < n-1 := by omega
      have hq := hr hm t (by omega) (by omega)
      simp only [S,queries,if_neg h.ne.symm,if_neg (not_lt_of_gt h),dif_pos hm]
      omega
  have hnon : ∀ (S' : Strategy n), 0 ≤ cost p S' :=
    fun S' => Finset.sum_nonneg (fun t _ => mul_nonneg (hp.1 t) (by positivity))
  have o : OPT p ≤ cost p S := ciInf_le ⟨0,by rintro _ ⟨S',rfl⟩; exact hnon S'⟩ S
  have tail : (∑ t ∈ Finset.univ.erase m, p t) = 1-p m := by
    have e := Finset.sum_erase_add Finset.univ p (Finset.mem_univ m)
    rw [hp.2] at e
    linarith
  have bound : cost p S ≤ 1+γ*(d:ℝ) := by
    unfold cost
    rw [← Finset.sum_erase_add Finset.univ (fun t : Fin n => p t * (queries S t:ℝ))
      (Finset.mem_univ m),qm,Nat.cast_one,mul_one]
    have hsum : (∑ t ∈ Finset.univ.erase m, p t * (queries S t:ℝ)) ≤
        (1-p m)*(1+(d:ℝ)) := by
      rw [← tail,Finset.sum_mul]
      apply Finset.sum_le_sum
      intro t _
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast q t) (hp.1 t)
    have h := mul_le_mul_of_nonneg_right (show 1-p m ≤ γ by linarith [hγ]) (Nat.cast_nonneg d)
    linarith
  refine ⟨o.trans bound,?_⟩
  intro hγ'
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have logn : 1 ≤ Real.logb 2 n := by
    simpa using (Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0:ℝ) < 2) hn')
  have hceil : (d:ℝ) ≤ 2*Real.logb 2 n := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ Real.logb 2 n by linarith)
    have en : ⌈Real.logb 2 (n:ℝ)⌉₊ = d := by simpa [d] using Real.natCeil_logb_natCast 2 n
    rw [en] at hc
    change (d:ℝ) < _ at hc
    linarith
  have hprod := (mul_le_mul_of_nonneg_right hγ' (Nat.cast_nonneg d)).trans
    (mul_le_mul_of_nonneg_left hceil (by positivity : 0 ≤ 1/(4*Real.logb 2 n)))
  have e : 1/(4*Real.logb 2 n)*(2*Real.logb 2 n) = 1/2 := by
    field_simp [show Real.logb 2 n ≠ 0 by linarith] <;> norm_num
  rw [e] at hprod
  linarith [o.trans bound]
