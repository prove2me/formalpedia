-- Prove2me | solution 1 for MDPFinance.JumpMarkets.theorem_9_4_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:34:51.73648+00:00
-- url     : https://prove2.me/submissions/89eaea84-45d9-480a-89f6-9669eda7d9f0

import Mathlib
import Definitions.Def_MDPFinance_JumpMarkets_TradeExecution

open MeasureTheory
open scoped ENNReal
open MeasureTheory Filter Topology

namespace MDPFinance.JumpMarkets

/-- discrete convexity: increments increase -/
lemma te_inc_mono (f : ℕ → ℝ) (hf : ∀ x, f (x + 1) - f x ≤ f (x + 2) - f (x + 1)) :
    ∀ a b, a ≤ b → f (a + 1) - f a ≤ f (b + 1) - f b := by
  intro a b hab
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction k with
  | zero => simp
  | succ k ih =>
    have := hf (a + k)
    have e1 : a + (k + 1) = a + k + 1 := by ring
    rw [e1]
    exact (ih (by omega)).trans this

lemma te_pair (f : ℕ → ℝ) (hf : ∀ x, f (x + 1) - f x ≤ f (x + 2) - f (x + 1)) :
    ∀ j m n p q : ℕ, p + q = m + n → m ≤ p → p ≤ q → p - m = j → f p + f q ≤ f m + f n := by
  intro j
  induction j with
  | zero =>
    intro m n p q h1 h2 h3 h4
    have : p = m := by omega
    subst this
    have : q = n := by omega
    subst this; exact le_rfl
  | succ j ih =>
    intro m n p q h1 h2 h3 h4
    have h5 := ih m n (p - 1) (q + 1) (by omega) (by omega) (by omega) (by omega)
    have h6 := te_inc_mono f hf (p - 1) q (by omega)
    have e : p - 1 + 1 = p := by omega
    rw [e] at h6
    linarith

lemma te_mid (f : ℕ → ℝ) (hf : ∀ x, f (x + 1) - f x ≤ f (x + 2) - f (x + 1)) (a b : ℕ) :
    f ((a + b) / 2) + f (a + b - (a + b) / 2) ≤ f a + f b := by
  rcases le_total a b with h | h
  · exact te_pair f hf _ a b _ _ (by omega) (by omega) (by omega) rfl
  · have := te_pair f hf _ b a ((a + b) / 2) (a + b - (a + b) / 2) (by omega) (by omega)
      (by omega) rfl
    linarith

variable (M : TradeExecution)

noncomputable def teG (v : ℝ × ℕ → ℝ) (r : ℝ) (x : ℕ) : ℝ :=
  (Finset.range (x + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
    (fun u => M.C u + v (r, x - u))

lemma teG_le (v : ℝ × ℕ → ℝ) (r : ℝ) (x u : ℕ) (hu : u ≤ x) :
    teG M v r x ≤ M.C u + v (r, x - u) :=
  Finset.inf'_le _ (Finset.mem_range.mpr (by omega))

lemma teG_exists (v : ℝ × ℕ → ℝ) (r : ℝ) (x : ℕ) :
    ∃ u ≤ x, teG M v r x = M.C u + v (r, x - u) := by
  obtain ⟨u, hu, h⟩ := Finset.exists_mem_eq_inf' (s := Finset.range (x + 1))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩ (fun u => M.C u + v (r, x - u))
  exact ⟨u, by simpa [Nat.lt_succ_iff] using hu, h⟩

lemma teG_le_of (v : ℝ × ℕ → ℝ) (r : ℝ) (x : ℕ) (y : ℝ)
    (h : ∀ u ≤ x, y ≤ M.C u + v (r, x - u)) : y ≤ teG M v r x := by
  obtain ⟨u, hu, e⟩ := teG_exists M v r x
  rw [e]; exact h u hu

lemma teG_zero (v : ℝ × ℕ → ℝ) (r : ℝ) : teG M v r 0 = v (r, 0) := by
  simp [teG, M.C_zero]

lemma teG_mono (v w : ℝ × ℕ → ℝ) (r r' : ℝ) (x : ℕ) (h : ∀ y ≤ x, v (r, y) ≤ w (r', y)) :
    teG M v r x ≤ teG M w r' x := by
  apply teG_le_of
  intro u hu
  exact (teG_le M v r x u hu).trans (by linarith [h (x - u) (by omega)])

lemma teG_lip (v w : ℝ × ℕ → ℝ) (r : ℝ) (x : ℕ) (K : ℝ)
    (h : ∀ y ≤ x, |v (r, y) - w (r, y)| ≤ K) : |teG M v r x - teG M w r x| ≤ K := by
  rw [abs_le]; constructor
  · have : teG M w r x - K ≤ teG M v r x := by
      apply teG_le_of; intro u hu
      have := teG_le M w r x u hu
      have := (abs_le.mp (h (x - u) (by omega))).1
      linarith
    linarith
  · have : teG M v r x - K ≤ teG M w r x := by
      apply teG_le_of; intro u hu
      have := teG_le M v r x u hu
      have := (abs_le.mp (h (x - u) (by omega))).2
      linarith
    linarith

lemma teG_xmono (v : ℝ × ℕ → ℝ) (r : ℝ) (x : ℕ) (hv : ∀ y, v (r, y) ≤ v (r, y + 1)) :
    teG M v r x ≤ teG M v r (x + 1) := by
  apply teG_le_of
  intro u hu
  rcases Nat.eq_zero_or_pos u with h0 | hpos
  · subst h0
    have := teG_le M v r x 0 (Nat.zero_le _)
    have := hv x
    simp only [Nat.sub_zero] at *
    linarith
  · have := teG_le M v r x (u - 1) (by omega)
    have h1 : x - (u - 1) = x + 1 - u := by omega
    rw [h1] at this
    have := M.C_strictMono.monotone (show u - 1 ≤ u by omega)
    linarith

lemma teG_convex (v : ℝ × ℕ → ℝ) (r : ℝ) (x : ℕ)
    (hv : ∀ y, v (r, y + 1) - v (r, y) ≤ v (r, y + 2) - v (r, y + 1)) :
    teG M v r (x + 1) - teG M v r x ≤ teG M v r (x + 2) - teG M v r (x + 1) := by
  obtain ⟨a, ha, ea⟩ := teG_exists M v r x
  obtain ⟨b, hb, eb⟩ := teG_exists M v r (x + 2)
  have hC := te_mid M.C (fun y => (M.C_convex y).le) a b
  have hV := te_mid (fun y => v (r, y)) hv (x - a) (x + 2 - b)
  have g1 := teG_le M v r (x + 1) ((a + b) / 2) (by omega)
  have g2 := teG_le M v r (x + 1) (a + b - (a + b) / 2) (by omega)
  have e1 : x + 1 - (a + b) / 2 = (x - a + (x + 2 - b)) - (x - a + (x + 2 - b)) / 2 := by omega
  have e2 : x + 1 - (a + b - (a + b) / 2) = (x - a + (x + 2 - b)) / 2 := by omega
  rw [e1] at g1; rw [e2] at g2
  linarith


lemma te_fstar_spec (v : ℝ × ℕ → ℝ) (t : ℝ) (x : ℕ) :
    M.fstar v (t, x) ≤ x ∧
    (∀ u' ≤ x, M.C (M.fstar v (t, x)) + v (t, x - M.fstar v (t, x)) ≤ M.C u' + v (t, x - u')) ∧
    (∀ u < M.fstar v (t, x), M.C (M.fstar v (t, x)) + v (t, x - M.fstar v (t, x)) <
      M.C u + v (t, x - u)) := by
  have hne : {u : ℕ | u ≤ x ∧ ∀ u' ≤ x, M.C u + v (t, x - u) ≤ M.C u' + v (t, x - u')}.Nonempty := by
    obtain ⟨u, hu, e⟩ := teG_exists M v t x
    refine ⟨u, hu, fun u' hu' => ?_⟩
    rw [← e]; exact teG_le M v t x u' hu'
  have hmem := Nat.sInf_mem hne
  refine ⟨hmem.1, hmem.2, fun u hu => ?_⟩
  have hnot := Nat.notMem_of_lt_sInf hu
  have hux : u ≤ x := le_trans hu.le hmem.1
  simp only [Set.mem_setOf_eq, not_and, not_forall, not_le] at hnot
  obtain ⟨u', hu', hlt⟩ := hnot hux
  exact lt_of_le_of_lt (hmem.2 u' hu') hlt

lemma te_fstar_eq (v : ℝ × ℕ → ℝ) (t : ℝ) (x : ℕ) :
    M.C (M.fstar v (t, x)) + v (t, x - M.fstar v (t, x)) = teG M v t x := by
  obtain ⟨h1, h2, -⟩ := te_fstar_spec M v t x
  apply le_antisymm
  · obtain ⟨u, hu, e⟩ := teG_exists M v t x
    rw [e]; exact h2 u hu
  · exact teG_le M v t x _ h1

lemma te_fstar_mono (v : ℝ × ℕ → ℝ) (t : ℝ) (x : ℕ)
    (hv : ∀ y, v (t, y + 1) - v (t, y) ≤ v (t, y + 2) - v (t, y + 1)) :
    M.fstar v (t, x) ≤ M.fstar v (t, x + 1) ∧
    M.fstar v (t, x + 1) ≤ M.fstar v (t, x) + 1 := by
  obtain ⟨hw1, hw2, hw3⟩ := te_fstar_spec M v t x
  obtain ⟨hu1, hu2, hu3⟩ := te_fstar_spec M v t (x + 1)
  set w := M.fstar v (t, x) with hw
  set u := M.fstar v (t, x + 1) with hu
  clear_value w u
  constructor
  · by_contra hcon
    push_neg at hcon
    have a1 := hw3 u hcon
    have a2 := hu2 w (by omega)
    have a3 := te_inc_mono (fun y => v (t, y)) hv (x - w) (x - u) (by omega)
    have e1 : x - w + 1 = x + 1 - w := by omega
    have e2 : x - u + 1 = x + 1 - u := by omega
    rw [e1, e2] at a3
    linarith
  · by_contra hcon
    push_neg at hcon
    have a1 := hw2 (u - 1) (by omega)
    have a2 := hu3 (w + 1) (by omega)
    have a3 := te_inc_mono M.C (fun y => (M.C_convex y).le) w (u - 1) (by omega)
    have e1 : x - (u - 1) = x + 1 - u := by omega
    have e2 : u - 1 + 1 = u := by omega
    have e3 : x + 1 - (w + 1) = x - w := by omega
    rw [e1] at a1; rw [e2] at a3; rw [e3] at a2
    linarith


lemma te_Top_eq (v : ℝ × ℕ → ℝ) (t : ℝ) (x : ℕ) :
    M.T_op v (t, x) = (∫ s in Set.Ioo (0 : ℝ) (M.T - t),
      M.lam * Real.exp (-M.lam * s) * teG M v (t + s) x) +
      Real.exp (-M.lam * (M.T - t)) * M.C x := rfl

lemma te_w_interval (a b : ℝ) :
    ∫ s in a..b, M.lam * Real.exp (-M.lam * s) = Real.exp (-M.lam * a) - Real.exp (-M.lam * b) := by
  have : ∀ s ∈ Set.uIcc a b, HasDerivAt (fun s => -Real.exp (-M.lam * s))
      (M.lam * Real.exp (-M.lam * s)) s := by
    intro s _
    have h := ((hasDerivAt_id s).const_mul (-M.lam)).exp.neg
    refine h.congr_deriv ?_; simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt this
    ((by fun_prop : Continuous fun s => M.lam * Real.exp (-M.lam * s)).intervalIntegrable _ _)]
  ring

lemma te_Ioo_eq_interval (f : ℝ → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫ s in Set.Ioo (0 : ℝ) τ, f s = ∫ s in (0 : ℝ)..τ, f s := by
  rw [intervalIntegral.integral_of_le hτ, integral_Ioc_eq_integral_Ioo]

lemma te_w_Ioo {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫ s in Set.Ioo (0 : ℝ) τ, M.lam * Real.exp (-M.lam * s) = 1 - Real.exp (-M.lam * τ) := by
  rw [te_Ioo_eq_interval _ hτ, te_w_interval]; simp

lemma te_w_nonneg (s : ℝ) : 0 ≤ M.lam * Real.exp (-M.lam * s) :=
  mul_nonneg M.lam_pos.le (Real.exp_pos _).le

lemma te_w_int (τ : ℝ) : IntegrableOn (fun s => M.lam * Real.exp (-M.lam * s)) (Set.Ioo 0 τ) :=
  (by fun_prop : Continuous fun s => M.lam * Real.exp (-M.lam * s)).integrableOn_Icc.mono_set
    Set.Ioo_subset_Icc_self

lemma te_lw_Ioo {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫⁻ s in Set.Ioo (0 : ℝ) τ, ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) =
      ENNReal.ofReal (1 - Real.exp (-M.lam * τ)) := by
  rw [← te_w_Ioo M hτ, ofReal_integral_eq_lintegral_ofReal (te_w_int M τ)
    (Eventually.of_forall (fun s => te_w_nonneg M s))]

def TeCont (v : ℝ × ℕ → ℝ) : Prop := ∀ y : ℕ, ContinuousOn (fun t => v (t, y)) (Set.Icc 0 M.T)

lemma teG_contOn (v : ℝ × ℕ → ℝ) (hv : TeCont M v) {t : ℝ} (ht : t ∈ Set.Icc 0 M.T) (x : ℕ) :
    ContinuousOn (fun s => teG M v (t + s) x) (Set.Icc 0 (M.T - t)) := by
  have : ∀ u ∈ Finset.range (x + 1), ContinuousOn (fun s => M.C u + v (t + s, x - u))
      (Set.Icc 0 (M.T - t)) := by
    intro u _
    apply ContinuousOn.add continuousOn_const
    refine (hv (x - u)).comp (continuousOn_const.add continuousOn_id) ?_
    intro s hs; simp only [Set.mem_Icc] at *; constructor <;> linarith
  have h := ContinuousOn.finset_inf'_apply ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩ this
  exact h

lemma te_int (v : ℝ × ℕ → ℝ) (hv : TeCont M v) {t : ℝ} (ht : t ∈ Set.Icc 0 M.T) (x : ℕ) :
    IntegrableOn (fun s => M.lam * Real.exp (-M.lam * s) * teG M v (t + s) x)
      (Set.Icc 0 (M.T - t)) :=
  (((by fun_prop : Continuous fun s => M.lam * Real.exp (-M.lam * s)).continuousOn).mul
    (teG_contOn M v hv ht x)).integrableOn_compact isCompact_Icc

lemma te_int' (v : ℝ × ℕ → ℝ) (hv : TeCont M v) {t : ℝ} (ht : t ∈ Set.Icc 0 M.T) (x : ℕ) :
    IntegrableOn (fun s => M.lam * Real.exp (-M.lam * s) * teG M v (t + s) x)
      (Set.Ioo 0 (M.T - t)) :=
  (te_int M v hv ht x).mono_set Set.Ioo_subset_Icc_self


lemma te_mem_shift {t s : ℝ} (ht : t ∈ Set.Icc 0 M.T) (hs : s ∈ Set.Icc 0 (M.T - t)) :
    t + s ∈ Set.Icc 0 M.T := by
  simp only [Set.mem_Icc] at *; constructor <;> linarith

lemma te_mem_shift' {t s : ℝ} (ht : t ∈ Set.Icc 0 M.T) (hs : s ∈ Set.Ioo 0 (M.T - t)) :
    t + s ∈ Set.Icc 0 M.T := te_mem_shift M ht (Set.Ioo_subset_Icc_self hs)

lemma te_nonneg {v : ℝ × ℕ → ℝ} (hv : M.IMcx v) {t : ℝ} (ht : t ∈ Set.Icc 0 M.T) (x : ℕ) :
    0 ≤ v (t, x) := by
  have := hv.2.2.2.2.2.2 t ht (Nat.zero_le x)
  simp only at this
  rw [hv.2.2.1 t ht] at this; exact this

lemma teG_nonneg {v : ℝ × ℕ → ℝ} (hv : M.IMcx v) {r : ℝ} (hr : r ∈ Set.Icc 0 M.T) (x : ℕ) :
    0 ≤ teG M v r x := by
  obtain ⟨u, -, e⟩ := teG_exists M v r x
  rw [e]; exact add_nonneg (M.C_nonneg u) (te_nonneg M hv hr _)

lemma teG_leC {v : ℝ × ℕ → ℝ} (hv : M.IMcx v) {r : ℝ} (hr : r ∈ Set.Icc 0 M.T) (x : ℕ) :
    teG M v r x ≤ M.C x := by
  have := teG_le M v r x x le_rfl
  rwa [Nat.sub_self, hv.2.2.1 r hr, add_zero] at this

lemma teG_contOn0 (v : ℝ × ℕ → ℝ) (hv : TeCont M v) (x : ℕ) :
    ContinuousOn (fun r => teG M v r x) (Set.Icc 0 M.T) := by
  have : ∀ u ∈ Finset.range (x + 1), ContinuousOn (fun r => M.C u + v (r, x - u))
      (Set.Icc 0 M.T) := fun u _ => continuousOn_const.add (hv (x - u))
  exact ContinuousOn.finset_inf'_apply ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩ this

lemma te_T_nonneg {v : ℝ × ℕ → ℝ} (hv : M.IMcx v) {t : ℝ} (ht : t ∈ Set.Icc 0 M.T) (x : ℕ) :
    0 ≤ M.T_op v (t, x) := by
  rw [te_Top_eq]
  refine add_nonneg (setIntegral_nonneg measurableSet_Ioo fun s hs => ?_)
    (mul_nonneg (Real.exp_pos _).le (M.C_nonneg x))
  exact mul_nonneg (te_w_nonneg M s) (teG_nonneg M hv (te_mem_shift' M ht hs) x)

lemma te_T_leC {v : ℝ × ℕ → ℝ} (hv : M.IMcx v) {t : ℝ} (ht : t ∈ Set.Icc 0 M.T) (x : ℕ) :
    M.T_op v (t, x) ≤ M.C x := by
  rw [te_Top_eq]
  have hτ : 0 ≤ M.T - t := by linarith [ht.2]
  have h1 : ∫ s in Set.Ioo (0 : ℝ) (M.T - t), M.lam * Real.exp (-M.lam * s) * teG M v (t + s) x
      ≤ ∫ s in Set.Ioo (0 : ℝ) (M.T - t), M.lam * Real.exp (-M.lam * s) * M.C x := by
    apply setIntegral_mono_on (te_int' M v hv.2.2.2.2.1 ht x) ((te_w_int M _).mul_const _)
      measurableSet_Ioo
    intro s hs
    exact mul_le_mul_of_nonneg_left (teG_leC M hv (te_mem_shift' M ht hs) x) (te_w_nonneg M s)
  rw [integral_mul_const, te_w_Ioo M hτ] at h1
  nlinarith [M.C_nonneg x]

lemma te_T_zero {v : ℝ × ℕ → ℝ} (hv : M.IMcx v) {t : ℝ} (ht : t ∈ Set.Icc 0 M.T) :
    M.T_op v (t, 0) = 0 := by
  rw [te_Top_eq, M.C_zero, mul_zero, add_zero]
  rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ))]
  · simp
  · intro s hs
    have := hv.2.2.1 _ (te_mem_shift' M ht hs)
    simp [teG, M.C_zero, this]


lemma te_T_xmono {v : ℝ × ℕ → ℝ} (hv : M.IMcx v) {t : ℝ} (ht : t ∈ Set.Icc 0 M.T) (x : ℕ) :
    M.T_op v (t, x) ≤ M.T_op v (t, x + 1) := by
  rw [te_Top_eq, te_Top_eq]
  have h1 := setIntegral_mono_on (te_int' M v hv.2.2.2.2.1 ht x) (te_int' M v hv.2.2.2.2.1 ht (x+1))
    measurableSet_Ioo (fun s hs => mul_le_mul_of_nonneg_left
      (teG_xmono M v (t + s) x (fun y => hv.2.2.2.2.2.2 _ (te_mem_shift' M ht hs) (Nat.le_succ y)))
      (te_w_nonneg M s))
  have h2 := M.C_strictMono.monotone (Nat.le_succ x)
  have h3 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-M.lam * (M.T - t))).le
  linarith

lemma te_T_convex {v : ℝ × ℕ → ℝ} (hv : M.IMcx v) {t : ℝ} (ht : t ∈ Set.Icc 0 M.T) (x : ℕ) :
    M.T_op v (t, x + 1) - M.T_op v (t, x) ≤ M.T_op v (t, x + 2) - M.T_op v (t, x + 1) := by
  rw [te_Top_eq, te_Top_eq, te_Top_eq]
  have hc := hv.2.2.2.2.1
  have h1 := setIntegral_mono_on ((te_int' M v hc ht (x+1)).add (te_int' M v hc ht (x+1)))
    ((te_int' M v hc ht x).add (te_int' M v hc ht (x+2)))
    measurableSet_Ioo (fun s hs => by
      have := teG_convex M v (t + s) x (fun y => hv.2.2.2.1 _ (te_mem_shift' M ht hs) y)
      have hw := te_w_nonneg M s
      simp only [Pi.add_apply]
      nlinarith)
  simp only [Pi.add_apply] at h1
  rw [integral_add (te_int' M v hc ht (x+1)) (te_int' M v hc ht (x+1)),
    integral_add (te_int' M v hc ht x) (te_int' M v hc ht (x+2))] at h1
  have h2 := M.C_convex x
  have h3 := mul_le_mul_of_nonneg_left h2.le (Real.exp_pos (-M.lam * (M.T - t))).le
  have e : x + 1 + 1 = x + 2 := rfl
  linarith

lemma te_T_tmono {v : ℝ × ℕ → ℝ} (hv : M.IMcx v) (x : ℕ) :
    MonotoneOn (fun t => M.T_op v (t, x)) (Set.Icc 0 M.T) := by
  intro t ht t' ht' htt
  simp only
  rw [te_Top_eq, te_Top_eq]
  have hc := hv.2.2.2.2.1
  have hτ' : 0 ≤ M.T - t' := by linarith [ht'.2]
  have hττ : M.T - t' ≤ M.T - t := by linarith
  rw [te_Ioo_eq_interval _ (hτ'.trans hττ), te_Ioo_eq_interval _ hτ']
  have hI : ∀ a b, a ∈ Set.Icc 0 (M.T - t) → b ∈ Set.Icc 0 (M.T - t) →
      IntervalIntegrable (fun s => M.lam * Real.exp (-M.lam * s) * teG M v (t + s) x) volume a b :=
    fun a b ha hb => ((te_int M v hc ht x).mono_set (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := M.T - t')
    (hI _ _ ⟨le_rfl, by linarith⟩ ⟨hτ', hττ⟩) (hI _ _ ⟨hτ', hττ⟩ ⟨by linarith, le_rfl⟩)]
  have h1 : ∫ s in (0:ℝ)..(M.T - t'), M.lam * Real.exp (-M.lam * s) * teG M v (t + s) x ≤
      ∫ s in (0:ℝ)..(M.T - t'), M.lam * Real.exp (-M.lam * s) * teG M v (t' + s) x := by
    apply intervalIntegral.integral_mono_on hτ' (hI _ _ ⟨le_rfl, by linarith⟩ ⟨hτ', hττ⟩)
      ((te_int M v hc ht' x).mono_set (by rw [Set.uIcc_of_le hτ'])).intervalIntegrable
    intro s hs
    apply mul_le_mul_of_nonneg_left _ (te_w_nonneg M s)
    apply teG_mono
    intro y _
    exact hv.2.2.2.2.2.1 y (te_mem_shift M ht ⟨hs.1, by linarith [hs.2]⟩) (te_mem_shift M ht' hs)
      (by linarith)
  have h2 : ∫ s in (M.T - t')..(M.T - t), M.lam * Real.exp (-M.lam * s) * teG M v (t + s) x ≤
      ∫ s in (M.T - t')..(M.T - t), M.lam * Real.exp (-M.lam * s) * M.C x := by
    apply intervalIntegral.integral_mono_on hττ (hI _ _ ⟨hτ', hττ⟩ ⟨by linarith, le_rfl⟩)
      ((by fun_prop : Continuous fun s => M.lam * Real.exp (-M.lam * s) * M.C x).intervalIntegrable _ _)
    intro s hs
    exact mul_le_mul_of_nonneg_left (teG_leC M hv (te_mem_shift M ht ⟨by linarith [hs.1], hs.2⟩) x)
      (te_w_nonneg M s)
  rw [intervalIntegral.integral_mul_const, te_w_interval] at h2
  nlinarith

lemma te_T_cont {v : ℝ × ℕ → ℝ} (hv : M.IMcx v) (x : ℕ) :
    ContinuousOn (fun t => M.T_op v (t, x)) (Set.Icc 0 M.T) := by
  have hc := hv.2.2.2.2.1
  set F : ℝ → ℝ := fun r => M.lam * Real.exp (-M.lam * r) * teG M v r x with hF
  have hFc : ContinuousOn F (Set.Icc 0 M.T) :=
    ((by fun_prop : Continuous fun s => M.lam * Real.exp (-M.lam * s)).continuousOn).mul
      (teG_contOn0 M v hc x)
  have hrep : ∀ t ∈ Set.Icc 0 M.T, M.T_op v (t, x) =
      Real.exp (M.lam * t) * (∫ r in t..M.T, F r) + Real.exp (-M.lam * (M.T - t)) * M.C x := by
    intro t ht
    rw [te_Top_eq, te_Ioo_eq_interval _ (by linarith [ht.2])]
    congr 1
    have := intervalIntegral.integral_comp_add_right
      (fun r => M.lam * Real.exp (-M.lam * (r - t)) * teG M v r x) (a := 0) (b := M.T - t) t
    simp only [add_sub_cancel_right, zero_add, sub_add_cancel] at this
    rw [show (fun s => M.lam * Real.exp (-M.lam * s) * teG M v (t + s) x) =
      fun s => M.lam * Real.exp (-M.lam * s) * teG M v (s + t) x by
        funext s; rw [add_comm t s], this, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    simp only [hF]
    rw [show -M.lam * (r - t) = M.lam * t + (-M.lam * r) by ring, Real.exp_add]
    ring
  refine ContinuousOn.congr ?_ hrep
  have hprim := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := M.T) (b := 0)
    (f := F) (by rw [Set.uIcc_comm, Set.uIcc_of_le M.T_pos.le]; exact hFc.integrableOn_Icc)
  rw [Set.uIcc_comm, Set.uIcc_of_le M.T_pos.le] at hprim
  have hprim' : ContinuousOn (fun t => ∫ r in t..M.T, F r) (Set.Icc 0 M.T) :=
    hprim.neg.congr (fun t _ => by rw [intervalIntegral.integral_symm]; rfl)
  exact ((by fun_prop : Continuous fun t => Real.exp (M.lam * t)).continuousOn.mul hprim').add
    ((by fun_prop : Continuous fun t => Real.exp (-M.lam * (M.T - t)) * M.C x).continuousOn)

lemma te_T_pres {v : ℝ × ℕ → ℝ} (hv : M.IMcx v) : M.IMcx (M.T_op v) := by
  refine ⟨⟨1, fun p hp => ?_⟩, fun p hp => ?_, fun t ht => te_T_zero M hv ht,
    fun t ht x => te_T_convex M hv ht x, fun x => te_T_cont M hv x, fun x => te_T_tmono M hv x,
    fun t ht => monotone_nat_of_le_succ (fun x => te_T_xmono M hv ht x)⟩
  · obtain ⟨ht, -⟩ := hp
    rw [one_mul, abs_le]
    exact ⟨by linarith [te_T_nonneg M hv ht p.2, M.C_nonneg p.2], te_T_leC M hv ht p.2⟩
  · exact te_T_leC M hv hp.1 p.2


lemma te_contr {v w : ℝ × ℕ → ℝ} (hv : M.IMcx v) (hw : M.IMcx w) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ p ∈ M.E, |v p - w p| ≤ K * M.C p.2) :
    ∀ p ∈ M.E, |M.T_op v p - M.T_op w p| ≤ (1 - Real.exp (-M.lam * M.T)) * K * M.C p.2 := by
  rintro ⟨t, x⟩ ⟨ht, -⟩
  simp only at ht ⊢
  rw [te_Top_eq, te_Top_eq, add_sub_add_right_eq_sub,
    ← integral_sub (te_int' M v hv.2.2.2.2.1 ht x) (te_int' M w hw.2.2.2.2.1 ht x)]
  have hτ : 0 ≤ M.T - t := by linarith [ht.2]
  have h1 := norm_integral_le_of_norm_le (((te_w_int M (M.T - t)).mul_const (K * M.C x)))
    (f := fun s => M.lam * Real.exp (-M.lam * s) * teG M v (t + s) x -
      M.lam * Real.exp (-M.lam * s) * teG M w (t + s) x)
    ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall (fun s hs => by
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (te_w_nonneg M s)]
      apply mul_le_mul_of_nonneg_left _ (te_w_nonneg M s)
      apply teG_lip
      intro y hy
      have hr := te_mem_shift' M ht hs
      exact (h (t + s, y) ⟨hr, Set.mem_univ _⟩).trans
        (mul_le_mul_of_nonneg_left (M.C_strictMono.monotone hy) hK))))
  rw [integral_mul_const, te_w_Ioo M hτ, Real.norm_eq_abs] at h1
  refine h1.trans ?_
  have : Real.exp (-M.lam * M.T) ≤ Real.exp (-M.lam * (M.T - t)) :=
    Real.exp_le_exp.mpr (by nlinarith [M.lam_pos, ht.1])
  have := mul_nonneg hK (M.C_nonneg x)
  nlinarith

lemma te_zero_IMcx : M.IMcx (fun _ => 0) := by
  refine ⟨⟨0, fun p _ => by simp⟩, fun p _ => M.C_nonneg _, fun _ _ => rfl, fun _ _ _ => by simp,
    fun _ => continuousOn_const, fun _ => monotoneOn_const, fun _ _ => monotone_const⟩

noncomputable def teSeq (n : ℕ) : ℝ × ℕ → ℝ := (M.T_op)^[n] (fun _ => 0)

lemma teSeq_succ (n : ℕ) : teSeq M (n + 1) = M.T_op (teSeq M n) :=
  Function.iterate_succ_apply' _ _ _

lemma teSeq_IMcx (n : ℕ) : M.IMcx (teSeq M n) := by
  induction n with
  | zero => exact te_zero_IMcx M
  | succ n ih => rw [teSeq_succ]; exact te_T_pres M ih

lemma te_beta_lt : 1 - Real.exp (-M.lam * M.T) < 1 := by
  have := Real.exp_pos (-M.lam * M.T); linarith

lemma te_beta_nonneg : 0 ≤ 1 - Real.exp (-M.lam * M.T) := by
  have : Real.exp (-M.lam * M.T) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [M.lam_pos, M.T_pos])
  linarith

lemma teSeq_diff (n : ℕ) : ∀ p ∈ M.E, |teSeq M (n + 1) p - teSeq M n p| ≤
    (1 - Real.exp (-M.lam * M.T)) ^ n * M.C p.2 := by
  induction n with
  | zero =>
    rintro ⟨t, x⟩ ⟨ht, -⟩
    simp only [pow_zero, one_mul]
    have e : teSeq M 0 = fun _ => 0 := rfl
    rw [teSeq_succ, e, sub_zero, abs_of_nonneg (te_T_nonneg M (te_zero_IMcx M) ht x)]
    exact te_T_leC M (te_zero_IMcx M) ht x
  | succ n ih =>
    intro p hp
    rw [teSeq_succ M (n + 1)]
    have := te_contr M (teSeq_IMcx M (n + 1)) (teSeq_IMcx M n)
      (pow_nonneg (te_beta_nonneg M) n) ih p hp
    rw [← pow_succ'] at this
    rw [teSeq_succ M n] at this ⊢
    exact this

lemma teSeq_tendsto {p : ℝ × ℕ} (hp : p ∈ M.E) :
    Tendsto (fun n => teSeq M n p) atTop (𝓝 (limUnder atTop (fun n => teSeq M n p))) := by
  have hc : CauchySeq (fun n => teSeq M n p) := by
    apply cauchySeq_of_le_geometric (1 - Real.exp (-M.lam * M.T)) (M.C p.2) (te_beta_lt M)
    intro n
    rw [Real.dist_eq, abs_sub_comm, mul_comm]
    exact teSeq_diff M n p hp
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete hc)

noncomputable def teW (p : ℝ × ℕ) : ℝ := limUnder atTop (fun n => teSeq M n p)

lemma teSeq_dist (n : ℕ) {p : ℝ × ℕ} (hp : p ∈ M.E) :
    |teSeq M n p - teW M p| ≤
      (1 - Real.exp (-M.lam * M.T)) ^ n / (1 - (1 - Real.exp (-M.lam * M.T))) * M.C p.2 := by
  have := dist_le_of_le_geometric_of_tendsto (1 - Real.exp (-M.lam * M.T)) (M.C p.2) (te_beta_lt M)
    (f := fun n => teSeq M n p) (fun n => by
      rw [Real.dist_eq, abs_sub_comm, mul_comm]; exact teSeq_diff M n p hp)
    (teSeq_tendsto M hp) n
  rw [Real.dist_eq] at this
  refine this.trans (le_of_eq ?_)
  ring


lemma te_bound_tendsto (c : ℝ) :
    Tendsto (fun n : ℕ => (1 - Real.exp (-M.lam * M.T)) ^ n /
      (1 - (1 - Real.exp (-M.lam * M.T))) * c) atTop (𝓝 0) := by
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (te_beta_nonneg M) (te_beta_lt M)).div_const
    (1 - (1 - Real.exp (-M.lam * M.T)))
  have := this.mul_const c
  simpa using this

lemma te_mem_E {t : ℝ} (ht : t ∈ Set.Icc 0 M.T) (x : ℕ) : (t, x) ∈ M.E := ⟨ht, Set.mem_univ _⟩

lemma te_W_IMcx : M.IMcx (teW M) := by
  have hlim := fun p (hp : p ∈ M.E) => teSeq_tendsto M hp
  refine ⟨⟨1, fun p hp => ?_⟩, fun p hp => ?_, fun t ht => ?_, fun t ht x => ?_, fun x => ?_,
    fun x t ht t' ht' htt => ?_, fun t ht => monotone_nat_of_le_succ (fun x => ?_)⟩
  · have h0 : 0 ≤ teW M p := ge_of_tendsto' (hlim p hp)
      (fun n => te_nonneg M (teSeq_IMcx M n) hp.1 p.2)
    have h1 : teW M p ≤ M.C p.2 := le_of_tendsto' (hlim p hp) (fun n => (teSeq_IMcx M n).2.1 p hp)
    rw [one_mul, abs_le]; constructor <;> linarith [M.C_nonneg p.2]
  · exact le_of_tendsto' (hlim p hp) (fun n => (teSeq_IMcx M n).2.1 p hp)
  · refine tendsto_nhds_unique (hlim _ (te_mem_E M ht 0)) ?_
    simp only [(teSeq_IMcx M _).2.2.1 t ht]
    exact tendsto_const_nhds
  · have := ((hlim _ (te_mem_E M ht (x + 2))).sub (hlim _ (te_mem_E M ht (x + 1)))).sub
      ((hlim _ (te_mem_E M ht (x + 1))).sub (hlim _ (te_mem_E M ht x)))
    have h := ge_of_tendsto' this (fun n => by
      have := (teSeq_IMcx M n).2.2.2.1 t ht x
      show (0:ℝ) ≤ _
      linarith)
    unfold teW; linarith
  · apply TendstoUniformlyOn.continuousOn (F := fun n t => teSeq M n (t, x))
    · rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have := (te_bound_tendsto M (M.C x)).eventually (gt_mem_nhds hε)
      filter_upwards [this] with n hn
      intro t ht
      rw [Real.dist_eq, abs_sub_comm]
      exact lt_of_le_of_lt (teSeq_dist M n (te_mem_E M ht x)) hn
    · exact (Eventually.of_forall (f := atTop)
        (fun n => (teSeq_IMcx M n).2.2.2.2.1 x)).frequently
  · exact le_of_tendsto_of_tendsto' (hlim _ (te_mem_E M ht x)) (hlim _ (te_mem_E M ht' x))
      (fun n => (teSeq_IMcx M n).2.2.2.2.2.1 x ht ht' htt)
  · exact le_of_tendsto_of_tendsto' (hlim _ (te_mem_E M ht x)) (hlim _ (te_mem_E M ht (x + 1)))
      (fun n => (teSeq_IMcx M n).2.2.2.2.2.2 t ht (Nat.le_succ x))

lemma te_W_fix : ∀ p ∈ M.E, M.T_op (teW M) p = teW M p := by
  intro p hp
  have h1 : Tendsto (fun n => teSeq M (n + 1) p) atTop (𝓝 (M.T_op (teW M) p)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using (te_bound_tendsto M (M.C p.2)).const_mul (1 - Real.exp (-M.lam * M.T)))
    rw [Real.norm_eq_abs, teSeq_succ, abs_sub_comm]
    have := te_contr M (te_W_IMcx M) (teSeq_IMcx M n)
      (K := (1 - Real.exp (-M.lam * M.T)) ^ n / (1 - (1 - Real.exp (-M.lam * M.T))))
      (div_nonneg (pow_nonneg (te_beta_nonneg M) n) (by linarith [te_beta_lt M]))
      (fun q hq => by rw [abs_sub_comm]; exact teSeq_dist M n hq) p hp
    refine this.trans (le_of_eq ?_)
    ring
  have h2 := (teSeq_tendsto M hp).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique h1 h2

lemma te_congr_IMcx {v w : ℝ × ℕ → ℝ} (hw : M.IMcx w) (h : ∀ p ∈ M.E, v p = w p) : M.IMcx v := by
  obtain ⟨⟨K, hK⟩, h1, h2, h3, h4, h5, h6⟩ := hw
  have h' : ∀ t ∈ Set.Icc 0 M.T, ∀ x, v (t, x) = w (t, x) := fun t ht x => h _ (te_mem_E M ht x)
  refine ⟨⟨K, fun p hp => by rw [h p hp]; exact hK p hp⟩, fun p hp => by rw [h p hp]; exact h1 p hp,
    fun t ht => by rw [h' t ht]; exact h2 t ht, fun t ht x => by
      rw [h' t ht, h' t ht, h' t ht]; exact h3 t ht x,
    fun x => (h4 x).congr (fun t ht => h' t ht x),
    fun x t ht t' ht' htt => by simp only; rw [h' t ht, h' t' ht']; exact h5 x ht ht' htt,
    fun t ht a b hab => by simp only; rw [h' t ht, h' t ht]; exact h6 t ht hab⟩

lemma te_T_congr {v w : ℝ × ℕ → ℝ} (h : ∀ p ∈ M.E, v p = w p) :
    ∀ p ∈ M.E, M.T_op v p = M.T_op w p := by
  rintro ⟨t, x⟩ ⟨ht, -⟩
  simp only at ht
  rw [te_Top_eq, te_Top_eq]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro s hs
  simp only
  congr 1
  unfold teG
  congr 1
  funext u
  rw [h _ (te_mem_E M (te_mem_shift' M ht hs) _)]

noncomputable def teClamp (t : ℝ) : ℝ := max 0 (min t M.T)

lemma teClamp_mem (t : ℝ) : teClamp M t ∈ Set.Icc 0 M.T :=
  ⟨le_max_left _ _, max_le M.T_pos.le (min_le_right _ _)⟩

lemma teClamp_eq {t : ℝ} (ht : t ∈ Set.Icc 0 M.T) : teClamp M t = t := by
  unfold teClamp; rw [min_eq_left ht.2, max_eq_right ht.1]

lemma teClamp_cont : Continuous (teClamp M) := by unfold teClamp; fun_prop

noncomputable def teV (p : ℝ × ℕ) : ℝ := teW M (teClamp M p.1, p.2)

lemma teV_eq : ∀ p ∈ M.E, teV M p = teW M p := by
  rintro ⟨t, x⟩ ⟨ht, -⟩
  simp only [teV]; rw [teClamp_eq M ht]

lemma teV_IMcx : M.IMcx (teV M) := te_congr_IMcx M (te_W_IMcx M) (teV_eq M)

lemma teV_fix : ∀ p ∈ M.E, M.T_op (teV M) p = teV M p := by
  intro p hp
  rw [te_T_congr M (teV_eq M) p hp, te_W_fix M p hp, teV_eq M p hp]

lemma teV_cont (x : ℕ) : Continuous (fun t => teV M (t, x)) := by
  have := ((te_W_IMcx M).2.2.2.2.1 x).comp_continuous (teClamp_cont M) (teClamp_mem M)
  exact this


lemma teV_meas : Measurable (teV M) :=
  measurable_from_prod_countable_left (fun x => (teV_cont M x).measurable)

lemma te_fstar_meas : Measurable (M.fstar (teV M)) := by
  apply measurable_from_prod_countable_left
  intro x
  set S : ℝ → ℕ → Prop := fun t u =>
    u ≤ x ∧ ∀ u' ≤ x, M.C u + teV M (t, x - u) ≤ M.C u' + teV M (t, x - u') with hS
  have hSm : ∀ u, Measurable (fun t => S t u) := by
    intro u
    refine Measurable.and measurable_const (Measurable.forall fun u' => Measurable.imp
      measurable_const ?_)
    exact measurableSet_setOfPred.mp (measurableSet_le
      (measurable_const.add ((teV_cont M _).measurable))
      (measurable_const.add ((teV_cont M _).measurable)))
  apply measurable_to_countable'
  intro k
  have : (fun t => M.fstar (teV M) (t, x)) ⁻¹' {k} = {t | S t k ∧ ∀ j, j < k → ¬ S t j} := by
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    have hne : {u | S t u}.Nonempty := by
      obtain ⟨u, hu, e⟩ := teG_exists M (teV M) t x
      exact ⟨u, hu, fun u' hu' => by rw [← e]; exact teG_le M _ t x u' hu'⟩
    have hdef : M.fstar (teV M) (t, x) = sInf {u | S t u} := rfl
    rw [hdef]
    constructor
    · rintro rfl
      exact ⟨Nat.sInf_mem hne, fun j hj => Nat.notMem_of_lt_sInf hj⟩
    · rintro ⟨h1, h2⟩
      apply le_antisymm (Nat.sInf_le h1)
      by_contra hc
      push_neg at hc
      exact h2 _ hc (Nat.sInf_mem hne)
  rw [this]
  exact measurableSet_setOfPred.mpr ((hSm k).and (Measurable.forall fun j =>
    Measurable.imp measurable_const ((hSm j).not)))

noncomputable def teOffer (p : ℝ × ℕ) : Offer :=
  ⟨fun s => M.fstar (teV M) (p.1 + s, p.2),
    (te_fstar_meas M).comp ((measurable_const.add measurable_id).prodMk measurable_const)⟩

noncomputable def tePol : ℕ → ℝ × ℕ → Offer := fun _ p => teOffer M p

lemma tePol_policy : TradeExecution.IsPolicy (tePol M) := by
  intro n
  refine ⟨?_, fun p s => (te_fstar_spec M (teV M) _ _).1⟩
  rintro _ ⟨S, hS, rfl⟩
  have : Measurable (fun p : ℝ × ℕ => (teOffer M p).val) := by
    apply measurable_pi_lambda
    intro s
    exact (te_fstar_meas M).comp ((measurable_fst.add measurable_const).prodMk measurable_snd)
  exact this hS


lemma te_int_gen (τ : ℝ) (F : ℝ → ℝ) (hF : Measurable F) (B : ℝ)
    (hB : ∀ s ∈ Set.Ioo 0 τ, |F s| ≤ B) : IntegrableOn F (Set.Ioo 0 τ) :=
  Integrable.of_bound hF.aestronglyMeasurable B ((ae_restrict_iff' measurableSet_Ioo).mpr
    (Eventually.of_forall (fun s hs => by rw [Real.norm_eq_abs]; exact hB s hs)))

lemma te_w_le {s : ℝ} (hs : 0 ≤ s) : M.lam * Real.exp (-M.lam * s) ≤ M.lam := by
  have : Real.exp (-M.lam * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [M.lam_pos])
  nlinarith [M.lam_pos]

lemma te_F1_int (a : Offer) {x : ℕ} (ha : a.Admissible x) (τ : ℝ) :
    IntegrableOn (fun s => M.lam * Real.exp (-M.lam * s) * M.C (a.val s)) (Set.Ioo 0 τ) := by
  refine te_int_gen τ _ ((by fun_prop : Measurable fun s => M.lam * Real.exp (-M.lam * s)).mul
    ((measurable_of_countable M.C).comp a.meas)) (M.lam * M.C x) (fun s hs => ?_)
  rw [abs_of_nonneg (mul_nonneg (te_w_nonneg M s) (M.C_nonneg _))]
  exact mul_le_mul (te_w_le M hs.1.le) (M.C_strictMono.monotone (ha s)) (M.C_nonneg _)
    M.lam_pos.le

lemma te_F2_meas (a : Offer) (t : ℝ) (x : ℕ) :
    Measurable (fun s => M.lam * Real.exp (-M.lam * s) * teV M (t + s, x - a.val s)) :=
  (by fun_prop : Measurable fun s => M.lam * Real.exp (-M.lam * s)).mul ((teV_meas M).comp
    ((measurable_const.add measurable_id).prodMk
      ((measurable_of_countable (fun k : ℕ => x - k)).comp a.meas)))

lemma te_F2_int (a : Offer) {t : ℝ} (ht : t ∈ Set.Icc 0 M.T) (x : ℕ) :
    IntegrableOn (fun s => M.lam * Real.exp (-M.lam * s) * teV M (t + s, x - a.val s))
      (Set.Ioo 0 (M.T - t)) := by
  refine te_int_gen _ _ (te_F2_meas M a t x) (M.lam * M.C x) (fun s hs => ?_)
  have hr := te_mem_shift' M ht hs
  have h0 := te_nonneg M (teV_IMcx M) hr (x - a.val s)
  have h1 := (teV_IMcx M).2.1 _ (te_mem_E M hr (x - a.val s))
  rw [abs_of_nonneg (mul_nonneg (te_w_nonneg M s) h0)]
  exact mul_le_mul (te_w_le M hs.1.le) (h1.trans (M.C_strictMono.monotone (Nat.sub_le _ _))) h0
    M.lam_pos.le

lemma te_c_eq (a : Offer) (p : ℝ × ℕ) : M.c a p =
    (∫ s in Set.Ioo (0 : ℝ) (M.T - p.1), M.lam * Real.exp (-M.lam * s) * M.C (a.val s)) +
      Real.exp (-M.lam * (M.T - p.1)) * M.C p.2 := rfl

lemma te_c_nonneg (a : Offer) (p : ℝ × ℕ) : 0 ≤ M.c a p := by
  rw [te_c_eq]
  exact add_nonneg (setIntegral_nonneg measurableSet_Ioo fun s _ =>
    mul_nonneg (te_w_nonneg M s) (M.C_nonneg _)) (mul_nonneg (Real.exp_pos _).le (M.C_nonneg _))

lemma te_step_le (a : Offer) {t : ℝ} (ht : t ∈ Set.Icc 0 M.T) {x : ℕ} (ha : a.Admissible x) :
    teV M (t, x) ≤ M.c a (t, x) +
      ∫ s in Set.Ioo (0 : ℝ) (M.T - t), M.lam * Real.exp (-M.lam * s) * teV M (t + s, x - a.val s) := by
  rw [← teV_fix M _ (te_mem_E M ht x), te_Top_eq, te_c_eq]
  have h := setIntegral_mono_on (te_int' M _ (teV_IMcx M).2.2.2.2.1 ht x)
    ((te_F1_int M a ha _).add (te_F2_int M a ht x)) measurableSet_Ioo (fun s hs => by
      simp only [Pi.add_apply]
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (teG_le M _ _ x _ (ha s)) (te_w_nonneg M s))
  simp only [Pi.add_apply] at h
  rw [integral_add (te_F1_int M a ha _) (te_F2_int M a ht x)] at h
  simp only
  linarith

lemma te_step_eq {t : ℝ} (ht : t ∈ Set.Icc 0 M.T) (x : ℕ) :
    teV M (t, x) = M.c (teOffer M (t, x)) (t, x) +
      ∫ s in Set.Ioo (0 : ℝ) (M.T - t), M.lam * Real.exp (-M.lam * s) *
        teV M (t + s, x - (teOffer M (t, x)).val s) := by
  have ha : (teOffer M (t, x)).Admissible x := fun s => (te_fstar_spec M (teV M) _ _).1
  rw [← teV_fix M _ (te_mem_E M ht x), te_Top_eq, te_c_eq]
  rw [setIntegral_congr_fun measurableSet_Ioo (g := fun s =>
    M.lam * Real.exp (-M.lam * s) * M.C ((teOffer M (t, x)).val s) +
    M.lam * Real.exp (-M.lam * s) * teV M (t + s, x - (teOffer M (t, x)).val s))
    (fun s hs => by
      simp only
      rw [← mul_add, ← te_fstar_eq M (teV M) (t + s) x]
      rfl)]
  rw [integral_add (te_F1_int M _ ha _) (te_F2_int M _ ht x)]
  simp only
  ring

lemma te_lint_eq (a : Offer) {t : ℝ} (ht : t ∈ Set.Icc 0 M.T) (x : ℕ) :
    ENNReal.ofReal (∫ s in Set.Ioo (0 : ℝ) (M.T - t),
      M.lam * Real.exp (-M.lam * s) * teV M (t + s, x - a.val s)) =
    ∫⁻ s in Set.Ioo (0 : ℝ) (M.T - t), ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) *
      ENNReal.ofReal (teV M (t + s, x - a.val s)) := by
  rw [ofReal_integral_eq_lintegral_ofReal (te_F2_int M a ht x)
    ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall (fun s hs =>
      mul_nonneg (te_w_nonneg M s) (te_nonneg M (teV_IMcx M) (te_mem_shift' M ht hs) _))))]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro s hs
  simp only
  rw [ENNReal.ofReal_mul (te_w_nonneg M s)]

lemma te_Jn_succ (n : ℕ) (f : ℕ → ℝ × ℕ → Offer) (p : ℝ × ℕ) :
    M.Jn (n + 1) f p = ENNReal.ofReal (M.c (f 0 p) p) +
        ∫⁻ s in Set.Ioo (0 : ℝ) (M.T - p.1), ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) *
          M.Jn n (fun k => f (k + 1)) (p.1 + s, p.2 - (f 0 p).val s) := rfl


lemma te_B (n : ℕ) : ∀ p ∈ M.E, M.Jn n (tePol M) p ≤ ENNReal.ofReal (teV M p) := by
  induction n with
  | zero => intro p _; exact bot_le
  | succ n ih =>
    rintro ⟨t, x⟩ ⟨ht, -⟩
    simp only at ht
    rw [te_Jn_succ]
    have e : (fun k => tePol M (k + 1)) = tePol M := rfl
    rw [e]
    have h1 : ∫⁻ s in Set.Ioo (0 : ℝ) (M.T - t), ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) *
        M.Jn n (tePol M) (t + s, x - (tePol M 0 (t, x)).val s) ≤
        ∫⁻ s in Set.Ioo (0 : ℝ) (M.T - t), ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) *
        ENNReal.ofReal (teV M (t + s, x - (teOffer M (t, x)).val s)) := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro s hs
      exact mul_le_mul_right (ih _ (te_mem_E M (te_mem_shift' M ht hs) _)) _
    refine (add_le_add le_rfl h1).trans (le_of_eq ?_)
    rw [← te_lint_eq M _ ht x, ← ENNReal.ofReal_add (te_c_nonneg M _ _)
      (setIntegral_nonneg measurableSet_Ioo fun s hs =>
        mul_nonneg (te_w_nonneg M s) (te_nonneg M (teV_IMcx M) (te_mem_shift' M ht hs) _))]
    rw [te_step_eq M ht x]
    rfl

lemma te_A (n : ℕ) : ∀ f : ℕ → ℝ × ℕ → Offer, TradeExecution.IsPolicy f → ∀ p ∈ M.E,
    ENNReal.ofReal (teV M p) ≤
      M.Jn n f p + ENNReal.ofReal ((1 - Real.exp (-M.lam * M.T)) ^ n * M.C p.2) := by
  induction n with
  | zero =>
    intro f _ p hp
    simp only [pow_zero, one_mul]
    exact (ENNReal.ofReal_le_ofReal ((teV_IMcx M).2.1 p hp)).trans le_add_self
  | succ n ih =>
    intro f hf p hp
    obtain ⟨t, x⟩ := p
    have ht : t ∈ Set.Icc 0 M.T := hp.1
    set a := f 0 (t, x) with ha_def
    have ha : a.Admissible x := (hf 0).2 (t, x)
    have hf' : TradeExecution.IsPolicy (fun k => f (k + 1)) := fun k => hf (k + 1)
    set β := 1 - Real.exp (-M.lam * M.T) with hβ
    have hτ : 0 ≤ M.T - t := by linarith [ht.2]
    have h0 := te_step_le M a ht ha
    have hI0 : 0 ≤ ∫ s in Set.Ioo (0 : ℝ) (M.T - t),
        M.lam * Real.exp (-M.lam * s) * teV M (t + s, x - a.val s) :=
      setIntegral_nonneg measurableSet_Ioo fun s hs =>
        mul_nonneg (te_w_nonneg M s) (te_nonneg M (teV_IMcx M) (te_mem_shift' M ht hs) _)
    have h1 := ENNReal.ofReal_le_ofReal h0
    rw [ENNReal.ofReal_add (te_c_nonneg M _ _) hI0, te_lint_eq M a ht x] at h1
    refine h1.trans ?_
    rw [te_Jn_succ, add_assoc]
    refine add_le_add le_rfl ?_
    have hwm : Measurable fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) := by fun_prop
    simp only
    calc ∫⁻ s in Set.Ioo (0 : ℝ) (M.T - t), ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) *
          ENNReal.ofReal (teV M (t + s, x - a.val s))
        ≤ ∫⁻ s in Set.Ioo (0 : ℝ) (M.T - t), (ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) *
          M.Jn n (fun k => f (k + 1)) (t + s, x - a.val s) +
          ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) * ENNReal.ofReal (β ^ n * M.C x)) := by
          apply setLIntegral_mono' measurableSet_Ioo
          intro s hs
          rw [← mul_add]
          apply mul_le_mul_right
          refine (ih _ hf' _ (te_mem_E M (te_mem_shift' M ht hs) _)).trans (add_le_add le_rfl ?_)
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_left (M.C_strictMono.monotone (Nat.sub_le _ _))
            (pow_nonneg (te_beta_nonneg M) n)
      _ = (∫⁻ s in Set.Ioo (0 : ℝ) (M.T - t), ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) *
          M.Jn n (fun k => f (k + 1)) (t + s, x - a.val s)) +
          ENNReal.ofReal (1 - Real.exp (-M.lam * (M.T - t))) * ENNReal.ofReal (β ^ n * M.C x) := by
          rw [lintegral_add_right _ (hwm.mul_const _), lintegral_mul_const _ hwm,
            te_lw_Ioo M hτ]
      _ ≤ _ := by
          have he : Real.exp (-M.lam * (M.T - t)) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by nlinarith [M.lam_pos])
          have he0 : 0 ≤ 1 - Real.exp (-M.lam * (M.T - t)) := by linarith
          rw [← ENNReal.ofReal_mul he0]
          refine add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_)
          have : Real.exp (-M.lam * M.T) ≤ Real.exp (-M.lam * (M.T - t)) :=
            Real.exp_le_exp.mpr (by nlinarith [M.lam_pos, ht.1])
          have := mul_nonneg (pow_nonneg (te_beta_nonneg M) n) (M.C_nonneg x)
          rw [pow_succ]
          nlinarith

lemma te_lower {f : ℕ → ℝ × ℕ → Offer} (hf : TradeExecution.IsPolicy f) {p : ℝ × ℕ}
    (hp : p ∈ M.E) : ENNReal.ofReal (teV M p) ≤ M.Jinfpi f p := by
  have hT : Tendsto (fun n => M.Jinfpi f p +
      ENNReal.ofReal ((1 - Real.exp (-M.lam * M.T)) ^ n * M.C p.2)) atTop
      (𝓝 (M.Jinfpi f p + ENNReal.ofReal 0)) := by
    refine tendsto_const_nhds.add (ENNReal.tendsto_ofReal ?_)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (te_beta_nonneg M)
      (te_beta_lt M)).mul_const (M.C p.2)
  rw [ENNReal.ofReal_zero, add_zero] at hT
  exact ge_of_tendsto' hT (fun n => (te_A M n f hf p hp).trans
    (add_le_add (le_iSup (fun n => M.Jn n f p) n) le_rfl))

lemma te_Jinf_eq {p : ℝ × ℕ} (hp : p ∈ M.E) :
    M.Jinf p = ENNReal.ofReal (teV M p) ∧ M.Jinfpi (tePol M) p = M.Jinf p := by
  have h1 : ENNReal.ofReal (teV M p) ≤ M.Jinf p :=
    le_iInf₂ (fun f hf => te_lower M hf hp)
  have h2 : M.Jinfpi (tePol M) p ≤ ENNReal.ofReal (teV M p) :=
    iSup_le (fun n => te_B M n p hp)
  have h3 : M.Jinf p ≤ M.Jinfpi (tePol M) p := iInf₂_le (tePol M) (tePol_policy M)
  exact ⟨le_antisymm (h3.trans h2) h1, le_antisymm (h2.trans h1) h3⟩

lemma te_uniq {v : ℝ × ℕ → ℝ} (hv : M.IMcx v) (hfix : ∀ p ∈ M.E, M.T_op v p = v p) :
    ∀ p ∈ M.E, v p = teV M p := by
  obtain ⟨K, hK⟩ := hv.1
  have hb : ∀ n : ℕ, ∀ p ∈ M.E, |v p - teV M p| ≤
      (1 - Real.exp (-M.lam * M.T)) ^ n * (|K| + 1) * M.C p.2 := by
    intro n
    induction n with
    | zero =>
      intro p hp
      have h1 := hK p hp
      have h2 := (teV_IMcx M).2.1 p hp
      have h3 := te_nonneg M (teV_IMcx M) hp.1 p.2
      have h4 : K * M.C p.2 ≤ |K| * M.C p.2 :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (M.C_nonneg _)
      rw [abs_le] at h1 ⊢
      constructor <;> nlinarith
    | succ n ih =>
      intro p hp
      have := te_contr M hv (teV_IMcx M) (mul_nonneg (pow_nonneg (te_beta_nonneg M) n)
        (by positivity)) ih p hp
      rw [hfix p hp, teV_fix M p hp] at this
      refine this.trans (le_of_eq ?_)
      ring
  intro p hp
  have hT : Tendsto (fun n : ℕ => (1 - Real.exp (-M.lam * M.T)) ^ n * (|K| + 1) * M.C p.2)
      atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (te_beta_nonneg M)
      (te_beta_lt M)).mul_const (|K| + 1)).mul_const (M.C p.2)
  have := ge_of_tendsto' hT (fun n => hb n p hp)
  have := abs_nonneg (v p - teV M p)
  have : |v p - teV M p| = 0 := by linarith
  rw [abs_eq_zero, sub_eq_zero] at this
  exact this

theorem theorem_9_4_2_core (M : TradeExecution) :
    ∃ V : ℝ × ℕ → ℝ, M.IMcx V ∧
      (∀ p ∈ M.E, M.Jinf p = ENNReal.ofReal (V p)) ∧
      (∀ p ∈ M.E, M.T_op V p = V p) ∧
      (∀ v : ℝ × ℕ → ℝ, M.IMcx v → (∀ p ∈ M.E, M.T_op v p = v p) → ∀ p ∈ M.E, v p = V p) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ x : ℕ,
        M.fstar V (t, x) ≤ M.fstar V (t, x + 1) ∧
        M.fstar V (t, x + 1) ≤ M.fstar V (t, x) + 1) ∧
      (∃ f : ℕ → ℝ × ℕ → Offer, TradeExecution.IsPolicy f ∧
        (∀ n, ∀ p ∈ M.E, ∀ s : ℝ, 0 ≤ s → (f n p).val s = M.fstar V (p.1 + s, p.2)) ∧
        ∀ p ∈ M.E, M.Jinfpi f p = M.Jinf p) :=
  ⟨teV M, teV_IMcx M, fun p hp => (te_Jinf_eq M hp).1, teV_fix M,
    fun v hv hfix => te_uniq M hv hfix,
    fun t ht x => te_fstar_mono M (teV M) t x (fun y => (teV_IMcx M).2.2.2.1 t ht y),
    ⟨tePol M, tePol_policy M, fun _ _ _ _ _ => rfl, fun p hp => (te_Jinf_eq M hp).2⟩⟩

end MDPFinance.JumpMarkets

open MDPFinance.JumpMarkets


theorem solution (M : TradeExecution) :
    ∃ V : ℝ × ℕ → ℝ, M.IMcx V ∧
      (∀ p ∈ M.E, M.Jinf p = ENNReal.ofReal (V p)) ∧
      (∀ p ∈ M.E, M.T_op V p = V p) ∧
      (∀ v : ℝ × ℕ → ℝ, M.IMcx v → (∀ p ∈ M.E, M.T_op v p = v p) → ∀ p ∈ M.E, v p = V p) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ x : ℕ,
        M.fstar V (t, x) ≤ M.fstar V (t, x + 1) ∧
        M.fstar V (t, x + 1) ≤ M.fstar V (t, x) + 1) ∧
      (∃ f : ℕ → ℝ × ℕ → Offer, TradeExecution.IsPolicy f ∧
        (∀ n, ∀ p ∈ M.E, ∀ s : ℝ, 0 ≤ s → (f n p).val s = M.fstar V (p.1 + s, p.2)) ∧
        ∀ p ∈ M.E, M.Jinfpi f p = M.Jinf p) := by
  exact theorem_9_4_2_core M
