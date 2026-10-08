-- Prove2me | solution 1 for MinimaxRegretRL.Bernstein.total_variance_episode
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:40:39.253034+00:00
-- url     : https://prove2.me/submissions/5fc7ff6b-5a9d-4208-bcca-1c584dce0b6f

import Mathlib
import Definitions.Def_MinimaxRegretRL_Bernstein_Path

set_option autoImplicit false

open scoped Classical

namespace TVEp

variable {S : Type*} [Fintype S]

def gst (x : S) {n : ℕ} (p : Fin n → S) (t : Fin n) : S :=
  if ht : t.val = 0 then x else p ⟨t.val - 1, by omega⟩

noncomputable def gprob (Q : ℕ → S → S → ℝ) (k : ℕ) (x : S) {n : ℕ} (p : Fin n → S) : ℝ :=
  ∏ t : Fin n, Q (k + t.val) (gst x p t) (p t)

noncomputable def grew (r : ℕ → S → ℝ) (k : ℕ) (x : S) {n : ℕ} (p : Fin n → S) : ℝ :=
  ∑ t : Fin n, r (k + t.val) (gst x p t)

noncomputable def gvar (Q : ℕ → S → S → ℝ) (W : ℕ → S → ℝ) (j : ℕ) (s : S) : ℝ :=
  (∑ y, Q j s y * W (j + 1) y ^ 2) - (∑ y, Q j s y * W (j + 1) y) ^ 2

noncomputable def gvs (Q : ℕ → S → S → ℝ) (W : ℕ → S → ℝ) (k : ℕ) (x : S) {n : ℕ}
    (p : Fin n → S) : ℝ :=
  ∑ t : Fin n, gvar Q W (k + t.val) (gst x p t)

noncomputable def gexp (Q : ℕ → S → S → ℝ) (k : ℕ) (x : S) (n : ℕ)
    (f : (Fin n → S) → ℝ) : ℝ :=
  ∑ p : Fin n → S, gprob Q k x p * f p

lemma gst_zero (x y : S) {n : ℕ} (q : Fin n → S) :
    gst x (Fin.cons y q : Fin (n + 1) → S) 0 = x := by
  simp [gst]

lemma gst_succ (x y : S) {n : ℕ} (q : Fin n → S) (t : Fin n) :
    gst x (Fin.cons y q : Fin (n + 1) → S) t.succ = gst y q t := by
  have k1 : ∀ i : Fin (n + 1), i = 0 → (Fin.cons y q : Fin (n + 1) → S) i = y := by
    rintro i rfl; simp
  have k2 : ∀ (i : Fin (n + 1)) (j : Fin n), i = j.succ →
      (Fin.cons y q : Fin (n + 1) → S) i = q j := by
    rintro i j rfl; simp
  unfold gst
  rw [dif_neg (by simp)]
  by_cases ht : t.val = 0
  · rw [dif_pos ht]; exact k1 _ (by ext; simp [ht])
  · rw [dif_neg ht]; exact k2 _ _ (by ext; simp; omega)

lemma gprob_cons (Q : ℕ → S → S → ℝ) (k : ℕ) (x y : S) {n : ℕ} (q : Fin n → S) :
    gprob Q k x (Fin.cons y q : Fin (n + 1) → S) = Q k x y * gprob Q (k + 1) y q := by
  unfold gprob
  rw [Fin.prod_univ_succ]
  simp only [gst_zero, gst_succ, Fin.val_zero, Fin.val_succ, Fin.cons_zero, Fin.cons_succ,
    add_zero]
  congr 1
  refine Finset.prod_congr rfl (fun t _ => ?_)
  rw [show k + (t.val + 1) = k + 1 + t.val by omega]

lemma grew_cons (r : ℕ → S → ℝ) (k : ℕ) (x y : S) {n : ℕ} (q : Fin n → S) :
    grew r k x (Fin.cons y q : Fin (n + 1) → S) = r k x + grew r (k + 1) y q := by
  unfold grew
  rw [Fin.sum_univ_succ]
  simp only [gst_zero, gst_succ, Fin.val_zero, Fin.val_succ, add_zero]
  congr 1
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [show k + (t.val + 1) = k + 1 + t.val by omega]

lemma gvs_cons (Q : ℕ → S → S → ℝ) (W : ℕ → S → ℝ) (k : ℕ) (x y : S) {n : ℕ}
    (q : Fin n → S) :
    gvs Q W k x (Fin.cons y q : Fin (n + 1) → S) = gvar Q W k x + gvs Q W (k + 1) y q := by
  unfold gvs
  rw [Fin.sum_univ_succ]
  simp only [gst_zero, gst_succ, Fin.val_zero, Fin.val_succ, add_zero]
  congr 1
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [show k + (t.val + 1) = k + 1 + t.val by omega]

lemma gexp_succ (Q : ℕ → S → S → ℝ) (k : ℕ) (x : S) (n : ℕ)
    (f : (Fin (n + 1) → S) → ℝ) :
    gexp Q k x (n + 1) f =
      ∑ y, Q k x y * gexp Q (k + 1) y n (fun q => f (Fin.cons y q)) := by
  unfold gexp
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => S)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  change gprob Q k x (Fin.cons y q : Fin (n + 1) → S) * f (Fin.cons y q) = _
  rw [gprob_cons]; ring

lemma gexp_zero (Q : ℕ → S → S → ℝ) (k : ℕ) (x : S) (f : (Fin 0 → S) → ℝ) :
    gexp Q k x 0 f = f Fin.elim0 := by
  unfold gexp gprob
  simp [Subsingleton.elim _ (Fin.elim0 : Fin 0 → S)]

lemma gexp_add (Q : ℕ → S → S → ℝ) (k : ℕ) (x : S) (n : ℕ)
    (f g : (Fin n → S) → ℝ) :
    gexp Q k x n (fun p => f p + g p) = gexp Q k x n f + gexp Q k x n g := by
  unfold gexp; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma gexp_const_mul (Q : ℕ → S → S → ℝ) (k : ℕ) (x : S) (n : ℕ) (c : ℝ)
    (f : (Fin n → S) → ℝ) :
    gexp Q k x n (fun p => c * f p) = c * gexp Q k x n f := by
  unfold gexp; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma gexp_one (Q : ℕ → S → S → ℝ) (hQ : ∀ j s, ∑ y, Q j s y = 1) :
    ∀ (n k : ℕ) (x : S), gexp Q k x n (fun _ => 1) = 1 := by
  intro n
  induction n with
  | zero => intro k x; simp [gexp_zero]
  | succ n ih =>
    intro k x
    rw [gexp_succ]
    simp only [ih, mul_one]
    exact hQ k x

lemma gexp_const (Q : ℕ → S → S → ℝ) (hQ : ∀ j s, ∑ y, Q j s y = 1)
    (n k : ℕ) (x : S) (c : ℝ) : gexp Q k x n (fun _ => c) = c := by
  have := gexp_const_mul Q k x n c (fun _ => 1)
  simp only [mul_one] at this
  rw [this, gexp_one Q hQ]; ring

theorem main (Q : ℕ → S → S → ℝ) (r : ℕ → S → ℝ) (W : ℕ → S → ℝ)
    (hQ : ∀ j s, ∑ y, Q j s y = 1)
    (hW : ∀ j s, W j s = r j s + ∑ y, Q j s y * W (j + 1) y) :
    ∀ (n k : ℕ), (∀ s, W (k + n) s = 0) → ∀ x : S,
      gexp Q k x n (fun p => grew r k x p) = W k x ∧
      gexp Q k x n (fun p => grew r k x p ^ 2) - W k x ^ 2 =
        gexp Q k x n (fun p => gvs Q W k x p) := by
  intro n
  induction n with
  | zero =>
    intro k hT x
    have hk : W k x = 0 := by simpa using hT x
    simp [gexp_zero, grew, gvs, hk]
  | succ n ih =>
    intro k hT x
    have hT' : ∀ s, W (k + 1 + n) s = 0 := by
      intro s; rw [show k + 1 + n = k + (n + 1) by omega]; exact hT s
    have IH := fun y => ih (k + 1) hT' y
    rw [gexp_succ, gexp_succ, gexp_succ]
    simp only [grew_cons, gvs_cons]
    have e1 : ∀ y, gexp Q (k + 1) y n (fun q => r k x + grew r (k + 1) y q) =
        r k x + W (k + 1) y := by
      intro y
      rw [gexp_add, gexp_const Q hQ, (IH y).1]
    have e2 : ∀ y, gexp Q (k + 1) y n (fun q => (r k x + grew r (k + 1) y q) ^ 2) =
        r k x ^ 2 + 2 * r k x * W (k + 1) y + gexp Q (k + 1) y n (fun q => grew r (k + 1) y q ^ 2) := by
      intro y
      have : (fun q : Fin n → S => (r k x + grew r (k + 1) y q) ^ 2) =
          (fun q : Fin n → S => (r k x ^ 2 + (2 * r k x) * grew r (k + 1) y q) + grew r (k + 1) y q ^ 2) := by
        funext q; ring
      rw [this, gexp_add, gexp_add, gexp_const Q hQ, gexp_const_mul, (IH y).1]
    have e3 : ∀ y, gexp Q (k + 1) y n (fun q => gvar Q W k x + gvs Q W (k + 1) y q) =
        gvar Q W k x + (gexp Q (k + 1) y n (fun q => grew r (k + 1) y q ^ 2) - W (k + 1) y ^ 2) := by
      intro y
      rw [gexp_add, gexp_const Q hQ, (IH y).2]
    simp only [e1, e2, e3]
    have hWk := hW k x
    have hq := hQ k x
    refine ⟨?_, ?_⟩
    · rw [hWk]
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hq, one_mul]
    · rw [hWk]
      unfold gvar
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, hq, one_mul]
      have a1 : ∑ y, Q k x y * (2 * r k x * W (k + 1) y) =
          2 * r k x * ∑ y, Q k x y * W (k + 1) y := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [a1]
      ring

end TVEp

open MinimaxRegretRL.Bernstein in
theorem solution {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty S] [Nonempty A] (M : MinimaxRegretRL.Hoeffding.MDP S A) (H : ℕ)
    (π : MinimaxRegretRL.Hoeffding.Policy S A H) (h : Fin H) (x : S) :
    pathExp M π h x (pathVarianceSum M π h x) =
      pathVar M π h x (pathReward M π h x) := by
  set Q : ℕ → S → S → ℝ := fun j s y =>
    if hj : j < H then M.P s (π s ⟨j, hj⟩) y else M.P s (Classical.arbitrary A) y with hQdef
  set r : ℕ → S → ℝ := fun j s => if hj : j < H then M.R s (π s ⟨j, hj⟩) else 0 with hrdef
  set W : ℕ → S → ℝ := fun j s => valueAt M π j s with hWdef
  have hQ : ∀ j s, ∑ y, Q j s y = 1 := by
    intro j s
    simp only [hQdef]
    split_ifs
    · exact (M.kernel s _).2
    · exact (M.kernel s _).2
  have hW : ∀ j s, W j s = r j s + ∑ y, Q j s y * W (j + 1) y := by
    intro j s
    simp only [hWdef, hrdef, hQdef]
    rw [valueAt]
    by_cases hj : j < H
    · simp only [hj, dite_true]
    · have h0 : ∀ y, valueAt M π (j + 1) y = 0 := by
        intro y; rw [valueAt]; simp only [show ¬ (j + 1 < H) by omega, dite_false]
      simp [hj, h0]
  have hT : ∀ s, W (h.val + (H - h.val)) s = 0 := by
    intro s
    simp only [hWdef]
    rw [valueAt]; simp only [show ¬ (h.val + (H - h.val) < H) by omega, dite_false]
  have hE : ∀ f : Path S H h → ℝ,
      pathExp M π h x f = TVEp.gexp Q h.val x (H - h.val) f := by
    intro f
    unfold pathExp TVEp.gexp
    refine Finset.sum_congr rfl (fun p _ => ?_)
    congr 1
    unfold pathProb TVEp.gprob
    refine Finset.prod_congr rfl (fun t _ => ?_)
    have ht : h.val + t.val < H := by omega
    simp only [hQdef, ht, dite_true]
    rfl
  have hR : pathReward M π h x = fun p => TVEp.grew r h.val x p := by
    funext p
    unfold pathReward TVEp.grew
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have ht : h.val + t.val < H := by omega
    simp only [hrdef, ht, dite_true]
    rfl
  have hV : pathVarianceSum M π h x = fun p => TVEp.gvs Q W h.val x p := by
    funext p
    unfold pathVarianceSum TVEp.gvs
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have ht : h.val + t.val < H := by omega
    unfold transitionVar finiteVar finiteExp TVEp.gvar
    simp only [hQdef, hWdef, ht, dite_true]
    rfl
  have key := TVEp.main Q r W hQ hW (H - h.val) h.val hT x
  rw [hV, hE, ← key.2]
  unfold pathVar
  rw [hR, hE, hE, key.1]
