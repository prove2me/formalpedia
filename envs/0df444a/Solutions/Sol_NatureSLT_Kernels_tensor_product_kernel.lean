-- Prove2me | solution 1 for NatureSLT.Kernels.tensor_product_kernel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:34:25.32453+00:00
-- url     : https://prove2.me/submissions/906f846e-3136-4f8e-a5f8-16bf6fc54013

import Mathlib

theorem g69f_sm {ι κ : Type*} (f : ι → ℝ) (g : κ → ℝ) (hn1 : Summable fun i => ‖f i‖)
    (hn2 : Summable fun J => ‖g J‖) :
    Summable (fun p : ι × κ => f p.1 * g p.2) := summable_mul_of_summable_norm hn1 hn2

theorem g69f_tm {ι κ : Type*} (f : ι → ℝ) (g : κ → ℝ) (hn1 : Summable fun i => ‖f i‖)
    (hn2 : Summable fun J => ‖g J‖) :
    ∑' p : ι × κ, f p.1 * g p.2 = (∑' i, f i) * ∑' j, g j :=
  (tsum_mul_tsum_of_summable_norm hn1 hn2).symm

theorem g69f_pi_prod {ι : Type*} (n : ℕ) : ∀ (g : Fin n → ι → ℝ), (∀ k, Summable (g k)) →
    Summable (fun I : Fin n → ι => ∏ k, g k (I k)) ∧
      ∑' I : Fin n → ι, ∏ k, g k (I k) = ∏ k, ∑' i, g k i := by
  induction n with
  | zero =>
    intro g _
    refine ⟨Summable.of_finite, ?_⟩
    simp
  | succ n ih0 =>
    intro g hg
    have ih := ih0 (fun k => g k.succ) (fun k => hg k.succ)
    have ihabs := ih0 (fun k i => |g k.succ i|) (fun k => (hg k.succ).abs)
    generalize hG : (fun J : Fin n → ι => ∏ k, g k.succ (J k)) = G
    have hGJ : ∀ J, G J = ∏ k, g k.succ (J k) := fun J => by rw [← hG]
    have hn1 : Summable fun i => ‖g 0 i‖ := by
      simpa [Real.norm_eq_abs] using (hg 0).abs
    have hn2 : Summable fun J : Fin n → ι => ‖G J‖ := by
      simp only [hGJ]
      simpa [Real.norm_eq_abs, Finset.abs_prod] using ihabs.1
    have hcomp : ∀ p : ι × (Fin n → ι),
        (∏ k, g k (Fin.consEquiv (fun _ : Fin (n + 1) => ι) p k)) = g 0 p.1 * G p.2 := by
      intro p; rw [hGJ]; simp [Fin.prod_univ_succ]
    have hsum : Summable (fun p : ι × (Fin n → ι) =>
        ∏ k, g k (Fin.consEquiv (fun _ : Fin (n + 1) => ι) p k)) := by
      simp only [hcomp]; exact g69f_sm _ _ hn1 hn2
    refine ⟨(Fin.consEquiv (fun _ : Fin (n + 1) => ι)).summable_iff.mp hsum, ?_⟩
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ι)).tsum_eq]
    simp only [hcomp]
    rw [g69f_tm _ _ hn1 hn2, Fin.prod_univ_succ]
    congr 1
    rw [← ih.2]
    simp only [hGJ]

theorem solution {X ι : Type*} (b : ι → X → ℝ)
    (hb : ∀ s t : X, Summable (fun i : ι => b i s * b i t)) (n : ℕ) (x y : Fin n → X) :
    Summable (fun I : Fin n → ι => (∏ k, b (I k) (x k)) * (∏ k, b (I k) (y k))) ∧
      ∑' I : Fin n → ι, (∏ k, b (I k) (x k)) * (∏ k, b (I k) (y k)) =
        ∏ k, ∑' i : ι, b i (x k) * b i (y k) := by
  simp_rw [← Finset.prod_mul_distrib]
  exact g69f_pi_prod n (fun k i => b i (x k) * b i (y k)) (fun k => hb (x k) (y k))
