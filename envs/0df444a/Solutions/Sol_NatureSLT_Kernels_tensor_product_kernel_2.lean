-- Prove2me | solution 2 for NatureSLT.Kernels.tensor_product_kernel
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:53:24.127862+00:00
-- url     : https://prove2.me/submissions/56db95de-5134-45df-a752-d32296dfdc27

import Mathlib
set_option autoImplicit false

theorem solution {X ι : Type*} (b : ι → X → ℝ)
    (hb : ∀ s t : X, Summable (fun i : ι => b i s * b i t)) (n : ℕ) (x y : Fin n → X) :
    Summable (fun I : Fin n → ι => (∏ k, b (I k) (x k)) * (∏ k, b (I k) (y k))) ∧
      ∑' I : Fin n → ι, (∏ k, b (I k) (x k)) * (∏ k, b (I k) (y k)) =
        ∏ k, ∑' i : ι, b i (x k) * b i (y k) := by
  have gen : ∀ (m : ℕ) (g : Fin m → ι → ℝ), (∀ k, Summable (fun i => ‖g k i‖)) →
      Summable (fun I : Fin m → ι => ‖∏ k, g k (I k)‖) ∧
        ∑' I : Fin m → ι, ∏ k, g k (I k) = ∏ k, ∑' i, g k i := by
    intro m
    induction m with
    | zero =>
      intro g hg
      refine ⟨(hasSum_fintype _).summable, ?_⟩
      simp
    | succ m ih =>
      intro g hg
      obtain ⟨hGs, hGt⟩ := ih (fun i => g i.succ) (fun k => hg k.succ)
      set e : (Fin (m + 1) → ι) ≃ ι × (Fin m → ι) := (Fin.consEquiv (fun _ : Fin (m + 1) => ι)).symm with he
      have hF : ∀ I : Fin (m + 1) → ι, ∏ k, g k (I k)
          = g 0 (e I).1 * ∏ i : Fin m, g i.succ ((e I).2 i) := by
        intro I
        rw [Fin.prod_univ_succ]
        rfl
      have hnorm : Summable (fun p : ι × (Fin m → ι) =>
          ‖g 0 p.1 * ∏ i : Fin m, g i.succ (p.2 i)‖) :=
        Summable.mul_norm (f := g 0) (g := fun J : Fin m → ι => ∏ i : Fin m, g i.succ (J i)) (hg 0) hGs
      constructor
      · have : Summable (fun I : Fin (m + 1) → ι =>
            ‖g 0 (e I).1 * ∏ i : Fin m, g i.succ ((e I).2 i)‖) := (e.summable_iff).mpr hnorm
        simpa [hF] using this
      · have h1 : ∑' I : Fin (m + 1) → ι, ∏ k, g k (I k)
            = ∑' p : ι × (Fin m → ι), g 0 p.1 * ∏ i : Fin m, g i.succ (p.2 i) := by
          rw [← e.tsum_eq]
          apply tsum_congr
          intro I
          exact hF _
        rw [h1, ← tsum_mul_tsum_of_summable_norm (hg 0) hGs, hGt, Fin.prod_univ_succ]
  have hg : ∀ k, Summable (fun i => ‖b i (x k) * b i (y k)‖) := fun k => (hb (x k) (y k)).abs
  obtain ⟨h1, h2⟩ := gen n (fun k i => b i (x k) * b i (y k)) hg
  have e : ∀ I : Fin n → ι, (∏ k, b (I k) (x k)) * (∏ k, b (I k) (y k))
      = ∏ k, (b (I k) (x k) * b (I k) (y k)) := by
    intro I; rw [Finset.prod_mul_distrib]
  simp only [e]
  exact ⟨h1.of_norm, h2⟩
