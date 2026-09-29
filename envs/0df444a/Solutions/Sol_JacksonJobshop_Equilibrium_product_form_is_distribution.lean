-- Prove2me | solution 1 for JacksonJobshop.Equilibrium.product_form_is_distribution
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:59:29.765338+00:00
-- url     : https://prove2.me/submissions/6ab14596-5b22-4993-811e-8ca4efc9c4ca

import Mathlib
import Definitions.Def_JacksonJobshop_Equilibrium_System

namespace JacksonJobshop.Equilibrium

theorem aux_pfd_lam_nonneg {N : ℕ} (sys : JobshopSystem N) (K : ℕ) : 0 ≤ sys.lam K := by
  rcases sys.lam_assumption with h | ⟨K₀, h1, h2⟩
  · exact (h K).le
  · by_cases hK : K ≤ K₀
    · exact (h1 K hK).le
    · rw [h2 K (by omega)]

theorem aux_pfd_W_nonneg {N : ℕ} (sys : JobshopSystem N) (K : ℕ) : 0 ≤ W sys K := by
  unfold W
  exact Finset.prod_nonneg (fun i _ => aux_pfd_lam_nonneg sys i)

theorem aux_pfd_w_nonneg {N : ℕ} (sys : JobshopSystem N) (k : Fin N → ℕ) : 0 ≤ w sys k := by
  unfold w
  refine Finset.prod_nonneg (fun n _ => Finset.prod_nonneg (fun i hi => ?_))
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  exact div_nonneg (sys.e_nonneg n) (sys.mu_pos n i (by omega)).le

theorem aux_pfd_hasSum {N : ℕ} (sys : JobshopSystem N)
    (hs : Summable (fun K => W sys K * T sys K)) :
    HasSum (fun k => w sys k * W sys (S k)) (∑' K, W sys K * T sys K) := by
  set f : (Fin N → ℕ) → ℝ := fun k => w sys k * W sys (S k) with hf
  let e := Finset.Nat.sigmaAntidiagonalTupleEquivTuple N
  have hfib : ∀ K : ℕ, HasSum (fun y : Finset.Nat.antidiagonalTuple N K => (f ∘ e) ⟨K, y⟩)
      (W sys K * T sys K) := by
    intro K
    have h1 : (fun y : Finset.Nat.antidiagonalTuple N K => (f ∘ e) ⟨K, y⟩) =
        fun y : Finset.Nat.antidiagonalTuple N K => W sys K * w sys (y : Fin N → ℕ) := by
      funext y
      have hy := Finset.Nat.mem_antidiagonalTuple.mp y.2
      simp only [Function.comp, hf, e, Finset.Nat.sigmaAntidiagonalTupleEquivTuple_apply, S, hy]
      rw [mul_comm]; rfl
    rw [h1, T, Finset.mul_sum]
    have h2 := hasSum_fintype (fun y : Finset.Nat.antidiagonalTuple N K => W sys K * w sys y)
    convert h2 using 1
    exact (Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple N K) _).symm
  have hnn : ∀ x, 0 ≤ (f ∘ e) x := fun x =>
    mul_nonneg (aux_pfd_w_nonneg sys _) (aux_pfd_W_nonneg sys _)
  have hsum : Summable (f ∘ e) := by
    rw [summable_sigma_of_nonneg hnn]
    refine ⟨fun K => (hfib K).summable, ?_⟩
    have : (fun K => ∑' y, (f ∘ e) ⟨K, y⟩) = fun K => W sys K * T sys K := by
      funext K; exact (hfib K).tsum_eq
    rw [this]; exact hs
  have h2 : HasSum (fun K => W sys K * T sys K) (∑' x, (f ∘ e) x) :=
    HasSum.sigma hsum.hasSum hfib
  have h3 : ∑' x, (f ∘ e) x = ∑' K, W sys K * T sys K := h2.tsum_eq.symm
  have h4 : HasSum (f ∘ e) (∑' K, W sys K * T sys K) := h3 ▸ hsum.hasSum
  exact (e.hasSum_iff).mp h4

end JacksonJobshop.Equilibrium

open JacksonJobshop.Equilibrium

theorem solution {N : ℕ} (sys : JobshopSystem N) (hπ : 0 < piConst sys) :
    (∀ k, 0 ≤ productForm sys k) ∧ HasSum (productForm sys) 1 := by
  have hs : Summable (fun K => W sys K * T sys K) := by
    by_contra h
    unfold piConst at hπ
    rw [if_neg h] at hπ
    exact lt_irrefl _ hπ
  have hpi : piConst sys = (∑' K, W sys K * T sys K)⁻¹ := by
    unfold piConst; rw [if_pos hs]
  have hS0 : 0 < ∑' K, W sys K * T sys K := by
    rw [hpi] at hπ; exact inv_pos.mp hπ
  refine ⟨fun k => ?_, ?_⟩
  · unfold productForm
    exact mul_nonneg (mul_nonneg hπ.le (aux_pfd_w_nonneg sys k)) (aux_pfd_W_nonneg sys _)
  · have h := (aux_pfd_hasSum sys hs).mul_left (piConst sys)
    rw [hpi, inv_mul_cancel₀ hS0.ne'] at h
    have : productForm sys = fun k => (∑' K, W sys K * T sys K)⁻¹ * (w sys k * W sys (S k)) := by
      funext k; unfold productForm; rw [hpi]; ring
    rw [this]; exact h
