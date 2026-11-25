-- Prove2me | solution 1 for NeuralCollapseUFM.critical_point_balance
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T14:45:32.259338+00:00
-- url     : https://prove2.me/submissions/16620acd-d6e6-464b-8e50-7a2b184396d9

import Mathlib
import Definitions.Def_NeuralCollapseUFM_Basic

open Matrix Filter Topology
namespace NeuralCollapseUFM

lemma cp_ce_diff {K n : ℕ} (hK : 2 ≤ K) (Z C : Matrix (Fin K) (Fin K × Fin n) ℝ) :
    DifferentiableAt ℝ (fun s : ℝ => ceRisk (Z - s • C)) 0 := by
  have hne : ∀ (s : ℝ) (c : Fin K × Fin n), 0 < ∑ l, Real.exp ((Z - s • C) l c) := by
    intro s c
    have : (Finset.univ : Finset (Fin K)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    exact Finset.sum_pos (fun _ _ => Real.exp_pos _) this
  unfold ceRisk ceLoss
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  refine DifferentiableAt.const_mul (DifferentiableAt.fun_sum fun k _ => DifferentiableAt.fun_sum fun i _ => ?_) _
  refine DifferentiableAt.neg (DifferentiableAt.log ?_ ?_)
  · refine DifferentiableAt.div (by fun_prop) (by fun_prop) ?_
    have := hne 0 (k, i); simpa using this.ne'
  · have := hne 0 (k, i)
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this
    exact (div_pos (Real.exp_pos _) this).ne'

lemma cp_frob {m p : Type*} [Fintype m] [Fintype p] (A B : Matrix m p ℝ) :
    HasDerivAt (fun t : ℝ => frobSq (A + t • B)) (∑ i, ∑ j, 2 * A i j * B i j) 0 := by
  unfold frobSq
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  have h : HasDerivAt (fun t : ℝ => A i j + t * B i j) (B i j) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (B i j)).const_add (A i j)
  have e : (fun t : ℝ => (A i j + t * B i j) ^ 2) = fun t => (A i j + t * B i j) * (A i j + t * B i j) := by
    funext t; ring
  rw [e]
  exact (h.mul h).congr_deriv (by ring)


lemma cp_key {K d n : ℕ} (hK : 2 ≤ K) (lamW lamH lamb : ℝ)
    (x : Params K d n) (hx : IsCriticalPoint (objective lamW lamH lamb) x)
    (S : Matrix (Fin d) (Fin d) ℝ) :
    lamW / 2 * (∑ i, ∑ j, 2 * x.1 i j * (x.1 * S) i j) +
      lamH / 2 * (∑ i, ∑ j, 2 * x.2.1 i j * (-(S * x.2.1)) i j) = 0 := by
  obtain ⟨W, H, b⟩ := x
  set φ : ℝ → ℝ := fun s => ceRisk (logits W H b - s • (W * S * (S * H))) with hφ
  have hfun : (fun t : ℝ => objective lamW lamH lamb ((W, H, b) + t • ((W * S, -(S * H), 0) : Params K d n))) =
      fun t => φ (t ^ 2) + lamW / 2 * frobSq (W + t • (W * S)) +
        lamH / 2 * frobSq (H + t • (-(S * H))) + lamb / 2 * sqNorm b := by
    funext t
    have hL : logits (W + t • (W * S)) (H + t • -(S * H)) b = logits W H b - t ^ 2 • (W * S * (S * H)) := by
      unfold logits
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_neg,
        Matrix.neg_mul, Matrix.mul_assoc]
      module
    simp only [objective, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_zero,
      add_zero, hφ]
    rw [hL]
  have h1 := hx ((W * S, -(S * H), 0) : Params K d n)
  rw [hfun] at h1
  have hd : DifferentiableAt ℝ φ 0 := cp_ce_diff hK _ _
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
    simpa using hasDerivAt_pow 2 (0:ℝ)
  have hcomp : HasDerivAt (fun t : ℝ => φ (t ^ 2)) (deriv φ 0 * 0) 0 := by
    have : HasDerivAt φ (deriv φ 0) ((0:ℝ) ^ 2) := by
      rw [show (0:ℝ) ^ 2 = 0 by norm_num]; exact hd.hasDerivAt
    exact HasDerivAt.comp (h₂ := φ) (h := fun t : ℝ => t ^ 2) (0:ℝ) this hsq
  have h2 := ((hcomp.add ((cp_frob W (W * S)).const_mul (lamW / 2))).add
    ((cp_frob H (-(S * H))).const_mul (lamH / 2))).add_const (lamb / 2 * sqNorm b)
  have := h1.unique h2
  simp only [mul_zero, zero_add] at this
  simpa using this.symm

theorem critical_point_balance {K d n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n)
    (lamW lamH lamb : ℝ) (hW : 0 < lamW) (hH : 0 < lamH) (hb : 0 < lamb)
    (x : Params K d n) (hx : IsCriticalPoint (objective lamW lamH lamb) x) :
    x.1ᵀ * x.1 = (lamH / lamW) • (x.2.1 * x.2.1ᵀ) ∧
      frobSq x.1 = lamH / lamW * frobSq x.2.1 := by
  have entry : ∀ i j, (x.1ᵀ * x.1) i j = ((lamH / lamW) • (x.2.1 * x.2.1ᵀ)) i j := by
    intro i j
    have := cp_key hK lamW lamH lamb x hx (Matrix.single j i 1)
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    have e1 : ∑ a, 2 * x.1 a i * x.1 a j = 2 * ∑ a, x.1 a i * x.1 a j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    have e2 : ∑ c, 2 * x.2.1 j c * x.2.1 i c = 2 * ∑ c, x.2.1 i c * x.2.1 j c := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, e2] at this
    field_simp
    linarith
  refine ⟨Matrix.ext entry, ?_⟩
  have diag : ∀ j, ∑ a, x.1 a j ^ 2 = lamH / lamW * ∑ c, x.2.1 j c ^ 2 := by
    intro j
    have := entry j j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] at this
    simpa [sq] using this
  unfold frobSq
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => diag j

end NeuralCollapseUFM
open NeuralCollapseUFM in
theorem solution {K d n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n)
    (lamW lamH lamb : ℝ) (hW : 0 < lamW) (hH : 0 < lamH) (hb : 0 < lamb)
    (x : Params K d n) (hx : IsCriticalPoint (objective lamW lamH lamb) x) :
    x.1ᵀ * x.1 = (lamH / lamW) • (x.2.1 * x.2.1ᵀ) ∧
      frobSq x.1 = lamH / lamW * frobSq x.2.1 :=
  critical_point_balance hK hn lamW lamH lamb hW hH hb x hx
