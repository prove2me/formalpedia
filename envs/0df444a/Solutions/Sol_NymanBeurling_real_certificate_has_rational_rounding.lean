-- Prove2me | solution 1 for NymanBeurling.real_certificate_has_rational_rounding
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T00:52:41.651351+00:00
-- url     : https://prove2.me/submissions/44634bce-e7b4-47ae-b585-82f8993ebc93

import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem solution
    (N H : ℕ) (b : Fin N → ℝ) (η : ℝ)
    (h : (∑ n ∈ Finset.range H,
      (1 - ∑ k : Fin N, b k * (((n+1) % (k.val+2) : ℕ) : ℝ) / (k.val+2 : ℝ))^2 /
        ((n+1 : ℝ)*(n+2 : ℝ))) + (1 + ∑ k : Fin N, |b k|)^2/(H+1) < η) :
    ∃ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N ∧
      (((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
        (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ) : ℝ) < η := by
  classical
  let F : (Fin N → ℝ) → ℝ := fun x =>
    (∑ n ∈ Finset.range H,
      (1 - ∑ k : Fin N, x k * (((n+1) % (k.val+2) : ℕ) : ℝ) / (k.val+2 : ℝ))^2 /
        ((n+1 : ℝ)*(n+2 : ℝ))) + (1 + ∑ k : Fin N, |x k|)^2/(H+1)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hd : DenseRange (fun q : Fin N → ℚ => fun k => (q k : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨q, hq⟩ := hd.exists_mem_open
    (isOpen_lt hF continuous_const) ⟨b, h⟩
  let d : Fin N →₀ ℚ := Finsupp.equivFunOnFinite.symm q
  let emb : Fin N ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let c : ℕ →₀ ℚ := d.embDomain emb
  have hsupp : c.support ⊆ Finset.range N := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hk
    exact Finset.mem_range.mpr i.isLt
  have hsum (g : ℕ → ℚ → ℚ) (hg : ∀ k, g k 0 = 0) :
      (∑ k ∈ c.support, g k (c k)) = ∑ i : Fin N, g i.val (q i) := by
    change c.sum g = _
    rw [Finsupp.sum_embDomain]
    exact Finsupp.sum_fintype _ _ (fun i => hg i.val)
  refine ⟨c, hsupp, ?_⟩
  have habs := hsum (fun _ t => |t|) (fun _ => abs_zero)
  have hres (n : ℕ) := hsum
    (fun k t => t * (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))
    (fun _ => by simp)
  simp_rw [habs, hres]
  push_cast
  exact hq
