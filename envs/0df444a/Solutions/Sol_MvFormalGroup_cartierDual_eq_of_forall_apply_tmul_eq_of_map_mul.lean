-- Prove2me | solution 1 for MvFormalGroup.cartierDual_eq_of_forall_apply_tmul_eq_of_map_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d983eebf-241d-5415-a512-0ad1898f3737

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_cartierDual_eq_of_forall_apply_tmul_eq_of_map_mul

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u v

namespace DerivUniq

variable {R : Type u} [CommRing R] {d : ℕ}

private noncomputable def quot (G : MvPowerSeries (Fin d) R) (j : Fin d) : MvPowerSeries (Fin d) R :=
  fun n => if (n + Finsupp.single j 1).support.min'
      ⟨j, by rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same]; omega⟩ = j
    then coeff (n + Finsupp.single j 1) G else 0

private theorem coeff_quot (G : MvPowerSeries (Fin d) R) (j : Fin d) (n : Fin d →₀ ℕ) :
    coeff n (quot G j) = if (n + Finsupp.single j 1).support.min'
      ⟨j, by rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same]; omega⟩ = j
    then coeff (n + Finsupp.single j 1) G else 0 := rfl

private theorem eq_C_add_sum_X_mul_quot (G : MvPowerSeries (Fin d) R) :
    G = C (constantCoeff G) + ∑ j : Fin d, X j * quot G j := by
  classical
  ext m
  rw [map_add, map_sum, coeff_C]
  have hterm : ∀ j : Fin d, coeff m (X j * quot G j) =
      if h : m j ≠ 0 then (if m.support.min' ⟨j, Finsupp.mem_support_iff.mpr h⟩ = j
        then coeff m G else 0) else 0 := by
    intro j
    rw [X_def, coeff_monomial_mul, one_mul]
    by_cases hj : m j ≠ 0
    · have hle : Finsupp.single j 1 ≤ m := by
        rw [Finsupp.single_le_iff]; omega
      rw [if_pos hle, dif_pos hj, coeff_quot]
      have heq : m - Finsupp.single j 1 + Finsupp.single j 1 = m := tsub_add_cancel_of_le hle
      simp only [heq]
    · rw [if_neg, dif_neg hj]
      intro hle
      apply hj
      have := hle j
      rw [Finsupp.single_eq_same] at this
      omega
  simp only [hterm]
  by_cases hm : m = 0
  · subst hm
    rw [if_pos rfl, coeff_zero_eq_constantCoeff_apply]
    simp
  · rw [if_neg hm, zero_add]
    have hne : m.support.Nonempty := by
      rw [Finsupp.support_nonempty_iff]; exact hm
    set j₀ := m.support.min' hne with hj₀
    have hj₀mem : m j₀ ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ _)
    rw [Finset.sum_eq_single j₀]
    · rw [dif_pos hj₀mem, if_pos rfl]
    · intro j _ hj
      by_cases h : m j ≠ 0
      · rw [dif_pos h, if_neg]
        intro h'
        exact hj h'.symm
      · rw [dif_neg h]
    · intro h
      exact absurd (Finset.mem_univ _) h

end DerivUniq

open DerivUniq in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
    {d : ℕ} (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R] [Module.Free 𝓞 R] [Module.Finite 𝓞 R]
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R) (hπ : Function.Surjective π)
    (hε : ∀ j, Coalgebra.counit (R := ZMod p) ((1 : ZMod p) ⊗ₜ[𝓞] π (X j)) = 0)
    (δ δ' : CartierDual (ZMod p) (ZMod p ⊗[𝓞] R))
    (hδ : ∀ a b : ZMod p ⊗[𝓞] R, δ (a * b) =
      δ a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * δ b)
    (hδ' : ∀ a b : ZMod p ⊗[𝓞] R, δ' (a * b) =
      δ' a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * δ' b)
    (h : ∀ j, δ ((1 : ZMod p) ⊗ₜ[𝓞] π (X j)) = δ' ((1 : ZMod p) ⊗ₜ[𝓞] π (X j))) :
    δ = δ' := by
  classical

  have hone : ∀ (D : CartierDual (ZMod p) (ZMod p ⊗[𝓞] R)),
      (∀ a b : ZMod p ⊗[𝓞] R, D (a * b) =
        D a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * D b) →
      D 1 = 0 := by
    intro D hD
    have h1 := hD 1 1
    rw [mul_one, Bialgebra.counit_one, mul_one, one_mul] at h1
    linear_combination -h1

  have key : ∀ G : MvPowerSeries (Fin d) 𝓞,
      δ ((1 : ZMod p) ⊗ₜ[𝓞] π G) = δ' ((1 : ZMod p) ⊗ₜ[𝓞] π G) := by
    intro G
    rw [DerivUniq.eq_C_add_sum_X_mul_quot G, map_add, map_sum, TensorProduct.tmul_add,
      TensorProduct.tmul_sum, map_add, map_add, map_sum, map_sum]
    congr 1
    ·
      have hC : π (C (constantCoeff G)) = algebraMap 𝓞 R (constantCoeff G) := by
        rw [← π.commutes]
        rfl
      have hc : ((1 : ZMod p) ⊗ₜ[𝓞] π (C (constantCoeff G)) : ZMod p ⊗[𝓞] R) =
          algebraMap 𝓞 (ZMod p) (constantCoeff G) • (1 : ZMod p ⊗[𝓞] R) := by
        rw [hC, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, algebraMap_smul,
          ← Algebra.TensorProduct.one_def]
      rw [hc, map_smul, map_smul, hone δ hδ, hone δ' hδ']
    · refine Finset.sum_congr rfl fun j _ => ?_
      have hsplit : ((1 : ZMod p) ⊗ₜ[𝓞] π (X j * DerivUniq.quot G j) : ZMod p ⊗[𝓞] R) =
          ((1 : ZMod p) ⊗ₜ[𝓞] π (X j)) * ((1 : ZMod p) ⊗ₜ[𝓞] π (DerivUniq.quot G j)) := by
        rw [map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rw [hsplit, hδ, hδ', hε, zero_mul, zero_mul, add_zero, add_zero, h]

  apply CartierDual.ext
  intro b
  induction b using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c r =>
    obtain ⟨G, rfl⟩ := hπ r
    have hs : (c ⊗ₜ[𝓞] π G : ZMod p ⊗[𝓞] R) = c • ((1 : ZMod p) ⊗ₜ[𝓞] π G) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hs, map_smul, map_smul, key]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end S_MvFormalGroup_cartierDual_eq_of_forall_apply_tmul_eq_of_map_mul
end P2MW
export P2MW.S_MvFormalGroup_cartierDual_eq_of_forall_apply_tmul_eq_of_map_mul (solution)
