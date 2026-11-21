-- Prove2me | solution 2 for MasulloRH.primePowerTraceTerm_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-20T22:19:25.015196+00:00
-- url     : https://prove2.me/submissions/e4897cec-33d1-4cda-879f-f1ff28dbd13d

import Definitions.Def_MasulloRH_RationalTrace
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
open MeasureTheory Set Filter
open MasulloRH

private theorem tail_zero {φ : ℝ → ℂ} (h : IsRationalTraceTest φ) :
    ∃ R : ℝ, ∀ t ≥ R, φ t = 0 ∧ φ t⁻¹ = 0 := by
  have h0 : (0:ℝ) ∉ tsupport φ := fun ht => (lt_irrefl (0 : ℝ)) (h.2.2.1 ht)
  have ht : φ =ᶠ[atTop] 0 :=
    (hasCompactSupport_iff_eventuallyEq.mp h.2.1).filter_mono (by rw [Filter.coclosedCompact_eq_cocompact]; exact atTop_le_cocompact)
  exact eventually_atTop.mp (ht.and (tendsto_inv_atTop_zero.eventually
    (notMem_tsupport_iff_eventuallyEq.mp h0)))

theorem solution (φ : ℝ → ℂ) (h : IsRationalTraceTest φ) :
    (Function.support (primePowerTraceTerm φ)).Finite := by
  obtain ⟨R, hR⟩ := tail_zero h
  obtain ⟨N, hN⟩ := exists_nat_gt R
  let q (i : Nat.Primes × ℕ) : ℕ := Nat.Primes.prodNatEquiv i
  have hi : Function.Injective q := Subtype.val_injective.comp Nat.Primes.prodNatEquiv.injective
  apply ((Set.finite_Iio N).preimage hi.injOn).subset
  rintro ⟨p,k⟩ ht
  change (p:ℕ)^(k+1) < N
  by_contra! hge
  have hh := hR ((p:ℕ)^(k+1):ℝ) (hN.le.trans (by exact_mod_cast hge))
  exact ht (by simp [primePowerTraceTerm, hh.1, hh.2])

