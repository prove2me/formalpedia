-- Prove2me | solution 1 for MasulloRH.primePowerTraceTerm_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:18:57.286843+00:00
-- url     : https://prove2.me/submissions/eccf5a6a-1785-40d4-a4ee-bb9de7094cab

import Mathlib
import Definitions.Def_MasulloRH_RationalTrace
open MasulloRH Set MeasureTheory
private theorem support_bounds (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    ∃ M : ℝ, ∀ x : ℝ, M < x → φ x = 0 ∧ φ x⁻¹ = 0 := by
  have hK : IsCompact (tsupport φ) := hφ.2.1
  obtain ⟨A, hA⟩ := hK.bddAbove
  have hi : ContinuousOn (fun x : ℝ => x⁻¹) (tsupport φ) :=
    continuousOn_id.inv₀ (fun x hx => (hφ.2.2.1 hx : 0 < x).ne')
  obtain ⟨D, hD⟩ := hK.bddAbove_image hi
  refine ⟨max A D, fun x hx => ⟨?_, ?_⟩⟩
  · by_contra hn
    exact (not_lt_of_ge (hA (subset_tsupport φ hn))) ((le_max_left A D).trans_lt hx)
  · by_contra hn
    have hb := hD ⟨x⁻¹, subset_tsupport φ hn, rfl⟩
    simp only [inv_inv] at hb
    exact (not_lt_of_ge hb) ((le_max_right A D).trans_lt hx)

theorem solution (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    (Function.support (primePowerTraceTerm φ)).Finite := by
  obtain ⟨M, hM⟩ := support_bounds φ hφ
  obtain ⟨N, hN⟩ := exists_nat_gt M
  let j (i : Nat.Primes × ℕ) : ℕ × ℕ := (i.1.val, i.2)
  have hj : Function.Injective j := by
    intro a b h
    have h₁ := congrArg (Prod.fst : ℕ × ℕ → ℕ) h
    have h₂ := congrArg (Prod.snd : ℕ × ℕ → ℕ) h
    exact Prod.ext (Subtype.ext h₁) h₂
  refine (((finite_Iic N).prod (finite_Iic N)).preimage hj.injOn).subset ?_
  intro i hi
  let q : ℕ := i.1.val ^ (i.2 + 1)
  have hq : q ≤ N := by
    by_contra! h
    have hcast : M < (q : ℝ) := hN.trans (by exact_mod_cast h)
    obtain ⟨h₁,h₂⟩ := hM q hcast
    apply hi
    simpa [primePowerTraceTerm, q, Nat.cast_pow] using
      (show ((Real.log i.1.val / Real.sqrt (q : ℝ) : ℝ) : ℂ) * (φ q + φ (q : ℝ)⁻¹) = 0 by rw [h₁,h₂]; simp)
  have hp : 1 < i.1.val := i.1.property.one_lt
  change i.1.val ≤ N ∧ i.2 ≤ N
  constructor
  · exact (le_self_pow₀ hp.le (Nat.succ_ne_zero _)).trans hq
  · have he : i.2 + 1 < q := Nat.lt_pow_self hp
    omega
