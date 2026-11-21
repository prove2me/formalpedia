-- Prove2me | solution 1 for MasulloGRH.operatorTrace_of_nuclear_series
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:06:35.980177+00:00
-- url     : https://prove2.me/submissions/7283d53b-eb06-404c-b240-8cfde32ad14b

import Definitions.Def_MasulloGRH_HilbertNuclear

set_option autoImplicit false

open MasulloGRH Filter Topology

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (x y : ℕ → H) (hs : Summable (fun m => ‖x m‖ * ‖y m‖))
    (hxy : ∀ u : H, HasSum (fun m => inner ℂ (x m) u • y m) (T u)) :
    operatorTrace T = ∑' m, inner ℂ (x m) (y m) := by
  let ι := (exists_hilbertBasis ℂ H).choose
  let e : HilbertBasis ι ℂ H := chosenHilbertBasis H
  let a (m : ℕ) (i : ι) := inner ℂ (x m) (e i) * inner ℂ (e i) (y m)
  -- Cauchy–Schwarz bounds the absolute sum of each row by its nuclear cost.
  have hrow (m : ℕ) : (Summable fun i => ‖a m i‖) ∧ ∑' i, ‖a m i‖ ≤ ‖x m‖ * ‖y m‖ := by
    have htwo : (2 : ENNReal).toReal.HolderConjugate (2 : ENNReal).toReal := by
      rw [Real.holderConjugate_iff]
      norm_num
    have habs (i : ι) : ‖a m i‖ = ‖e.repr (x m) i‖ * ‖e.repr (y m) i‖ := by
      simp only [a, norm_mul, e.repr_apply_apply]
      rw [norm_inner_symm (𝕜 := ℂ) (x m) (e i)]
    simpa only [habs, e.repr.norm_map] using lp.tsum_mul_le_mul_norm htwo (e.repr (x m)) (e.repr (y m))
  have hsumNorm : Summable (fun z : ℕ × ι => ‖a z.1 z.2‖) := by
    apply (summable_prod_of_nonneg (fun z => norm_nonneg (a z.1 z.2))).mpr
    exact ⟨fun m => (hrow m).1, Summable.of_nonneg_of_le
      (fun m => tsum_nonneg fun i => norm_nonneg (a m i)) (fun m => (hrow m).2) hs⟩
  have habs : Summable (Function.uncurry a) := hsumNorm.of_norm
  have hdiag (i : ι) : inner ℂ (e i) (T (e i)) = ∑' m, a m i := by
    have h := (hxy (e i)).mapL (innerSL ℂ (e i))
    simpa only [a, innerSL_apply_apply, inner_smul_right] using h.tsum_eq.symm
  unfold operatorTrace
  change (∑' i, inner ℂ (e i) (T (e i))) = ∑' m, inner ℂ (x m) (y m)
  calc
    _ = ∑' i, ∑' m, a m i := tsum_congr hdiag
    _ = ∑' m, ∑' i, a m i := habs.tsum_comm
    _ = _ := tsum_congr fun m => e.tsum_inner_mul_inner (x m) (y m)
