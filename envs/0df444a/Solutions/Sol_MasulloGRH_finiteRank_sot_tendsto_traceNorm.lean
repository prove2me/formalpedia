-- Prove2me | solution 1 for MasulloGRH.finiteRank_sot_tendsto_traceNorm
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:59:59.857185+00:00
-- url     : https://prove2.me/submissions/6e08dcf9-80ab-4893-ac4c-e30628551d91

import Theorems.Thm_MasulloGRH_traceNorm_le_nuclear_series

set_option autoImplicit false
set_option linter.unusedVariables false

open MasulloGRH Filter Topology

namespace FiniteRankTraceAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The trace norm is nonnegative. -/
theorem traceNorm_nonneg (S : H →L[ℂ] H) : 0 ≤ traceNorm S := by
  unfold traceNorm operatorTrace
  have hpos : (0 : H →L[ℂ] H) ≤ operatorAbs S := CFC.sqrt_nonneg _
  have hterm : ∀ i, 0 ≤ (inner ℂ (chosenHilbertBasis H i)
      (operatorAbs S (chosenHilbertBasis H i))).re := by
    intro i
    have h1 := (ContinuousLinearMap.nonneg_iff_isPositive _).1 hpos
    exact h1.re_inner_nonneg_right _
  by_cases hs : Summable fun i => inner ℂ (chosenHilbertBasis H i)
      (operatorAbs S (chosenHilbertBasis H i))
  · rw [Complex.re_tsum hs]
    exact tsum_nonneg hterm
  · rw [tsum_eq_zero_of_not_summable hs]
    simp

end FiniteRankTraceAux

open FiniteRankTraceAux in
theorem solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (F : H →L[ℂ] H)
    (hF : FiniteDimensional ℂ (LinearMap.range (F : H →ₗ[ℂ] H)))
    {ι : Type*} (l : Filter ι) (P : ι → H →L[ℂ] H)
    (hP : ∀ u : H, Filter.Tendsto (fun i => P i u) l (nhds 0)) :
    Filter.Tendsto (fun i => traceNorm (P i ∘L F)) l (nhds 0) := by
  -- an orthonormal basis of the finite-dimensional range of `F`
  let V : Submodule ℂ H := LinearMap.range (F : H →ₗ[ℂ] H)
  have : FiniteDimensional ℂ V := hF
  obtain ⟨n, hn⟩ : ∃ n, n = Module.finrank ℂ V := ⟨_, rfl⟩
  let b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V := stdOrthonormalBasis ℂ V
  -- the sequences of the finite nuclear representation, padded by zeros
  let x : ℕ → H := fun m => if h : m < Module.finrank ℂ V then
    ContinuousLinearMap.adjoint F (b ⟨m, h⟩ : H) else 0
  let y : ℕ → H := fun m => if h : m < Module.finrank ℂ V then (b ⟨m, h⟩ : H) else 0
  have hx0 : ∀ m, ¬ m < Module.finrank ℂ V → x m = 0 := fun m hm => dif_neg hm
  have hy0 : ∀ m, ¬ m < Module.finrank ℂ V → y m = 0 := fun m hm => dif_neg hm
  -- `F u = ∑_{m < n} ⟨u, x m⟩ y m`
  have hFu : ∀ u : H, F u = ∑ m ∈ Finset.range (Module.finrank ℂ V), inner ℂ (x m) u • y m := by
    intro u
    have hmem : F u ∈ V := ⟨u, rfl⟩
    have h1 := b.sum_repr' ⟨F u, hmem⟩
    have h2 : ((∑ k, inner ℂ (b k) (⟨F u, hmem⟩ : V) • b k : V) : H) = F u :=
      congrArg (Subtype.val : V → H) h1
    rw [Finset.sum_range fun m => inner ℂ (x m) u • y m]
    rw [← h2, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hxk : x (k : ℕ) = ContinuousLinearMap.adjoint F (b k : H) := by
      change (if h : (k : ℕ) < Module.finrank ℂ V then
        ContinuousLinearMap.adjoint F (b ⟨(k : ℕ), h⟩ : H) else 0) = _
      rw [dif_pos k.2]
    have hyk : y (k : ℕ) = (b k : H) := by
      change (if h : (k : ℕ) < Module.finrank ℂ V then (b ⟨(k : ℕ), h⟩ : H) else 0) = _
      rw [dif_pos k.2]
    rw [hxk, hyk, ContinuousLinearMap.adjoint_inner_left, Submodule.coe_smul]
    rfl
  -- the trace-norm bound
  have hbound : ∀ i, traceNorm (P i ∘L F) ≤
      ∑ m ∈ Finset.range (Module.finrank ℂ V), ‖x m‖ * ‖P i (y m)‖ := by
    intro i
    have hzero : ∀ m, m ∉ Finset.range (Module.finrank ℂ V) → ‖x m‖ * ‖P i (y m)‖ = 0 := by
      intro m hm
      rw [hx0 m (by simpa using hm)]
      simp
    have hs : Summable fun m => ‖x m‖ * ‖(fun m => P i (y m)) m‖ :=
      summable_of_ne_finset_zero hzero
    have hxy : ∀ u : H, HasSum (fun m => inner ℂ (x m) u • (fun m => P i (y m)) m)
        ((P i ∘L F) u) := by
      intro u
      rw [ContinuousLinearMap.comp_apply, hFu u, map_sum]
      have h1 : ∀ m ∈ Finset.range (Module.finrank ℂ V),
          P i (inner ℂ (x m) u • y m) = inner ℂ (x m) u • P i (y m) := fun m _ => map_smul _ _ _
      rw [Finset.sum_congr rfl h1]
      refine hasSum_sum_of_ne_finset_zero fun m hm => ?_
      rw [hx0 m (by simpa using hm)]
      simp
    have h2 := traceNorm_le_nuclear_series (P i ∘L F) x (fun m => P i (y m)) hs hxy
    rw [tsum_eq_sum hzero] at h2
    exact h2
  -- the bound tends to zero
  have hlim : Tendsto (fun i => ∑ m ∈ Finset.range (Module.finrank ℂ V), ‖x m‖ * ‖P i (y m)‖)
      l (𝓝 0) := by
    have h1 : ∀ m ∈ Finset.range (Module.finrank ℂ V),
        Tendsto (fun i => ‖x m‖ * ‖P i (y m)‖) l (𝓝 (‖x m‖ * 0)) := fun m _ => by
      have h2 := (hP (y m)).norm
      rw [norm_zero] at h2
      exact h2.const_mul _
    have h3 := tendsto_finsetSum _ h1
    simpa using h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun i => traceNorm_nonneg _) hbound
