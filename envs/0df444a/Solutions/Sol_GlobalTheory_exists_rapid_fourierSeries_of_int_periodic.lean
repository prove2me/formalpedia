-- Prove2me | solution 1 for GlobalTheory.exists_rapid_fourierSeries_of_int_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:57:50.771796+00:00
-- url     : https://prove2.me/submissions/18cf37a2-9559-4c66-81f4-eda0b8af08d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRapidFourierSeriesOfIntPeriodic
import Theorems.Thm_GlobalTheory_exists_bound_of_lattice_periodic
import Theorems.Thm_GlobalTheory_latticeFourier_of_contDiff
import Theorems.Thm_GlobalTheory_mem_innerDual_iff
import Theorems.Thm_GlobalTheory_pow_mul_norm_latticeFourierCoeff_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Matrix
open scoped ContDiff BigOperators Real RealInnerProductSpace
namespace GlobalTheory
private theorem mem_intLattice_iff {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis) ↔
      ∃ ν : Fin n → ℤ, x = WithLp.toLp 2 fun k => (ν k : ℝ) := by
  rw [Module.Basis.mem_span_iff_repr_mem]
  constructor
  · intro h
    choose ν hν using h
    refine ⟨ν, ?_⟩
    ext k
    simpa using (hν k).symm
  · rintro ⟨ν, rfl⟩ i
    exact ⟨ν i, by simp⟩
private theorem mem_intLattice_dual_iff {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n)))
      (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)) ↔
      ∃ ν : Fin n → ℤ, x = WithLp.toLp 2 fun k => (ν k : ℝ) := by
  rw [mem_innerDual_iff]
  constructor
  · intro h
    choose m hm using fun k => h ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis k)
      (Submodule.subset_span ⟨k, rfl⟩)
    refine ⟨m, ?_⟩
    ext k
    simpa [EuclideanSpace.inner_single_right] using (hm k).symm
  · rintro ⟨ν, rfl⟩ y hy
    obtain ⟨μ, rfl⟩ := (mem_intLattice_iff y).1 hy
    exact ⟨∑ k, μ k * ν k, by simp [PiLp.inner_apply]⟩
end GlobalTheory
end

set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real RealInnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (n : ℕ) (w : (Fin n → ℝ) → ℂ), ContDiff ℝ ∞ w →
      (∀ (ν : Fin n → ℤ) x, w (x + fun k => (ν k : ℝ)) = w x) →
      ∃ c : (Fin n → ℤ) → ℂ, (∀ N : ℕ, ∃ C : ℝ, ∀ ν, ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N ≤ C) ∧
        ∀ x, w x = ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) := by
  intro n w hw hper
  set L : Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
    Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis) with hL
  set A : EuclideanSpace ℝ (Fin n) → ℂ := fun y => w y.ofLp with hAdef
  have hA : ContDiff ℝ ∞ A := hw.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff
  have hAp : ∀ x ∈ L, Function.Periodic A x := fun x hx y => by
    obtain ⟨ν, rfl⟩ := (mem_intLattice_iff x).1 hx
    exact hper ν y.ofLp
  let v : (Fin n → ℤ) → EuclideanSpace ℝ (Fin n) := fun ν => WithLp.toLp 2 fun k => (ν k : ℝ)
  have hv : ∀ ν, v ν ∈ LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n))) L :=
    fun ν => (mem_intLattice_dual_iff _).2 ⟨ν, rfl⟩
  let φ : (Fin n → ℤ) ≃
      LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n))) L :=
    Equiv.ofBijective (fun ν => ⟨v ν, hv ν⟩) ⟨fun ν μ h => by
      funext k
      have := congrArg (fun z => (z.1 : EuclideanSpace ℝ (Fin n)).ofLp k) h
      simpa [v] using this, fun z => by
      obtain ⟨ν, hν⟩ := (mem_intLattice_dual_iff z.1).1 z.2
      exact ⟨ν, Subtype.ext hν.symm⟩⟩
  have hbd : ∀ k : ℕ, ∃ M, ∀ ν, (4 * ‖v ν‖) ^ k * ‖latticeFourierCoeff L A (v ν)‖ ≤ M := by
    intro k
    have hAk : ContDiff ℝ k A := hA.of_le (by exact_mod_cast le_top)
    obtain ⟨M, hM⟩ := exists_bound_of_lattice_periodic (L := L) (f := iteratedFDeriv ℝ k A)
      (fun x hx b ↦ by
        rw [← iteratedFDeriv_comp_add_right, show (fun z ↦ A (z + x)) = A from funext (hAp x hx)])
      (hAk.continuous_iteratedFDeriv le_rfl)
    exact ⟨M, fun ν => pow_mul_norm_latticeFourierCoeff_le hAp hAk hM (hv ν)⟩
  refine ⟨fun ν => latticeFourierCoeff L A (v ν), fun N => ?_, fun x => ?_⟩
  · obtain ⟨M₀, h₀⟩ := hbd 0
    obtain ⟨M, hM⟩ := hbd N
    refine ⟨2 ^ (N - 1) * (M₀ + n ^ N * M), fun ν => ?_⟩
    have hS0 : 0 ≤ ∑ k, |(ν k : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hS : ∑ k, |(ν k : ℝ)| ≤ n * (4 * ‖v ν‖) := by
      calc ∑ k, |(ν k : ℝ)| ≤ ∑ _k : Fin n, 4 * ‖v ν‖ := by
            refine Finset.sum_le_sum fun k _ => ?_
            have h1 : ‖(v ν).ofLp k‖ ≤ ‖v ν‖ := PiLp.norm_apply_le _ _
            have h2 : ‖(v ν).ofLp k‖ = |(ν k : ℝ)| := rfl
            linarith [norm_nonneg (v ν)]
        _ = _ := by simp
    have h1 := add_pow_le zero_le_one hS0 N
    have h2 : (∑ k, |(ν k : ℝ)|) ^ N ≤ n ^ N * (4 * ‖v ν‖) ^ N := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hS0 hS N
    have h3 := h₀ ν
    have h4 := mul_le_mul_of_nonneg_left (hM ν) (show (0 : ℝ) ≤ n ^ N by positivity)
    rw [pow_zero, one_mul] at h3
    rw [one_pow] at h1
    set c := ‖latticeFourierCoeff L A (v ν)‖
    have hc : 0 ≤ c := norm_nonneg _
    calc c * (1 + ∑ k, |(ν k : ℝ)|) ^ N
        ≤ c * (2 ^ (N - 1) * (1 + n ^ N * (4 * ‖v ν‖) ^ N)) := by
          refine mul_le_mul_of_nonneg_left (h1.trans ?_) hc
          gcongr
      _ = 2 ^ (N - 1) * (c + n ^ N * ((4 * ‖v ν‖) ^ N * c)) := by ring
      _ ≤ _ := by gcongr
  · have h := (latticeFourier_of_contDiff (L := L) hA hAp).2.2.1 (WithLp.toLp 2 x)
    rw [← φ.hasSum_iff] at h
    refine h.tsum_eq.symm.trans (tsum_congr fun ν => ?_)
    change cexp (2 * π * I * ((⟪v ν, WithLp.toLp 2 x⟫ : ℝ) : ℂ)) •
      latticeFourierCoeff L A (v ν) = _
    rw [smul_eq_mul, mul_comm]
    congr 3
    simp [v, PiLp.inner_apply, mul_comm]
end GlobalTheory
