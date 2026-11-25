-- Prove2me | solution 1 for John.norm_sum_weight_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:10:20.069062+00:00
-- url     : https://prove2.me/submissions/03d57cbb-ec91-4199-944c-78340cdcca00

module
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_CompactConvexHull
public import Definitions.Def_BasicResults_JohnIngredients
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Seminorm
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BasicResults_John
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_John_sum_weight_inner_sq
attribute [local simp] John.rankOneSA_apply

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped InnerProductSpace ComplexConjugate
open RCLike (re)
open John
variable {𝕜 : Type u} [RCLike 𝕜] {k : ℕ}
namespace John
theorem _root_.solution {N : ℕ} (c : Fin N → ℝ)
    (u : Fin N → EuclideanSpace 𝕜 (Fin k))
    (hdec : ∀ x, ∑ i, ((c i : 𝕜) * ⟪u i, x⟫_𝕜) • u i = x)
    (hc : ∀ i, 0 ≤ c i) (a : Fin N → 𝕜) :
    ‖∑ i, ((c i : 𝕜) * a i) • u i‖ ≤ Real.sqrt (∑ i, c i * ‖a i‖ ^ 2) := by
  set w := ∑ i, ((c i : 𝕜) * a i) • u i with hw
  have hB : 0 ≤ ∑ i, c i * ‖a i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (sq_nonneg _)
  -- `‖w‖² = re ⟪w, w⟫ ≤ ∑ᵢ cᵢ ‖aᵢ‖ ‖⟪uᵢ, w⟫‖`.
  have hww : ‖w‖ ^ 2 ≤ ∑ i, c i * (‖a i‖ * ‖⟪u i, w⟫_𝕜‖) := by
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜) w]
    nth_rewrite 1 [hw]
    rw [sum_inner, map_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [inner_smul_left, map_mul (starRingEnd 𝕜), RCLike.conj_ofReal, mul_assoc,
      RCLike.re_ofReal_mul]
    refine mul_le_mul_of_nonneg_left ?_ (hc i)
    calc re (conj (a i) * ⟪u i, w⟫_𝕜) ≤ ‖conj (a i) * ⟪u i, w⟫_𝕜‖ := RCLike.re_le_norm _
      _ = ‖a i‖ * ‖⟪u i, w⟫_𝕜‖ := by rw [norm_mul, RCLike.norm_conj]
  -- Weighted Cauchy–Schwarz on the reals, then `∑ᵢ cᵢ ‖⟪uᵢ,w⟫‖² = ‖w‖²`.
  have hCS : (∑ i, c i * (‖a i‖ * ‖⟪u i, w⟫_𝕜‖)) ^ 2
      ≤ (∑ i, c i * ‖a i‖ ^ 2) * (∑ i, c i * ‖⟪u i, w⟫_𝕜‖ ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => Real.sqrt (c i) * ‖a i‖) (fun i => Real.sqrt (c i) * ‖⟪u i, w⟫_𝕜‖)
    have e1 : ∀ i, Real.sqrt (c i) * ‖a i‖ * (Real.sqrt (c i) * ‖⟪u i, w⟫_𝕜‖)
        = c i * (‖a i‖ * ‖⟪u i, w⟫_𝕜‖) := fun i => by
      rw [mul_mul_mul_comm, Real.mul_self_sqrt (hc i)]
    have e2 : ∀ i, (Real.sqrt (c i) * ‖a i‖) ^ 2 = c i * ‖a i‖ ^ 2 := fun i => by
      rw [mul_pow, Real.sq_sqrt (hc i)]
    have e3 : ∀ i, (Real.sqrt (c i) * ‖⟪u i, w⟫_𝕜‖) ^ 2 = c i * ‖⟪u i, w⟫_𝕜‖ ^ 2 := fun i => by
      rw [mul_pow, Real.sq_sqrt (hc i)]
    simpa only [e1, e2, e3] using h
  rw [sum_weight_inner_sq c u hdec w] at hCS
  rcases eq_or_lt_of_le (norm_nonneg w) with h0 | hpos
  · rw [← h0]; exact Real.sqrt_nonneg _
  · have ht : (0 : ℝ) < ‖w‖ ^ 2 := by positivity
    have hle : ‖w‖ ^ 2 ≤ ∑ i, c i * ‖a i‖ ^ 2 := by
      refine le_of_mul_le_mul_right ?_ ht
      calc ‖w‖ ^ 2 * ‖w‖ ^ 2 = (‖w‖ ^ 2) ^ 2 := (pow_two _).symm
        _ ≤ (∑ i, c i * (‖a i‖ * ‖⟪u i, w⟫_𝕜‖)) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity) hww
        _ ≤ (∑ i, c i * ‖a i‖ ^ 2) * ‖w‖ ^ 2 := hCS
    calc ‖w‖ = Real.sqrt (‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
      _ ≤ Real.sqrt (∑ i, c i * ‖a i‖ ^ 2) := Real.sqrt_le_sqrt hle
end John
