-- Prove2me | solution 1 for John.norm_add_smul_le_of_inner_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:08:56.216376+00:00
-- url     : https://prove2.me/submissions/65c2e93e-f66e-4ff4-bc10-fac44971b70e

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
theorem _root_.solution
    {H : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)}
    {u : EuclideanSpace 𝕜 (Fin k)} (hu : ‖u‖ = 1) {t δ : ℝ} (ht0 : 0 < t)
    (h1 : t * ‖H‖ ^ 2 ≤ δ / 2) (h2 : t * δ ≤ 4)
    (hA : re ⟪u, H u⟫_𝕜 ≤ -(δ / 2)) :
    ‖u + ((t : ℝ) : 𝕜) • H u‖ ≤ 1 - t * δ / 4 := by
  have hHu : ‖H u‖ ≤ ‖H‖ := by simpa [hu] using H.le_opNorm u
  have hnorm : ‖u + ((t : ℝ) : 𝕜) • H u‖ ^ 2 ≤ 1 - t * δ / 2 := by
    rw [norm_add_sq (𝕜 := 𝕜), hu, inner_smul_right, norm_smul,
      RCLike.re_ofReal_mul, RCLike.norm_ofReal, abs_of_pos ht0]
    have e1 : t * re ⟪u, H u⟫_𝕜 ≤ t * (-(δ / 2)) := mul_le_mul_of_nonneg_left hA ht0.le
    have e2 : (t * ‖H u‖) ^ 2 ≤ (t * ‖H‖) ^ 2 := by
      have h3 : t * ‖H u‖ ≤ t * ‖H‖ := mul_le_mul_of_nonneg_left hHu ht0.le
      exact pow_le_pow_left₀ (by positivity) h3 2
    have e3 : (t * ‖H‖) ^ 2 ≤ t * (δ / 2) := by
      have h4 : (t * ‖H‖) ^ 2 = t * (t * ‖H‖ ^ 2) := by ring
      rw [h4]
      exact mul_le_mul_of_nonneg_left h1 ht0.le
    nlinarith [e1, e2, e3]
  have h3 : (0 : ℝ) ≤ 1 - t * δ / 4 := by linarith
  have h4 : ‖u + ((t : ℝ) : 𝕜) • H u‖ ^ 2 ≤ (1 - t * δ / 4) ^ 2 := by
    nlinarith [hnorm, sq_nonneg (t * δ)]
  exact le_of_sq_le_sq h4 h3
end John
