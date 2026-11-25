-- Prove2me | solution 1 for John.one_sub_le_norm_det_one_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:08:58.052773+00:00
-- url     : https://prove2.me/submissions/9ab446ae-c27f-4bf4-993f-0320ad8d0294

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
public import Theorems.Thm_LinearMap_det_eq_prod_of_apply_eq_smul
public import Theorems.Thm_one_sub_two_mul_sum_sq_le_prod_one_add

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
    (hHsa : IsSelfAdjoint H)
    (htr : LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
      (H : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) = 0)
    {t : ℝ} (ht0 : 0 < t) (htH : t * ‖H‖ ≤ 1 / 2) :
    1 - 2 * (t ^ 2 * ((k : ℝ) * ‖H‖ ^ 2))
      ≤ ‖(ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k))
          + ((t : ℝ) : 𝕜) • H).det‖ := by
  classical
  set T : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
    ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)) + ((t : ℝ) : 𝕜) • H with hT
  -- eigenvalues of `H`
  have hsym : (H : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hHsa
  have hn : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin k)) = k := finrank_euclideanSpace_fin
  set lam : Fin k → ℝ := hsym.eigenvalues hn with hlam
  set b : OrthonormalBasis (Fin k) 𝕜 (EuclideanSpace 𝕜 (Fin k)) :=
    hsym.eigenvectorBasis hn with hb
  have hbnorm : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have hbeig : ∀ i, H (b i) = ((lam i : ℝ) : 𝕜) • b i := fun i => by
    have h := hsym.apply_eigenvectorBasis hn i
    rw [hlam, hb]
    exact h
  have hsum0 : ∑ i, lam i = 0 := by
    have h := hsym.trace_eq_sum_eigenvalues hn
    rw [htr] at h
    exact_mod_cast h.symm
  have hlam_le : ∀ i, |lam i| ≤ ‖H‖ := fun i => by
    have h1 : ‖H (b i)‖ = |lam i| := by
      rw [hbeig i, norm_smul, RCLike.norm_ofReal, hbnorm i, mul_one]
    calc |lam i| = ‖H (b i)‖ := h1.symm
      _ ≤ ‖H‖ * ‖b i‖ := H.le_opNorm _
      _ = ‖H‖ := by rw [hbnorm i, mul_one]
  have hlam_half : ∀ i, |t * lam i| ≤ 1 / 2 := fun i => by
    rw [abs_mul, abs_of_pos ht0]
    calc t * |lam i| ≤ t * ‖H‖ := mul_le_mul_of_nonneg_left (hlam_le i) ht0.le
      _ ≤ 1 / 2 := htH
  have hfac_pos : ∀ i, 0 < 1 + t * lam i := fun i => by
    have h := abs_le.mp (hlam_half i)
    linarith [h.1]
  -- `det (id + tH) = ∏ (1 + tλᵢ)` in the eigenbasis
  have hTeig : ∀ i, T (b i) = ((1 + t * lam i : ℝ) : 𝕜) • b i := fun i => by
    rw [hT, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, hbeig i, smul_smul, RCLike.ofReal_add,
      RCLike.ofReal_one, RCLike.ofReal_mul, add_smul, one_smul]
  have hdetT : T.det = ∏ i, ((1 + t * lam i : ℝ) : 𝕜) := by
    have h := LinearMap.det_eq_prod_of_apply_eq_smul b.toBasis
      (T : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))
      (fun i => ((1 + t * lam i : ℝ) : 𝕜))
      (fun i => by simpa [OrthonormalBasis.coe_toBasis] using hTeig i)
    simpa [ContinuousLinearMap.det] using h
  -- the product bound, with `∑λᵢ² ≤ k‖H‖²`
  have hprod : 1 - 2 * (t ^ 2 * ((k : ℝ) * ‖H‖ ^ 2)) ≤ ∏ i, (1 + t * lam i) := by
    have h := one_sub_two_mul_sum_sq_le_prod_one_add Finset.univ (fun i => t * lam i)
      (fun i _ => hlam_half i) (by rw [← Finset.mul_sum, hsum0, mul_zero])
    have hΛle : ∑ i, (t * lam i) ^ 2 ≤ t ^ 2 * ((k : ℝ) * ‖H‖ ^ 2) := by
      calc ∑ i, (t * lam i) ^ 2 ≤ ∑ _i : Fin k, t ^ 2 * ‖H‖ ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h2 : lam i ^ 2 ≤ ‖H‖ ^ 2 := by
              rw [← sq_abs (lam i)]
              exact pow_le_pow_left₀ (abs_nonneg _) (hlam_le i) 2
            nlinarith [sq_nonneg t]
        _ = t ^ 2 * ((k : ℝ) * ‖H‖ ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    linarith [h]
  rw [hdetT, norm_prod]
  calc 1 - 2 * (t ^ 2 * ((k : ℝ) * ‖H‖ ^ 2)) ≤ ∏ i, (1 + t * lam i) := hprod
    _ = ∏ i, ‖((1 + t * lam i : ℝ) : 𝕜)‖ := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [RCLike.norm_ofReal, abs_of_pos (hfac_pos i)]
end John
