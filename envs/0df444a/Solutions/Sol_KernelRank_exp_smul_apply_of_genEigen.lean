-- Prove2me | solution 1 for KernelRank.exp_smul_apply_of_genEigen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:34:29.207798+00:00
-- url     : https://prove2.me/submissions/5deca206-d5bc-4c2d-8359-e3ed25f67d90

import Definitions.Def_KernelRankLean_TranslationSemigroup
import Definitions.Def_KernelRankLean_Representation
import Definitions.Def_KernelRankLean_Necessity
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
attribute [local instance] translateNormedAddCommGroup translateNormedSpace
  translateUniformSpace translateCompleteSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
namespace KernelRank
theorem _root_.solution (A : E →L[ℂ] E) (μ : ℂ) {v : E} {k : ℕ}
    (hv : ((A.toLinearMap - μ • 1) ^ k) v = 0) (t : ℂ) :
    NormedSpace.exp (t • A) v = ∑ m ∈ Finset.range k,
      (Complex.exp (μ * t) * ((m.factorial : ℂ)⁻¹ * t ^ m)) • ((A - μ • 1) ^ m) v := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ _
  let N := A - μ • (1 : E →L[ℂ] E)
  let L := ContinuousLinearMap.apply ℂ E v
  have hv' : (N ^ k) v = 0 := by
    change (N ^ k).toLinearMap v = 0
    simpa only [N, ContinuousLinearMap.toLinearMap_pow, ContinuousLinearMap.toLinearMap_sub,
      ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one] using hv
  have hsplit : t • A = algebraMap ℂ (E →L[ℂ] E) (μ * t) + t • N := by
    simp only [N, Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul]
    rw [mul_comm t μ]
    abel
  -- The exponential series of the nilpotent part stops after `k` terms.
  have hseries := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (t • N)).map
    L.toLinearMap.toAddMonoidHom L.continuous
  have hterm : ∀ m, L ((m.factorial⁻¹ : ℂ) • (t • N) ^ m) =
      ((m.factorial : ℂ)⁻¹ * t ^ m) • (N ^ m) v := by
    intro m
    change (((m.factorial⁻¹ : ℂ) • (t • N) ^ m) v) = _
    simp [_root_.smul_pow, smul_smul]
  have hfin : HasSum (fun m => L
      ((m.factorial⁻¹ : ℂ) • (t • N) ^ m))
      (∑ m ∈ Finset.range k, ((m.factorial : ℂ)⁻¹ * t ^ m) • (N ^ m) v) := by
    simp only [hterm]
    refine hasSum_sum_of_ne_finset_zero fun m hm => ?_
    rw [Finset.mem_range, not_lt] at hm
    have hzero : (N ^ m) v = 0 := by
      rw [← Nat.sub_add_cancel hm, pow_add, mul_apply_eq_comp, hv', map_zero]
    rw [hzero, smul_zero]
  have hexpN := hseries.unique hfin
  rw [hsplit, NormedSpace.exp_add_of_commute (Algebra.commutes _ _),
    ← NormedSpace.algebraMap_exp_comm, Algebra.algebraMap_eq_smul_one,
    mul_apply_eq_comp, smul_apply, one_apply_eq_self, ← Complex.exp_eq_exp_ℂ]
  change Complex.exp (μ * t) • L (NormedSpace.exp (t • N)) = _
  refine (congrArg (Complex.exp (μ * t) • ·) hexpN).trans ?_
  rw [Finset.smul_sum]
  simp only [smul_smul, N]
end KernelRank
