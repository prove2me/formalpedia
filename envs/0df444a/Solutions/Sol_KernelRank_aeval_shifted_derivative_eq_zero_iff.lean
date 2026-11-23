-- Prove2me | solution 1 for KernelRank.aeval_shifted_derivative_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:38:12.807482+00:00
-- url     : https://prove2.me/submissions/6a0e1485-83fb-4a4f-afbc-063515f04dd3

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
import Theorems.Thm_KernelRank_aeval_derivative_eq_zero_iff
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution (q : ℂ[X]) {P : ℂ[X]} (hP : P ≠ 0) (μ : ℂ) :
    aeval ((derivative : Module.End ℂ ℂ[X]) + μ • 1) q P = 0 ↔
      (X - C μ) ^ (P.natDegree + 1) ∣ q := by
  have hshift :
      aeval ((derivative : Module.End ℂ ℂ[X]) + μ • 1) q =
        aeval (derivative : Module.End ℂ ℂ[X]) (taylor μ q) := by
    rw [taylor_apply, aeval_comp]
    simp [Algebra.algebraMap_eq_smul_one]
  rw [hshift, aeval_derivative_eq_zero_iff _ hP]
  constructor
  · intro h
    have h' := (taylorAlgHom (-μ)).map_dvd h
    change taylor (-μ) (X ^ (P.natDegree + 1)) ∣ taylor (-μ) (taylor μ q) at h'
    rw [taylor_taylor] at h'
    simpa [taylor_taylor, taylor_apply, sub_eq_add_neg] using h'
  · intro h
    have h' := (taylorAlgHom μ).map_dvd h
    simpa [taylor_apply] using h'
end KernelRank
