-- Prove2me | solution 1 for KernelRank.exists_sum_expPoly_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:36:52.255612+00:00
-- url     : https://prove2.me/submissions/b872a7e6-da86-4cab-9727-e83a45fb26f1

import Definitions.Def_KernelRankLean_TranslationSemigroup
import Definitions.Def_KernelRankLean_Representation
import Definitions.Def_KernelRankLean_Necessity
import Theorems.Thm_KernelRank_exp_smul_apply_of_genEigen
import Theorems.Thm_KernelRank_exists_translation_generator
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_profile_of_generator
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
theorem _root_.solution (ψ : ℝ → ℂ)
    [FiniteDimensional ℂ (translateSpan ψ)] (hψ : ContinuousOn ψ (Set.Ici 0)) :
    ∃ S : Finset ℂ, ∃ Q : ℂ → ℂ[X], ∀ t, 0 ≤ t → ψ t = ∑ μ ∈ S, expPoly (Q μ) μ t := by
  classical
  obtain ⟨A, hA⟩ := exists_translation_generator ψ hψ
  -- Split the starting vector into generalized eigenvectors.
  have hx : initialProfile ψ ∈ ⨆ μ, Module.End.maxGenEigenspace A.toLinearMap μ := by
    rw [Module.End.iSup_maxGenEigenspace_eq_top]
    trivial
  obtain ⟨f, hf, hfsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hx
  choose k hk using fun μ => (Module.End.mem_maxGenEigenspace _ _ _).mp (hf μ)
  let Q : ℂ → ℂ[X] := fun μ =>
    ∑ m ∈ Finset.range (k μ),
      C ((m.factorial : ℂ)⁻¹ * evalW ψ 0 (((A - μ • 1) ^ m) (f μ))) * X ^ m
  refine ⟨f.support, Q, fun t ht => ?_⟩
  rw [profile_of_generator ψ A hA ht, ← hfsum, Finsupp.sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [exp_smul_apply_of_genEigen A μ (hk μ)]
  simp only [Q, expPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    map_sum, map_smul, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring
end KernelRank
