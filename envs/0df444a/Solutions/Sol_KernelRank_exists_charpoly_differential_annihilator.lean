-- Prove2me | solution 1 for KernelRank.exists_charpoly_differential_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:39:04.098345+00:00
-- url     : https://prove2.me/submissions/ec76e862-6535-4ea3-9af8-45b451bab3c7

import Definitions.Def_KernelRankLean_TranslationSemigroup
import Definitions.Def_KernelRankLean_Differential
import Theorems.Thm_KernelRank_differentialOperator_congr
import Theorems.Thm_KernelRank_differentialOperator_operatorOrbit
import Theorems.Thm_KernelRank_exists_translation_generator
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_profile_of_generator
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open Polynomial NNReal
open KernelRank
attribute [local instance] translateNormedAddCommGroup translateNormedSpace
  translateUniformSpace translateCompleteSpace
namespace KernelRank
theorem _root_.solution (ψ : ℝ → ℂ)
    [FiniteDimensional ℂ (translateSpan ψ)] (hψ : ContinuousOn ψ (Set.Ici 0)) :
    ∃ q : ℂ[X], q.Monic ∧ q.natDegree = Module.finrank ℂ (translateSpan ψ) ∧
      ∀ t, 0 ≤ t → differentialOperator q ψ t = 0 := by
  obtain ⟨A, hA⟩ := exists_translation_generator ψ hψ
  let q := A.toLinearMap.charpoly
  have hzero : aeval A q = 0 := by
    change aeval ((Module.End.toContinuousLinearMap (translateSpan ψ)) A.toLinearMap) q = 0
    rw [aeval_algHom_apply, LinearMap.aeval_self_charpoly, map_zero]
  let v := initialProfile ψ
  let β := evalW ψ 0
  have heq : Set.EqOn ψ (operatorOrbit A v β) (Set.Ici 0) :=
    fun _ ht => profile_of_generator ψ A hA ht
  refine ⟨q, A.toLinearMap.charpoly_monic, A.toLinearMap.charpoly_natDegree, ?_⟩
  intro t ht
  rw [differentialOperator_congr q heq ht,
    differentialOperator_operatorOrbit A v β q ht, hzero]
  simp [operatorOrbit]
end KernelRank
