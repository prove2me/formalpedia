-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.sub_avgOver_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:57:53.096012+00:00
-- url     : https://prove2.me/submissions/6e911eb8-4518-4807-a1bf-fc72d264e75e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_sum_translates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Set
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
  {K : Subgroup G} {f : G → W}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hf : AvgFinite K f) :
    f - avgOver K f ∈ Submodule.span ℂ {g | ∃ k ∈ K, g = (fun y => f (y * k)) - f} := by
  classical
  have : ((rightStab f).subgroupOf K).FiniteIndex := ⟨hf⟩
  let _ := Fintype.ofFinite (K ⧸ (rightStab f).subgroupOf K)
  have hI : (((rightStab f).relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hf
  have hcard : Fintype.card (K ⧸ (rightStab f).subgroupOf K) = (rightStab f).relIndex K := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  have key : f - avgOver K f = -((((rightStab f).relIndex K : ℂ)⁻¹) •
      ∑ q : K ⧸ (rightStab f).subgroupOf K,
        ((fun y => f (y * ((Quotient.out q : K) : G))) - f)) := by
    rw [avgOver_eq_sum_translates, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      hcard, ← Nat.cast_smul_eq_nsmul ℂ, smul_sub, smul_smul, inv_mul_cancel₀ hI, one_smul,
      neg_sub]
  rw [key]
  refine Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_))
  exact Submodule.subset_span ⟨_, (Quotient.out q).2, rfl⟩
end GroundTheory.Automorphic.Parabolic
