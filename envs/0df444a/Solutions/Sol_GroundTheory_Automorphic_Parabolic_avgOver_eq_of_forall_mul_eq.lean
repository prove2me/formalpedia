-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_eq_of_forall_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:30.241889+00:00
-- url     : https://prove2.me/submissions/aca4c143-1f07-4d89-94e4-55f95c847469

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCount
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_sum


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
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {K : Subgroup G} {f : G → W} (hf : AvgFinite K f) {x : G}
    {c : W} (hc : ∀ k ∈ K, f (x * k) = c) : avgOver K f x = c := by
  classical
  have : ((rightStab f).subgroupOf K).FiniteIndex := ⟨hf⟩
  let _ := Fintype.ofFinite (K ⧸ (rightStab f).subgroupOf K)
  rw [avgOver_eq_sum]
  have hterm : ∀ q : K ⧸ (rightStab f).subgroupOf K, f (x * ((Quotient.out q : K) : G)) = c :=
    fun q => hc _ (Quotient.out q).2
  rw [Fintype.sum_congr _ _ hterm, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hcard : (Fintype.card (K ⧸ (rightStab f).subgroupOf K) : ℂ) =
      (rightStab f).relIndex K := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  rw [hcard, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hf), one_smul]
end GroundTheory.Automorphic.Parabolic
