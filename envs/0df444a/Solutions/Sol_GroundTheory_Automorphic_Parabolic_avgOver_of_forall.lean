-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:45:56.369581+00:00
-- url     : https://prove2.me/submissions/ad6b0fba-1e80-45d6-b970-3e1be8c2d7f0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgSub_eq_sum
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_avgSub

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
theorem _root_.solution (h : ∀ k ∈ K, ∀ y, f (y * k) = f y) : avgOver K f = f := by
  classical
  have hle : (⊤ : Subgroup K) ≤ (rightStab f).subgroupOf K := fun k _ => h k k.2
  have hi : (⊤ : Subgroup K).index ≠ 0 := by rw [Subgroup.index_top]; exact one_ne_zero
  have : (⊤ : Subgroup K).FiniteIndex := ⟨hi⟩
  let _ := Fintype.ofFinite (K ⧸ (⊤ : Subgroup K))
  funext x
  rw [avgOver_eq_avgSub hle hi, avgSub_eq_sum]
  have hterm : ∀ q : K ⧸ (⊤ : Subgroup K), f (x * ((Quotient.out q : K) : G)) = f x :=
    fun q => h _ (Quotient.out q).2 x
  rw [Fintype.sum_congr _ _ hterm, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, ← Subgroup.index, Subgroup.index_top, one_smul, Nat.cast_one,
    inv_one, one_smul]
end GroundTheory.Automorphic.Parabolic
