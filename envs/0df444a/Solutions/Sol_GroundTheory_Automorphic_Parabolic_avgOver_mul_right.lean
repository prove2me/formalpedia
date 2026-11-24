-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:46:37.604095+00:00
-- url     : https://prove2.me/submissions/f49e65e9-e7a1-4728-b6e3-2a418df7dbf0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgSub_eq_sum

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
variable {K : Subgroup G} {f : G → W}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hf : AvgFinite K f) {k : G} (hk : k ∈ K) (x : G) :
    avgOver K f (x * k) = avgOver K f x := by
  classical
  set S := (rightStab f).subgroupOf K
  have : S.FiniteIndex := ⟨hf⟩
  let _ := Fintype.ofFinite (K ⧸ S)
  simp only [avgOver]
  rw [avgSub_eq_sum, avgSub_eq_sum]
  congr 1
  let k' : K := ⟨k, hk⟩
  refine Fintype.sum_equiv (MulAction.toPerm k') _ _ fun q => ?_
  show f (x * k * (Quotient.out q : K)) = f (x * (Quotient.out (k' • q) : K))
  have h1 : k' • q = (QuotientGroup.mk (k' * Quotient.out q) : K ⧸ S) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [h1]
  obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul S (k' * Quotient.out q)
  rw [hb]
  have hb' : ((b : K) : G) ∈ rightStab f := b.2
  simp only [Subgroup.coe_mul]
  rw [← mul_assoc, ← mul_assoc, hb' _, mul_assoc]
end GroundTheory.Automorphic.Parabolic
