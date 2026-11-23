-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgSub_comp_mul_right_of_normal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:17.95026+00:00
-- url     : https://prove2.me/submissions/0f01daad-6e3b-4eaf-9523-5ce6219e6329

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
  {K : Subgroup G} {f : G → W}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {S : Subgroup K} [S.Normal] (hSi : S.index ≠ 0)
    (hS : S ≤ (rightStab f).subgroupOf K) {k : G} (hk : k ∈ K) (x : G) :
    avgSub K S (fun y => f (y * k)) x = avgSub K S f x := by
  classical
  have : S.FiniteIndex := ⟨hSi⟩
  let _ := Fintype.ofFinite (K ⧸ S)
  rw [avgSub_eq_sum, avgSub_eq_sum]
  congr 1
  let k' : K := ⟨k, hk⟩
  refine Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk k' : K ⧸ S)) _ _ fun q => ?_
  show f (x * ((Quotient.out q : K) : G) * k) =
    f (x * ((Quotient.out (q * (QuotientGroup.mk k' : K ⧸ S)) : K) : G))
  have h1 : q * (QuotientGroup.mk k' : K ⧸ S) = QuotientGroup.mk (Quotient.out q * k') := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  rw [h1]
  obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul S (Quotient.out q * k')
  rw [hb]
  have hb' : ((b : K) : G) ∈ rightStab f := hS b.2
  simp only [Subgroup.coe_mul]
  rw [← mul_assoc, ← mul_assoc, hb' _, mul_assoc]
end GroundTheory.Automorphic.Parabolic
