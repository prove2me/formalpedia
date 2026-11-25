-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_eq_avgSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:02:56.229453+00:00
-- url     : https://prove2.me/submissions/7363cdf4-3eea-4f89-8c7d-a080bf322155

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_sum_quotient_out_of_le
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
theorem _root_.solution {S : Subgroup K} (hS : S ≤ (rightStab f).subgroupOf K) (hSi : S.index ≠ 0)
    (x : G) : avgOver K f x = avgSub K S f x := by
  classical
  set t := (rightStab f).subgroupOf K
  have : S.FiniteIndex := ⟨hSi⟩
  have hti : t.index ≠ 0 := fun h0 => hSi (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.index_dvd_of_le hS))
  have : t.FiniteIndex := ⟨hti⟩
  have hrel : S.relIndex t ≠ 0 := by
    intro h0
    apply hSi
    rw [← Subgroup.relIndex_mul_index hS, h0, zero_mul]
  have : (S.subgroupOf t).FiniteIndex := ⟨hrel⟩
  let _ := Fintype.ofFinite (K ⧸ S)
  let _ := Fintype.ofFinite (K ⧸ t)
  let _ := Fintype.ofFinite (t ⧸ S.subgroupOf t)
  rw [avgOver, avgSub_eq_sum, avgSub_eq_sum,
    sum_quotient_out_of_le hS (fun k : K => f (x * (k : G))) (fun a b hb => by
      show f (x * ((a : G) * (b : G))) = f (x * a)
      rw [← mul_assoc]
      exact hb _),
    ← Subgroup.relIndex_mul_index hS, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_mul]
  congr 1
  have : (S.relIndex t : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hrel
  have h2 : (t.index : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hti
  field_simp
  exact div_self h2
end GroundTheory.Automorphic.Parabolic
