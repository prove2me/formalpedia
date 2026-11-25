-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:48.223149+00:00
-- url     : https://prove2.me/submissions/80c3ecc3-42f6-4403-ab00-6c962e92b10b

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
theorem _root_.solution {g : G → W} (hf : AvgFinite K f) (hg : AvgFinite K g) :
    avgOver K (f + g) = avgOver K f + avgOver K g := by
  classical
  set S := (rightStab f ⊓ rightStab g).subgroupOf K
  have hSi : S.index ≠ 0 := Subgroup.relIndex_inf_ne_zero hf hg
  have h1 : S ≤ (rightStab f).subgroupOf K := fun k hk => (Subgroup.mem_inf.1 hk).1
  have h2 : S ≤ (rightStab g).subgroupOf K := fun k hk => (Subgroup.mem_inf.1 hk).2
  have h3 : S ≤ (rightStab (f + g)).subgroupOf K := fun k hk y => by
    show f (y * (k : G)) + g (y * (k : G)) = f y + g y
    exact congrArg₂ (· + ·) ((Subgroup.mem_inf.1 hk).1 y) ((Subgroup.mem_inf.1 hk).2 y)
  have : S.FiniteIndex := ⟨hSi⟩
  let _ := Fintype.ofFinite (K ⧸ S)
  funext x
  rw [Pi.add_apply, avgOver_eq_avgSub h3 hSi, avgOver_eq_avgSub h1 hSi, avgOver_eq_avgSub h2 hSi,
    avgSub_eq_sum, avgSub_eq_sum, avgSub_eq_sum, ← smul_add, ← Finset.sum_add_distrib]
  rfl
end GroundTheory.Automorphic.Parabolic
