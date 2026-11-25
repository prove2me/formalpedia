-- Prove2me | solution 1 for GroundTheory.Automorphic.continuous_multilinear_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:13:59.718864+00:00
-- url     : https://prove2.me/submissions/3e74074a-3e8f-4c79-889d-b104f34a99e4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology Asymptotics
open scoped ContDiff
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)
omit [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
namespace GroundTheory.Automorphic.IsExpLieAlgebra
namespace _root_.GroundTheory.Automorphic
theorem _root_.solution {ι : Type*} [Fintype ι]
    [DecidableEq ι] {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : MultilinearMap ℝ (fun _ : ι => M) F) : Continuous f := by
  let b := Module.finBasis ℝ M
  have key : ∀ Y : ι → M, f Y = ∑ r ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset (Fin (Module.finrank ℝ M)))),
      (∏ i, b.repr (Y i) (r i)) • f (fun i => b (r i)) := by
    intro Y
    have hY : Y = fun i => ∑ j, b.repr (Y i) j • b j := funext fun i => (b.sum_repr (Y i)).symm
    conv_lhs => rw [hY]
    rw [f.map_sum_finset]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact f.map_smul_univ (fun i => b.repr (Y i) (r i)) (fun i => b (r i))
  have e : (f : (ι → M) → F) = fun Y => ∑ r ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset (Fin (Module.finrank ℝ M)))),
      (∏ i, b.repr (Y i) (r i)) • f (fun i => b (r i)) := funext key
  rw [e]
  refine continuous_finsetSum _ fun r _ => ?_
  refine (continuous_finsetProd _ fun i _ => ?_).smul continuous_const
  exact ((b.coord (r i)).continuous_of_finiteDimensional).comp (continuous_apply i)
end _root_.GroundTheory.Automorphic
end GroundTheory.Automorphic.IsExpLieAlgebra
