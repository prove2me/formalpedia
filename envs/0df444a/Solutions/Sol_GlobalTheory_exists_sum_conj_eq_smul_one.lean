-- Prove2me | solution 1 for GlobalTheory.exists_sum_conj_eq_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:46:52.055304+00:00
-- url     : https://prove2.me/submissions/a382d34d-af31-449e-a9e2-c66a33c07144

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrrCharOneMulFinsumConjMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [ρ.IsIrreducible] (x : G) :
    ∃ c : ℂ, ∑ h : G, ρ (h * x * h⁻¹) = c • (1 : Module.End ℂ V) := by
  have hc : ∀ g : G, (∑ h : G, ρ (h * x * h⁻¹)) * ρ g = ρ g * ∑ h : G, ρ (h * x * h⁻¹) := by
    intro g
    rw [Finset.sum_mul, Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_).symm
    rw [← map_mul, ← map_mul]
    congr 1
    simp [mul_assoc]
  let T : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := ∑ h : G, ρ (h * x * h⁻¹)
      isIntertwining' := fun g => hc g }
  obtain ⟨c, hT⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).2 T
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  change T v = c • v
  rw [← hT, Algebra.algebraMap_eq_smul_one]
  rfl
end GlobalTheory
