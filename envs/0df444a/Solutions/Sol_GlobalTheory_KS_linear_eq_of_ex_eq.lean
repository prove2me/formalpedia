-- Prove2me | solution 1 for GlobalTheory.KS.linear_eq_of_ex_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:46:57.102815+00:00
-- url     : https://prove2.me/submissions/35628442-72bb-4e01-94e0-2bd256c5cdca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqZeroOfLineSubsetDiscrete
import Theorems.Thm_GlobalTheory_KS_eq_zero_of_line_subset_discrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS
namespace GlobalTheory.KS
theorem _root_.solution {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)
    (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, u.ex (F z) = u.ex (F' z)) : F = F' := by
  have hd := u.discrete
  have hm : ∀ z, F z - F' z ∈ u.Λ := by
    intro z
    rw [← u.ker]
    have h1 := u.ex_add (F z - F' z) (F' z)
    rw [sub_add_cancel, h z] at h1
    exact (mul_eq_right.mp h1.symm)
  refine LinearMap.ext fun z => sub_eq_zero.mp (eq_zero_of_line_subset_discrete u.Λ _ fun t => ?_)
  have := hm (t • z)
  rwa [map_smul, map_smul, ← smul_sub] at this
end GlobalTheory.KS
