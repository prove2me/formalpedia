-- Prove2me | solution 1 for GlobalTheory.CMNormIdentity.lift_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:18:01.642816+00:00
-- url     : https://prove2.me/submissions/a09e5356-e17b-4f36-92d3-d944fd418ec2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsLinearOfIsMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingSmul
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CMNormIdentity
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.CMNormIdentity
theorem _root_.solution {g₀ : ℕ} (F F' : (Fin g₀ → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, u.ex (F z) = u.ex (F' z)) :
    F = F' := by
  have hm : ∀ z, (F - F') z ∈ u.Λ := fun z => by
    rw [← u.ker]
    have h1 := u.ex_add ((F - F') z) (F' z)
    rw [LinearMap.sub_apply, sub_add_cancel, h z] at h1
    exact (right_eq_mul.1 h1)
  haveI := u.discrete
  have hc : Continuous (fun z => (⟨(F - F') z, hm z⟩ : u.Λ)) :=
    (LinearMap.continuous_of_finiteDimensional (F - F')).subtype_mk _
  refine LinearMap.ext fun z => ?_
  have := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := z) (y := 0))
  simpa [sub_eq_zero] using this
end GlobalTheory.CMNormIdentity
