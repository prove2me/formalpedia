-- Prove2me | solution 1 for GlobalTheory.TorusTransfer.frame_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:54:33.110914+00:00
-- url     : https://prove2.me/submissions/37de7f76-0b2c-4225-913e-cd502f0df365

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FderivEqZeroOfAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_PolarisedTorusAlgebraicOfParts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqZeroOfFderivEqZero
import Theorems.Thm_GlobalTheory_ThetaSeparation_dense_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_ex_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real CategoryTheory.Obj
open GlobalTheory GlobalTheory.TorusTransfer
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.TorusTransfer
theorem _root_.solution (th : L.Sec) (θ a : (Fin g → ℂ) → ℂ) (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0) (ha : Continuous a)
    (hth : u.IsFn th θ) (l : Fin g → ℂ) (hl : l ∈ u.Λ) (hlaw : ∀ z, θ (z + l) = a z * θ z) (i : L.ι) (z : Fin g → ℂ)
    (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) : u.fr i z = a z * u.fr i (z + l) := by
  have he : ∀ z, u.ex (z + l) = u.ex z := fun z => by rw [u.ex_add, (u.ker l).2 hl, _root_.mul_one]
  have hO := (u.hol (L.U i) 0).1
  have hc : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → ContinuousAt (u.fr i) z := fun z hz =>
    (u.fr_hol i).continuousOn.continuousAt (hO.mem_nhds hz)
  have hd := ThetaSeparation.dense_ne_zero hθ (Function.ne_iff.1 h0)
  have h1 : ContinuousAt (fun z => a z * u.fr i (z + l)) z :=
    ha.continuousAt.mul (ContinuousAt.comp (f := fun z => z + l) (hc _ (by rw [he]; exact hz)) (by fun_prop))
  refine tendsto_nhds_unique_of_frequently_eq (hc z hz) h1 ?_
  refine ((mem_closure_iff_frequently.1 (hd z)).and_eventually (hO.mem_nhds hz)).mono fun y hy => ?_
  have h2 := hth i y hy.2
  have h3 := hth i (y + l) (by rw [he]; exact hy.2)
  rw [he, h2, hlaw] at h3
  apply mul_left_cancel₀ hy.1
  rw [h3]; ring
end GlobalTheory.TorusTransfer
