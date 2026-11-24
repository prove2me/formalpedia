-- Prove2me | solution 1 for GlobalTheory.KS.fderiv_fn_resG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:33.683175+00:00
-- url     : https://prove2.me/submissions/64f6245f-9d0a-4a2f-be08-a7a3d8a6c048

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFibreCoords

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
theorem _root_.solution {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g)
    {X : Scheme.{0}} (m : A₀.left ⟶ X) {W W' : X.Opens} (h : W' ≤ W) (f : Γ(X, W)) {z : Fin g → ℂ}
    (hz : z ∈ dom u m W') : fderiv ℂ (fn u m W' (resG X h f)) z = fderiv ℂ (fn u m W f) z := by
  have key : ∀ (y : Sp ℂ ⟶ X), ⊤ ≤ y ⁻¹ᵁ W' → valAt' y W' (resG X h f) = valAt' y W f := by
    intro y hy
    have hy2 : ⊤ ≤ y ⁻¹ᵁ W := hy.trans (fun q hq => h hq)
    unfold valAt'
    rw [dif_pos hy, dif_pos hy2]
    unfold valAt
    congr 1
    rw [← Scheme.Hom.map_appLE y hy (homOfLE h).op]
    rfl
  have hopen : IsOpen (dom u m W') := by
    exact (u.hol (m ⁻¹ᵁ W') 0).1
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hopen.mem_nhds hz] with z' hz'
  exact key _ hz'
end GlobalTheory.KS
