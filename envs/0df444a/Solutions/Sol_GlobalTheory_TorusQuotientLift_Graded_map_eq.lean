-- Prove2me | solution 1 for GlobalTheory.TorusQuotientLift.Graded.map_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:47:21.613281+00:00
-- url     : https://prove2.me/submissions/9af382f0-1300-4d0b-bad5-3fc63d1dab0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSchemeOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfRingMaps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTorusQuotientSchemeOverNilpotentThickening

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open GlobalTheory.UU GlobalTheory.AffineThickening
noncomputable section
open GlobalTheory GlobalTheory.TorusQuotientLift
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
variable {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'} {V : G.left.Opens} {V' : G'.left.Opens}
namespace GlobalTheory.TorusQuotientLift
namespace Graded
theorem _root_.solution (h : Graded i' V') (p : Γ(G.left, V) →+* Γ(G'.left, V'))
    (hp : ∀ χ x, IsWt i V x χ → IsWt i' V' (p x) χ) {a : X →₀ Γ(G.left, V)} (ha : ∀ χ, IsWt i V (a χ) χ) {χ : X}
    (hy : IsWt i' V' (p (a.sum fun _ x => x)) χ) : p (a χ) = p (a.sum fun _ x => x) := by
  classical
  have := h.2 (a.mapRange p (map_zero p) - Finsupp.single χ (p (a.sum fun _ x => x))) (fun ψ => by
    refine (wtSub i' V' ψ).sub_mem (hp _ _ (ha ψ)) ?_
    rw [Finsupp.single_apply]
    split_ifs with e
    · exact e ▸ hy
    · exact zero_mem _) (by
      rw [Finsupp.sum_sub_index (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
        Finsupp.sum_mapRange_index (fun _ => rfl), map_finsuppSum, sub_self])
  simpa [sub_eq_zero] using DFunLike.congr_fun this χ
end Graded
end GlobalTheory.TorusQuotientLift
