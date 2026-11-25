-- Prove2me | solution 1 for GlobalTheory.ThetaFn.isFnAt_iff_of_isPullSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:26:17.334156+00:00
-- url     : https://prove2.me/submissions/27e85760-db2f-4b5d-9a00-357754a4bc00

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_P2M_GlobalTheory_ThetaFn_valAt__appLE__46c54dbc5e3c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p}
variable (u p)
variable {u p}
namespace GlobalTheory.ThetaFn
theorem _root_.solution {T' : Over (Sp ℂ)} {p' : 𝟙_ (Over (Sp ℂ)) ⟶ T'}
    {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A} {k : ℤ} {s : LB.Sec (LPow A L k T)}
    {s' : LB.Sec (LPow A L k T')} (hs : IsPullSec A L k h hh s s')
    (hp : ∀ z, exAt u p' z ≫ h.left = exAt u p z) (θ : (Fin g → ℂ) → ℂ) :
    IsFnAt u p' k s' θ ↔ IsFnAt u p k s θ := by
  refine forall_congr' fun j => forall_congr' fun z => ?_
  rw [exAt_mem_chart_iff u p k j z, ← exAt_mem_chart_iff u p' k j z]
  refine imp_congr_right fun hj => ?_
  rw [hs j, ← hp z]
  exact Eq.congr_left (valAt'_appLE' _ h.left (chart_le_res A L h hh k j) hj _)
end GlobalTheory.ThetaFn
