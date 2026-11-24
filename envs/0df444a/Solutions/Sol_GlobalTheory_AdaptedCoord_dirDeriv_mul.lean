-- Prove2me | solution 1 for GlobalTheory.AdaptedCoord.dirDeriv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:54:10.577666+00:00
-- url     : https://prove2.me/submissions/d8faeab1-b2ae-48fc-b1b0-679ba76db65b

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FderivEqZeroOfAffine
import Theorems.Thm_GlobalTheory_AdaptedCoord_dirDeriv_apply
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2


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
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.AdaptedCoord
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.AdaptedCoord
theorem _root_.solution {U : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U) (w : Fin g → ℂ) (f f' : Γ(A.left, U)) :
    dirDeriv u h w (f * f') =
      valAt' (u.ex 0).left U f * dirDeriv u h w f' + valAt' (u.ex 0).left U f' * dirDeriv u h w f := by
  rw [dirDeriv_apply, dirDeriv_apply, dirDeriv_apply]
  have hprod : (fun z => valAt' (u.ex z).left U (f * f')) =
      fun z => valAt' (u.ex z).left U f * valAt' (u.ex z).left U f' := by
    funext z
    exact valAt'_mul _ _ _ _
  rw [hprod, fderiv_fun_mul (differentiableAt_val u h f) (differentiableAt_val u h f')]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
end GlobalTheory.AdaptedCoord
