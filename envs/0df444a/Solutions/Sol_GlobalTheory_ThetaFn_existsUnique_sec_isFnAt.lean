-- Prove2me | solution 1 for GlobalTheory.ThetaFn.existsUnique_sec_isFnAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:56:06.601641+00:00
-- url     : https://prove2.me/submissions/3994e33f-6580-4e26-b23c-a9d9bc373b12

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_GlobalTheory_ThetaFn_isFnAt_iff_isFnPow
import Theorems.Thm_GlobalTheory_ThetaFn_isFnAt_ofFibre_iff

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
namespace GlobalTheory.ThetaFn
theorem _root_.solution [IsIso p] {n : ℕ} {θ : (Fin g → ℂ) → ℂ}
    (h : ∃! s, u.IsFnPow n s θ) : ∃! s : LB.Sec (LPow A L n T), IsFnAt u p n s θ := by
  obtain ⟨s, hs, huniq⟩ := h
  refine ⟨ofFibre A L T n s, (isFnAt_ofFibre_iff u p n s θ).2 hs, fun s' hs' => ?_⟩
  rw [← huniq _ ((isFnAt_iff_isFnPow u p n s' θ).1 hs'), ofFibre_toFibre]
end GlobalTheory.ThetaFn
