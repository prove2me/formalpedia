-- Prove2me | solution 1 for GlobalTheory.ThetaFn.IsFnAt.add_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:45:14.572742+00:00
-- url     : https://prove2.me/submissions/4126a1c4-752a-41b5-bbe9-74343fc08af4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_add_period

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
namespace GlobalTheory.ThetaFn
namespace IsFnAt
theorem _root_.solution (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (hAH : u.IsAH Hm χ) {k : ℤ} {s : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p k s θ) (l : u.Λ) (z : Fin g → ℂ) :
    θ (z + l) =
      (χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l)) ^ k * θ z := by
  obtain ⟨j, hj⟩ := exists_chart_exAt u p hL k z
  have hj' : ⊤ ≤ exAt u p (z + l) ⁻¹ᵁ (LPow A L k T).U j := by
    rw [exAt_add_period u p z l l.2]; exact hj
  have h2 := h j (z + l) hj'
  rw [exAt_add_period u p z l l.2, h j z hj,
    hAH.2.2.2 l _ z ((exAt_mem_chart_iff u p k j z).1 hj), mul_zpow, ← _root_.mul_assoc] at h2
  rw [← mul_right_cancel₀ (fr_zpow_ne_zero u p hj' k) h2, _root_.mul_comm]
  rfl
end IsFnAt
end GlobalTheory.ThetaFn
