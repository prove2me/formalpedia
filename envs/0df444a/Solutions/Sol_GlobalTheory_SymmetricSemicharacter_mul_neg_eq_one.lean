-- Prove2me | solution 1 for GlobalTheory.SymmetricSemicharacter.mul_neg_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:59:58.627854+00:00
-- url     : https://prove2.me/submissions/1a30dc12-82de-4384-a284-6b0275c1e2d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_exists_chart
import Theorems.Thm_GlobalTheory_CubeValues_ex_add_period


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.SymmetricSemicharacter
open CubeValues
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.SymmetricSemicharacter
theorem _root_.solution (hv : ValueRules) (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) (l : u.Λ) : χ l * χ (-l) = 1 := by
  obtain ⟨i, hi⟩ := exists_chart u hv hL 0
  have hi' : ⊤ ≤ (u.ex (0 + l)).left ⁻¹ᵁ L.U i := by rwa [ex_add_period u 0 l l.2]
  have h1 := h.2.2.2 l i 0 hi
  have h2 := h.2.2.2 (-l) i _ hi'
  rw [h2] at h1
  simp only [zero_add, Submodule.coe_neg, add_neg_cancel, star_neg, Matrix.mulVec_neg,
    dotProduct_neg, neg_dotProduct, neg_neg, zero_dotProduct, mul_zero] at h1
  set b := (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))
  have he : Complex.exp (Real.pi / 2 * b) * Complex.exp (Real.pi * -b + Real.pi / 2 * b) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  refine mul_right_cancel₀ (u.fr_ne i 0 hi) ?_
  linear_combination -h1 - χ l * χ (-l) * u.fr i 0 * he
end GlobalTheory.SymmetricSemicharacter
