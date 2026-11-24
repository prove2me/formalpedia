-- Prove2me | solution 1 for GlobalTheory.DegreeGrowth.pow_mul_mem_boxSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:00:35.265253+00:00
-- url     : https://prove2.me/submissions/5cbeeb73-b5bc-43e6-aba2-a0b337628fc4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankTotalDegreeImageGrowth
import Theorems.Thm_GlobalTheory_DegreeGrowth_mul_mem_boxSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.DegreeGrowth
variable {K B : Type} [Field K] [CommRing B] [Algebra K B]
namespace GlobalTheory.DegreeGrowth
theorem _root_.solution {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D d : ℕ) (z : B)
    (hz : ∀ l, z * b l ∈ boxSpan K y b d) (k : ℕ) {x : B} (hx : x ∈ boxSpan K y b D) :
    z ^ k * x ∈ boxSpan K y b (k * d + D) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    have := mul_mem_boxSpan y b _ d z hz ih
    rw [show (k + 1) * d + D = d + (k * d + D) by ring, show z ^ (k + 1) * x = z * (z ^ k * x) by ring]
    exact this
end GlobalTheory.DegreeGrowth
