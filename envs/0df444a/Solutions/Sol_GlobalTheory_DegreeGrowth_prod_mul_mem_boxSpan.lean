-- Prove2me | solution 1 for GlobalTheory.DegreeGrowth.prod_mul_mem_boxSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:05.949647+00:00
-- url     : https://prove2.me/submissions/d8105770-66fd-49a1-857d-dc12e3c08260

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankTotalDegreeImageGrowth
import Theorems.Thm_GlobalTheory_DegreeGrowth_pow_mul_mem_boxSpan

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
theorem _root_.solution {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D d : ℕ) {I : Type}
    (r : I → B) (hr : ∀ i l, r i * b l ∈ boxSpan K y b d) (S : Finset I) (a : I → ℕ) {x : B}
    (hx : x ∈ boxSpan K y b D) :
    (∏ i ∈ S, r i ^ a i) * x ∈ boxSpan K y b ((∑ i ∈ S, a i) * d + D) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hx
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, _root_.mul_assoc, add_mul, add_assoc]
    exact pow_mul_mem_boxSpan y b _ d (r i) (hr i) (a i) ih
end GlobalTheory.DegreeGrowth
