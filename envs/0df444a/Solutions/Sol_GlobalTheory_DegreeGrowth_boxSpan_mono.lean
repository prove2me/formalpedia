-- Prove2me | solution 1 for GlobalTheory.DegreeGrowth.boxSpan_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:33.294802+00:00
-- url     : https://prove2.me/submissions/ca4aa503-59a5-4123-80de-2b21e39fdabc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankTotalDegreeImageGrowth
import Theorems.Thm_GlobalTheory_DegreeGrowth_monomial_mul_mem

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
theorem _root_.solution {s n : ℕ} (y : Fin s → B) (b : Fin n → B) {D E : ℕ} (h : D ≤ E) :
    boxSpan K y b D ≤ boxSpan K y b E := by
  intro x hx
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa using monomial_mul_mem y b D d (fun _ => 0) (fun _ => Nat.zero_le _) hx
end GlobalTheory.DegreeGrowth
