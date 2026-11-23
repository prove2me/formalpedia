-- Prove2me | solution 1 for GlobalTheory.DegreeGrowth.mem_boxSpan
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:20.909688+00:00
-- url     : https://prove2.me/submissions/6951fdff-b39c-46ec-b729-04ac0e37fdea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankTotalDegreeImageGrowth

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
theorem _root_.solution {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D : ℕ) (a : Fin s → ℕ)
    (ha : ∀ i, a i ≤ D) (l : Fin n) : (∏ i, y i ^ a i) * b l ∈ boxSpan K y b D :=
  Submodule.subset_span ⟨(fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩, l), rfl⟩
end GlobalTheory.DegreeGrowth
