-- Prove2me | solution 1 for GlobalTheory.AnDim.singularLocus_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:04.33518+00:00
-- url     : https://prove2.me/submissions/c90dd5cb-c4d0-4800-9400-310930258b3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_BoundaryPolynomialFunctions_regularLocus_univ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology
noncomputable section
open GlobalTheory.AnDim
variable {d : ℕ} {X : Type} [TopologicalSpace X]
namespace GlobalTheory.AnDim
theorem _root_.solution (A : FinHolAtlas d X) : singularLocus A Set.univ = ∅ :=
  Set.diff_eq_empty.2 fun x _ => Set.mem_iUnion.2 ⟨d, by rw [regularLocus_univ]; trivial⟩
end GlobalTheory.AnDim
