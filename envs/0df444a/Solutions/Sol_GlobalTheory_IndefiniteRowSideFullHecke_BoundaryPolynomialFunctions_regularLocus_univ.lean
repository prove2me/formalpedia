-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions.regularLocus_univ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:23.091344+00:00
-- url     : https://prove2.me/submissions/ebd37534-6fcb-404a-b1f7-97c3fbfa1530

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_BoundaryPolynomialFunctions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal LinearAlgebra.Projectivization
noncomputable section
variable {d : ℕ} {X : Type} [TopologicalSpace X]
namespace GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
theorem _root_.solution (A : FinHolAtlas d X) : regularLocus A Set.univ d = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ⟨trivial, ?_⟩
  obtain ⟨j, hj⟩ := A.cover x
  refine ⟨A.chart j, ⟨le_rfl, fun i => ⟨A.holo i j, A.holo j i⟩, ?_⟩, hj⟩
  ext y
  simp only [Set.univ_inter, Set.mem_setOf_eq]
  exact ⟨fun h => ⟨h, fun k hk => absurd k.2 (not_lt.2 hk)⟩, fun h => h.1⟩
end GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
