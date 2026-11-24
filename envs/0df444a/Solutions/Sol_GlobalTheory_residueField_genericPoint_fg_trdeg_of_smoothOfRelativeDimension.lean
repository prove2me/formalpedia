-- Prove2me | solution 1 for GlobalTheory.residueField_genericPoint_fg_trdeg_of_smoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:06.408447+00:00
-- url     : https://prove2.me/submissions/e13c7c3d-1288-47f6-af92-9942cccbffd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsIsOpenImmersionIsStandardSmoothOfRelativeD
import Theorems.Thm_GlobalTheory_residueField_fg_trdeg_of_smoothOfRelativeDimension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ), SmoothOfRelativeDimension d f → ∀ (Z : Set X) (hZ : Z ∈ irreducibleComponents X), letI : Algebra K (X.residueField (hZ.1 : IsIrreducible Z).genericPoint) := (Spec.preimage (X.fromSpecResidueField (hZ.1 : IsIrreducible Z).genericPoint ≫ f)).hom.toAlgebra; (⊤ : IntermediateField K (X.residueField (hZ.1 : IsIrreducible Z).genericPoint)).FG ∧ Algebra.trdeg K (X.residueField (hZ.1 : IsIrreducible Z).genericPoint) = d := by
  intro K _ X f d hf Z hZ
  refine residueField_fg_trdeg_of_smoothOfRelativeDimension f d hf _ fun y hy => ?_
  have hg := (hZ.1 : IsIrreducible Z).isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents Z hZ)
  have h1 : Z ⊆ closure {y} := by
    rw [← hg.def]
    exact specializes_iff_closure_subset.mp hy
  have h2 : closure {y} ⊆ Z := hZ.2 isIrreducible_singleton.closure h1
  exact (hy.antisymm (hg.specializes (h2 (subset_closure rfl)))).eq
end GlobalTheory
