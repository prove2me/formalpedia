-- Prove2me | solution 2 for GlobalTheory.basisVal_eq_of_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:36:16.25086+00:00
-- url     : https://prove2.me/submissions/cc2d3d75-2311-4332-b5a9-a08ad0d4c88a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_basisVal_eq_of_le_one
import Theorems.Thm_GlobalTheory_basisVal_le_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open Module
variable {R Γ₀ ι κ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation R Γ₀) {M : Type*} [AddCommGroup M] [Module R M] (b : Basis ι R M)
  {O : Type*} [CommRing O] [Algebra O R] [Module O M] [IsScalarTower O R M]
namespace GlobalTheory
theorem _root_.solution (hO : v.Integers O) (c : Basis κ R M)
    (h : Submodule.span O (Set.range b) = Submodule.span O (Set.range c)) (x : M) :
    basisVal v b x = basisVal v c x :=
  basisVal_eq_of_le_one v b c
    (fun i => (basisVal_le_one_iff v c hO).mpr (h ▸ Submodule.subset_span ⟨i, rfl⟩))
    (fun j => (basisVal_le_one_iff v b hO).mpr (h.symm ▸ Submodule.subset_span ⟨j, rfl⟩)) x
end GlobalTheory
