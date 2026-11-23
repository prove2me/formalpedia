-- Prove2me | solution 1 for GlobalTheory.polyDeriv_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:56.368402+00:00
-- url     : https://prove2.me/submissions/1a3aa946-6550-48c1-92f1-1c08cf3cb97f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormPderivIterLeOfAnalyticAt
import Theorems.Thm_GlobalTheory_polyDerivLinear_apply
import Theorems.Thm_GlobalTheory_polyDeriv_zero
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero


attribute [local simp] GlobalTheory.polyDerivLinear_apply
attribute [local simp] GlobalTheory.polyDeriv_zero

set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
namespace GlobalTheory
theorem _root_.solution (α : ι →₀ ℕ) (c : 𝕜) (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv (MvPolynomial.monomial α c) F a = c • pderivIter α F a := by
  rw [polyDeriv_eq_sum_of_subset _ (s := {α}) MvPolynomial.support_monomial_subset]
  simp
end GlobalTheory
