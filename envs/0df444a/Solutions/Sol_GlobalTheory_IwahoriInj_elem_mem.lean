-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.elem_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:49.76902+00:00
-- url     : https://prove2.me/submissions/05ad619b-5b68-4b44-b860-3a41102a412e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Theorems.Thm_GlobalTheory_IwahoriInj_Deep_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.IwahoriInj
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.IwahoriInj
theorem _root_.solution {f : n → n → ℤ} (hf : Conc f) {i j : n} (h : i ≠ j) {y : k} (hy : Deep (f i j) y) :
    elem h y ∈ grp k hf := by
  have : ∀ y : k, Deep (f i j) y → ∀ a b, Deep (f a b) (transvection i j y a b) := fun y hy a b => by
    have h1 := (grp k hf).one_mem.1 a b
    by_cases c : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := c
      simpa [transvection, one_apply_ne h] using hy
    · simpa [transvection, single_apply, c] using h1
  exact ⟨this y hy, this _ hy.neg⟩
end GlobalTheory.IwahoriInj
