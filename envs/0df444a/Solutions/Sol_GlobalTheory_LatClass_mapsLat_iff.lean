-- Prove2me | solution 1 for GlobalTheory.LatClass.mapsLat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:12.282826+00:00
-- url     : https://prove2.me/submissions/12227dc4-bed0-4106-a975-f8431ad7aea9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
import Theorems.Thm_GlobalTheory_StepData_mem_latOf_one
import Theorems.Thm_GlobalTheory_StepData_mulVec_mem_latOf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.LatClass
variable {k : Type} [Field k] [ValuativeRel k] {ϖ : kˣ}
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.LatClass
theorem _root_.solution {x : Matrix Y Y' k} {g : GL Y' k} {h : GL Y k} :
    MapsLat x (latOf g) (latOf h) ↔ IntM ((h⁻¹).val * x * g.val) := by
  constructor
  · intro H i j
    have : g.val *ᵥ Pi.single j 1 ∈ latOf g := by
      have := (mulVec_mem_latOf g (g := 1) (y := Pi.single j 1)).2 (mem_latOf_one.2 fun l => by
        rw [Pi.single_apply]; split_ifs
        exacts [one_mem _, zero_mem _])
      rwa [mul_one] at this
    have := H _ this i
    rwa [mulVec_mulVec, mulVec_mulVec, mulVec_single_one] at this
  · intro H y hy i
    have : (h⁻¹).val *ᵥ (x *ᵥ y) = ((h⁻¹).val * x * g.val) *ᵥ ((g⁻¹).val *ᵥ y) := by
      simp [mulVec_mulVec, Matrix.mul_assoc]
    rw [this]
    exact sum_mem fun l _ => mul_mem (H i l) (hy l)
end GlobalTheory.LatClass
