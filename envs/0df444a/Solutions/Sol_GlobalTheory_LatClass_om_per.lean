-- Prove2me | solution 1 for GlobalTheory.LatClass.om_per
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:00:22.516144+00:00
-- url     : https://prove2.me/submissions/d10a579e-67fa-4703-baef-5c344a4b728d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
import Theorems.Thm_GlobalTheory_LatClass_mapsLat_iff

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
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.LatClass
theorem _root_.solution (hϖ : valuation k (ϖ : k) = uniformizer k) {μ : kˣ →* ℂˣ} {Φ : Matrix Y Y' k → ℂ}
    (hp : ∀ x y, MaxM y → Φ (x + y) = Φ x) (g : GL Y' k) (h : GL Y k)
    (x y : Matrix Y Y' k) (hy : MapsLat y (latOf g) (latOf h)) :
    om μ g h Φ (x + (ϖ : k) • y) = om μ g h Φ x := by
  unfold om
  rw [Matrix.mul_add, Matrix.add_mul, hp]
  intro i j
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, hϖ]
  exact mul_lt_one_of_nonneg_of_lt_one_left zero_le uniformizer_lt_one (mapsLat_iff.1 hy i j)
end GlobalTheory.LatClass
