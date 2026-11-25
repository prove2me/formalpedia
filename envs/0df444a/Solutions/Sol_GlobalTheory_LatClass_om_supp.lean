-- Prove2me | solution 1 for GlobalTheory.LatClass.om_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:00:26.3258+00:00
-- url     : https://prove2.me/submissions/0af5af2a-c149-47e6-8bc0-c614572007b1

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
theorem _root_.solution {μ : kˣ →* ℂˣ} {Φ : Matrix Y Y' k → ℂ} (hs : ∀ x, Φ x ≠ 0 → IntM x) (g : GL Y' k) (h : GL Y k)
    (x : Matrix Y Y' k) (hx : om μ g h Φ x ≠ 0) : MapsLat x (latOf g) (latOf h) :=
  mapsLat_iff.2 (hs _ (right_ne_zero_of_mul hx))
end GlobalTheory.LatClass
