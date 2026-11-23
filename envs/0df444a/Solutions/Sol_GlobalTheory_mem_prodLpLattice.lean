-- Prove2me | solution 1 for GlobalTheory.mem_prodLpLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:09.108737+00:00
-- url     : https://prove2.me/submissions/548d4658-4b1a-49c0-91b4-fef8821d7076

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Submodule Set
open GlobalTheory
noncomputable section
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] (L : Submodule ℤ E) (L' : Submodule ℤ E')
namespace GlobalTheory
theorem _root_.solution {x : WithLp 2 (E × E')} :
    x ∈ prodLpLattice L L' ↔ x.fst ∈ L ∧ x.snd ∈ L' := Iff.rfl
end GlobalTheory
