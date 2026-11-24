-- Prove2me | solution 1 for GlobalTheory.BK.algebraMap_omegaOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:41:15.83431+00:00
-- url     : https://prove2.me/submissions/3152258a-d610-4eed-89dc-0ae7a49b43dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
variable {O K l e a ι} {κ : Type} [Fintype κ] [DecidableEq κ] {η H η' H' : ℕ}
omit [NeZero a] [TameDescentExponentData K l e a]
variable [TameDescentExponentData K l e 1]
omit [IsUltrametricDist K]
namespace GlobalTheory.BK
theorem _root_.solution (g : TameGal K l e 1) : algebraMap O K (omegaOne O g) = g.root 0 :=
  (exists_algebraMap_eq_root g).choose_spec
end GlobalTheory.BK
