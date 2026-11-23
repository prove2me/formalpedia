-- Prove2me | solution 1 for GlobalTheory.LevelUnimod.conj_levDiag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:54.52187+00:00
-- url     : https://prove2.me/submissions/a7910c69-e5dd-4141-9426-d3f8ebbcd804

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GlCharacterEqOneOfTransposeInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevels
import Theorems.Thm_GlobalTheory_LevelUnimod_levDiag_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped Topology
open GlobalTheory GlobalTheory.LevelUnimod
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.LevelUnimod
theorem _root_.solution (lev : ι → ℕ) (t : kˣ) (g : GL ι k) (r s : ι) :
    ((levDiag lev t)⁻¹ * g * levDiag lev t).val r s =
      ((t⁻¹ : kˣ) : k) ^ lev r * g.val r s * (t : k) ^ lev s := by
  rw [levDiag_inv, Units.val_mul, Units.val_mul]
  simp only [levDiag, mul_diagonal, diagonal_mul]
end GlobalTheory.LevelUnimod
