-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.IsPeriodic.residue_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:52.751565+00:00
-- url     : https://prove2.me/submissions/46211a4d-c253-4c0a-ab50-3cf25bd0c573

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticResidues
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_comp_add
import Theorems.Thm_GroundTheory_Global_Elliptic_residue_comp_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped Interval Real
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
namespace IsPeriodic
theorem _root_.solution {f : ℂ → ℂ} (hp : IsPeriodic L f) (hf : Meromorphic f) {l : ℂ}
    (hl : l ∈ L.lattice) (z : ℂ) : residue f (z + l) = residue f z := by
  rw [← residue_comp_add (hf (z + l)), hp.comp_add hl]
end IsPeriodic
end GroundTheory.Global.Elliptic
