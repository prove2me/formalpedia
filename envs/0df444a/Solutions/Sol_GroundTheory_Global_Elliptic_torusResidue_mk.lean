-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.torusResidue_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:23.07573+00:00
-- url     : https://prove2.me/submissions/7aaf1058-dd58-4e8a-ae74-6ba01d36c600

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticResidues
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_residue_eq_of_mk_eq

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
theorem _root_.solution {f : ℂ → ℂ} (hf : IsEllipticFunction L f) (z : ℂ) :
    torusResidue L f (Torus.mk L z) = residue f z :=
  hf.2.residue_eq_of_mk_eq hf.1 (QuotientAddGroup.out_eq' (Torus.mk L z))
end GroundTheory.Global.Elliptic
