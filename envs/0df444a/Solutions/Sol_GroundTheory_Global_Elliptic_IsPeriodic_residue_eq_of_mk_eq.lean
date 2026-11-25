-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.IsPeriodic.residue_eq_of_mk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:45:34.423905+00:00
-- url     : https://prove2.me/submissions/b96c5a36-8f35-4f9c-8216-dbb385b5312b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticResidues
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_residue_add
import Theorems.Thm_GroundTheory_Global_Elliptic_Torus_mk_eq_mk_iff


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
theorem _root_.solution {f : ℂ → ℂ} (hp : IsPeriodic L f) (hf : Meromorphic f)
    {z w : ℂ} (h : Torus.mk L z = Torus.mk L w) : residue f z = residue f w := by
  have hzw := (Torus.mk_eq_mk_iff L).1 h
  have := hp.residue_add hf hzw w
  rwa [add_sub_cancel] at this
end IsPeriodic
end GroundTheory.Global.Elliptic
