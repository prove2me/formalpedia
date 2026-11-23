-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.Torus.mk_eq_mk_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:31.480831+00:00
-- url     : https://prove2.me/submissions/1181263f-bfb3-4e50-be42-a37492d45d48

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions

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
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable (L : PeriodPair)
namespace GroundTheory.Global.Elliptic
namespace Torus
theorem _root_.solution {z w : ℂ} : Torus.mk L z = Torus.mk L w ↔ z - w ∈ L.lattice := by
  rw [Torus.mk, Torus.mk, QuotientAddGroup.eq_iff_sub_mem]
  rfl
end Torus
end GroundTheory.Global.Elliptic
