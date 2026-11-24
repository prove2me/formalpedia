-- Prove2me | solution 1 for GlobalTheory.JR.DualLattice.mem_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:59:50.690101+00:00
-- url     : https://prove2.me/submissions/612e9a47-4124-44db-9b2c-23e12a97ab2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.DualLattice
variable {F : Type} [NontriviallyNormedField F]
variable {V : Type} [AddCommGroup V] [Module F V]
namespace GlobalTheory.JR.DualLattice
theorem _root_.solution [IsUltrametricDist F] {ι : Type} (e : Module.Basis ι F V) (r : ℝ) (hr : 0 ≤ r) (x : V) :
    x ∈ box e r hr ↔ ∀ i, ‖e.repr x i‖ ≤ r := Iff.rfl
end GlobalTheory.JR.DualLattice
