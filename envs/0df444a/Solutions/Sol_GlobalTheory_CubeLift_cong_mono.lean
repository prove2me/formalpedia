-- Prove2me | solution 1 for GlobalTheory.CubeLift.cong_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:33.284104+00:00
-- url     : https://prove2.me/submissions/baf68a74-c2f0-489a-a7c0-ae072598b3fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_rd_mono
import Theorems.Thm_P2M_GlobalTheory_CubeLift_mem_cong__73390d79565c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.CubeLift
variable {A : Type} [CommRing A] {X Y W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup W]
namespace GlobalTheory.CubeLift
theorem _root_.solution {I I' : Ideal A} (h : I ≤ I') {u : (A[X])ˣ} (hu : u ∈ cong I) : u ∈ cong I' :=
  mem_cong'.2 (rd_mono h (mem_cong'.1 hu))
end GlobalTheory.CubeLift
